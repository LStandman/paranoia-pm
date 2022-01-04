import sys
import os
from hashlib import pbkdf2_hmac
from getpass import getpass
from argparse import ArgumentParser
from secrets import token_bytes, choice
from io import StringIO
from enum import Enum
from cffi import FFI
from time import time_ns, monotonic_ns, time, monotonic
from msvcrt import getch
from functools import partial

# declarations
class SectionType(Enum):
    SERVICE = bytes.fromhex('AA')
    ACCOUNT = bytes.fromhex('55')
    PASSWORD = bytes.fromhex('7F')

# constants
KDF_RAND_SALT_SIZE_BYTES    = 31
KDF_NUM_ITERATIONS          = 400000
KDF_HASHING_ALGORITHM       = 'sha256'
AES_KEY_SIZE_BYTES          = 32
AES_IV_SIZE_BYTES           = 16
AES_BLOCK_SIZE_BYTES        = 16
AES_ENCRYPT                 = 1
AES_DECRYPT                 = 0
OPENSSL_KEY_SIZE_INTS       = 61
TEXT_ENCODING               = 'utf-8'
END_OF_RECORD               = '\n'
END_OF_VALUE                = '\\'
END_OF_DATA                 = '|'
FILE_HEADER_SIZE            = KDF_RAND_SALT_SIZE_BYTES

# globals
global done

expired_services = []
expired_accounts = {}
dirty_records = {}
password_changed = False

# definitions
def verbose(str):
    global verbosity
    if verbosity:
        print(str)

def clear():
    os.system("cls")

def caseless_getch(whitelist):
    char = getch().decode(TEXT_ENCODING)

    while char.lower() not in whitelist.lower():
        char = getch().decode(TEXT_ENCODING)

    return char.lower()

def init_libcrypto():
    global ffi
    global crypto

    # init libcrypto
    ffi = FFI()
    ffi.cdef(   """
                    int ERR_load_CRYPTO_strings(void);
                    int OPENSSL_init_crypto(uint64_t opts, const void *settings);
                    int AES_set_encrypt_key(const unsigned char *userKey, const int bits, void *key);
                    int AES_set_decrypt_key(const unsigned char *userKey, const int bits, void *key);
                    void AES_cbc_encrypt(const unsigned char *in, unsigned char *out, size_t length, const void *key, unsigned char *ivec, const int enc);
                """)
    crypto = ffi.dlopen("libcrypto-1_1-x64.dll")

    # Load the human readable error strings for libcrypto
    crypto.ERR_load_CRYPTO_strings()

    # Load all digest and cipher algorithms
    crypto.OPENSSL_init_crypto(ffi.cast("uint64_t", 0x0c), ffi.NULL)

def _aes_encrypt(key, iv, input, op):
    global ffi
    global crypto

    c_user_key = ffi.new("unsigned char[{}]".format(AES_KEY_SIZE_BYTES), key)
    c_key = ffi.new("unsigned int[{}]".format(OPENSSL_KEY_SIZE_INTS))

    if (op == AES_ENCRYPT):
        crypto.AES_set_encrypt_key(c_user_key, ffi.cast("int", AES_KEY_SIZE_BYTES * 8), c_key)
    elif (op == AES_DECRYPT):
        crypto.AES_set_decrypt_key(c_user_key, ffi.cast("int", AES_KEY_SIZE_BYTES * 8), c_key)
    else:
        raise ValueError("Invalid operation")

    c_iv = ffi.new("unsigned char[{}]".format(AES_IV_SIZE_BYTES), iv)
    c_in = ffi.new("unsigned char[{}]".format(len(input)), input)
    c_out = ffi.new("unsigned char[{}]".format(len(input)))

    crypto.AES_cbc_encrypt(c_in, c_out, ffi.cast("size_t", len(input)), c_key, c_iv, ffi.cast("int", op))

    return bytes(c_out)

def aes_encrypt(key, iv, plain):
    return _aes_encrypt(key, iv, plain, AES_ENCRYPT)

def aes_decrypt(key, iv, cipher):
    return _aes_encrypt(key, iv, cipher, AES_DECRYPT)

def serialize_registry(registry):
    global next_password_key
    global next_account_key
    global next_service_key

    def generate_pone(section_type):
        TIME_SEGMENT_BYTES = 4
        LAYER_SEGMENT_BYTES = 1
        RAND_SEGMENT_BYTES = AES_BLOCK_SIZE_BYTES - (TIME_SEGMENT_BYTES + LAYER_SEGMENT_BYTES)
    
        return section_type.value + int(time()).to_bytes(TIME_SEGMENT_BYTES, sys.byteorder) + token_bytes(RAND_SEGMENT_BYTES)

    def padded(data):
        return bytes(data, TEXT_ENCODING) + token_bytes((AES_BLOCK_SIZE_BYTES - (len(data) % AES_BLOCK_SIZE_BYTES)) % AES_BLOCK_SIZE_BYTES)

    def aes_size(data):
        return ((len(data) + AES_BLOCK_SIZE_BYTES - 1) // AES_BLOCK_SIZE_BYTES)

    def shuffle(registry):
        password_stream   = StringIO()
        accounts = [(service, account, password) for service in registry for account, password in registry[service].items()]
        p_offsets = {}

        p_offset   = 0
        
        # "[pass(S, A)]\n"
        # "[pass(S, A)]\n"
        # "[pass(S, A)]\n"
        # ...
        while (len(accounts)):
            account = choice(accounts)
            accounts.remove(account)

            p_offsets[(account[0], account[1])] = p_offset

            p_offset += password_stream.write("{}{}".format(account[2], END_OF_RECORD))

        yield password_stream.getvalue()

        account_stream   = StringIO()
        services = list(registry)
        a_offsets = {}

        a_offset   = 0
        
        # "[A = acc(S, N)]\\[addr(pass(S, A))]\n"
        # "[A = acc(S, N)]\\[addr(pass(S, A))]\n"
        # "[A = acc(S, N)]\\[addr(pass(S, A))]\n"
        # ...
        while (len(services)):
            service = choice(services)
            services.remove(service)

            a_offsets[service] = a_offset

            a_size = 0
            
            for account in sorted(registry[service]):
                a_size += account_stream.write("{}{}{}{}".format(account, END_OF_VALUE, format(p_offsets[(service, account)], 'x'), END_OF_RECORD))
        
            a_offset += a_size + account_stream.write("{}".format(END_OF_DATA))
            
        yield account_stream.getvalue()

        service_stream   = StringIO()

        # "[S = srv(N)]\\[addr(acc(S, 1))]\n"
        # "[S = srv(N)]\\[addr(acc(S, 1))]\n"
        # "[S = srv(N)]\\[addr(acc(S, 1))]\n"
        # ...
        for service in sorted(registry):        
            service_stream.write("{}{}{}{}".format(service, END_OF_VALUE, format(a_offsets[service], 'x'), END_OF_RECORD))
        
        service_stream.write("{}".format(END_OF_DATA))
        
        yield service_stream.getvalue()

    MAXIMUM_HEADER_BLOCKS = 1

    serialized = shuffle(registry)

    # instead of keeping the IV the first cipher block is used as the IV
    password_bytes  = generate_pone(SectionType.PASSWORD) + padded(next(serialized))
    account_bytes   = generate_pone(SectionType.ACCOUNT) + padded(next(serialized))
    service_txt     = next(serialized)

    header_stream   = StringIO()

    account_blocks = aes_size(account_bytes)
    header_stream.write("{}{}{}".format(END_OF_VALUE, format(account_blocks, 'x'), END_OF_RECORD))
    header_txt = header_stream.getvalue()
    
    service_blocks = aes_size(service_txt) + 1
    master_blocks = service_blocks
    master_blocks = aes_size(format(master_blocks, 'x') + header_txt + service_txt) + 1
    master_blocks = aes_size(format(master_blocks, 'x') + header_txt + service_txt) + 1

    if (master_blocks - service_blocks > MAXIMUM_HEADER_BLOCKS):
        raise ValueError("Large header sizes are not supported")

    master_bytes = generate_pone(SectionType.SERVICE) + padded(format(master_blocks, 'x') + header_txt + service_txt)

    return  aes_encrypt(next_service_key, token_bytes(AES_IV_SIZE_BYTES), master_bytes)     + \
            aes_encrypt(next_account_key, token_bytes(AES_IV_SIZE_BYTES), account_bytes)    + \
            aes_encrypt(next_password_key, token_bytes(AES_IV_SIZE_BYTES), password_bytes)

def gen_keyset(password, salt):
    yield pbkdf2_hmac(KDF_HASHING_ALGORITHM, bytes(password, TEXT_ENCODING), SectionType.PASSWORD.value + salt, KDF_NUM_ITERATIONS, dklen=AES_KEY_SIZE_BYTES)
    yield pbkdf2_hmac(KDF_HASHING_ALGORITHM, bytes(password, TEXT_ENCODING), SectionType.ACCOUNT.value + salt, KDF_NUM_ITERATIONS, dklen=AES_KEY_SIZE_BYTES)
    yield pbkdf2_hmac(KDF_HASHING_ALGORITHM, bytes(password, TEXT_ENCODING), SectionType.SERVICE.value + salt, KDF_NUM_ITERATIONS, dklen=AES_KEY_SIZE_BYTES)

def f_passwords(start, offset):
    global cipher_stream
    global current_password_key

    cipher_stream.seek(start + offset - (offset % AES_BLOCK_SIZE_BYTES))
    
    iv = cipher_stream.read(AES_BLOCK_SIZE_BYTES)
    cipher = cipher_stream.read(AES_BLOCK_SIZE_BYTES)
    
    plain = aes_decrypt(current_password_key, iv, cipher)
    passwords = plain[(offset % AES_BLOCK_SIZE_BYTES):].split(bytes(END_OF_RECORD, TEXT_ENCODING))

    password = passwords[0]
    
    # password may be split among more than 1 block
    while len(passwords) == 1:
        iv = cipher
        cipher = cipher_stream.read(AES_BLOCK_SIZE_BYTES)
        
        plain = aes_decrypt(current_password_key, iv, cipher)
        passwords = plain.split(bytes(END_OF_RECORD, TEXT_ENCODING))
        password += passwords[0]

    return password.decode(TEXT_ENCODING)

def f_iterator(start, offset, key, first_plain, function_gen, upto):
    global cipher_stream
    
    cipher_stream.seek(start + offset - (offset % AES_BLOCK_SIZE_BYTES))

    iv = cipher_stream.read(AES_BLOCK_SIZE_BYTES)
    cipher = cipher_stream.read(AES_BLOCK_SIZE_BYTES)

    plain = aes_decrypt(key, iv, cipher)
    records = plain[(offset % AES_BLOCK_SIZE_BYTES):].split(bytes(END_OF_RECORD, TEXT_ENCODING))

    # function saves any meta-data-records as a 'token' for the function generator and returns any remaining data-records
    res = first_plain(records)

    records = res[0]
    token   = res[1]

    while True:
        # the last record may be split
        # its parsing will be carried over to the next block
        for record in records[0:-1]:
            if len(record) and (record[0] == ord(END_OF_DATA)):
                return

            values = record.split(bytes(END_OF_VALUE, TEXT_ENCODING))
            name = values[0]
            offset = int(values[1], 16)

            # the record names are anum sorted
            # if the name is ordered after upto, we passed the matching records
            if (upto is not None):
                if (upto.lower() < name.decode(TEXT_ENCODING)[0:len(upto)].lower()):
                    return
                elif (upto.lower() > name.decode(TEXT_ENCODING)[0:len(upto)].lower()):
                    continue

            store = cipher_stream.tell()
            yield (name.decode(TEXT_ENCODING), function_gen(start, offset, token))
            cipher_stream.seek(store)

        remainder = records[-1]

        # don't carry over the last record if it is an end-of-data record
        if len(remainder) and (remainder[0] == ord(END_OF_DATA)):
            return
        
        iv = cipher
        cipher = cipher_stream.read(AES_BLOCK_SIZE_BYTES)
        
        plain = aes_decrypt(key, iv, cipher)
        records = plain.split(bytes(END_OF_RECORD, TEXT_ENCODING))
        records[0] = remainder + records[0]

    return

def f_accounts(start, offset, account_blocks, upto=None):
    global current_account_key

    return f_iterator(  start, 
                        offset, 
                        current_account_key, 
                        lambda records: (records, None), 
                        lambda start, offset, token : partial(f_passwords, start + (account_blocks * AES_BLOCK_SIZE_BYTES), offset), 
                        upto)

def f_services(upto=None):
    def first_plain(records):
        header = records[0].split(bytes(END_OF_VALUE, TEXT_ENCODING))
        service_blocks = int(header[0], 16)
        account_blocks = int(header[1], 16)

        return (records[1:], (service_blocks, account_blocks))

    global current_service_key

    return f_iterator(  FILE_HEADER_SIZE, 
                        0, 
                        current_service_key, 
                        first_plain,
                        # token[0] = service_blocks
                        # token[1] = account_blocks
                        lambda start, offset, token : partial(f_accounts, start + (token[0] * AES_BLOCK_SIZE_BYTES), offset, token[1]),
                        upto)

def m_password(service_name, account_name, gen):
    global dirty_records

    if (service_name in dirty_records) and (account_name in dirty_records[service_name]):
        return dirty_records[service_name][account_name]
    else:
        return gen()
    
def m_iterator(dirty_records, expired_records, gen_gen, upto):   
    if gen_gen is not None:
        record_gen = gen_gen(upto)

        try:
            while True:
                record = next(record_gen)
                record_name = record[0]

                if (record_name in expired_records):
                    continue
                
                is_dirty = False

                if record_name in dirty_records:
                    dirty_records.remove(record_name)
                    is_dirty = True

                yield (record_name, is_dirty, record[1])
        except StopIteration:
            pass

    for record_name in dirty_records:
        if (upto is not None) and (upto != record_name[0:len(upto)]):
            continue

        yield (record_name, True, None)

    return

def m_accounts(service_name, gen_gen, upto=None):
    global dirty_records

    return m_iterator(  list(dirty_records[service_name].keys()) if (service_name in dirty_records) else [],
                        expired_accounts[service_name] if (service_name in expired_accounts) else [],
                        gen_gen,
                        upto)

def m_services(upto=None):
    global dirty_records
    global is_new

    return m_iterator(  list(dirty_records.keys()),
                        expired_services,
                        None if is_new else f_services,
                        upto)

def get_pass(prompt='password:'):
    global is_blind

    if is_blind:
        return getpass(prompt)
    else:
        return input(prompt)

def browse(iter, num_items):
    remainder = next(iter)
    is_stopped = False
    index = 0
    cache = []
    
    while True:
        if (index < 0):
            return
        elif (index > len(cache)):
            return
        elif (index == len(cache)):
            if is_stopped:
                return
            else:
                page = []
            
                try:
                    for i in range(num_items):
                        page.append(remainder)
                        remainder = next(iter)
                except StopIteration:
                    is_stopped = True

                cache.append(page)

        can_prev = (index != 0)
        can_next = (not is_stopped or (index < len(cache) - 1))

        action = (yield (cache[index], can_prev, can_next))

        if (action == 'prev'):
            index -= 1
        elif (action == 'next') or (action is None):
            index += 1

def selector(header, file_iter, buttons):
    MAX_RECORDS_ON_SCREEN   = 9
    STATIC_LIST_LENGTH      = True
    DELIMITER               = '========================='
    
    page_iter = browse(file_iter, MAX_RECORDS_ON_SCREEN)

    res = next(page_iter)
    records = res[0]
    can_prev = res[1]
    can_next = res[2]

    while True:
        clear()
        whitelist = ''

        print(DELIMITER)
        print(header)
        print(DELIMITER)

        i = 0
        for item in records:
            i_str = str(i + 1)

            item_name = ('*' if item[1] else '') + item[0]
            print(i_str + '. ' + item_name)

            i += 1
            whitelist += i_str

        if STATIC_LIST_LENGTH:
            for i in range(i, MAX_RECORDS_ON_SCREEN):
                print('')

        print(DELIMITER)

        if can_next and can_prev:
            print('b. back           n. next')
            whitelist += 'bn'
        elif can_next:
            print('                  n. next')
            whitelist += 'n'
        elif can_prev:
            print('b. back                  ')
            whitelist += 'b'
        else:
            print('                         ')

        print(DELIMITER)
        print(DELIMITER)

        for button in buttons:
            print('{}. {}'.format(button[0], button[1]))
            whitelist += button[0]

        char = caseless_getch(whitelist)
        
        clear()

        if (char >= '1') and (char <= '9'):
            return (char, records[int(char) - 1])
        elif (char == 'b'):
            res = page_iter.send('prev')
        elif (char == 'n'):
            res = page_iter.send('next')
        else:
            return (char)

        records = res[0]
        can_prev = res[1]
        can_next = res[2]

def selector2(header, buttons2, buttons):
    MAX_RECORDS_ON_SCREEN   = 9
    STATIC_LIST_LENGTH      = True
    DELIMITER               = '========================='

    clear()
    whitelist = ''

    print(DELIMITER)
    print(header)
    print(DELIMITER)

    i = 0
    for item_name in buttons2:
        i_str = str(i + 1)

        print(i_str + '. ' + item_name)

        i += 1
        whitelist += i_str

    if STATIC_LIST_LENGTH:
        for i in range(i, MAX_RECORDS_ON_SCREEN):
            print('')

    print(DELIMITER)
    print('                         ')
    print(DELIMITER)
    print(DELIMITER)

    for button in buttons:
        print('{}. {}'.format(button[0], button[1]))
        whitelist += button[0]

    char = caseless_getch(whitelist)
    
    clear()

    return (char)

def rand_ascii_printables(length):
    res = ''

    for i in range(length):
        res += chr(choice(range(32, 127)))

    return res

def account_ctx(is_virgin, service_name, account_name, gen):
    global dirty_records

    header = 'acount {}//{}:'.format(service_name, account_name)

    buttons = [('c', 'change password'),
               ('r', 'randomize password'),
               ('d', 'delete account'),
               ('u', 'up'),
               ('q', 'quit')]

    buttons2 = ['password']

    while True:
        char = ('\0')

        if is_virgin:
            char = ('c')
        else:
            char = selector2(header, buttons2, buttons)
        
        if char[0] == 'q':
            done()
        elif (char[0] == 'c') or (char[0] == 'r'):
            if (char[0] == 'c'):
                password = get_pass()
            else:
                length = int(input("password length:"))
                password = rand_ascii_printables(length)
                
                print('password set to:')
                print(password)
                input()

            if service_name not in dirty_records:
                dirty_records[service_name] = {}

            dirty_records[service_name][account_name] = password

            is_virgin = False
            
            break
        elif char[0] == '1':
            print(m_password(service_name, account_name, gen))
            input()
        elif char[0] == 'd':
            if service_name not in expired_accounts:
                expired_accounts[service_name] = []

            expired_accounts[service_name].append(account_name)

            if (service_name in dirty_records) and (account_name in dirty_records[service_name]):
                del dirty_records[service_name][account_name]

            break
        elif char[0] == 'u':
            break
        else:
            raise ValueError("Unhandled key press")

    clear()

    return is_virgin

def service_ctx(is_virgin, service_name, gen):
    global dirty_records

    header = 'service {}:'.format(service_name)

    buttons = [#('s', 'search accounts'),
               ('a', 'add acoount'),
               ('d', 'delete service'),
               ('u', 'up'),
               ('q', 'quit')]


    while True:
        char = ('\0')

        if (char[0] == 's'):
            upto = input('search:')
            
            iter = m_accounts(service_name, gen, upto)
        else:
            iter = m_accounts(service_name, gen)

        if is_virgin:
            char = ('a')
        else:
            char = selector(header, iter, buttons)

        if char[0] == 'q':
            done()
        elif char[0] == 'u':
            break
        elif char[0] == 'a':
            account_name = input('new account:')

            is_virgin = account_ctx(True, service_name, account_name, None) and is_virgin
        elif char[0] == 'd':
            expired_services.append(service_name)

            if (service_name in dirty_records):
                del dirty_records[service_name]

            break
        elif (char[0] == 's'):
            continue
        elif (char[0] >= '1') and (char[0] <= '9'):
            account_ctx(False, service_name, char[1][0], char[1][2])
        else:
            raise ValueError("Unhandled key press")

    clear()

    return is_virgin

def master_ctx(is_virgin):
    global is_new
    global next_salt
    global next_password_key
    global next_service_key
    global next_account_key
    global password_changed

    header = 'services:'

    buttons = [#('s', 'search services'),
               ('a', 'add service'),
               ('c', 'change master password'),
               ('q', 'quit')]

    while True:
        char = ('\0')

        if (char[0] == 's'):
            upto = input('search:')
            
            iter = m_services(upto)
        else:
            iter = m_services()

        if is_virgin:
            char = ('a')
        else:
            char = selector(header, iter, buttons)
        
        if char[0] == 'q':
            done()
        elif char[0] == 'a':
            service_name = input('new service:')

            is_virgin = service_ctx(True, service_name, None) and is_virgin
        elif (char[0] == 'c'):
            clear()
            master_pass = getpass()
            clear()
            
            next_salt = token_bytes(KDF_RAND_SALT_SIZE_BYTES)
            keygen = gen_keyset(master_pass, next_salt)

            next_password_key   = next(keygen)
            next_account_key    = next(keygen)
            next_service_key    = next(keygen)

            del master_pass

            password_changed = True
        elif (char[0] == 's'):
            continue
        elif (char[0] >= '1') and (char[0] <= '9'):
            service_ctx(False, char[1][0], char[1][2])
        else:
            raise ValueError("Unhandled key press")

    clear()

    return is_virgin

def done():
    global cipher_stream
    global expired_accounts
    global expired_services
    global dirty_records

    clear()

    if len(expired_accounts) or len(expired_services) or len(dirty_records) or password_changed:
        print("save changes to file? (y/n)")
        ans = caseless_getch('yn')

        if ans == 'y':
            complete_record = {}

            service_iter = m_services()

            try:
                while True:
                    service = next(service_iter)

                    service_name = service[0]
                    account_gen = service[2]

                    complete_record[service_name] = {}

                    account_iter = m_accounts(service_name, account_gen)
            
                    try:
                        while True:
                            account = next(account_iter)

                            account_name = account[0]
                            password_gen = account[2]

                            password = m_password(service_name, account_name, password_gen)

                            complete_record[service_name][account_name] = password
                    except StopIteration:
                        pass
            except StopIteration:
                pass

            cipher_stream.seek(0)
            cipher_stream.write(next_salt)
            cipher_stream.write(serialize_registry(complete_record))
            cipher_stream.close()

    print('goodbye')
    sys.exit(0)

def serialization_test(file_name):
    global next_password_key
    global next_account_key
    global next_service_key
    global current_password_key
    global current_account_key
    global current_service_key
    global cipher_stream

    registry = {
                    'Cheetah Inc.'  : { 'sam'       : 'slay3r',
                                        'aaron'     : 'password1',
                                        'bob'       : 'T)Y$4b0b',
                                        'tyr'       : '@nd4eva',
                                        ''          : 'pattERcake'},
                    'Aardvark Co.'  : { ''          : 'evensteven',
                                        'beelzebub' : 'k1ngofh3ll',
                                        'clarice'   : 's!lent',
                                        'bigben'    : 'anykey',
                                        'baal'      : 'baldur'},
                    'ACME'          : { 'boby'      : 'hill44',
                                        'butthead'  : 'MTV2',
                                        '10101010'  : '00011100101111101110110110110111011101110',
                                        'yoyoma'    : 'yu-gi-oh!',
                                        'merlin'    : 'dear google'}
                }

    master_pass = 'ayy lmao'
    next_salt = token_bytes(KDF_RAND_SALT_SIZE_BYTES)

    keygen = gen_keyset(master_pass, next_salt)
    next_password_key   = next(keygen)
    next_account_key    = next(keygen)
    next_service_key    = next(keygen)

    cipher_stream = open(file_name, 'wb')

    cipher_stream.write(next_salt)
    cipher_stream.write(serialize_registry(registry))
    cipher_stream.close()

    input('serialization end')

    cipher_stream = open(file_name, 'rb')
    current_salt = cipher_stream.read(KDF_RAND_SALT_SIZE_BYTES)

    keygen2 = gen_keyset(master_pass, current_salt)
    current_password_key   = next(keygen2)
    current_account_key    = next(keygen2)
    current_service_key    = next(keygen2)

    iter1 = f_services()

    try:
        while True:
            service = next(iter1)
            
            iter2 = service[1]()

            print('|_' + service[0] + '')
            
            try:
                while True:
                    account = next(iter2)
                    password = account[1]()

                    print('\t|_' + account[0] + '')
                    print('\t\t|_' + password + '')
            except StopIteration:
                pass
    except StopIteration:
        pass

    input('deserialization end')

# main
# parse CLA into global variables
parser = ArgumentParser()
parser.add_argument("passdb", help="the password data-base file")
parser.add_argument("-n", "--new", action="store_true", help="create a new password data-base file")
parser.add_argument("-v", "--verbose", action="store_true", help="verbosity control")
parser.add_argument("-f", "--force", action="store_true", help="force operation")
parser.add_argument("-b", "--blind", action="store_true", help="hide all entered passwords")
parser.add_argument("-t", "--test", action="store_true", help="run a serialization test")
args = parser.parse_args()

verbosity   = args.verbose
is_new      = args.new
is_forced   = args.force
is_blind    = args.blind
is_test     = args.test
file_name   = args.passdb

init_libcrypto()

current_salt = b''

if (is_test):
    serialization_test(file_name)
    done()

if (is_new):
    print("creating data-base file \"{}\"...".format(file_name))

    try:
        cipher_stream = open(file_name, 'xb')
    except FileExistsError:
        if not is_forced:
            print("the file already exists. overwrite? (y/n)")
            ans = caseless_getch('yn')

            if ans == 'n':
                done()

            clear()
            print("overwriting data-base file \"{}\"...".format(file_name))

        cipher_stream = open(file_name, 'wb')
    is_virgin = True

else:
    print("opening file \"{}\"...".format(file_name))

    try:
        cipher_stream = open(file_name, 'r+b')
    except FileNotFoundError:
        print("file not found.")
        done()

    print("parsing metadata...")
    current_salt = cipher_stream.read(KDF_RAND_SALT_SIZE_BYTES)

    verbose("existing salt is " + current_salt.hex())
    is_virgin = False

clear()
master_pass = getpass()
clear()

next_salt = token_bytes(KDF_RAND_SALT_SIZE_BYTES)
keygen = gen_keyset(master_pass, next_salt)

next_password_key   = next(keygen)
next_account_key    = next(keygen)
next_service_key    = next(keygen)

if not is_new:
    keygen = gen_keyset(master_pass, current_salt)
    current_password_key    = next(keygen)
    current_account_key     = next(keygen)
    current_service_key     = next(keygen)

del master_pass

if False:
    complete_record = {}

    service_iter = m_services()

    try:
        while True:
            service = next(service_iter)

            service_name = service[0]
            account_gen = service[2]

            complete_record[service_name] = {}

            account_iter = m_accounts(service_name, account_gen)
            
            try:
                while True:
                    account = next(account_iter)

                    account_name = account[0]
                    password_gen = account[2]

                    password = password_gen()

                    complete_record[service_name][account_name] = password
            except StopIteration:
                pass
    except StopIteration:
        pass

    print(complete_record)

    while True:
        pass


master_ctx(is_new)

done()
