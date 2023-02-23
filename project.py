#!/usr/bin/env python3.10

import argparse
import pathlib
import sys
import typing
import urllib.parse
import socket
import secrets
from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature, encode_dss_signature
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey
from cryptography import x509
from cryptography.x509.oid import ExtensionOID
from cryptography.hazmat.primitives.asymmetric.ec import ECDSA , SECP256R1
from cryptography.hazmat.primitives.asymmetric import padding

import datetime


from cryptography.hazmat.primitives.asymmetric import x25519
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ec import EllipticCurvePublicKey
from cryptography.hazmat.primitives.asymmetric.rsa import RSAPublicKey
from public import pretty_hex, bytes_from_pretty, pretty_hex_dict
import hashlib 
from public import ProtocolVersion,HandshakeType,CipherSuite,ExtensionType,NamedGroup,ContentType,Error
from Crypto.Cipher import AES
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.hkdf import HKDFExpand
import hmac
import functools

import certifi
import simple_bson

# hack to allow relative import for all CLI call variants:
# * python -m <module>
# * python <file>.py
sys.path.append(str(pathlib.Path(__file__).parent))

def scaffolding_uint32(x: int) -> bytes: 
    #record-encode x as a 32-bit unsigned integer
    return x.to_bytes(4,"big")

def scaffolding_uint8(x: int) -> bytes: 
    #record-encode x as a 8-bit unsigned integer
    return x.to_bytes(1,"big")

def scaffolding_uint16(x: int) -> bytes: 
    #record-encode x as a 16-bit unsigned integer
    return x.to_bytes(2,"big")

def scaffolding_uint24(x: int) -> bytes:
    #record-encode x as a 24-bit unsigned integer
    return x.to_bytes(3,"big")

def scaffolding_vector_opaque(data: bytes) -> bytes:
    return data


def scaffolding_variable_vector_opaque(
    n: int,
    data: bytes,
) -> bytes:
    return len(data).to_bytes(n, "big") + data

def scaffolding_variable_vector_uint16(
    n: int,
    data: list[int],
) -> bytes:

    vardata=b""
    for i in data:
        vardata += scaffolding_uint16(i)
    return scaffolding_variable_vector_opaque(n,vardata)

        
def scaffolding_variable_vector_opaque_items(
    n: int,
    l: int,
    data: list[bytes],
) -> bytes:
  
    vardata = b""
    for i in data:
        vardata += scaffolding_variable_vector_opaque(l,i)
    return scaffolding_variable_vector_opaque(n,vardata)
    

def get_server_encoded(data:bytes):
    #server name (variable length, < (2^8)^2 == 65536)
    hostname = data
    hostname_len = scaffolding_uint16(len(data)) #(2 bytes)
    type = b'\x00\x00' # (2 bytes)
    entry_type = b'\x00' #DNS' indicates hostname (1 byte)
    extension_len = scaffolding_uint16((len(entry_type)+len(hostname_len)+len(hostname))) #(2 bytes)
    servername_len= scaffolding_uint16((len(entry_type)+len(hostname_len)+len(hostname)+len(extension_len)))

    
    return type + servername_len + extension_len + entry_type + hostname_len + hostname

class KeyShare:
    def __init__(self,hostname):
        self.type = b'\x00\x33' #(2 bytes)
        self.kex_group_ID =  b'\x00\x1d' # i.e. x25519 (2 bytes)
        self.public_key_len = 32 #i.e. 32 bytes (2 bytes)
        self.private_key = X25519PrivateKey.generate()
        """
        print(private_key.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption()))
        """
        self.public_key = self.private_key.public_key() #(32 bytes)
        self.key_share_len = scaffolding_uint16((len(self.kex_group_ID)+ self.public_key_len+2))#(+2 bytes of pk length 0020)
        self.extension_len = scaffolding_uint16((len(self.key_share_len)+len(self.kex_group_ID)+ self.public_key_len+2)) #(^2 bytes)
        self.public_bytes = self.public_key.public_bytes(encoding=serialization.Encoding.Raw,format=serialization.PublicFormat.Raw)
        #loaded_public_key = x25519.X25519PublicKey.from_public_bytes(public_bytes)

    def getKeyShare(self) -> bytes:
        return self.type + self.extension_len + self.key_share_len + self.kex_group_ID + b'\x00\x20'+ self.public_bytes
    def getPrivatekey(self) -> X25519PrivateKey:
        return self.private_key
    def getPublicKeyBytes(self) -> bytes:
        return self.public_bytes

class ClientHello:
    def __init__(self, hostname:bytes):
        self.client_version = b'\x03\x03'#disguise as TLS1.2
        self.client_random = secrets.token_bytes(32) #32 bytes of random client data
        self.random_session_length = secrets.randbelow(33)
        self.compatability_session_id= scaffolding_uint8(self.random_session_length)+ secrets.token_bytes(self.random_session_length)
        #unused_legacy_session_ID = b'\x00'
        self.cipher_suites = b'\x00\x02\x13\x01' #TLS_AES_128_GCM_SHA256 only
        self.unused_legacy_compression_methods =  b'\x01\x00'
        self.supported_algorithms = b'\x00\x0d\x00\x04\x00\x02\x04\x03'
        self.supported_versions= b'\x00\x2b\x00\x03\x02\x03\x04'+self.supported_algorithms #7 bytes total type, extension len, version len, version
        self.server_name = get_server_encoded (hostname)
        self.supported_groups = b'\x00\x0a\x00\x04\x00\x02\x00\x1d' #for simplicity, the project will only support a single curve x25519.
        self.key_share_info = KeyShare(hostname)
        self.key_share = self.key_share_info.getKeyShare()
        self.extensions_length = scaffolding_uint16((len(self.supported_versions)+len(self.supported_groups)+len(self.key_share)+len(self.server_name))) # sum of extension
        self.handshake = b'\x01' + scaffolding_uint24((len(self.server_name)+len(self.compatability_session_id)+len(self.client_version)+len(self.client_random) + len(self.cipher_suites)+ len(self.unused_legacy_compression_methods)+len(self.extensions_length)+len(self.supported_versions)+len(self.supported_groups)+len(self.key_share))) # +  uint24 of remaining message bytes
        self.record_header = b'\x16\x03\x01' + scaffolding_uint16((len(self.server_name)+len(self.compatability_session_id)+len(self.handshake)+len(self.client_version)+len(self.client_random) + len(self.cipher_suites)+ len(self.unused_legacy_compression_methods)+len(self.extensions_length)+len(self.supported_versions)+len(self.supported_groups)+len(self.key_share)))#Handshake beginning + uint16 of remaining message bytes
    def getSessionId(self) -> bytes:
        return self.compatability_session_id

    def getRandom(self) -> bytes:
        return self.client_random

    def returnHello(self) -> bytes:
        return  self.record_header + self.handshake + self.client_version + self.client_random + self.compatability_session_id + self.cipher_suites + self.unused_legacy_compression_methods + self.extensions_length + self.supported_versions + self.server_name + self.supported_groups + self.key_share
    
    def getClientKeyShareInfo(self) -> KeyShare:
        return self.key_share_info

       
def scaffolding_generate_client_hello(hostname: bytes) -> bytes:
    hello=ClientHello(hostname)
    return hello.returnHello()


def scaffolding_parse_record_type(record: bytes) -> bytes:
    for byte in record:
        value = byte.to_bytes(1,"big")
        for v in ContentType:
            if value==v.value:
                return value
        
def scaffolding_validate_server_hello(
    client_random: bytes, client_session_id: bytes, server_hello: bytes
) -> bool:

    server_hello_bytes = server_hello
    valid = True
    if scaffolding_parse_record_type(server_hello) == ContentType.HANDSHAKE.value:
        try:
            assert server_hello_bytes.index(ProtocolVersion.TLS12.value)==1 ## check 03 03 next
        except:
            return False
        hello_length_bytes = server_hello_bytes[3:5]
        hello_length = int.from_bytes(hello_length_bytes,'big')
        remaining_bytes = server_hello_bytes[5:]
        if (len(remaining_bytes)!= hello_length):
            print("Expected ", hello_length," bytes but got ", len(remaining_bytes))
            return False
        try:
            assert remaining_bytes.startswith(HandshakeType.SERVER_HELLO.value)

        except:
            return False
        if(int.from_bytes(remaining_bytes[1:4],'big')!= len(remaining_bytes[4:])):
            return False
        remaining_bytes = remaining_bytes[4:]
        try:
          assert remaining_bytes.startswith(ProtocolVersion.TLS12.value)
        except: 
            return False
        
        random=remaining_bytes[2:34]
        try:
            assert random != client_random
        except:
            print("Client random data should not be the same as server random data")
            return False    
        remaining_bytes = remaining_bytes[34:] # everything past client random - > session id data 
        session_id_length = int.from_bytes(remaining_bytes[0:1],'big')
        session_id = remaining_bytes[1:session_id_length+1]
        remaining_bytes= remaining_bytes[session_id_length+1:]
        try:
            assert session_id == client_session_id , "Session id mismatch"
        except:
                print("Session id invalid")
                return False
        cipher_suites=remaining_bytes[0:2]
        try:
            assert cipher_suites ==  CipherSuite.TLS_AES_128_GCM_SHA256.value, "Check the cipher suite"
        except:
            print("Cipher suite invalid")
            return False
        compression=remaining_bytes[2:3]
        try:
            assert compression == b'\x00'
        except:
            print("Compression invalid")
            return False
        remaining_bytes=remaining_bytes[3:]
        extension_length= remaining_bytes[0:2]
        extensions = remaining_bytes[2:]
        try:
            assert int.from_bytes(extension_length,'big') == len(extensions)
        except:
            print("Extension length invalid")
            return False
        remaining_bytes=remaining_bytes[2:]
        supported_versions = remaining_bytes[0:6]
        try:
            assert supported_versions == b'\x00\x2b\x00\x02\x03\x04'
        except:
            print("Supported versions invalid")
            return False
        remaining_bytes=remaining_bytes[6:]
        key_share=remaining_bytes[:2] 
    
        try:
            assert key_share == ExtensionType.KEY_SHARE.value
        except:
            print('key_share invalid')
            return False
        try:
            assert int.from_bytes(remaining_bytes[2:4],'big') == len(remaining_bytes[4:]),"incorrect keyshare length"
        except:
            print('key share length invalid')
            return False
        remaining_bytes=remaining_bytes[4:]
        curve = remaining_bytes[:2]
        try:
            assert curve == NamedGroup.X25519.value
        except:
            print('curve invalid')
            return False
        key_length = remaining_bytes[2:4]
        try:
            assert key_length==b'\x00\x20'
        except:
            print("incorrect key length")
            return False
        public_key= remaining_bytes[4:]
        try:
            assert int.from_bytes(key_length,'big') == len(public_key)
        except:
            print ("key lenghts don't match")
            return False
        return valid
    else:
        name=""
        for c in ContentType:
            if c.value == scaffolding_parse_record_type(server_hello):
                name = c.name
        print ('not of type handshake but type', name)
        valid = False
        return valid


def remove_record_header(hello_message: bytes)-> bytes: 
    to_hash = hello_message[5:]
    return to_hash

def scaffolding_transcript_hash_hellos(
    client_hello: bytes, server_hello: bytes
) -> bytes:
    
    client = remove_record_header(client_hello)
    server = remove_record_header(server_hello)

    return hashlib.sha256(client+server).digest()

def scaffolding_hkdf_extract(key: bytes, salt: bytes) -> bytes:
    #PRK = HMAC-Hash(salt, IKM)
    missing_salt=scaffolding_uint8(0) * 32
    if salt == b'':
        PRK=hmac.HMAC(missing_salt, digestmod=hashlib.sha256)
        PRK.update(key)
        return PRK.digest()
    else:
        PRK=hmac.HMAC(salt, digestmod=hashlib.sha256)
        PRK.update(key)
        return PRK.digest()

class HKDFLabel:
    def __init__(self,context:bytes, label:bytes, length:int):
        self.length = scaffolding_uint16(length)
        self.label = scaffolding_variable_vector_opaque(1,b"tls13 "+label)
        self.context = scaffolding_variable_vector_opaque(1,context)
    def getHKDFLabel(self)->bytes:
        return self.length + self.label + self.context

def scaffolding_hkdf_expand_label(
    secret: bytes, label: bytes, context: bytes, length: int
) -> bytes:

    hkdf_label = HKDFLabel(context,label,length)
    hkdf_label = hkdf_label.getHKDFLabel()
    hkdf = HKDFExpand( 
    algorithm=hashes.SHA256(),
    length=length,
    info=hkdf_label,
    )
    return hkdf.derive(secret)
    


class IncrementalKey(typing.TypedDict):
    iv: bytes
    key: bytes
    counter: int

def xor_bytes(data: typing.List[bytes]) -> bytes:
    return bytes(functools.reduce(lambda a, b: a ^ b, i) for i in zip(*data)) # copied from John Guevara ps1.py

def scaffolding_incrementing_key(iv: bytes, counter: int) -> bytes:

    encryption_nonce = xor_bytes((iv , counter.to_bytes(len(iv),"big")))
    return encryption_nonce

class KeyScheduleValues(typing.TypedDict):
    """
    Complete TLS key schedule
    Note all fields are optional here.
    In autograder we will only check whatever fields you actually
    return here. You can use this as a sanity check for the specific keys
    you are having issues with.
    """

    dh_key: typing.Optional[bytes]

    empty_hash: typing.Optional[bytes]
    early_secret: typing.Optional[bytes]

    handshake_derived: typing.Optional[bytes]
    handshake_secret: typing.Optional[bytes]

    client_handshake_secret: typing.Optional[bytes]
    server_handshake_secret: typing.Optional[bytes]

    client_handshake_key: typing.Optional[IncrementalKey]
    server_handshake_key: typing.Optional[IncrementalKey]

    master_derived: typing.Optional[bytes]
    master_secret: typing.Optional[bytes]

    client_app_secret: typing.Optional[bytes]
    server_app_secret: typing.Optional[bytes]

    client_app_key: typing.Optional[IncrementalKey]
    server_app_key: typing.Optional[IncrementalKey]

    exporter_secret: typing.Optional[bytes]
    resumption_secret: typing.Optional[bytes]

    """
    secret
        Secret to expand with the label
    label
        TLS label suffix for the expansion.
        Note this does not include "tls13 " prefix.
        It is just just the "Label" as defined in HkdfLabel in RFC.
        For example this will be "c hs traffic".
    context
        Expansion context. In some cases can be:
        * transcript hash up until that point in the handshake
        * fixed empty hash
        * empty (for iv+key calculation)
    length
        Different key schedule parameters will be of different length.
        This parameter specifies for how long to expand secret
        from the given parameters.
        Note we always use sha256 for this project.

    for the handshake, Secret refers to the handshake secret. for the symmetric session, it refers to the application secret.

    the master secret is then derived from the handshake secret, and that master secret is used to derive client and server application traffic secrets
             Salt 
01             0  context = hashlib.sha256(bytes:Message).digest() #Where message is the last item in second paranthesis 
02             |
03   IKM       v
04   PSK = b'\\x00'*32 -> scaffolding_hkdf_extract( PSK , b'') -> bytes: = early_secret
05             |
06             +-----> scaffolding_hkdf_expand_label( secret, label, context, length) -> bytes: = (early_secret, b"ext binder", b"") = binder_key
07             |                                                                                  (early_secret,  b"res binder", b"") = res_binder_key
08             |
09             +-----> scaffolding_hkdf_expand_label( secret, label, context, length) = (early_secret, b"c e traffic", client Hello) = client_early_traffic_secret
10             |                     
11             |
12             +-----> scaffolding_hkdf_expand_label( secret, label, context, length) = (early_secret, b"e exp master", client Hello)= early_exporter_master_secret
13             |                     
14             v
15       scaffolding_hkdf_expand_label( early_secret, b"derived", b"", 32) = (early_secret, b"derived", b"") = handshake_derived
16             |
17             v
18   dh_key -> scaffolding_hkdf_extract( dh_key , handshake_derived) = handshake_secret
19             |
20             +-----> scaffolding_hkdf_expand_label(handshake_secret, b"c hs traffic", context, 32) = (handshake_secret, b"c hs traffic",client Hello...server Hello)= client_handshake_secret # has incrementing key : ik
21             |                                                                                                                                         client_handshake_key = scaffolding_hkdf_expand_label(client_handshake_secret, b"key", b"", length) 
23             |                                                                                                                                         application_traffic_secret_N+1 = scaffolding_hkdf_expand_label(client_handshake_secret_N,"traffic upd", b"", Hash.length) -> keys: client_write_key = scaffolding_hkdf_expand_label(Secret, b"key", b"", key_length) & client_write_iv  = scaffolding_hkdf_expand_label(Secret, b"iv", b"", iv_length)
24             +-----> scaffolding_hkdf_expand_label( handshake_secret, b"s hs traffic", context, 32) = (handshake_secret, b"s hs traffic",client Hello...server Hello) = server_handshake_secret #ik
25             |                                                                                                                                          server_handshake_key = scaffolding_hkdf_expand_label(server_handshake_secret, b"key", b"", length)
26             |                                                                                                                                          application_traffic_secret_N+1 = scaffolding_hkdf_expand_label(server_handshake_secret_N,"traffic upd", b"", Hash.length) -> keys: server_write_key = scaffolding_hkdf_expand_label(Secret, b"key", b"", key_length) & server_write_iv  = scaffolding_hkdf_expand_label(Secret, b"iv", b"", iv_length)
27             v                                                                                                                                            
28      scaffolding_hkdf_expand_label(handshake_secret,  b"derived", empty_hash, 32) = (handshake_secret, b"derived", "") = master_derived
29             |
30             v
31   0 -> scaffolding_hkdf_extract (b'\x00' * 32 #check between this and 0, master_derived) = master_secret
32             |
33             +-----> scaffolding_hkdf_expand_label( master_secret, b"c ap traffic", context, 32) = (master_secret, b"c ap traffic", client Hello...server Finished) = client_app_secret 0#ik 
34             |                                                                                                                                           client_app_key = scaffolding_hkdf_expand_label(client_app_secret, b"key", b"", length)
35             |                                                                                                                                           application_traffic_secret_N+1 = scaffolding_hkdf_expand_label(client_app_secret_N,"traffic upd", b"", Hash.length)-> keys: client_write_key = scaffolding_hkdf_expand_label(Secret, b"key", b"", key_length) & client_write_iv  = scaffolding_hkdf_expand_label(Secret, b"iv", b"", iv_length)
36             |
37             +-----> scaffolding_hkdf_expand_label( secret, label, context, length) = (master_secret, b"s ap traffic", client Hello...server Finished) = server_app_secret 0#ik 
38             |                                                                                                                                           server_app_key = scaffolding_hkdf_expand_label(server_app_secret, b"key", b"", length)
39             |                                                                                                                                           application_traffic_secret_N+1 = scaffolding_hkdf_expand_label(server_app_secret_N,"traffic upd", b"", Hash.length) -> keys: server_write_key = scaffolding_hkdf_expand_label(Secret, b"key", b"", key_length) & server_write_iv  = scaffolding_hkdf_expand_label(Secret, b"iv", b"", iv_length)
40             |
41             +-----> scaffolding_hkdf_expand_label(master_secret, b"exp master", client Hello...server Finished) = (master_secret, b"exp master", client Hello...server Finished) = exporter_secret
42             |                    
43             |                    
44             |
45             +-----> scaffolding_hkdf_expand_label( secret, label, context, length) = (master_secret, b"res master",client Hello...client Finished)= resumption_secret
46                                   
47                                   
    """
def scaffolding_key_schedule(
    dh_key: bytes,
    client_server_hello_transcript: bytes,
    server_finished_transcript: bytes,
    client_finished_transcript: bytes,
) -> KeyScheduleValues:
    
    psk_disabled= b'\x00' * 32
    
    empty_hash =  hashlib.sha256(b"").digest()
    early_secret=  scaffolding_hkdf_extract(psk_disabled,b'') 

    handshake_derived = scaffolding_hkdf_expand_label (early_secret, b"derived", empty_hash, 32)
    handshake_secret = scaffolding_hkdf_extract(dh_key , handshake_derived)

    client_handshake_secret = scaffolding_hkdf_expand_label(handshake_secret, b"c hs traffic", client_server_hello_transcript, 32)
    server_handshake_secret = scaffolding_hkdf_expand_label(handshake_secret, b"s hs traffic", client_server_hello_transcript, 32)

    client_handshake_key_IV = scaffolding_hkdf_expand_label(client_handshake_secret, b"iv", b"", 12)
    client_handshake_key_IK = scaffolding_hkdf_expand_label(client_handshake_secret, b"key", b"", 16) 

    server_handshake_key_IV = scaffolding_hkdf_expand_label(server_handshake_secret, b"iv", b"", 12)
    server_handshake_key_IK = scaffolding_hkdf_expand_label(server_handshake_secret, b"key", b"", 16)

    client_handshake_key : IncrementalKey ={
        'iv' : client_handshake_key_IV,
        'key' : client_handshake_key_IK,
        'counter' : 0
    } 
    server_handshake_key : IncrementalKey ={
        'iv' : server_handshake_key_IV,
        'key' : server_handshake_key_IK,
        'counter' : 0
    }
  
    master_derived = scaffolding_hkdf_expand_label(handshake_secret,  b"derived", empty_hash, 32)
    master_secret = scaffolding_hkdf_extract (b'\x00'*32, master_derived)

    client_app_secret = scaffolding_hkdf_expand_label(master_secret, b"c ap traffic", server_finished_transcript, 32)
    server_app_secret =scaffolding_hkdf_expand_label(master_secret, b"s ap traffic", server_finished_transcript, 32)

    client_app_key_IV = scaffolding_hkdf_expand_label(client_app_secret, b"iv", b"", 12)
    client_app_key_IK = scaffolding_hkdf_expand_label(client_app_secret, b"key", b"", 16)


    server_app_key_IV = scaffolding_hkdf_expand_label(server_app_secret, b"iv", b"", 12)
    server_app_key_IK = scaffolding_hkdf_expand_label(server_app_secret, b"key", b"", 16)

    client_app_key : IncrementalKey ={
        'iv' : client_app_key_IV,
        'key' : client_app_key_IK,
        'counter' : 0
    } 
    server_app_key : IncrementalKey ={
        'iv' : server_app_key_IV,
        'key' : server_app_key_IK,
        'counter' : 0
    } 

    exporter_secret = scaffolding_hkdf_expand_label(master_secret, b"exp master", server_finished_transcript,32)
    resumption_secret = scaffolding_hkdf_expand_label(master_secret, b"res master",client_finished_transcript,32)


    key_scheduled_values: KeyScheduleValues = {
    
    'dh_key': dh_key,

    'empty_hash': empty_hash,
    'early_secret': early_secret ,

    'handshake_derived': handshake_derived,
    'handshake_secret': handshake_secret,

    'client_handshake_secret': client_handshake_secret,
    'server_handshake_secret': server_handshake_secret,

    'client_handshake_key': client_handshake_key,
    'server_handshake_key': server_handshake_key,

    'master_derived': master_derived,
    'master_secret': master_secret,

    'client_app_secret': client_app_secret,
    'server_app_secret': server_app_secret,

    'client_app_key': client_app_key,
    'server_app_key': server_app_key,

    'exporter_secret': exporter_secret ,
    'resumption_secret': resumption_secret
    }

    return key_scheduled_values

class FirstKeySchedule(typing.TypedDict):
    """
    First Key Schedule TLS key schedule
    """

    dh_key: typing.Optional[bytes]

    empty_hash: typing.Optional[bytes]
    early_secret: typing.Optional[bytes]

    handshake_derived: typing.Optional[bytes]
    handshake_secret: typing.Optional[bytes]

    client_handshake_secret: typing.Optional[bytes]
    server_handshake_secret: typing.Optional[bytes]

    client_handshake_key: typing.Optional[IncrementalKey]
    server_handshake_key: typing.Optional[IncrementalKey]

    master_derived: typing.Optional[bytes]
    master_secret: typing.Optional[bytes]

def first_key_schedule(
    dh_key: bytes,
    client_server_hello_transcript: bytes,
) -> FirstKeySchedule:
    
    psk_disabled= b'\x00' * 32
    
    empty_hash =  hashlib.sha256(b"").digest()
    early_secret=  scaffolding_hkdf_extract(psk_disabled,b'') 

    handshake_derived = scaffolding_hkdf_expand_label (early_secret, b"derived", empty_hash, 32)
    handshake_secret = scaffolding_hkdf_extract(dh_key , handshake_derived)

    client_handshake_secret = scaffolding_hkdf_expand_label(handshake_secret, b"c hs traffic", client_server_hello_transcript, 32)
    server_handshake_secret = scaffolding_hkdf_expand_label(handshake_secret, b"s hs traffic", client_server_hello_transcript, 32)

    client_handshake_key_IV = scaffolding_hkdf_expand_label(client_handshake_secret, b"iv", b"", 12)
    client_handshake_key_IK = scaffolding_hkdf_expand_label(client_handshake_secret, b"key", b"", 16) 

    server_handshake_key_IV = scaffolding_hkdf_expand_label(server_handshake_secret, b"iv", b"", 12)
    server_handshake_key_IK = scaffolding_hkdf_expand_label(server_handshake_secret, b"key", b"", 16)

    client_handshake_key : IncrementalKey ={
        'iv' : client_handshake_key_IV,
        'key' : client_handshake_key_IK,
        'counter' : 0
    } 
    server_handshake_key : IncrementalKey ={
        'iv' : server_handshake_key_IV,
        'key' : server_handshake_key_IK,
        'counter' : 0
    }
  
    master_derived = scaffolding_hkdf_expand_label(handshake_secret,  b"derived", empty_hash, 32)
    master_secret = scaffolding_hkdf_extract (b'\x00'*32, master_derived)

    first_key_schedule : FirstKeySchedule = {
    
    'dh_key': dh_key,

    'empty_hash': empty_hash,
    'early_secret': early_secret ,

    'handshake_derived': handshake_derived,
    'handshake_secret': handshake_secret,

    'client_handshake_secret': client_handshake_secret,
    'server_handshake_secret': server_handshake_secret,

    'client_handshake_key': client_handshake_key,
    'server_handshake_key': server_handshake_key,

    'master_derived': master_derived,
    'master_secret': master_secret
    }

    return first_key_schedule

class SescondKeySchedule(typing.TypedDict):
    client_app_secret: typing.Optional[bytes]
    server_app_secret: typing.Optional[bytes]

    client_app_key: typing.Optional[IncrementalKey]
    server_app_key: typing.Optional[IncrementalKey]

    exporter_secret: typing.Optional[bytes]
    resumption_secret: typing.Optional[bytes]

def second_key_schedule(master_secret:bytes, server_finished_transcript:bytes, client_finished_transcript:bytes ) -> SescondKeySchedule:

    client_app_secret = scaffolding_hkdf_expand_label(master_secret, b"c ap traffic", server_finished_transcript, 32)
    server_app_secret =scaffolding_hkdf_expand_label(master_secret, b"s ap traffic", server_finished_transcript, 32)

    client_app_key_IV = scaffolding_hkdf_expand_label(client_app_secret, b"iv", b"", 12)
    client_app_key_IK = scaffolding_hkdf_expand_label(client_app_secret, b"key", b"", 16)


    server_app_key_IV = scaffolding_hkdf_expand_label(server_app_secret, b"iv", b"", 12)
    server_app_key_IK = scaffolding_hkdf_expand_label(server_app_secret, b"key", b"", 16)

    client_app_key : IncrementalKey ={
        'iv' : client_app_key_IV,
        'key' : client_app_key_IK,
        'counter' : 0
    } 
    server_app_key : IncrementalKey ={
        'iv' : server_app_key_IV,
        'key' : server_app_key_IK,
        'counter' : 0
    } 

    exporter_secret = scaffolding_hkdf_expand_label(master_secret, b"exp master", server_finished_transcript,32)
    resumption_secret = scaffolding_hkdf_expand_label(master_secret, b"res master",client_finished_transcript,32)
    second_key_schedule : SescondKeySchedule = {

    'client_app_secret': client_app_secret,
    'server_app_secret': server_app_secret,

    'client_app_key': client_app_key,
    'server_app_key': server_app_key,

    'exporter_secret': exporter_secret ,
    'resumption_secret': resumption_secret
    }

    return second_key_schedule


   
def scaffolding_decrypt_record(
    data: bytes, iv: bytes, key: bytes, counter: int
) -> list[bytes]:
    record_type = b'\x17' # (1 byte)
    unused_legacy_protocol_version = b'\x03\x03' #(2 bytes)
    parsing_data = data
    decrypted_records = []
    instance = 0 
    #count = counter

    if scaffolding_parse_record_type(data) == ContentType.APPLICATION_DATA.value:
      
        while (len(parsing_data)>0):
            try:
                assert scaffolding_parse_record_type(parsing_data) == ContentType.APPLICATION_DATA.value
                assert parsing_data[1:3] == ProtocolVersion.TLS12.value
            
            except:
                print ("check protocol version/ record header on instance ", instance)
                
            length_bytes = parsing_data[3:5]
            record_data_length = int.from_bytes(parsing_data[3:5],'big')#(2 bytes)
            encrypted_application_data_ciphertext = parsing_data[5:5+record_data_length]  #(variable length)

            #authentication_tag 16 bytes for AES GCM
            #We feed nonce into the AES cipher as an IV to decrypt records. Note that the sequence number must be incremented after each record in the handshake is sent or recieved.

            nonce = scaffolding_incrementing_key(iv, counter)

            cipher = AES.new(key, AES.MODE_GCM, nonce=nonce) # from Pycryptodome docs
            cipher.update(record_type + unused_legacy_protocol_version + length_bytes) #per RFC
            

            plaintext= cipher.decrypt(encrypted_application_data_ciphertext[:-16])
            #print('decrypting ....' , count, pretty_hex(encrypted_application_data_ciphertext))
            cipher.verify(encrypted_application_data_ciphertext[-16:])
            counter = counter +1
            instance = instance+1
            parsing_data = parsing_data [5+record_data_length:] 
           
            decrypted_records.append(plaintext[-1:]+b'\x03\x03'+ scaffolding_variable_vector_opaque(2,plaintext[:-1]))
  
        return decrypted_records
    else:
        print (instance, "Not APPLICATION_DATA")

def scaffolding_decrypt_record_app(
    data: bytes, iv: bytes, key: bytes, counter: IncrementalKey
) -> list[bytes]:
    record_type = b'\x17' # (1 byte)
    unused_legacy_protocol_version = b'\x03\x03' #(2 bytes)
    parsing_data = data
    decrypted_records = []
    instance = 0 
    #count = counter

    if scaffolding_parse_record_type(data) == ContentType.APPLICATION_DATA.value:
      
        while (len(parsing_data)>0):
            try:
                assert scaffolding_parse_record_type(parsing_data) == ContentType.APPLICATION_DATA.value
                assert parsing_data[1:3] == ProtocolVersion.TLS12.value
            
            except:
                print ("check protocol version/ record header on instance ", instance)
            length_bytes = parsing_data[3:5]
            record_data_length = int.from_bytes(parsing_data[3:5],'big')#(2 bytes)
            encrypted_application_data_ciphertext = parsing_data[5:5+record_data_length]  #(variable length)

            #authentication_tag 16 bytes for AES GCM
            #We feed nonce into the AES cipher as an IV to decrypt records. Note that the sequence number must be incremented after each record in the handshake is sent or recieved.

            nonce = scaffolding_incrementing_key(iv, counter['counter'])

            cipher = AES.new(key, AES.MODE_GCM, nonce=nonce) # from Pycryptodome docs
            cipher.update(record_type + unused_legacy_protocol_version + length_bytes) #per RFC
            

            plaintext= cipher.decrypt(encrypted_application_data_ciphertext[:-16])
            
            cipher.verify(encrypted_application_data_ciphertext[-16:])

            counter['counter'] +=1
            instance = instance+1
            parsing_data = parsing_data [5+record_data_length:] 
           
            decrypted_records.append(plaintext[-1:]+b'\x03\x03'+ scaffolding_variable_vector_opaque(2,plaintext[:-1]))
  
        return decrypted_records
    else:
        print (instance, "Not APPLICATION_DATA")


def scaffolding_encrypt(data: bytes, iv: bytes, key: bytes, counter: int) -> bytes:

    ciphertext_length = (len(data)+17).to_bytes(2,'big') #length of plaintext inner type and tag
    record_header = b'\x17\x03\x03' + ciphertext_length # construct record header for this instance 
    inner_type = ContentType.APPLICATION_DATA.value 
    nonce = scaffolding_incrementing_key(iv, counter)
    cipher = AES.new(key, AES.MODE_GCM, nonce=nonce)
    cipher.update(record_header) # feed record header into AES
    ciphertext, tag = cipher.encrypt_and_digest(data+inner_type)

    return record_header + ciphertext + tag

def scaffolding_encrypt_app(data: bytes, iv: bytes, key: bytes, counter: IncrementalKey) -> bytes:

    ciphertext_length = (len(data)+17).to_bytes(2,'big') #length of plaintext inner type and tag
    record_header = b'\x17\x03\x03' + ciphertext_length # construct record header for this instance 
    inner_type = ContentType.APPLICATION_DATA.value 
    nonce = scaffolding_incrementing_key(iv, counter['counter'])
    cipher = AES.new(key, AES.MODE_GCM, nonce=nonce)
    cipher.update(record_header) # feed record header into AES
    ciphertext, tag = cipher.encrypt_and_digest(data+inner_type)
    counter['counter']+=1

    return record_header + ciphertext + tag

def encrypt_handshake(data: bytes, iv: bytes, key: bytes, counter: IncrementalKey) -> bytes:

    ciphertext_length = (len(data)+17).to_bytes(2,'big') #length of plaintext inner type and tag
    record_header = b'\x17\x03\x03' + ciphertext_length # construct record header for this instance 
    inner_type = ContentType.HANDSHAKE.value 
    nonce = scaffolding_incrementing_key(iv, counter['counter'])
    cipher = AES.new(key, AES.MODE_GCM, nonce=nonce)
    cipher.update(record_header) # feed record header into AES
    #print(pretty_hex(data+inner_type), 'ciphertext we encrypted')
    ciphertext, tag = cipher.encrypt_and_digest(data+inner_type)
    counter['counter'] +=1

    return record_header + ciphertext + tag

class TLSResponse(typing.TypedDict):
    data: bytes
    error: str

def tls13_http_get(
    *,
    path: bytes,
    ip: bytes,
    port: int,
    hostname: bytes,
    ca: bytes,
) -> TLSResponse:

    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.connect((ip,port))
    client_hello = ClientHello(hostname)
    client_session_id = client_hello.getSessionId()[1:]
    client_keyshare = client_hello.getClientKeyShareInfo()
    client_random = client_hello.getRandom()
    dh_key = b''

    sock.send(client_hello.returnHello())
    response = sock.recv(4096) #pretty_hex print to debug
    server_hello_length = int.from_bytes(response[3:5],'big')
    server_hello = response [:server_hello_length+5] #parse data size: record header + server_hello_length 
    extensions = response [server_hello_length+5:]
    encrypted_extensions = extensions[:38]
    server_hello_length = len(server_hello)

    if (scaffolding_validate_server_hello(client_random,client_session_id,server_hello) == True):
        #lets do DH
        server_pk = server_hello[-32:]
     
       
        server_loaded_public_key = x25519.X25519PublicKey.from_public_bytes(server_pk)
        dh_key = client_keyshare.getPrivatekey().exchange(server_loaded_public_key)
        client_server_hello_transcript = scaffolding_transcript_hash_hellos(client_hello.returnHello(),server_hello)

        first_ks = first_key_schedule(dh_key, client_server_hello_transcript)
        server_handshake_key=first_ks["server_handshake_key"]
        record = response[6+server_hello_length:] #chop server hello and 14 03 03 00 01 01 "middlebox compatibility mode" this record is sent to help disguise the session as a TLS 1.2 session.
      
        decrypted_record = scaffolding_decrypt_record_app(record,server_handshake_key['iv'],server_handshake_key['key'],server_handshake_key)
        decrypted_encrypted_extensions = decrypted_record[0][5:] 
    

        signature_length = int.from_bytes(decrypted_record[2][11:13],'big')
    

        #Load the certificates
        certificates =  decrypted_record[1][16:]
        certificates = certificates[:-2]

       
        first_cert_len= int.from_bytes(decrypted_record[1][13:16],'big')
        first = certificates [:first_cert_len]
        second_cert_length = int.from_bytes(certificates[first_cert_len+2:first_cert_len+5],'big')
        second = certificates [-second_cert_length:]
        cert = x509.load_der_x509_certificate(first) #leaf 
        cert2 = x509.load_der_x509_certificate(second) #inter

        
        #Verify the certificates
        ca_file =  x509.load_pem_x509_certificate(ca)

        try:
            ext = cert.extensions.get_extension_for_oid(ExtensionOID.SUBJECT_ALTERNATIVE_NAME)
            assert ext.value.get_values_for_type(x509.DNSName)[0] == hostname.decode()

        except:
            try:
                assert cert.subject.rfc4514_string()[3:] == hostname.decode()
            except: 
                tls_response: TLSResponse = {
                'data': b'',
                'error': Error.INVALID_HOSTNAME.value
                }
                sock.close()
                print('thhis one')
                return tls_response
        try:
            assert ca_file.issuer == cert2.issuer
            assert cert.issuer == cert2.subject
        except:       
            tls_response: TLSResponse = {
            'data': b"",
            'error': Error.BAD_CERTIFICATE.value
            }
            sock.close()
            return tls_response

        now = datetime.datetime.now()

        #verify we are not before not valid before 
        if (cert.not_valid_before < now) == False or (cert2.not_valid_before < now)== False:
            tls_response: TLSResponse = {
            'data': b'',
            'error': Error.BAD_CERTIFICATE_VALIDITY.value
            }
            sock.close()
            return tls_response

        #check we are not afer not valid after aka expired
        if (cert.not_valid_after > now) == False or (cert2.not_valid_after > now)==False:
            tls_response: TLSResponse = {
            'data': b'',
            'error': Error.BAD_CERTIFICATE_VALIDITY.value
            }
            sock.close()
            return tls_response
        

       #If certificate is valid so far lets verify the signature
        ecpk :  EllipticCurvePublicKey = cert.public_key()#.public_bytes(encoding=serialization.Encoding.DER,format=serialization.PublicFormat.SubjectPublicKeyInfo)
        rsa_inter_pk : RSAPublicKey = cert2.public_key() #.public_bytes(encoding=serialization.Encoding.PEM,format=serialization.PublicFormat.SubjectPublicKeyInfo)
        rsa_root_pk : RSAPublicKey = ca_file.public_key()
        signature = decrypted_record[2][-signature_length:]
      
        #The digital signature is then computed over the concatenation of:
        #A string that consists of octet 32 (0x20) repeated 64 times , #The context string# A single 0 byte which serves as the separator
        # The content that was signed against
        ec_content = (b'\x20'*64) + b'TLS 1.3, server CertificateVerify' + b'\x00' +  hashlib.sha256(remove_record_header(client_hello.returnHello())+ remove_record_header(server_hello) + decrypted_encrypted_extensions + remove_record_header(decrypted_record[1])).digest() #decrypted_record[1][9:676] first cert without record header

        
        try:
            assert rsa_inter_pk.verify(signature=cert.signature,data=cert.tbs_certificate_bytes,padding=padding.PKCS1v15(),algorithm=hashes.SHA256()) == None , 'check cert sig leaf'
            assert rsa_root_pk.verify(signature=cert2.signature,data=cert2.tbs_certificate_bytes,padding=padding.PKCS1v15(),algorithm=hashes.SHA256()) == None , 'check cert sig inter'
            assert ecpk.verify(signature, ec_content, ECDSA(hashes.SHA256())) == None , 'check sig certverify' 

        except:
            tls_response: TLSResponse = {
            'data': b"",
            'error': '<error:bad signature>'
            }

            sock.close()
            return tls_response

        #So far so good lets check the server finished : ServerFinished
        server_finished_HMAC = decrypted_record [3][-32:]
        s_finished_key = scaffolding_hkdf_expand_label(first_ks['server_handshake_secret'], b"finished", b"", 32)
        transcript_hash = hashlib.sha256(remove_record_header(client_hello.returnHello())+ remove_record_header(server_hello) + decrypted_encrypted_extensions + remove_record_header(decrypted_record[1]) + remove_record_header(decrypted_record[2])).digest()
        verify_server_finish_data =hmac.HMAC(s_finished_key, digestmod=hashlib.sha256)
        verify_server_finish_data.update(transcript_hash)
        assert verify_server_finish_data.digest() == server_finished_HMAC


        #Now that we have validated the server stuff : ClientFinished 
        server_finished = decrypted_record[3]
        client_change_cipher_spec = b'\x14\x03\x03\x00\x01\x01'
        client_handshake_key=first_ks["client_handshake_key"]
        c_finished_key = scaffolding_hkdf_expand_label(first_ks['client_handshake_secret'], b"finished", b"", 32)
        client_finished_transcript = hashlib.sha256(remove_record_header(client_hello.returnHello())+ remove_record_header(server_hello) + decrypted_encrypted_extensions + remove_record_header(decrypted_record[1]) + remove_record_header(decrypted_record[2]) + remove_record_header(server_finished) ).digest() 
        client_verify_data = hmac.HMAC(c_finished_key, digestmod=hashlib.sha256)
        client_verify_data.update(client_finished_transcript)

        #Then encrypt_handshake:
        client_finished_header = HandshakeType.FINISHED.value + scaffolding_uint24(len(client_verify_data.digest()))
        encrypted_client_fin = encrypt_handshake(client_finished_header+client_verify_data.digest(), client_handshake_key['iv'],client_handshake_key['key'],client_handshake_key)
    
        #Then send with change cipher spec to indicate we have changed to encrypted data 

        #After ClientFinished we receive some data
        sock.send(client_change_cipher_spec)
        sock.send(encrypted_client_fin)
        server_res = sock.recv(4096) #pretty_hex print to debug
        #print (pretty_hex(server_res),'server response to client finished : server ticket')
        client_finished_sent_transcript = hashlib.sha256(remove_record_header(client_hello.returnHello())+ remove_record_header(server_hello) + decrypted_encrypted_extensions + remove_record_header(decrypted_record[1]) + remove_record_header(decrypted_record[2]) + remove_record_header(server_finished) + (client_finished_header+client_verify_data.digest())).digest()
        second_ks = second_key_schedule(first_ks['master_secret'],client_finished_transcript,client_finished_sent_transcript)
   
        #We must decrypt this data with application secret key
        server_app_key = second_ks['server_app_key']
        decrypted_ticket = scaffolding_decrypt_record_app(server_res,server_app_key['iv'],server_app_key['key'],server_app_key)

        #Now lets send HTTP GET request to server

        request = b'GET '+path+b' HTTP/1.0\r\nHost: '+ hostname+b'\r\n\r\n'
        client_app_key = second_ks['client_app_key'] #lets get the client app key to encrypt application data 
        wrapped_req = scaffolding_encrypt_app(request,client_app_key['iv'],client_app_key['key'],client_app_key )
        sock.send(wrapped_req)
        server_app_data = sock.recv(4096)
        http_data= scaffolding_decrypt_record_app(server_app_data,server_app_key['iv'],server_app_key['key'],server_app_key)
        
        while scaffolding_parse_record_type(http_data[0]) == ContentType.HANDSHAKE.value:
            sock.send(wrapped_req)
            server_app_data = sock.recv(4096)
            http_data= scaffolding_decrypt_record_app(server_app_data,server_app_key['iv'],server_app_key['key'],server_app_key)

        tls_response: TLSResponse = {
        'data': http_data[0][5:],
        'error': ''
        }

        sock.close()
        return tls_response

    else:
        print ("not a valid server hello" )
        tls_response: TLSResponse = {
        'data': b"",
        'error': Error.BAD_TLS_VERSION.value
        }

        sock.close()
        return tls_response

print(tls13_http_get(
    path='/'.encode(),
    ip='127.0.0.1'.encode(),
    port=8443,
    hostname='cs-gy6903.nyu.edu'.encode(),
    ca=pathlib.Path('./nginx/certs/root.pem').read_bytes(),))

def main() -> int:

    parser = argparse.ArgumentParser("TLS1.3 basic client")

    def path_type(value: str) -> pathlib.Path:
        path = pathlib.Path(value).resolve()
        if not path.exists() or not path.is_file():
            return parser.error(f"{value!r} does not exist or is not a file")
        return path

    def url_type(value: str) -> urllib.parse.SplitResult:
        parsed = urllib.parse.urlsplit(value)
        if parsed.scheme != "https":
            return parser.error(f"{value!r} does not use https scheme")
        if not parsed.hostname:
            return parser.error(f"{value!r} does not have hostname")
        return parsed

    parser.add_argument("url", type=url_type, help="URL to send request to")
    parser.add_argument(
        "--cafile",
        type=path_type,
        default=certifi.where(),
        help="Path to CA cert file in PEM format",
    )
    parser.add_argument(
        "--ip", help="Do not resolve hostname but instead connect to this ip"
    )
    parser.add_argument(
        "-i", "--include", action="store_true", help="Include response http headers"
    )
    args = parser.parse_args()

    ca = args.cafile.read_bytes()

    url: urllib.parse.SplitResult = args.url
    assert url.hostname
    hostname: bytes = url.hostname.encode()
    ip: bytes = (args.ip or url.hostname).encode()
    port: int = url.port or 443
    path: bytes = (url.path or "/").encode()

    response = tls13_http_get(path=path, ip=ip, port=port, hostname=hostname, ca=ca)

    if response["error"]:
        print(response["error"])
        return 1

    data = response["data"].decode()

    if not args.include:
        data = data.split("\r\n\r\n", 1)[-1]

    print(data)
    return 0

if __name__ == "__main__":
    if sys.stdin.isatty():
        sys.exit(main())
    else:
        inputs = simple_bson.loads(sys.stdin.buffer.read())
        solutions = {
            k: globals()[k.split("__")[0]](**v)
            for k, v in inputs.items()
            if k in globals()
        }
        sys.stdout.buffer.write(simple_bson.dumps(solutions))