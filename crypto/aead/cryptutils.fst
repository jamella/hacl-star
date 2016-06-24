module Cryptutils

open GF128
open SBuffer

type crypt = gf128 -> gf128 -> Tot gf128
assume val aes_encrypt: crypt
