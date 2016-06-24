module GCM

open SBuffer
open GF128
open Cryptutils

val text_encrypt: list gf128 -> crypt -> gf128 -> gf128 -> Tot (list gf128)
let rec text_encrypt p aes k cnt =
  match p with
  | [] -> []
  | hd::tl -> (add hd (aes k cnt))::(text_encrypt tl aes k (incr cnt))

val encrypt: list gf128 -> crypt -> gf128 -> list gf128 -> list gf128 -> Tot (list gf128 * gf128)
let encrypt p aes k iv a =
  let h = aes k zero in
  let y_0 = match iv with
    | [] -> ghash h [] [] zero
    | hd::tl -> ghash h [] iv zero
    in
  let c = text_encrypt p aes k (incr y_0) in
  let t = add (ghash h a c zero) (aes k y_0) in
  (c, t)

val text_decrypt: list gf128 -> crypt -> gf128 -> gf128 -> list gf128
let rec text_decrypt c aes k cnt =
  match c with
  | [] -> []
  | hd::tl -> (add hd (aes k cnt))::(text_decrypt tl aes k (incr cnt))

exception FAIL_DECRYPT

val decrypt: list gf128 -> crypt -> gf128 -> list gf128 -> list gf128 -> gf128 -> list gf128
let decrypt c aes k iv a t =
  let h = aes k zero in
  let y_0 = match iv with
    | [] -> ghash h [] [] zero
    | hd::tl -> ghash h [] iv zero
    in
  let t' = add (ghash h a c zero) (aes k y_0) in
  if eq t t' then text_decrypt c aes k (incr y_0) else raise FAIL_DECRYPT
