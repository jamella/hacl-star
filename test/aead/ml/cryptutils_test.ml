open Cryptutils

open Big_int
open Printf

let test name ans res = 
  printf "Test %s:\nExpect: %s\nResult: %s\n\n" name ans res

let test_to_hex_string ans dec bits =
  test ("Key_" ^ bits) ans (to_hex_string (big_int_of_string dec, big_int_of_string bits))
         
let _ =
  test_to_hex_string "000102030405060708090A0B0C0D0E0F" "5233100606242806050955395731361295" "128";
  test_to_hex_string "000102030405060708090A0B0C0D0E0F1011121314151617" "96533667595335344311200144916688449305687896108635671" "192";
  test_to_hex_string "000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F" "1780731860627700044960722568376592200742329637303199754547598369979440671" "256"

let test_to_nat ans hex =
  test "GF128" ans (string_of_big_int (to_nat hex))

let _ =
  test_to_nat "5233100606242806050955395731361295" "000102030405060708090A0B0C0D0E0F"

let test_aes_encrypt ans key text =
  test ("AES Encrypt " ^ (string_of_int (4 * String.length key))) ans (to_hex_string ((aes_encrypt (to_nat key, big_int_of_int (4 * String.length key)) (to_nat text)), big_int_of_string "128"))
              
let _ =
  test_aes_encrypt "69C4E0D86A7B0430D8CDB78070B4C55A" "000102030405060708090A0B0C0D0E0F" "00112233445566778899AABBCCDDEEFF";
  test_aes_encrypt "DDA97CA4864CDFE06EAF70A0EC0D7191" "000102030405060708090A0B0C0D0E0F1011121314151617" "00112233445566778899AABBCCDDEEFF";
  test_aes_encrypt "8EA2B7CA516745BFEAFC49904B496089" "000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F" "00112233445566778899AABBCCDDEEFF";
  test_aes_encrypt "0388dace60b6a392f328c2b971b2fe78" "00000000000000000000000000000000" "00000000000000000000000000000002"
