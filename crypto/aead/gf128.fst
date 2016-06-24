module GF128

open FStar.Mul
open FStar.Seq
open FStar.UInt.UInt32

type uint32 = uint32

private val min: a:int -> b:int -> Tot (m:int{(m = a && m <= b) || (m = b && m <= a)})
let min a b = if a >= b then b else a
private val max: a:int -> b:int -> Tot (m:int{(m = a && m >= b) || (m = b && m >= a)})
let max a b = if a >= b then a else b

private val u_0: u:uint32{forall i. 0 <= i && i < 32 ==> get_bit u i = false}
let u_0 = int_to_uint32 0
private val u_1: uint32
let u_1 = int_to_uint32 1

#reset-options

private val concat: h:uint32 -> t:uint32 -> b:nat{b <= 32} -> Tot uint32
let concat h t b = (h ^<< b) ^| (t ^>> (32 - b))

private val concat_lemma_1: h:uint32 -> t:uint32 -> b:nat{b <= 32} -> i:nat{i < b} ->
  Lemma (requires True) (ensures get_bit (concat h t b) i = get_bit t (i - b + 32))
    [SMTPat (get_bit (concat h t b) i)]
let concat_lemma_1 h t b i = ()

private val concat_lemma_2: h:uint32 -> t:uint32 -> b:nat{b <= 32} -> i:nat{i >= b && i < 32} ->
  Lemma (requires True) (ensures get_bit (concat h t b) i = get_bit h (i - b))
  [SMTPat (get_bit (concat h t b) i)]
let concat_lemma_2 h t b i = ()

#reset-options

private val seq_get_bit: s:seq uint32 -> i:nat{i < 32 * length s} -> Tot bool
let seq_get_bit a i = get_bit (index a (i / 32)) (i % 32)

private val seq_shift_left: s:seq uint32 -> b:nat -> Tot (ns:seq uint32{length s = length ns}) (decreases (length s))
let rec seq_shift_left s b = match length s with
  | 0 -> s
  | l -> (* here satisfies constant time but seems not nessisary *)
      let ph = index s (max (l - 1 - b / 32) 0) in
      let pt = index s (max (l - 2 - b / 32) 0) in
      let h = if l - 1 - b / 32 < 0 then u_0 else ph in
      let t = if l - 2 - b / 32 < 0 then u_0 else pt in
      let n = concat h t (b % 32) in
      append (seq_shift_left (slice s 0 (l - 1)) b) (create 1 n)

private val seq_shift_left_lb_lemma_1: s:seq uint32{length s > 0} -> b:nat -> i:nat{i >= 32 * length s - 32 && i < b && i < 32 * length s} ->
  Lemma (requires True) (ensures seq_get_bit (seq_shift_left s b) i = false)
let seq_shift_left_lb_lemma_1 s b i = ()

assume val seq_shift_left_lb_lemma_2: s:seq uint32{length s > 0} -> b:nat -> i:nat{i >= 32 * length s - 32 && i >= b && i < 32 * length s} ->
  Lemma (requires True) (ensures seq_get_bit (seq_shift_left s b) i = seq_get_bit s (i - b))

#reset-options

private val seq_shift_left_lemma_1: s:seq uint32 -> b:nat -> i:nat{i < b && i < 32 * length s} ->
  Lemma (requires True) (ensures seq_get_bit (seq_shift_left s b) i = false) (decreases (length s))
let rec seq_shift_left_lemma_1 s b i =
  if i < 32 * length s - 32 then seq_shift_left_lemma_1 (slice s 0 (length s - 1)) b i
  else seq_shift_left_lb_lemma_1 s b i

private val seq_shift_left_lemma_2: s:seq uint32 -> b:nat -> i:nat{i >= b && i < 32 * length s} ->
  Lemma (requires True) (ensures seq_get_bit (seq_shift_left s b) i = seq_get_bit s (i - b)) (decreases (length s))
let rec seq_shift_left_lemma_2 s b i =
  if i < 32 * length s - 32 then seq_shift_left_lemma_2 (slice s 0 (length s - 1)) b i
  else seq_shift_left_lb_lemma_2 s b i

#reset-options

private val seq_shift_right: s:seq uint32 -> b:nat -> Tot (ns:seq uint32{length s = length ns}) (decreases (length s))
let rec seq_shift_right s b = match length s with
  | 0 -> s
  | l ->
      let pt = index s (min (b / 32) (l - 1)) in
      let ph = index s (min (b / 32 + 1) (l - 1)) in
      let t = if b / 32 >= l then u_0 else pt in
      let h = if b / 32 + 1 >= l then u_0 else ph in
      let n = concat h t (32 - b % 32) in
      append (create 1 n) (seq_shift_right (slice s 1 l) b)

assume val mod_lemma: a:nat -> b:nat{b > 0 && b <= a} -> Lemma (requires True) (ensures (a - b) % b = a % b)
assume val div_lemma: a:nat -> b:nat{b > 0 && b <= a} -> Lemma (requires True) (ensures (a - b) / b = a / b - 1)

private val seq_shift_right_bsc_lemma: s:seq uint32 -> b:nat -> i:nat{i >= 32 && i < 32 * length s} ->
  Lemma (requires True) (ensures seq_get_bit (seq_shift_right s b) i = seq_get_bit (seq_shift_right (slice s 1 (length s)) b) (i - 32))
let seq_shift_right_bsc_lemma s b i = mod_lemma i 32; div_lemma i 32

assume val seq_shift_right_fb_lemma_1: s:seq uint32{length s > 0} -> b:nat -> i:nat{i >= 32 * length s - b && i < 32} ->
  Lemma (requires True) (ensures seq_get_bit (seq_shift_right s b) i = false)
(*let seq_shift_right_fb_lemma_1 s b i = ()*)

assume val seq_shift_right_fb_lemma_2: s:seq uint32{length s > 0} -> b:nat -> i:nat{i < 32 * length s - b && i < 32} ->
  Lemma (requires True) (ensures seq_get_bit (seq_shift_right s b) i = seq_get_bit s (i + b))

#reset-options

private val seq_shift_right_lemma_1: s:seq uint32 -> b:nat -> i:nat{i >= 32 * length s - b && i < 32 * length s} ->
  Lemma (requires True) (ensures seq_get_bit (seq_shift_right s b) i = false) (decreases (length s))
let rec seq_shift_right_lemma_1 s b i =
  if length s = 0 then ()
  else if i < 32 then seq_shift_right_fb_lemma_1 s b i
  else admit()

private val seq_shift_right_lemma_2: s:seq uint32 -> b:nat -> i:nat{i < 32 * length s - b} ->
  Lemma (requires True) (ensures seq_get_bit (seq_shift_right s b) i = seq_get_bit s (i + b)) (decreases (length s))
let rec seq_shift_right_lemma_2 s b i = 
  if length s = 0 then ()
  else if i < 32 then seq_shift_right_fb_lemma_2 s b i
  else admit()

#reset-options

private val seq_logxor: s_1:seq uint32 -> s_2:seq uint32{length s_1 = length s_2} -> Tot (r:seq uint32{length r = length s_1 /\ length r = length s_2}) (decreases (length s_1))
let rec seq_logxor s_1 s_2 = match length s_1 with
  | 0 -> s_1
  | l -> append (seq_logxor (slice s_1 0 (l - 1)) (slice s_2 0 (l - 1))) (create 1 (logand (index s_1 (l - 1)) (index s_2 (l - 1))))

private val seq_logxor_lemma: s_1:seq uint32 -> s_2:seq uint32{length s_1 = length s_2} -> i:nat{i < 32 * length s_1} ->
  Lemma (requires True) (ensures seq_get_bit (seq_logxor s_1 s_2) i = (seq_get_bit s_1 i && seq_get_bit s_2 i))
let rec seq_logxor_lemma s_1 s_2 i = match length s_1 with 
  | 0 -> ()
  | l -> admit()

type gf128 = s:seq uint32{length s = 4}

val get_bit: a:gf128 -> b:nat{b < 128} -> Tot bool
let get_bit a b = seq_get_bit a b

val shift_left: gf128 -> nat -> Tot gf128
let shift_left a b = seq_shift_left a b

val shift_right: gf128 -> nat -> Tot gf128
let shift_right a b = seq_shift_right a b

val add: gf128 -> gf128 -> Tot gf128
let add a b = seq_logxor a b

private val u_r: uint32
let u_r = 
  admit();
  int_to_uint32 3774873600

private val r_for_mul: gf128
let r_for_mul = 
  let zero = create 4 u_0 in
  upd zero 0 u_r

val zero: gf128
let zero = create 4 u_0

val one: gf128
let one = upd zero 3 u_1

val eq: gf128 -> gf128 -> Tot bool
let eq a b = (index a 0 = index b 0) && (index a 1 = index b 1) && (index a 2 = index b 2) && (index a 3 = index b 3)


#reset-options "z3timeout 60"

private val mul_rec: x:gf128 -> y:gf128 -> b:nat{b <= 128} -> Tot gf128 (decreases b)
let rec mul_rec x y b =
  let zero = create 4 u_0 in
  if b = 0 then create 4 u_0 else
       let r_add = if (get_bit x 0) then create 4 u_0 else r_for_mul in
       let x_add = if (get_bit y (128 - b)) then x else create 4 u_0 in
       add x_add (mul_rec (add r_add (shift_right x 1)) (shift_right (shift_left x (129 - b)) (129 - b)) (b - 1))

#reset-options

val mul: gf128 -> gf128 -> Tot gf128
let mul x y = mul_rec x y 128

val incr: gf128 -> Tot gf128
let incr x = upd x 3 (add_mod (index x 3) u_1)

val shift_left_lemma_1: a:gf128 -> b:nat -> i:nat{i < b && i < 128} ->
  Lemma (requires True) (ensures get_bit (shift_left a b) i = false)
  [SMTPat (get_bit (shift_left a b) i)]
let shift_left_lemma_1 a b i = seq_shift_left_lemma_1 a b i

val shift_left_lemma_2: a:gf128 -> b:nat -> i:nat{i >= b && i < 128} ->
  Lemma (requires True) (ensures get_bit (shift_left a b) i = get_bit a (i - b))
  [SMTPat (get_bit (shift_left a b) i)]
let shift_left_lemma_2 a b i = seq_shift_left_lemma_2 a b i

val shift_right_lemma_1: a:gf128 -> b:nat -> i:nat{i >= 128 - b && i < 128} ->
  Lemma (requires True) (ensures get_bit (shift_right a b) i = false)
  [SMTPat (get_bit (shift_right a b) i)]
let shift_right_lemma_1 a b i = seq_shift_right_lemma_1 a b i

val shift_right_lemma_2: a:gf128 -> b:nat -> i:nat{i < 128 - b} ->
  Lemma (requires True) (ensures get_bit (shift_right a b) i = get_bit a (i + b))
  [SMTPat (get_bit (shift_right a b) i)]
let shift_right_lemma_2 a b i = seq_shift_right_lemma_2 a b i

#reset-options

open SBuffer

(* Using new version of uint
private val uint8s_prefix_to_gf128: a:uint8s{SBuffer.length a = 16} -> Tot gf128
let uint8s_prefix_to_gf128 a =
    let c0 = Seq.create 4 u_0 in
    let c00 = Seq.upd c0 0 (SBuffer.index a 0) in
    let c01 = Seq.upd c00 1 (SBuffer.index a 4) in
    let c02 = Seq.upd c01 2 (SBuffer.index a 8) in
    let c03 = Seq.upd c02 3 (SBuffer.index a 12) in
    let c1 = shift_left c03 8 in
    let c10 = Seq.upd c1 0 (Seq.index c1 0 ^+% SBuffer.index a 1) in
    let c11 = Seq.upd c10 1 (Seq.index c10 1 ^+% SBuffer.index a 5) in
    let c12 = Seq.upd c11 2 (Seq.index c11 2 ^+% SBuffer.index a 9) in
    let c13 = Seq.upd c12 3 (Seq.index c12 3 ^+% SBuffer.index a 13) in
    let c2 = shift_left c13 8 in
    let c20 = Seq.upd c2 0 (Seq.index c2 0 ^+% SBuffer.index a 2) in
    let c21 = Seq.upd c20 1 (Seq.index c20 1 ^+% SBuffer.index a 6) in
    let c22 = Seq.upd c21 2 (Seq.index c21 2 ^+% SBuffer.index a 10) in
    let c23 = Seq.upd c22 3 (Seq.index c22 3 ^+% SBuffer.index a 14) in
    let c3 = shift_left c23 8 in
    let c30 = Seq.upd c3 0 (Seq.index c3 0 ^+% SBuffer.index a 3) in
    let c31 = Seq.upd c30 1 (Seq.index c30 1 ^+% SBuffer.index a 7) in
    let c32 = Seq.upd c31 2 (Seq.index c31 2 ^+% SBuffer.index a 11) in
    let c33 = Seq.upd c32 3 (Seq.index c32 3 ^+% SBuffer.index a 15) in
    c33

private val uint8s_tail: a:uint8s{SBuffer.length a >= 16} -> St (t:uint8s{SBuffer.length a - 16 = SBuffer.length t})
let uint8s_tail a = sub a 0 (SBuffer.elength a - 16)
*)

(* This is just an offline version of ghash which need to be rewritten*)
private val ghash_rec: gf128 -> list gf128 -> list gf128 -> gf128 -> gf128 -> Tot gf128
let rec ghash_rec h a c l res =
  match a with
  | a_hd::a_tl ->
    ghash_rec h a_tl c l (mul h (add res (a_hd)))
  | [] -> match c with
    | c_hd::c_tl ->
      ghash_rec h [] c_tl l (mul h (add res (c_hd)))
    | [] -> mul h (add res l)
      
val ghash: gf128 -> list gf128 -> list gf128 -> gf128 -> Tot gf128
let ghash h a c l = 
  let zero = Seq.create 4 u_0 in
  ghash_rec h a c l zero

(*
private val ghash_rec: gf128 -> a:uint8s -> c:uint8s -> gf128 -> gf128 -> Tot gf128 (decreases SBuffer.length a + SBuffer.length c)
let rec ghash_rec h a c l res =


val ghash: gf128 -> uint8s -> uint8s -> gf128 -> Tot gf128
let ghash h a c l =
    let zero = create 4 u_0 in
    ghash_rec h a c l zero
*)
