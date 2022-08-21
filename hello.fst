module Hello

type vec (a:Type) : nat -> Type =
| Nil : vec a 0
| Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n+1)

let rec append #a #n #m (v1:vec a n) (v2:vec a m)
: vec a (n+m)
= match v1 with
| Nil -> v2
| Cons hd tl -> Cons hd (append tl v2)

(* Reversing a vector does not change its length: *)
let rec reverse #a #n (v:vec a n)
: vec a n
= match v with
| Nil -> Nil
| Cons hd tl -> append (reverse tl) (Cons hd Nil)

(* Refinement type: show that the index i is less than the length of
   the vector: *)
let rec get #a #n (i:nat{i<n}) (v:vec a n) : a =
  let Cons hd tl = v in
  if i = 0 then hd
  else get (i-1) tl

type account = {processed : bool}
let processed = x:account{x.processed = true} (* boolean refinement type *)
(* processed is a subtype of account *)

(* How to use refinement subtyping to introduce and eliminate refinement
   types. *)

let incr = fun (x:int) -> x + 1
let incr' x = x + 1
let incr'' x = x + 1 <: int
let incr''' (x : int) : (y : int { y = x + 1}) = x + 1

let (/) (x : int) (divisor : int { divisor <> 0 }) = x / divisor

let id (a:Type) (x:a) : a = x
let _ : bool = id bool true
let _ :int = id int (-1)
let _ : nat = id nat 0
let _ : string = id string "hello"
let _ : int -> int = id (int -> int) (id int)

(*
# Local Variables:
# compile-command: "fstar.exe hello.fst"
# End:
*)
