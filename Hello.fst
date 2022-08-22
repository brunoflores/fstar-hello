module Hello


type vec (a:Type) : nat -> Type =
| Nil : vec a 0
| Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n+1)

(* a n and m are implicit arguments *)
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

let apply (a b : Type) f : (a -> b) -> (a -> b) = fun x -> f x
let compose (a b c : Type) f g : (b -> c) -> (a -> b) -> (a -> c) = fun x -> f (g x)

(* prove that 17 is >= 0 *)
let _ = 17 <: x : int {x >= 0}
let _ = assert (17 >= 0) (* static assertion *)

open FStar.Mul
let sqr_is_nat (x:int) : unit = assert (x * x >= 0) (* static assertion *)

let max x y = if x > y then x else y
let _ = assert (max 0 1 = 1)
let _ = assert (forall x y. max x y >= x /\
                       max x y >= y /\
                       (max x y = x \/ max x y = y))

(* CARE: assumptions *)
let sqr_is_pos (x:int) = assume (x <> 0); assert (x * x > 0)
(* Like assert, the type of assume p is unit *)
(* The term admit () type to anything: *)
let sqr_is_pos' (x:int) : y:nat{y > 0} = admit ()

type three =
| One_of_three : three
| Two_of_three : three
| Three_of_three : three
(* prove that they are distinct *)
let distinct = assert (One_of_three <> Two_of_three /\
                       Two_of_three <> Three_of_three /\
                       Three_of_three <> One_of_three)
(* prove that they are the only terms of the type *)
let exhaustive (x:three) = assert (x = One_of_three \/
                                   x = Two_of_three \/
                                   x = Three_of_three)
(* match like in OCaml *)
let is_one (x:three) : bool
= match x with
| One_of_three -> true
| _ -> false
(* Discriminator: for every constructor T of an inductive type t, F* generates
   a function name T? which test if a v:t matches T. *)
let three_as_int (x:three) : int
= if One_of_three? x then 1
  else if Two_of_three? x then 2
  else 3
(* Exhaustiveness checking in F* is a semantic check and can use the SMT solver: *)
let only_two_as_int (x:three { not (Three_of_three? x) }) : int
= match x with
| One_of_three -> 1
| Two_of_three -> 2

(* Tuple *)
type tup2 (a:Type) (b:Type) =
| Tup2 : fst:a -> snd:b -> tup2 a b
(* Project the components with a match: *)
let tup2_fst #a #b (x:tup2 a b) : a
= match x with
| Tup2 fst _ -> fst
(* Generated projectors: *)
let my_tup2 = Tup2 "Bruno" 88
let fst = Tup2?.fst my_tup2
let snd = Tup2?.snd my_tup2


(*
# Local Variables:
# compile-command: "fstar.exe hello.fst"
# End:
*)
