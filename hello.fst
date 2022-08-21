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

(*
# Local Variables:
# compile-command: "fstar.exe hello.fst"
# End:
*)
