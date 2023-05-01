module Vec

type option a =
  | None : option a
  | Some : a -> option a

// One type constructor, one type parameter, one index (nat).
type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n+1)

// Getting an element from a vector
let rec get #a #n (i:nat{i < n}) (v:vec a n) : a
  = let Cons hd tl = v in
    if i=0 then hd
    else get (i-1) tl

// Concatenate vectors
val append (#a:Type) (#n #m:nat) (v1:vec a n) (v2:vec a m) : vec a (n+m)
let rec append #a #n #m (v1: vec a n) (v2:vec a m) : vec a (n+m)
  = match v1 with
    | Nil -> v2
    | Cons hd tl -> Cons hd (append tl v2)

// Can do without vectors. Observe:

let rec length #a (l:list a) : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

let rec get_lst #a (i:nat) (v:list a {i < length v}) : a
  = let hd :: tl = v in
    if i=0 then hd
    else get_lst (i-1) tl

let rec append_lst #a (l1 l2 : list a)
  : v:list a {length v == length l1 + length l2}
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append_lst tl l2
