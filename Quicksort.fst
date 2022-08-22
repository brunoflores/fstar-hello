module Quicksort

(* Proving quicksort: *)

(* Auxiliary functions: *)
let rec length #a (l:list a) : nat
= match l with
| [] -> 0
| _ :: tl -> 1 + length tl

let rec append #a (l1 l2:list a) : list a
= match l1 with
| [] -> l2
| hd :: tl -> hd :: append tl l2

(* Function to decide when a list of integers is sorted in increasing order *)
let rec sorted (l:list int) : bool
= match l with
| [] -> true
| [_] -> true
| x :: y :: xs -> x <= y && sorted (y :: xs)

(* Decide if a given element is in a list *)
let rec mem (#a:eqtype) (i:a) (l:list a) : bool
= match l with
| [] -> false
| hd :: tl -> hd = i || mem i tl

(* partition f l returns a pair of lists l1 and l2, a partitioning of the
   elements in l such that every element in l1 satisfies f and the elements in
   l2 do not. *)
let rec partition (#a:Type) (f:a -> bool) (l:list a)
: x:(list a & list a) { length (fst x) + length (snd x) = length l }
= match l with
| [] -> [], []
| hd :: tl ->
  let l1, l2 = partition f tl in
  if f hd then hd::l1, l2
  else l1, hd::l2

(* Want to prove the property (still a bit too weak):
   forall l. sorted (sort l) /\ (forall i. mem i l <==> mem i (sort l)) *)
(* One implementation: *)
let rec sort (l:list int)
: Tot (list int) (decreases (length l))
= match l with
| [] -> []
| pivot :: tl ->
  let hi, lo = partition (( <= ) pivot) tl in
  append (sort lo) (pivot :: sort hi)

(* Proving sort correct *)

(* Relate partition to mem.
   Prove what was left out in the intrinsic speficication of partition:
   All elements in l1 satisfy f, the elements in l2 do not, and every element
   in l appears in either l1 or l2. *)
let rec partition_mem (#a:eqtype) (f:(a -> bool)) (l:list a)
: Lemma (let l1, l2 = partition f l in
         (forall x. mem x l1 ==> f x) /\
         (forall x. mem x l2 ==> not (f x)) /\
         (forall x. mem x l = (mem x l1 || mem x l2)))
= match l with
| [] -> ()
| _ :: tl -> partition_mem f tl

(* Very specific to Quicksort: If l1 and l2 are already sorted, and
   partitioned by pivot, then slotting pivot in the middle of l1 and l2
   produces a sorted list. *)
let rec sorted_concat (l1:list int{sorted l1}) (l2:list int{sorted l2}) (pivot:int)
: Lemma (requires (forall y. mem y l1 ==> not (pivot <= y)) /\
                  (forall y. mem y l2 ==> pivot <= y))
        (ensures sorted (append l1 (pivot :: l2)))
= match l1 with
| [] -> ()
| _ :: tl -> sorted_concat tl l2 pivot

(* A simple property about append and mem *)
let rec append_mem (#t:eqtype) (l1 l2:list t)
: Lemma (ensures (forall a. mem a (append l1 l2) = (mem a l1 || mem a l2)))
= match l1 with
| [] -> ()
| _ :: tl -> append_mem tl l2

(* Put the pieces together for our top-level statement about the
   correctness of sort *)
let rec sort_correct (l: list int)
: Lemma (ensures (let m = sort l in
                  sorted m /\ (forall i. mem i l = mem i m)))
        (decreases (length l))
= match l with
| [] -> ()
| pivot :: tl ->
  let partition_fun = ( <= ) pivot in
  let hi, lo = partition partition_fun tl in
  sort_correct hi;
  sort_correct lo;
  partition_mem partition_fun tl;
  sorted_concat (sort lo) (sort hi) pivot;
  append_mem (sort lo) (pivot :: sort hi)

(* Annotated version *)
let sort_ok (l:list int) =
 let m = sort l in
 sorted m /\ (forall i. mem i l = mem i m)

let rec sort_correct_annotated (l:list int)
: Lemma (ensures sort_ok l)
        (decreases (length l))
= match l with
| [] -> ()
| pivot :: tl ->
  let partition_fun = ( <= ) pivot in
  let hi, lo = partition partition_fun tl in
  assert (length hi + length lo = length tl);

  sort_correct_annotated hi;
  assert (sort_ok hi);

  sort_correct_annotated lo;
  assert (sort_ok lo);

  partition_mem partition_fun tl;
  assert (forall i. mem i tl = mem i hi || mem i lo);
  assert (forall i. mem i hi ==> pivot <= i);
  assert (forall i. mem i lo ==> i < pivot);
  assert (sort l == (append (sort lo) (pivot :: sort hi)));

  sorted_concat (sort lo) (sort hi) pivot;
  assert (sorted (sort l));

  append_mem (sort lo) (pivot :: sort hi);
  assert (forall i. mem i l = mem i (sort l))

(* Just to demonstrate that we can avoid some code duplication by
   inserting Lemma calls in the implementation. *)
let rec sort_intrinsic (l:list int)
: Tot (m:list int {
         sorted m /\ (forall i. mem i l = mem i m)
       })
  (decreases (length l))
= match l with
| [] -> []
| pivot :: tl ->
  let hi, lo = partition (fun x -> pivot <= x) tl in

  (* Lemmas: *)
  partition_mem (fun x -> pivot <= x) tl;
  sorted_concat (sort_intrinsic lo) (sort_intrinsic hi) pivot;
  append_mem (sort_intrinsic lo) (pivot :: sort_intrinsic hi);

  append (sort_intrinsic lo) (pivot :: sort_intrinsic hi)
