module LemmasInduction

open FStar.Mul

let rec fib (a b n:nat) : Tot nat (decreases n)
  = match n with
    | 0 -> a
    | _ -> fib b (a+b) (n-1)

let fibonacci (n:nat) : nat = fib 1 1 n

type pos = n:nat{n >= 1}

let rec factorial (n:pos) : nat =
  if n=1 then 1
  else n * (factorial (n-1))

let _ = assert (factorial 5 = 120)

// A lemma is a function that always returns the ():unit value.
let rec factorial_is_positive (n:pos)
  : u:unit{factorial n > 0}
  = if n = 1 then ()
    else factorial_is_positive (n-1)

// Special syntax for lemmas:
let rec factorial_is_pos (x:pos)
  : Lemma (requires x >= 0)
          (ensures factorial x > 0)
  = if x = 1 then ()
    else factorial_is_pos (x-1)

let rec factorial_is_greater_than_arg (x:int)
  : Lemma (requires x > 2)
          (ensures factorial x > x)
  = if x = 3 then ()
    else factorial_is_greater_than_arg (x-1)

// By induction on n:nat{n >= 2}
let rec fibonacci_is_greater_than_arg (n:nat{n >= 2})
  : Lemma (ensures fibonacci n >= n)
  = if n <= 3 then ()
    else (
      admit ()
      // fibonacci_is_greater_than_arg (n-1);
      // fibonacci_is_greater_than_arg (n-2)
    )

let rec append #a (l1 l2 : list a) : list a
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2

let rec length #a (l : list a) : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

val app_length (#a:Type) (l1 l2 : list a)
  : Lemma (length (append l1 l2) = length l1 + length l2)

let rec app_length #a l1 l2
  = match l1 with
    | [] -> ()
    | _ :: tl -> app_length tl l2

// Instrinsic vs extrinsic
let rec reverse #a (l:list a) : list a
  = match l with
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd]

// Proving that list reverse is involutive
val rev_involutive (#a:Type) (l:list a)
  : Lemma (reverse (reverse l) == l)

let snoc l h = append l [h] // Add an element to the end of the list
let rec snoc_cons #a (l:list a) (h:a)
  : Lemma (reverse (snoc l h) == h :: reverse l)
  = match l with
    | [] -> ()
    | hd :: tl -> snoc_cons tl h

let rec rev_involutive #a (l:list a)
  = match l with
    | [] -> ()
    | hd :: tl ->
      rev_involutive tl;
      snoc_cons (reverse tl) hd
