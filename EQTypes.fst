module EQTypes

// Definitional equality
type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n+1)

// A single step of computation suffices:
let conv_vec_0 (#a:Type) (v:vec a ((fun x -> x) 0))
  : vec a 0
  = v

// A step of computation followed by a step of integer arithmetic:
let conv_vec_1 (#a:Type) (v:vec a ((fun x -> x + 1) 0))
  : vec a 1
  = v

// Definitional equality applies everywhere:
let conv_int (x : (fun b -> if b then int else bool) true )
  : int
  = x + 1

// Propositional equality
// (provable equality)


// Extensional equality of functions

// Decidable equality
