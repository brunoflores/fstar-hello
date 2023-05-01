module Merkle

// Preliminaries:

// Length-indexed strings.
// The type of strings of length n.
// An indexed type using refinement.
let lstring (n:nat) = s:string {String.length s == n}

// Concatenate strings.
let concat #n #m (s0 : lstring n) (s1 : lstring m) : lstring (n+m)
  = String.concat_length s0 s1;
    s0 ^ s1

// A parameter: length of the hash in characters.
assume
val hash_size : nat

// The type of a hashed value.
let hash_t  = lstring hash_size

// The hash function itself.
assume
val hash (m:string) : hash_t

// The type of resources stored in the tree - an alias for string.
let resource = string

// Defining the Merkle tree

// The type of Merkle tree has two indices, such that mtree n h is a tree
// of height n whose root node is associated with the hash h.
type mtree : nat -> hash_t -> Type =
  | L:
     res:resource ->
     mtree 0 (hash res)
  | N:
     #n:nat ->
     #hl:hash_t ->
     #hr:hash_t ->
     left: mtree n hl ->
     right: mtree n hr ->
     mtree (n+1) (hash (concat hl hr))

// A resource identifier is a path in the tree from the root to the leaf
// storing that resource. A path is just a list of booleans describing
// whether to descend left or right from a node.
let resource_id = list bool

// Access an element.
let rec get #h
            (ri : resource_id)
            (tree : mtree (List.length ri) h)
  : Tot resource (decreases ri)
  = match ri with
    | [] -> L?.res tree
    | b :: ri' ->
      if b then get ri' (N?.left tree)
      else get ri' (N?.right tree)

// The Prover

// Packages a resource with its id and hashes.
// A RES r ri hs is a proof of the membership of r in the tree at the
// location ri.
type resource_with_evidence : nat -> Type =
  | RES:
      res : resource ->
      ri : resource_id ->
      hashes : list hash_t {List.length ri == List.length hashes} ->
      resource_with_evidence (List.length ri)

// Retrieves data referenced by the path, together with the hashes
// of the sibling nodes along that path.
let rec get_with_evidence
  (#h : _)
  (rid : resource_id)
  (tree : mtree (List.length rid) h)
  : Tot (resource_with_evidence (List.length rid))
        (decreases rid)
  = match rid with
    | [] -> RES (L?.res tree) [] []
    | bit :: rid' ->
      let N #_ #hl #hr left right = tree in
      if bit then
        let p = get_with_evidence rid' left in
        RES p.res rid (hr :: p.hashes)
      else
        let p = get_with_evidence rid' right in
        RES p.res rid (hl :: p.hashes)

// The Verifier
// The checker of of claimed proofs.

// The function verify takes a resource with evidence, re-computes the root
// hash from the evidence presented, and then checks that that hash matches
// the root hash of a given tree (the tree itself is irrelevant).
let tail #n (p:resource_with_evidence n {n > 0})
  : resource_with_evidence (n-1)
  = let ri = List.Tot.tail p.ri in
    let hashes = List.Tot.tail p.hashes in
    assert (List.length ri = List.length hashes);
    RES p.res ri hashes

let rec compute_root_hash (#n:nat) (p:resource_with_evidence n) : hash_t
  = let RES d ri hashes = p in
    match ri with
    | [] -> hash p.res
    | bit :: ri' ->
      let h' = compute_root_hash (tail p) in
      if bit then hash (concat h' (List.Tot.hd hashes))
      else hash (concat (List.Tot.hd hashes) h')

let verify #h #n (p : resource_with_evidence n)
                 (tree : mtree n h)
  : bool
  = compute_root_hash p = h

// Correctness theorem:
// Using get_with_evidence's with compute_root_hash correctly
// reconstructs the root hash.
//
// The proof is by induction on the height of the tree
// (the length of resource id).
//
// Evidence constructed by a honest prover is accepted by our verifier.
let rec correctness (#h:hash_t)
                    (rid:resource_id)
                    (tree:mtree (List.length rid) h)
  : Lemma (ensures (verify (get_with_evidence rid tree) tree))
          (decreases rid)
  = match rid with
    | [] -> ()
    | bit :: rid' ->
      let N left right = tree in
      if bit then correctness rid' left
      else correctness rid' right
