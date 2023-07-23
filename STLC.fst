module STLC

type typ =
  | TUnit : typ
  | TArr : typ -> typ -> typ

let var = nat
type exp =
  | EUnit : exp
  | EVar : var -> exp
  | ELam : typ -> exp -> exp (* Using de Bruijin's representation so name of binder ignored. *)
  | EApp : exp -> exp -> exp

(* Formalising an Operational Semantics *)

let sub0 = var -> exp
let sub_beta0 (e:exp) : sub0 =
  fun (y:var) ->
    if y=0 then e (* substitute *)
    else EVar (y-1) (* shift -1 *)

let sub_inc0 : sub0 = fun y -> EVar (y+1)

[@@expect_failure [19;19]]
let rec subst0 (s:sub0) (e:exp) : exp
  = match e with
    | EUnit -> EUnit
    | EVar x -> s x
    | EApp e1 e2 -> EApp (subst0 s e1) (subst0 s e2)
    | ELam t e1 -> ELam t (subst0 (sub_elam0 s) e1)
and sub_elam0 (s:sub0) : sub0
  = fun y ->
      if y=0 then EVar y
      else subst0 sub_inc0 (s (y-1))

(* [sub true] is the type of renamings, substitutions that map variables to variables;
   [sub false] are substitutions that map at least one variable to a non-variable. *)
let sub (renaming:bool) =
  f:(var -> exp) {renaming <==> (forall x. EVar? (f x))}

(* [sub_inc] is a renaming: *)
let sub_inc : sub true = fun y -> EVar (y+1)

(* [sub_beta] is the analog of [sub_beta0], but with a type that tracks whether
   it is a renaming or not. *)
let sub_beta (e:exp) : sub (EVar? e)
  = let f =
      fun (y:var) ->
        if y=0 then e (* substitute *)
        else (EVar (y-1)) (* shift -1 *)
    in
    if not (EVar? e)
    then introduce exists (x:var). ~(EVar? (f x))
      with 0 and ();
    f

let bool_order (b:bool) = if b then 0 else 1
let is_var (e:exp) : int = if EVar? e then 0 else 1

let rec subst (#r:bool)
              (s:sub r)
              (e:exp)
  : Tot (e':exp {r ==> (EVar? e <==> EVar? e')})
        (decreases %[bool_order (EVar? e);
                     bool_order r;
                     1;
                     e])
  = match e with
    | EUnit -> EUnit
    | EVar x -> s x
    | EApp e1 e2 -> EApp (subst s e1) (subst s e2)
    | ELam t  e1 -> ELam t (subst (sub_elam s) e1)
and sub_elam (#r:bool) (s:sub r)
  : Tot (sub r)
        (decreases %[1;
                     bool_order r;
                     0;
                     EVar 0])
  = let f : var -> exp =
      fun y ->
        if y=0 then EVar y
        else subst sub_inc (s (y-1))
    in
    assert (not r ==> (forall x. ~(EVar? (s x)) ==> ~(EVar? (f (x+1)))));
    f

(* The inductive type [step] describes a single step of computation in
   a "small-step operational semantics".

   The type [step e e'] is a relation between an initial program [e] and a
   program [e'] that results after taking one step of computation on some
   sub-term of [e]. *)
type step : exp -> exp -> Type =
  (* Beta-reduction. *)
  | Beta :
      t:typ ->
      e1:exp ->
      e2:exp ->
      step (EApp (ELam t e1) e2) (subst (sub_beta e2) e1)

  (* Reduce the left subterm of [EApp e1 e2]. *)
  | AppLeft :
      #e1:exp ->
      e2:exp ->
      #e1':exp ->
      hst:step e1 e1' ->
      step (EApp e1 e2) (EApp e1' e2)

  (* Reduce the right subterm of [EApp e1 e2]. *)
  | AppRight :
      e1:exp ->
      #e2:exp ->
      #e2':exp ->
      hst:step e2 e2' ->
      step (EApp e1 e2) (EApp e1 e2')

(* The inductive relation [steps : exp -> exp -> Type] represents the transitive
   closure of [step]. *)
type steps : exp -> exp -> Type =
  | Single :
      #e0:exp ->
      #e1:exp ->
      step e0 e1 ->
      steps e0 e1

  | Many :
      #e0:exp ->
      #e1:exp ->
      #e2:exp ->
      step e0 e1 ->
      steps e1 e2 ->
      steps e0 e2

(* Type System *)

(* The type system is an inductively defined relation [typing g e t] between a:
     * typing environment [g:env], a partial map from variable indexes in a
       particular scope to their annotated types;
     * a program expressions [e:exp];
     * and its type [t:typ]. *)

(* A representation of typing environments as a total function from variable
   indexes [var] to [Some t] or [None]. *)
let env = var -> option typ
let empty : env = fun _ -> None
(* Extending an environment [g] associating a type [t] with a new variable
   at index 0 involves shifting up the indexes of all other variables in [g]
   by 1. *)
let extend (t:typ) (g:env)
  : env
  = fun y -> if y=0 then Some t
          else g (y-1)

noeq
type typing : env -> exp -> typ -> Type =
  (* The unit value [EUnit] has type [TUnit] in all environments. *)
  | TyUnit :
      #g:env ->
      typing g EUnit TUnit

  (* A variable [x] is well-typed only in an environment [g] that binds
     its type to [Some t], in which case, the program [EVar x] has type [t]. *)
  | TyVar :
      #g:env ->
      x:var {Some? (g x)} ->
      typing g (EVar x) (Some?.v (g x))

  (* A function literal [ELam t e1] has type [TArr t t'] in environment [g]
     when the body of the function [e1] has type [t'] in an environment that
     extends [g] with a binding for the new variable at type [t] (while shifting
     and retaining all other variables). *)
  | TyLam :
      #g:env ->
      t:typ ->
      #e1:exp ->
      #t':typ ->
      hbody:typing (extend t g) e1 t' ->
      typing g (ELam t e1) (TArr t t')

  (* Allows applying [e1] to [e2] only when [e1] has an arrow type and the
     argument [e2] has the type of the formal parameter of [e1] - the entire
     term has the return type of [e1]. *)
  | TyApp :
      #g:env ->
      #e1:exp ->
      #e2:exp ->
      #t11:typ ->
      #t12:typ ->
      h1:typing g e1 (TArr t11 t12) ->
      h2:typing g e2 t11 ->
      typing g (EApp e1 e2) t12

(* Progress *)

(* A well-typed non-unit or lambda term with no free variables can take a
   single step of computation. *)
let is_value (e:exp) : bool = ELam? e || EUnit? e
let rec progress (#e:exp { ~(is_value e) })
                 (#t:typ)
                 (h:typing empty e t)
  : (e':exp & step e e')
  = let TyApp #g #e1 #e2 #t11 #t12 h1 h2 = h in
    match e1 with
    | ELam t e1' -> (| subst (sub_beta e2) e1', Beta t e1' e2 |)
    | _          -> let (| e1', h1' |) = progress h1 in
                   (| EApp e1' e2, AppLeft e2 h1' |)

(* Preservation *)

let subst_typing #r (s:sub r) (g1:env) (g2:env) =
  x:var { Some? (g1 x) } -> typing g2 (s x) (Some?.v (g1 x))

let rec substitution (#g1:env)
                     (#e:exp)
                     (#t:typ)
                     (#r:bool)
                     (s:sub r)
                     (#g2:env)
                     (h1:typing g1 e t)
                     (hs:subst_typing s g1 g2)
  : Tot (typing g2 (subst s e) t)
        (decreases %[bool_order (EVar? e);
                     bool_order r;
                     e])
  = match h1 with
    | TyUnit -> TyUnit
    | TyVar x -> hs x
    | TyApp hfun harg -> TyApp (substitution s hfun hs) (substitution s harg hs)
    | TyLam tlam hbody ->
        let hs'' : subst_typing sub_inc g2 (extend tlam g2) =
          fun x -> TyVar (x+1)
        in
        let hs' : subst_typing (sub_elam s) (extend tlam g1) (extend tlam g2) =
          fun y -> if y=0 then TyVar y
                else substitution sub_inc (hs (y-1)) hs''
        in
        TyLam tlam (substitution (sub_elam s) hbody hs')

let substitution_beta #e #v #t_x #t #g
                      (h1:typing g v t_x)
                      (h2:typing (extend t_x g) e t)
  : typing g (subst (sub_beta v) e) t
  = let hs : subst_typing (sub_beta v) (extend t_x g) g =
      fun y -> if y=0 then h1
            else TyVar (y-1)
    in
    substitution (sub_beta v) h2 hs

(* Given a well-typed term satisfying [typing g e t] and [steps e e'], we
   would like to prove that [e'] has the same type as [e]. *)
let rec preservation_step #e #e' #g #t (ht:typing g e t) (hs:step e e')
  : typing g e' t
  = let TyApp h1 h2 = ht in
    match hs with
    | Beta tx e1' e2' -> substitution_beta h2 (TyLam?.hbody h1)
    | AppLeft e2' hs1 -> TyApp (preservation_step h1 hs1) h2
    | AppRight e1' hs2 -> TyApp h1 (preservation_step h2 hs2)

let rec preservation #e #e' #g #t (ht:typing g e t) (hs:steps e e')
  : Tot (typing g e' t)
        (decreases hs)
  = match hs with
    | Single s -> preservation_step ht s
    | Many s0 s1 ->
        let ht' = preservation_step ht s0 in
        preservation ht' s1
