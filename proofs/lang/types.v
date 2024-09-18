From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST.

Inductive effect_atom : Type :=
| Exn : effect_atom               (* exception effect *)
| Div : effect_atom               (* divergence effect *)
| Hst : ident -> effect_atom      (* heap effect *).

Inductive effect : Type :=
| Empty : effect                           (* empty effect *)
| Esingle : effect_atom -> effect          (* single effect *)
| Erow : effect -> effect -> effect        (* row of effects *)
| Evar : ident -> effect                   (* effect variable *).

Inductive primitive_type : Type :=
| Tunit : primitive_type
| Tint : primitive_type
| Tbool : primitive_type.

Inductive basic_type : Type :=
| Bprim : primitive_type -> basic_type 
| Bpair : nat -> list basic_type -> basic_type    (* pair of types *).

Inductive type : Type :=
| Btype : basic_type -> type                              (* basic types *)
| Ftype : list type -> nat -> effect -> type -> type      (* function/arrow type *)
| Reftype : effect -> basic_type -> type                  (* reference type ref<h,int> *)
| Ptype : nat -> list type -> type                        (* pair type *). 


(* Equality on types *)
Definition eq_effect_atom (e1 e2 : effect_atom) : bool :=
match e1, e2 with 
| Exn, Exn => true 
| Div, Div => true 
| Hst id1, Hst id2 => (id1 =? id2)%positive
| _, _ => false
end.

Fixpoint eq_effect (e1 e2 : effect) : bool :=
match e1, e2 with 
| Empty, Empty => true 
| Esingle e, Esingle e' => eq_effect_atom e e'
| Erow e es, Erow e' es' => eq_effect e e' && eq_effect es es'
| Evar id1, Evar id2 => (id1 =? id2)%positive
| _, _ => false
end.

Definition eq_primitive_type (p1 p2 : primitive_type) : bool :=
match p1, p2 with 
| Tunit, Tunit => true 
| Tint, Tint => true
| Tbool, Tbool => true
| _, _ => false
end.   

Section Eq_basic_types.

Variable eq_basic_type : basic_type -> basic_type -> bool.

Fixpoint eq_basic_types (bs1 bs2 : list basic_type) : bool :=
match bs1, bs2 with 
| nil, nil => true 
| x :: xs, x' :: xs' => eq_basic_type x x' && eq_basic_types xs xs'
| _, _ => false
end.

End Eq_basic_types.

Fixpoint eq_basic_type (b1 b2 : basic_type) : bool :=
match b1, b2 with 
| Bprim p1, Bprim p2 => eq_primitive_type p1 p2
| Bpair n1 es1, Bpair n2 es2 => (n1 =? n2) && eq_basic_types eq_basic_type es1 es2
| _, _ => false
end.

Section Eq_types.

Variable eq_type : type -> type -> bool.

Fixpoint eq_types (t1 t2: list type) : bool :=
match t1, t2 with 
| nil, nil => true 
| x :: xs, x' :: xs' => eq_type x x' && eq_types xs xs'
| _, _ => false
end.

End Eq_types.

Fixpoint eq_type (t1 t2 : type) : bool :=
match t1,t2 with 
| Btype b1, Btype b2 => eq_basic_type b1 b2
| Ftype ts1 n1 e1 t1, Ftype ts2 n2 e2 t2 => 
  eq_types eq_type ts1 ts2 && (n1 =? n2)%nat && eq_effect e1 e2 && eq_type t1 t2
| Reftype e1 b1, Reftype e2 b2 => eq_effect e1 e2 && eq_basic_type b1 b2 
| Ptype n1 ts1, Ptype n2 ts2 => (n1 =? n2)%nat && eq_types eq_type ts1 ts2
| _, _ => false
end.


(* Typing context *)
Definition ty_context := list (ident * type).
Definition store_context := list (ident * type).

Fixpoint remove_var_ty (t : ty_context) (k : ident) (T : type) : ty_context :=
match t with 
| nil => nil 
| x :: xs => if ((k =? x.1)%positive && (eq_type T x.2)) then xs else x :: remove_var_ty xs k T
end.

Fixpoint is_mem (k : ident) (t : ty_context) : bool :=
match t with 
| nil => false
| x :: xs => if (k =? x.1)%positive then true else is_mem k xs
end.

Fixpoint extend_context (t : ty_context) (k : ident) (v : type) : ty_context := 
match t with 
| nil => [:: (k, v)]
| h :: t => if (k =? h.1)%positive then (k, v) :: t else h :: extend_context t k v
end. 

Fixpoint append_context (t1 : ty_context) (t2 : ty_context) : ty_context :=
match t2 with 
| nil => t1
| h :: t =>  append_context (extend_context t1 h.1 h.2) t
end.

Fixpoint get_ty (t : ty_context) (k : ident) : option type :=
match t with 
| nil => None 
| x :: xs => if (x.1 =? k)%positive then Some x.2 else get_ty xs k
end.

Fixpoint extend_contexts (t : ty_context) (ks : list (ident * type)) : ty_context := 
match ks with 
| nil => t
| k :: ks => extend_contexts (extend_context t k.1 k.2) ks
end. 

