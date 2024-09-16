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
| ESeq : effect_atom -> effect -> effect   (* row of effects *)
| Evar : ident -> effect                   (* effect variable *).

Inductive signedness : Type :=
| Signed: signedness
| Unsigned: signedness.

Inductive intsize : Type :=
| I8: intsize
| I16: intsize
| I32: intsize
| IBool: intsize.

Inductive primitive_type : Type :=
| Tunit : primitive_type
| Tint : intsize -> signedness -> primitive_type
| Tbool : bool -> primitive_type.

Inductive basic_type : Type :=
| Bprim : primitive_type -> basic_type 
| Bpair : nat -> list basic_type -> basic_type    (* pair of types *).

Inductive type : Type :=
| Btype : basic_type -> type                      (* basic types *)
| Ftype : list type -> nat -> effect -> type      (* function/arrow type *)
| Reftype : effect -> basic_type -> type          (* reference type ref<h,int> *)
| Ptype : nat -> list type -> type                (* pair type *). 

