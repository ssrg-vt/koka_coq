From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST.

Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness.

Inductive intsize : Type :=
  | I8: intsize
  | I16: intsize
  | I32: intsize
  | IBool: intsize.


(* FIX ME *)
Inductive effect : Type :=
| Exn : effect
| Div : effect. 

Inductive ktype : Type :=
| Tfun : list ktype -> effect -> ktype -> ktype (* (t1, ..., tn) -> e, rt *)
| Tint : intsize -> signedness -> ktype. 
