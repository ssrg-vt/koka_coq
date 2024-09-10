From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST types Maps.

(* The source language never exposes the heap binding construct hpφ.e directly to the user 
   but during evaluation the reductions on heap operations create heaps and use them. *)
Inductive expr : Type :=
| Var : ident -> ktype -> expr                 (* variable *)
| Const : int -> expr                          (* constant (only allows integer *)
| HeapVar : ident -> ktype -> expr             (* heap variable *)
| Ref : expr -> ktype -> expr                  (* address of &r *)
| Deref : expr -> ktype -> expr                (* pointer dereference (!r) *).

Inductive instr : Type :=
| Abs : ident -> ktype -> instr -> instr       (* Lambda x : T. instr *)                   
| App : instr -> instr -> instr                (* Lambda x : T.instr.[x] *)
| Letb : ident -> instr -> instr -> instr      (* let x = i1 in i2 *)
| Cond : expr -> instr -> instr -> instr       (* if e then i1 else i2 *)
| Assgn : expr -> expr -> instr                (* lval := expr *)
| Seq : instr -> instr -> instr                (* i1;i2 *). 

(** A value is either:
- Vundef: denoting an arbitrary value, such as the value of an uninitialized variable
- an integer
- an abstraction : as there is no rule for reduction for abstraction ;
*)

(* Values *)
Inductive val: Type :=
| Vundef: val
| Vint: int -> val.
(*| Vabs : ident -> ktype -> instr -> val.*)

Definition heap := PMap.t val.
Definition vmap := PTree.t val.

Section EXPR.
Variable VM : vmap.
Variable H : heap.

(* Semantics of expressions *) Print PTree.
Inductive eval_expr : expr -> val -> Prop :=
| EVar : forall x t v,
         PTree.get x VM = Some v ->
         eval_expr (Var x t) v
| EConst : forall i,
               eval_expr (Const i) (Vint i).



