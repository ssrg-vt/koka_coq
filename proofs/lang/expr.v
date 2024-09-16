From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST types Maps.

Inductive constant : Type :=
| ConsInt : int -> constant
| ConsBool : bool -> constant
| ConsUnit : constant.

(* The source language never exposes the heap binding construct hpφ.e directly to the user 
   but during evaluation the reductions on heap operations create heaps and use them. *)
Inductive expr : Type :=
| Var : type -> ident -> expr                             (* variable *)
| Const : constant -> expr                                (* constant *)
| Abs : nat -> list (ident * type) -> expr -> expr        (* f(x1,.., xn) = e *)
| App : expr -> nat -> list expr -> expr                  (* e en *)
| Addr : ident -> expr                                    (* address *)
| Ref : type -> expr -> expr                              (* allocation : ref t e allocates e of type t and returns the fresh address *)
| Deref : type -> expr -> expr                            (* dereference : deref t e returns the value of type t present at location e *)
| Run : expr -> expr                                      (* eliminate heap effect : [r1-> v1, ..., ern->vn] e reduces to e  
                                                             captures the essence of state isolation and reduces to a value discarding the heap *)
| Sexpr : expr -> expr                                    (* assign value at a location l (l := e) 
                                                             assigns the evaluation of e to the reference cell l *)
| Hexpr : ident -> expr -> expr                           (* heap effect *) (* ident should be heapmap *) 
| Lexpr : ident -> type -> expr -> expr                   (* let binding *)
| Cond : expr -> expr -> expr                             (* if e then e else e *).


(* A value is either:
- a constant
- an abstraction : as there is no rule for reduction for abstraction ;
- a memory location
*)

(* Values *)
Inductive value: expr -> Prop :=
| Vconst : forall c,
           value (Const c)
| Vabs : forall n xt e,
         value (Abs n xt e)
| Vloc : forall l,
         value (Addr l).

Definition heap := list (ident * expr).
Definition vmap := list (ident * expr).
         


(*(* Memory and Variable Map *)
Module M := FMapAVL.Make  Positive_as_OT.
Module P := WProperties_fun Positive_as_OT M.
Module F := P.F.

(* Map from ident to val: Map is build using a AVL tree for fast operations *)
Definition heap := M.t val. 
Definition vmap := M.t val.*)





