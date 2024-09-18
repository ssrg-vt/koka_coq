From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST types Maps.

Inductive constant : Type :=
| ConsInt : Z -> constant
| ConsBool : bool -> constant
| ConsUnit : constant.

(* The source language never exposes the heap binding construct hpφ.e directly to the user 
   but during evaluation the reductions on heap operations create heaps and use them. *)
Inductive expr : Type :=
| Var : type -> ident -> expr                             (* variable *)
| Const : constant -> expr                                (* constant *)
| Abs : nat -> list (ident * type) -> expr -> expr        (* f(x1,.., xn) = e *)
| App : expr -> nat -> list expr -> expr                  (* e en *)
| Addr : type -> ident -> expr                            (* address *)
| Ref : type -> expr -> expr                              (* allocation : ref t e allocates e of type t 
                                                             and returns the fresh address *)
| Deref : type -> expr -> expr                            (* dereference : deref t e returns the value of type t 
                                                             present at location e *)
| Run : expr -> expr                                      (* eliminate heap effect : [r1-> v1, ..., ern->vn] e 
                                                             reduces to e captures the essence of state isolation 
                                                             and reduces to a value discarding the heap *)
| Sexpr : expr -> expr                                    (* assign value at a location l (l := e) 
                                                             assigns the evaluation of e to the reference cell l *)
| Hexpr : heap -> expr -> expr                            (* heap effect *) 
| Lexpr : ident -> type -> expr -> expr                   (* let binding *)
| Cond : expr -> expr -> expr                             (* if e then e else e *)
with heap : Type := 
| H : list (ident * expr) -> heap.

Scheme expr_heap_rec := Induction for expr Sort Set
 with heap_expr_rec := Induction for heap Sort Set.

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
| Vloc : forall t l,
         value (Addr t l).

Definition vmap := list (ident * expr).

(* Typing Rules *)
Inductive ty_expr : ty_context -> expr -> type -> effect -> Type :=
(* Since the variable and constant evaluation produces no effect, 
   we are free to assume any arbitrary effect *)
| Ty_var : forall Gamma t x ef,
           get_ty Gamma x = Some t ->
           ty_expr Gamma (Var t x) t ef
| Ty_const_int : forall Gamma i ef,
                 ty_expr Gamma (Const (ConsInt i)) (Btype (Bprim Tint)) ef
| Ty_const_bool : forall Gamma b ef,
                  ty_expr Gamma (Const (ConsBool b)) (Btype (Bprim Tbool)) ef
| Ty_const_unit : forall Gamma ef,
                  ty_expr Gamma (Const (ConsUnit)) (Btype (Bprim Tunit)) ef
| Ty_abs : forall Gamma Gamma' n xs e t2 ef2 ef,
           extend_contexts Gamma xs = Gamma' ->
           ty_expr Gamma' e t2 ef2 ->
           ty_expr Gamma (Abs n xs e) (Ftype (unzip2 xs) n ef2 t2) ef
| Ty_app : forall Gamma e es ts n ef t1,
           ty_expr Gamma e (Ftype ts n ef t1) ef ->
           ty_exprs Gamma es ts ef ->
           ty_expr Gamma (App e n es) t1 ef
(*| Ty_addr : forall Gamma t l,
            ty_expr Gamma (Addr t l) (Reftype *)
with ty_exprs : ty_context -> list expr -> list type -> effect -> Prop :=
| Ty_nil : forall Gamma,
           ty_exprs Gamma nil [::(Btype(Bprim Tunit))] Empty
| Ty_cons : forall Gamma e es t ef ts efs,
            ty_expr Gamma e t ef ->
            ty_exprs Gamma es ts efs ->
            ty_exprs Gamma (e :: es) (t :: ts) (Erow ef efs).


Scheme ty_expr_exprs_rec := Induction for ty_expr Sort Prop
 with ty_exprs_expr_rec := Induction for ty_exprs Sort Prop.





