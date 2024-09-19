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
| Addr : basic_type -> ident -> expr                      (* address *)
| Ref : basic_type -> expr -> expr                        (* allocation : ref t e allocates e of type t 
                                                             and returns the fresh address *)
| Deref : basic_type -> expr -> expr                      (* dereference : deref t e returns the value of type t 
                                                             present at location e *)
| Mexpr : expr -> expr -> expr                            (* assign value at a location l (l := e) 
                                                             assigns the evaluation of e to the reference cell l *)
| Run : expr -> expr                                      (* eliminate heap effect : [r1-> v1, ..., ern->vn] e 
                                                             reduces to e captures the essence of state isolation 
                                                             and reduces to a value discarding the heap *)
| Hexpr : heap -> expr -> expr                            (* heap effect *) 
| Lexpr : ident -> type -> expr -> expr -> expr           (* let binding *)
| Cond : expr -> expr -> expr -> expr                     (* if e then e else e *)
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

Fixpoint get (l : list (ident * expr)) (k : ident) : option expr :=
match l with 
| nil => None 
| v :: vm => if (k =? v.1)%positive then Some v.2 else get vm k
end.

(* Typing Rules *)
Inductive ty_expr : ty_context -> store_context -> expr -> type -> effect -> Type :=
(* Since the variable and constant evaluation produces no effect, 
   we are free to assume any arbitrary effect *)
| Ty_var : forall Gamma Sigma t x ef,
           get_ty Gamma x = Some t ->
           ty_expr Gamma Sigma (Var t x) t ef
| Ty_const_int : forall Gamma Sigma i ef,
                 ty_expr Gamma Sigma (Const (ConsInt i)) (Btype (Bprim Tint)) ef
| Ty_const_bool : forall Gamma Sigma b ef,
                  ty_expr Gamma Sigma (Const (ConsBool b)) (Btype (Bprim Tbool)) ef
| Ty_const_unit : forall Gamma Sigma ef,
                  ty_expr Gamma Sigma (Const (ConsUnit)) (Btype (Bprim Tunit)) ef
| Ty_abs : forall Gamma Gamma' Sigma n xs e t2 ef2 ef,
           extend_contexts Gamma xs = Gamma' ->
           ty_expr Gamma' Sigma e t2 ef2 ->
           ty_expr Gamma Sigma (Abs n xs e) (Ftype (unzip2 xs) n ef2 t2) ef
| Ty_app : forall Gamma Sigma e es ts n ef t1,
           ty_expr Gamma Sigma e (Ftype ts n ef t1) ef ->
           ty_exprs Gamma Sigma es ts ef ->
           ty_expr Gamma Sigma (App e n es) t1 ef
| Ty_addr : forall Gamma Sigma l t h ef,
            get_sty Sigma l = Some t -> 
            ty_expr Gamma Sigma (Addr t l) (Reftype h t) ef
| Ty_ref : forall Gamma Sigma e t h ef,
           ty_expr Gamma Sigma e (Btype t) ef->
           ty_expr Gamma Sigma (Ref t e) (Reftype h t) (Erow (Esingle (Hst h)) ef)
| Ty_deref : forall Gamma Sigma e t h ef,
             ty_expr Gamma Sigma e (Reftype h t) ef ->
             ty_expr Gamma Sigma (Deref t e) (Btype t) (Erow (Esingle (Hst h)) ef)
| Ty_mexpr : forall Gamma Sigma e1 t e2 h ef,
             ty_expr Gamma Sigma e1 (Reftype h t) ef ->
             ty_expr Gamma Sigma e2 (Btype t) ef ->
             ty_expr Gamma Sigma (Mexpr e1 e2) (Btype (Bprim Tunit)) (Erow (Esingle (Hst h)) ef)
| Ty_run : forall Gamma Sigma e t h ef, (* Need to add that h is not a free variable in Gamma and Sigma *)
           ty_expr Gamma Sigma e t (Erow (Esingle (Hst h)) ef) ->
           ty_expr Gamma Sigma (Run e) t ef
| Ty_hexpr : forall Gamma Sigma H e t h ef, (* FIX ME *)
             ty_expr Gamma Sigma e t ef ->
             ty_expr Gamma Sigma (Hexpr H e) t (Erow (Esingle (Hst h)) ef)
| Ty_let : forall Gamma Sigma x t e1 e2 ef Gamma' t',
           ty_expr Gamma Sigma e1 t Empty -> 
           extend_context Gamma x t = Gamma' ->
           ty_expr Gamma' Sigma e2 t' ef ->  
           ty_expr Gamma Sigma (Lexpr x t e1 e2) t' ef
| Ty_cond : forall Gamma Sigma e1 e2 e3 t ef1 ef2,
            ty_expr Gamma Sigma e1 (Btype (Bprim Tbool)) ef1 ->
            ty_expr Gamma Sigma e2 t ef2 ->
            ty_expr Gamma Sigma e3 t ef2 ->
            ty_expr Gamma Sigma (Cond e1 e2 e3) t (Erow ef1 ef2)
with ty_exprs : ty_context -> store_context -> list expr -> list type -> effect -> Prop :=
| Ty_nil : forall Gamma Sigma,
           ty_exprs Gamma Sigma nil [::(Btype(Bprim Tunit))] Empty
| Ty_cons : forall Gamma Sigma e es t ef ts efs,
            ty_expr Gamma Sigma e t ef ->
            ty_exprs Gamma Sigma es ts efs ->
            ty_exprs Gamma Sigma (e :: es) (t :: ts) (Erow ef efs).


Scheme ty_expr_exprs_rec := Induction for ty_expr Sort Prop
 with ty_exprs_expr_rec := Induction for ty_exprs Sort Prop.


(* State is made from heap and virtual map (registers to values) *)
Inductive state : Type :=
| State : heap -> vmap -> state.

Definition get_vmap (st : state) : vmap :=
match st with 
| State h vm => vm
end.

Definition get_heap (st : state) : heap :=
match st with 
| State h vm => h
end.

(* Substitution *)
Fixpoint subst (x:ident) (e':expr) (e:expr) : expr :=
match e with
| Var t y => if (x =? y)%positive then e' else e
| Const c => Const c
| _ => e
end.


(* Operational Semantics *)
Inductive sem_expr : state -> expr -> state -> expr -> Prop :=
| sem_var : forall st x t vm v,
            get_vmap st = vm ->
            get vm x = Some v ->
            sem_expr st (Var t x) st v.
            
            
            
