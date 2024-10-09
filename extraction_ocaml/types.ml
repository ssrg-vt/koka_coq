
type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y



type positive =
| XI of positive
| XO of positive
| XH

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')
 end

module Pos =
 struct
  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)
 end

type ident = positive

type effect_label =
| Exn
| Div
| Hst of ident

type effect =
| Empty
| Esingle of effect_label
| Erow of effect * effect
| Evar of ident

type primitive_type =
| Tunit
| Tint
| Tbool

type basic_type =
| Bprim of primitive_type
| Bpair of nat * basic_type list

type type0 =
| Btype of basic_type
| Ftype of type0 list * nat * effect * type0
| Reftype of ident * basic_type
| Ptype of nat * type0 list

(** val eq_effect_label : effect_label -> effect_label -> bool **)

let eq_effect_label e1 e2 =
  match e1 with
  | Exn -> (match e2 with
            | Exn -> true
            | _ -> false)
  | Div -> (match e2 with
            | Div -> true
            | _ -> false)
  | Hst id1 -> (match e2 with
                | Hst id2 -> Pos.eqb id1 id2
                | _ -> false)

(** val eq_effect : effect -> effect -> bool **)

let rec eq_effect e1 e2 =
  match e1 with
  | Empty -> (match e2 with
              | Empty -> true
              | _ -> false)
  | Esingle e ->
    (match e2 with
     | Esingle e' -> eq_effect_label e e'
     | _ -> false)
  | Erow (e, es) ->
    (match e2 with
     | Erow (e', es') -> (&&) (eq_effect e e') (eq_effect es es')
     | _ -> false)
  | Evar id1 -> (match e2 with
                 | Evar id2 -> Pos.eqb id1 id2
                 | _ -> false)

(** val eq_primitive_type : primitive_type -> primitive_type -> bool **)

let eq_primitive_type p1 p2 =
  match p1 with
  | Tunit -> (match p2 with
              | Tunit -> true
              | _ -> false)
  | Tint -> (match p2 with
             | Tint -> true
             | _ -> false)
  | Tbool -> (match p2 with
              | Tbool -> true
              | _ -> false)

(** val eq_basic_types :
    (basic_type -> basic_type -> bool) -> basic_type list -> basic_type list
    -> bool **)

let rec eq_basic_types eq_basic_type0 bs1 bs2 =
  match bs1 with
  | [] -> (match bs2 with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs ->
    (match bs2 with
     | [] -> false
     | x' :: xs' ->
       (&&) (eq_basic_type0 x x') (eq_basic_types eq_basic_type0 xs xs'))

(** val eq_basic_type : basic_type -> basic_type -> bool **)

let rec eq_basic_type b1 b2 =
  match b1 with
  | Bprim p1 ->
    (match b2 with
     | Bprim p2 -> eq_primitive_type p1 p2
     | Bpair (_, _) -> false)
  | Bpair (n1, es1) ->
    (match b2 with
     | Bprim _ -> false
     | Bpair (n2, es2) ->
       (&&) (Nat.eqb n1 n2) (eq_basic_types eq_basic_type es1 es2))

(** val eq_types :
    (type0 -> type0 -> bool) -> type0 list -> type0 list -> bool **)

let rec eq_types eq_type0 t1 t2 =
  match t1 with
  | [] -> (match t2 with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs ->
    (match t2 with
     | [] -> false
     | x' :: xs' -> (&&) (eq_type0 x x') (eq_types eq_type0 xs xs'))

(** val eq_type : type0 -> type0 -> bool **)

let rec eq_type t1 t2 =
  match t1 with
  | Btype b1 -> (match t2 with
                 | Btype b2 -> eq_basic_type b1 b2
                 | _ -> false)
  | Ftype (ts1, n1, e1, t3) ->
    (match t2 with
     | Ftype (ts2, n2, e2, t4) ->
       (&&)
         ((&&) ((&&) (eq_types eq_type ts1 ts2) (Nat.eqb n1 n2))
           (eq_effect e1 e2)) (eq_type t3 t4)
     | _ -> false)
  | Reftype (e1, b1) ->
    (match t2 with
     | Reftype (e2, b2) -> (&&) (Pos.eqb e1 e2) (eq_basic_type b1 b2)
     | _ -> false)
  | Ptype (n1, ts1) ->
    (match t2 with
     | Ptype (n2, ts2) -> (&&) (Nat.eqb n1 n2) (eq_types eq_type ts1 ts2)
     | _ -> false)

type ty_context = (ident * type0) list

(** val remove_var_ty : ty_context -> ident -> type0 -> ty_context **)

let rec remove_var_ty t k t0 =
  match t with
  | [] -> []
  | x :: xs ->
    if (&&) (Pos.eqb k (fst x)) (eq_type t0 (snd x))
    then xs
    else x :: (remove_var_ty xs k t0)
