
type nat =
| O
| S of nat

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2



type positive =
| XI of positive
| XO of positive
| XH

module Nat :
 sig
  val eqb : nat -> nat -> bool
 end

module Pos :
 sig
  val eqb : positive -> positive -> bool
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

val eq_effect_label : effect_label -> effect_label -> bool

val eq_effect : effect -> effect -> bool

val eq_primitive_type : primitive_type -> primitive_type -> bool

val eq_basic_types :
  (basic_type -> basic_type -> bool) -> basic_type list -> basic_type list ->
  bool

val eq_basic_type : basic_type -> basic_type -> bool

val eq_types : (type0 -> type0 -> bool) -> type0 list -> type0 list -> bool

val eq_type : type0 -> type0 -> bool

type ty_context = (ident * type0) list

val remove_var_ty : ty_context -> ident -> type0 -> ty_context
