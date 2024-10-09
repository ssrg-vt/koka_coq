
type nat =
| O
| S of nat



type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

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

type constant =
| ConsInt of z
| ConsBool of bool
| ConsUnit

type expr =
| Var of type0 * ident
| Const of constant
| Abs of nat * (ident * type0) list * expr
| App of expr * nat * expr list
| Addr of basic_type * ident
| Ref of basic_type * expr
| Deref of basic_type * expr
| Massgn of expr * expr
| Run of expr
| Hexpr of heap * expr
| Lexpr of ident * type0 * expr * expr
| Cond of expr * expr * expr
and heap =
| H of (ident * expr) list
