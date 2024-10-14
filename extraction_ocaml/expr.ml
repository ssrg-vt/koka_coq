
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
| Panic
| Divergence
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

type uop =
| Not
| Incr
| Decr
| Sizeof
| Neg

type bop =
| Plus
| Minus
| Mult
| Div
| Eq
| Neq
| Lt
| Lte
| Gt
| Gte

type val0 =
| Vunit
| Vint of z
| Vbool of bool
| Vloc of nat

type loc = positive

type heap = (loc * val0) list

type builtin =
| Ref
| Deref
| Massgn
| Run of heap
| Uop of uop
| Bop of bop
| Extfun

type expr =
| Var of type0 * ident
| Const of constant
| App of expr * nat * type0 list * expr list
| Bfun of builtin * type0 list * expr list
| Lexpr of ident * type0 * expr * expr
| Cond of expr * expr * expr
| Addr of basic_type * loc
| Hexpr of heap * expr
