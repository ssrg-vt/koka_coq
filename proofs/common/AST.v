(** This file defines a number of data types and operations used in
  the abstract syntax trees of many of the intermediate languages. *)

Require Import String.
Require Import Coqlib Integers.

Set Implicit Arguments.

(** * Syntactic elements *)

(** Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by the type [positive] of positive integers. *)

Definition ident := positive.

Definition ident_eq := peq.


