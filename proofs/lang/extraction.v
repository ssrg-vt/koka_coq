From Coq Require ExtrOcamlBasic.
From Coq Require ExtrOcamlNativeString.
From Coq Require ExtrOCamlInt63.

(** This module is meant as the minimal dependency of extracted code. *)
Require expr.

Extraction "extraction_ocaml/expr.ml" expr.expr. 
Extraction "extraction_ocaml/types.ml" types.type.
Extraction "extraction_ocaml/types.ml" types.eq_type. 
Extraction "extraction_ocaml/types.ml" types.get_ty.
Extraction "extraction_ocaml/types.ml" types.remove_var_ty.



