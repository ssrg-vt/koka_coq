From Coq Require ExtrOcamlBasic.
From Coq Require ExtrOcamlNativeString.
From Coq Require ExtrOCamlInt63.

Require koka_clight_compiler.

Extraction "extraction_ocaml/expr.ml" expr.expr. 
Extraction "extraction_ocaml/types.ml" types.type.
Extraction "extraction_ocaml/types.ml" types.eq_type. 
Extraction "extraction_ocaml/types.ml" types.get_ty.
Extraction "extraction_ocaml/types.ml" types.remove_var_ty.



