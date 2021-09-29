Require Import Ascii.
Require Extraction.

Definition u8 := ascii.

Extract Inductive bool => "bool" [ "true" "false" ].
Extraction "unicode.ml" u8.
