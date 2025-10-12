Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S m => n * factorial m
  end.
Require Coq.extraction.Extraction.
Extraction Language OCaml.
Extraction "factorial.ml" factorial.