From mathcomp Require Import all_ssreflect ssrint ssrnat fintype matrix.
Require Import hrel param refinements seqmx seqmx_complements.

Typeclasses eauto := debug.

Existing Instance implem_ord.

Definition Mn3 := \matrix_(i, j < 3) 5%N.

Goal (M3 ord0 ord0 = 3%:Z).
Proof.
  Time by coqeal.
Abort.

Goal (M3 (Ordinal (erefl (1 < 2)%N)) ord0 = 3%:Z).
Proof.
  Time by coqeal.
Abort.
