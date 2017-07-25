From mathcomp Require Import all_ssreflect ssrint ssrnat fintype matrix.
Require Import hrel param refinements seqmx seqmx_complements.

Existing Instance implem_ord.

Definition S3 := \matrix_(i, j < 1) 5%:Z.
Definition Mn3 := \matrix_(i < 3, j < 1) 5%:Z.
Definition e2 := @delta_mx _ 1 3 ord0 (Ordinal (erefl (1 < 3)%N))
  : 'M[int]_(1, 3).

Goal (M3 ord0 ord0 = 3%:Z).
Proof.
  Time by coqeal.
Abort.

Goal (M3 (Ordinal (erefl (1 < 2)%N)) ord0 = 3%:Z).
Proof.
  Time by coqeal.
Abort.

Goal (Mn3 *m S3) ord0 ord0 = 25%:Z.
Proof.
  Time by coqeal.
Abort.

Goal (e2 *m Mn3) == S3.
Proof.
  Time by coqeal.
Abort.