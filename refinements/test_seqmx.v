From mathcomp Require Import all_ssreflect ssrint ssrnat fintype matrix.
Require Import hrel param refinements seqmx seqmx_complements.

Existing Instance implem_ord.

Definition S3 := \matrix_(i, j < 1) 5%:Z.
Definition Mn3 := \matrix_(i < 3, j < 1) 5%:Z.
Definition M3N := \matrix_(i < 3, j < 1) 5%:Z.

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

Instance eq_option {m} :
  forall (x y : option 'I_m), option_R eq x y -> refines eq x y.
Proof.
  rewrite refinesE => x y /=; case; last by [].
  by move => a b ->.
Qed.

Global Instance Roption_eq m :
  refines (option_R eq ==> option_R eq ==> bool_R)
          (@eqtype.eq_op (option_eqType (ordinal_finType m))) eq_op.
Proof.
  rewrite refinesE=> x x' /= hx y y' /= hy.
  have -> : eq x x' by apply refinesP; apply: eq_option; exact: hx.
  have -> : eq y y' by apply refinesP; apply: eq_option; exact: hy.
  by case/boolP: (x' == y').
Qed.

Global Instance Roption_ord_eq m :
  refines (
  option_R (Rord (nat_Rxx m)) ==> option_R (Rord (nat_Rxx m))  ==> bool_R)
          (@eqtype.eq_op (option_eqType (ordinal_finType m))) eq_op.
Proof.
Admitted.

Typeclasses eauto := debug.

Goal ([pick i | M3N i ord0 != 0]) == (Some ord0).
Proof.
  try by coqeal.
Abort.