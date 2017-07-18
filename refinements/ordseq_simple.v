(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)

From mathcomp Require Import all_ssreflect.

From CoqEAL Require Import hrel param refinements trivial_seq.

Import Refinements.Op.

Local Open Scope rel_scope.

Section Classes.

(* cardinality, union, intersection, complement, asymmetric difference *)
Class card_of fset :=
  card_op : forall n : nat, fset n -> nat.
Class union_of fset :=
  union_op : forall n : nat, fset n -> fset n -> fset n.
Class inter_of fset :=
  inter_op : forall n : nat, fset n -> fset n -> fset n.
Class compl_of fset :=
  compl_op : forall n : nat, fset n -> fset n.
Class adiff_of fset :=
  adiff_op : forall n : nat, fset n -> fset n -> fset n.
(* Null set, singleton, subset *)
Class empty_of fset :=
  empty_op : forall n : nat, fset n.
Class singl_of fset :=
  singl_op : forall n : nat, 'I_n -> fset n.
Class subset_of fset :=
  subset_op : forall n : nat, fset n -> fset n -> bool.

End Classes.

Typeclasses Transparent card_of union_of inter_of compl_of adiff_of.
Typeclasses Transparent empty_of singl_of subset_of.

(** ordseq.v: An implementation of sets of ordinals as sorted sequences
    of ordinals containing unique elements *)

Section ordseq_op.

Instance implem_ord : forall n, implem_of 'I_n 'I_n := fun _ => implem_id.

Definition hset := fun (m : nat) => seq 'I_m.

(** Building ordseqs and sets from a sequence *)
Definition seq_from_set {m} (I : {set 'I_m}) : hset m :=
  [seq i | i <- enum I].

Definition set_from_seq {m} (I : seq 'I_m) : {set 'I_m} := [set i in I].

(** Building ordseqs and sets from a predicate *)
Definition seq_from_pred {m} (p : pred 'I_m) : hset m :=
  filter p (ord_enum m).

Definition set_from_pred {m} (p : pred 'I_m) : {set 'I_m} :=
  [set i in 'I_m | p i].

(** From finsets to seqs and vice-versa *)
Definition Rfin {m} : {set 'I_m} -> (hset m) -> Type := fun_hrel (@set_from_seq m).
Definition Rordseq {m} : (hset m) -> {set 'I_m} -> Type := fun_hrel (@seq_from_set m).

Definition RfinP {m} : {set 'I_m} -> pred 'I_m -> Type := fun_hrel (@set_from_pred m).
Definition RordseqP {m} : hset m -> pred 'I_m -> Type := fun_hrel (@seq_from_pred m).

Definition ordleq {m1 m2} (x : 'I_m1) (y : 'I_m2) :=
  (nat_of_ord x <= nat_of_ord y)%N.

Global Instance ordseq0 : empty_of hset := fun _ => [::].

(* Inlining of && should provide lazyness here. *)
Fixpoint eq_seq {T : Type} f (s1 s2 : seq T) :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => f x1 x2 && eq_seq f s1' s2'
  | _, _ => false
  end.

Global Instance ord_eq {m} : eq_of 'I_m := fun x y => x == y :> nat.

Global Instance ordseq_eq {m} : eq_of (hset m) := eq_seq eq_op.

Global Instance ordseq_card : card_of hset := fun _ s => size s.

Global Instance ordseq_singleton : singl_of hset := fun _ e => [:: e].

Global Instance ordseq_empty : empty_of hset := fun _ => [::].

Global Instance ordseq_adiff : adiff_of hset :=
  fix aux _ p q := match q with
  | [::] => p
  | h :: t => aux _ (rem h p) t
  end.

Global Instance ordseq_union : union_of hset :=
  fun _ a b => merge ordleq a (ordseq_adiff _ b a).

Section ordseq_theory.

Lemma ordseq_adiff_nil {m} (I : hset m) :
  ordseq_adiff _ I [::] = I.
Proof. by elim: I. Qed.

Lemma ordseq_nil_adiff {m} (I : hset m) :
  ordseq_adiff _ [::] I = [::].
Proof. by elim: I. Qed.

Lemma rem_sorted {m} (I : hset m) i :
  sorted ordleq I -> sorted ordleq (rem i I).
Proof.
  move: (rem_subseq i I) => Hsub HsI.
  apply: subseq_sorted;
  [ exact: leq_trans |
    exact: Hsub |
    exact: HsI ].
Qed.

Lemma ordseq_adiff_sorted {m} (I J : hset m) :
  sorted ordleq I -> sorted ordleq J -> sorted ordleq (ordseq_adiff _ I J).
Proof.
  elim: J I => [// | j J Hind] [// | i I] //.
  - move => _ _. by rewrite ordseq_nil_adiff.
  - move => HsI HsJ. rewrite /ordseq_adiff.
    have Hs: sorted ordleq (rem j (i :: I)) by apply: (@rem_sorted m).
    apply: Hind; first by exact: Hs.
    move: (subseq_cons J j) => Hcons. apply: subseq_sorted;
    [ exact: leq_trans | exact: Hcons | exact: HsJ].
Qed.

Lemma ordseq_adiff_uniq {m} (I J : hset m) :
  uniq I -> uniq J -> uniq (ordseq_adiff _ I J).
Proof.
  elim: J I => [// | j J Hind] [// | i I] //.
  - move => _ _; by rewrite ordseq_nil_adiff.
  - move => HuI. rewrite cons_uniq; move => /andP[_ HuJ].
    have Hu: uniq (rem j (i :: I)) by apply: rem_uniq.
    apply: Hind; [ exact: Hu | done ].
Qed.

Lemma rem_is_sub {m} (I : hset m) :
  forall i, i \in I -> uniq I -> i \notin rem i I.
Proof.
  move => i. elim: I => [// | hi I Hind] H.
  case/boolP : (hi == i) => Hin.
  - rewrite /rem cons_uniq => /andP[Hi Hu].
    move/eqP: Hin => Hin. rewrite Hin in Hi; move/eqP: Hin ->; exact: Hi.
  - have Hneq : hi == i = false by apply/eqP; move/eqP: Hin.
    rewrite /rem Hneq in_cons eq_sym Hneq orFb cons_uniq => /andP[_ ?].
    apply: Hind; move: H; by rewrite in_cons eq_sym Hneq orFb //.
Qed.

Lemma ordseq_adiff_is_adiff {m} (I J : hset m) i :
  i \in ordseq_adiff _ I J -> i \in I /\ i \notin J.
Proof.
  elim: J I => [// | j J Hind] [// | hi I] //.
  - by rewrite ordseq_nil_adiff //=.
  - (* TODO *)
Admitted.

Lemma ordseq_union_sorted {m} (I J : hset m) :
  sorted ordleq I -> sorted ordleq J -> sorted ordleq (ordseq_union _ I J).
Proof.
  move => Hi Hj. apply: merge_sorted.
  - rewrite /total => x y. case/boolP: (ordleq x y) => //.
    by rewrite -ltnNge ltn_neqAle => /andP[_ ?].
  - exact: Hi.
  - exact: ordseq_adiff_sorted.
Qed.

Lemma ordseq_union_nil {m} (I : hset m) :
  ordseq_union _ I [::] = I.
Proof.
  rewrite /ordseq_union ordseq_nil_adiff; by elim: I.
Qed.

Lemma ordseq_nil_union {m} (I : hset m) :
  ordseq_union _ [::] I = I.
Proof.
  rewrite /ordseq_union; by elim: I.
Qed.

Lemma ordseq_union_is_union {m} (I J : hset m) :
  sorted ordleq I -> sorted ordleq J ->
  forall (i : 'I_m), (i \in ordseq_union _ I J) -> i \in I \/ i \in J.
Proof.
  move => Hi Hj i; case Icomp: I.
  - rewrite ordseq_nil_union => ?; by apply/orP.
  - rewrite /ordseq_union mem_merge mem_cat.
    move/orP; case => Hin; apply/orP.
    - by rewrite Hin.
    - move: Hin; rewrite -Icomp => Hsub.
      have : i \in J /\ (i \notin I) by exact: ordseq_adiff_is_adiff.
      move => [Hj' _]; by rewrite Hj' orbT.
Qed.

End ordseq_theory.

Section ordseq_refinements.

Section spec_and_implem.

Global Instance implem_ordseq m : implem_of {set 'I_m} (hset m) := seq_from_set.

Local Instance implem_ordseq_irr m1 m2 (rm : nat_R m1 m2) :
  implem_of {set 'I_m1} (hset m2).
Proof.
  rewrite -(nat_R_eq rm); exact: implem_ordseq.
Qed.

Global Instance spec_ordseq m : spec_of (hset m) {set 'I_m} := set_from_seq.

Local Instance spec_ordseq_irr m1 m2 (rm : nat_R m1 m2) :
  spec_of (hset m2) {set 'I_m1}.
Proof.
  rewrite -(nat_R_eq rm); exact: spec_ordseq.
Qed.

Global Instance eq_repr {n} :
  refines (@Rfin n ==> Rfin ==> bool_R) eqtype.eq_op eq_op.
Proof.
  rewrite refinesE => //=.
  move => h hs Hrf h' hs' Hrf'.
Admitted.

Global Instance eq_finset {n} :
  refines (@Rordseq n ==> Rordseq ==> bool_R) eq_op eqtype.eq_op.
Proof.
  rewrite refinesE => hs h Hrf hs' h' Hrf'.
  rewrite /Rordseq /fun_hrel /seq_from_set in Hrf, Hrf'.
  case/boolP: (h == h') => /eqP-Heq.
  - suff Heqseq : ([seq i | i <- enum h] == [seq i | i <- enum h'])%C
    by rewrite -Hrf -Hrf' Heqseq.
    admit.
  - suff Hneqseq : ([seq i | i <- enum h] == [seq i | i <- enum h'])%C = false
    by rewrite -Hrf -Hrf' Hneqseq.
    admit.
Admitted.

End spec_and_implem.

Definition eq_ordseq {m1 m2} (s1 : seq 'I_m1) (s2 : seq 'I_m2) :=
  eqseq (map (@nat_of_ord m1) s1) (map (@nat_of_ord m2) s2).

(* In the spirit of Rseqmx...
   TODO: Need to add elemwise equality! *)
CoInductive Rordseq_p {m1 m2} (rm : nat_R m1 m2) :
  {set 'I_m1} -> hset m2 -> Type :=
  Rordseq_p_spec (I : {set 'I_m1}) (J : hset m2) of
    (forall j, j \in J -> (j < m1)%N) &
    (uniq J) & (sorted ordleq J) &
    (eq_ordseq J (seq_from_set I)) : Rordseq_p rm I J.

Section Rordseq_theory.

Instance ordseq_of {m} : implem_of (seq 'I_m) (hset m) := map id.

Global Instance Rordseq_p_ordseq_of m :
  refines (list_R (ordinal_R (nat_Rxx m)) ==> Rordseq_p (nat_Rxx m))
          (@set_from_seq m) (@ordseq_of m).
Proof.
  rewrite refinesE => x y Heq; constructor.
Admitted.

Global Instance Rfin_ordseq_of m :
  refines (eq ==> Rfin)
          (@set_from_seq m) (@ordseq_of m).
Proof.
  rewrite refinesE => x y ->; rewrite /Rfin.
  by rewrite /ordseq_of map_id.
Qed.

Lemma set_seqK {m} : cancel (@set_from_seq m) seq_from_set.
Proof.
  rewrite /cancel => x; rewrite /seq_from_set /set_from_seq.
Admitted.

Lemma seq_setK {m} : cancel (@seq_from_set m) set_from_seq.
Proof.
  rewrite /cancel => x; rewrite /seq_from_set /set_from_seq.
Admitted.

(** Refinements for creating seqs and sets *)
Global Instance Rfinp_ordseq_of m :
  refines (Rfin ==> eq)
          (@seq_from_set m) id.
Proof.
  rewrite refinesE => ? ?; rewrite /Rfin /fun_hrel => <-; exact: set_seqK.
Qed.

Global Instance Rordseq_ordseq_of m :
  refines (Rordseq ==> eq)
    (@set_from_seq m) id.
Proof.
  rewrite refinesE => ? ?; rewrite /Rordseq /fun_hrel => <-; exact: seq_setK.
Qed.

Lemma in_ordseq_lt {m1 m2} (rm : nat_R m1 m2) I J j :
  Rordseq_p rm I J -> j \in J -> (j < m1)%N.
Proof. case. move => ? ? Hind _ _ ?. by apply: Hind. Qed.

Lemma in_ordseq_uniq {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq_p rm I J -> uniq J.
Proof. by case. Qed.

Lemma in_ordseq_sorted {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq_p rm I J -> sorted ordleq J.
Proof. by case. Qed.

Lemma in_ordseq_eq {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq_p rm I J -> eq_ordseq J (seq_from_set I).
Proof. by case. Qed.

(** Refinement for empty set *)
Global Instance Rfin_empty m :
  refines (@Rfin m) set0 (ordseq_empty m).
Proof.
  by rewrite refinesE.
Qed.

Global Instance Rfin_singleton m :
  forall i : 'I_m, refines (@Rfin m) (set1 i) ([:: i]).
Proof.
  move => i. rewrite refinesE /Rfin /fun_hrel /set_from_seq //=.
Admitted.

Global Instance Rfin_sub {m} :
  refines (@Rfin m ==> Rfin ==> Rfin)
  (@setD (ordinal_finType m)) (@ordseq_adiff m).
Proof.
Admitted.

Global Instance Rordseq_p_sub {m1 m2} (rm : nat_R m1 m2) :
  refines (Rordseq_p rm ==> Rordseq_p rm ==> Rordseq_p rm)
  (@setD (ordinal_finType m1)) (@ordseq_adiff m2).
Proof.
  rewrite refinesE => I' J' Ho Ialt Jalt Ho' //=; constructor.
  - move => j Hj.
    have : (j \in J') /\ j \notin Jalt. apply: ordseq_adiff_is_adiff.
    + exact: Hj.
    move => [Hj' _]. exact: (in_ordseq_lt rm I' J').
  - apply: ordseq_adiff_uniq; [
      exact: in_ordseq_uniq Ho |
      exact: in_ordseq_uniq Ho' ].
  - apply: ordseq_adiff_sorted; [
      exact: (in_ordseq_sorted rm I' J') |
      exact: (in_ordseq_sorted rm Ialt Jalt) ].
  - admit. (* TODO *)
Admitted.

Global Instance Rfin_add {m} :
  refines (@Rfin m ==> Rfin ==> Rfin)
  (@setU (ordinal_finType m)) (@ordseq_union m).
Proof.
Admitted.

Global Instance Rordseq_p_add m1 m2 (rm : nat_R m1 m2) :
  refines (Rordseq_p rm ==> Rordseq_p rm ==> Rordseq_p rm)
  (@setU (ordinal_finType m1)) (@ordseq_union m2).
Proof.
  rewrite refinesE => I' J' Ho Ialt Jalt Ho'; constructor.
  - move => j Hjadd. have : j \in J' \/ j \in Jalt.
    + apply: ordseq_union_is_union.
      * apply: (in_ordseq_sorted _ _ J'); exact: Ho.
      * apply: (in_ordseq_sorted _ _ Jalt); exact: Ho'.
      * exact: Hjadd.
    + case; apply: in_ordseq_lt; [exact: Ho | exact: Ho'].
  - rewrite merge_uniq cat_uniq; apply/and3P; split.
    + exact: (in_ordseq_uniq rm I' J').
    + apply/hasPn => x Hnot. have [_ ->] : x \in Jalt /\ x \notin J';
      [ exact: ordseq_adiff_is_adiff | done ].
    + apply: ordseq_adiff_uniq; [
      exact: in_ordseq_uniq Ho' | exact: in_ordseq_uniq Ho ].
  - apply: ordseq_union_sorted; apply: in_ordseq_sorted;
    [ exact: Ho | exact: Ho' ].
  - admit. (* TODO *)
Admitted.

Global Instance refine_ordseq_spec {m} :
  refines (@Rfin m ==> eq) spec_id spec.
Proof.
  by rewrite refinesE => // *.
Qed.

Global Instance refine_ordseq_implem {m} :
  refines (eq ==> @Rfin m) implem_id implem.
Proof.
  rewrite refinesE => // *.
  rewrite /implem /implem_id /implem_ordseq /seq_from_set.
  move => _ y ->. rewrite /Rfin /fun_hrel map_id.
Admitted.

End Rordseq_theory.

End ordseq_refinements.

End ordseq_op.

Close Scope rel_scope.


Section test.

Existing Instance implem_ord.

Definition ss1 := set_from_seq [::
  Ordinal (erefl (0 < 7)%N);
  Ordinal (erefl (1 < 7)%N);
  Ordinal (erefl (3 < 7)%N);
  Ordinal (erefl (4 < 7)%N)].

Definition ss2 := [::
  Ordinal (erefl (0 < 7)%N);
  Ordinal (erefl (1 < 7)%N);
  Ordinal (erefl (3 < 7)%N);
  Ordinal (erefl (5 < 7)%N)].

Definition s1 :=
  ord0 |: ((Ordinal (erefl (1 < 7))) |: ((Ordinal (erefl (3 < 7)%N)) |: set0)).

Definition s2 :=
  ord0 |: ((Ordinal (erefl (1 < 7))) |: ((Ordinal (erefl (4 < 7)%N)) |: set0)).

Definition ss1' := seq_from_set s1 : hset 7.
Definition ss2' := seq_from_set s2 : hset 7.

Definition q1 := @set0 (ordinal_finType 6).
Definition q2 := [set i | i in [::]] : {set ordinal_finType 6}.

Definition q1' := @set1 (ordinal_finType 6) ord0.
Definition q2' := @set1 (ordinal_finType 6) (Ordinal (erefl (1 < 6))).

Goal q1 = set0.
Proof.
  by coqeal.
Abort.

Goal q1 != q2'.
Proof.
  by coqeal.
Abort.

Goal ((Ordinal (erefl (1 < 6))) |: q1') == (ord0 |: q2').
Proof.
  by coqeal.
Abort.

Goal ~~ (s1 == s2).
Proof.
  by coqeal.
Abort.

End test.