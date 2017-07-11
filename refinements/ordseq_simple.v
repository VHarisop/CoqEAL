(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)

From mathcomp Require Import all_ssreflect.

From CoqEAL Require Import hrel param refinements.

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

Definition hset := fun (m : nat) => seq 'I_m.

(** Converting a set of ordinals to a sequence of nats and vice-versa *)
Definition seq_from_set {m} (I : {set 'I_m}) : hset m :=
  [seq i | i <- enum I].

Definition set_from_seq {m} (I : seq 'I_m) : {set 'I_m} := [set i in I].

Definition Rfin {m} : {set 'I_m} -> (hset m) -> Type := fun_hrel (@set_from_seq m).
Definition Rordseq {m} : (hset m) -> {set 'I_m} -> Type := fun_hrel (@seq_from_set m).

Definition oleq {m1 m2} (x : 'I_m1) (y : 'I_m2) :=
  (nat_of_ord x <= nat_of_ord y)%N.

Global Instance ordseq0 : empty_of hset := fun _ => [::].

(* Inlining of && should provide lazyness here. *)
Fixpoint eq_seq {T : Type} f (s1 s2 : seq T) :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => f x1 x2 && eq_seq f s1' s2'
  | _, _ => false
  end.

Global Instance ord_eq {m} : eq_of 'I_m := fun x y => x == y.

Global Instance ordseq_eq {m} : eq_of (hset m) := eq_seq eq_op.

Global Instance ordseq_card : card_of hset := fun _ s => size s.

Global Instance ordseq_singleton : singl_of hset := fun _ e => [:: e].

Global Instance ordseq_adiff : adiff_of hset :=
  fix aux _ p q := match q with
  | [::] => p
  | h :: t => aux _ (rem h p) t
  end.

Global Instance ordseq_union : union_of hset :=
  fun _ a b => merge oleq a (ordseq_adiff _ b a).

Section ordseq_theory.

Lemma ordseq_adiff_nil {m} (I : hset m) :
  ordseq_adiff _ I [::] = I.
Proof. by elim: I. Qed.

Lemma ordseq_nil_adiff {m} (I : hset m) :
  ordseq_adiff _ [::] I = [::].
Proof. by elim: I. Qed.

Lemma rem_sorted {m} (I : hset m) i :
  sorted oleq I -> sorted oleq (rem i I).
Proof.
  move: (rem_subseq i I) => Hsub HsI.
  apply: subseq_sorted;
  [ exact: leq_trans |
    exact: Hsub |
    exact: HsI ].
Qed.

Lemma ordseq_adiff_sorted {m} (I J : hset m) :
  sorted oleq I -> sorted oleq J -> sorted oleq (ordseq_adiff _ I J).
Proof.
  elim: J I => [// | j J Hind] [// | i I] //.
  - move => _ _. by rewrite ordseq_nil_adiff.
  - move => HsI HsJ. rewrite /ordseq_adiff.
    have Hs: sorted oleq (rem j (i :: I)) by apply: (@rem_sorted m).
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
  forall i, i \in I -> i \notin rem i I.
Proof.
  move => i. elim: I => [// | hi I Hind].
  (* TODO *)
Admitted.

Lemma ordseq_adiff_is_adiff {m} (I J : hset m) i :
  i \in ordseq_adiff _ I J -> i \in I /\ i \notin J.
Proof.
  elim: J I => [// | j J Hind] [// | hi I] //.
  - by rewrite ordseq_nil_adiff //=.
  - (* TODO *)
Admitted.

Lemma ordseq_union_sorted {m} (I J : hset m) :
  sorted oleq I -> sorted oleq J -> sorted oleq (ordseq_union _ I J).
Proof.
  move => Hi Hj. apply: merge_sorted.
  - rewrite /total => x y. case/boolP: (oleq x y) => //.
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
  sorted oleq I -> sorted oleq J ->
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

End spec_and_implem.

Definition eq_ordseq {m1 m2} (s1 : seq 'I_m1) (s2 : seq 'I_m2) :=
  eqseq (map (@nat_of_ord m1) s1) (map (@nat_of_ord m2) s2).

(* In the spirit of Rseqmx...
   TODO: Need to add elemwise equality! *)
CoInductive Rordseq_p {m1 m2} (rm : nat_R m1 m2) :
  {set 'I_m1} -> hset m2 -> Type :=
  Rordseq_p_spec (I : {set 'I_m1}) (J : hset m2) of
    (forall j, j \in J -> (j < m1)%N) &
    (uniq J) & (sorted oleq J) & 
    (eq_ordseq J (seq_from_set I)) : Rordseq_p rm I J.

Section Rordseq_theory.

Lemma in_ordseq_lt {m1 m2} (rm : nat_R m1 m2) I J j :
  Rordseq_p rm I J -> j \in J -> (j < m1)%N.
Proof. case. move => ? ? Hind _ _ ?. by apply: Hind. Qed.

Lemma in_ordseq_uniq {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq_p rm I J -> uniq J.
Proof. by case. Qed.

Lemma in_ordseq_sorted {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq_p rm I J -> sorted oleq J.
Proof. by case. Qed.

Lemma in_ordseq_eq {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq_p rm I J -> eq_ordseq J (seq_from_set I).
Proof. by case. Qed.

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
  refines (Rordseq_p (nat_Rxx m) ==> eq) spec_id spec.
Proof.
  rewrite refinesE => // *. move => J Js; case.
  move => I J0 Hltn Huniq Hsorted Heq.
  rewrite /spec_id /spec /spec_ordseq.
  have -> : J0 = [seq i | i <- enum I].
  (* TODO *)
Admitted.

Global Instance refine_ordseq_implem {m} :
  refines (eq ==> Rordseq_p (nat_Rxx m)) implem_id implem.
Proof.
  rewrite refinesE => // *. move => J Js HJs.
  rewrite /implem /implem_ordseq.
  split.
  - move => j _; exact: ltn_ord.
  - rewrite /seq_from_set map_id; exact: enum_uniq.
  - rewrite /seq_from_set map_id /sorted. admit.
  - by rewrite HJs; apply/eqP.
Admitted.

Definition Rset {n} (E : {set 'I_n}) (s : hset n) :=
  s = seq_from_set E.

Definition oCard {n} (E : {set 'I_n}) := #|E|.

Lemma Rset_cardE {n} x y: @Rset n x y -> #|x| = size y.
Proof.
  by rewrite /Rset => ->; rewrite size_map cardE.
Qed.

Global Instance Rordseq_p_card {m} :
  refines (@Rset m ==> eq) oCard (@ordseq_card m).
Proof.
  rewrite refinesE => ? ? Hp. exact: Rset_cardE.
Qed.

Close Scope rel_scope.

End Rordseq_theory.

End ordseq_refinements.

End ordseq_op.

From CoqEAL Require Import binord.

Definition s1 := set_from_seq [::
  Ordinal (erefl (0 < 7)%N);
  Ordinal (erefl (1 < 7)%N);
  Ordinal (erefl (3 < 7)%N);
  Ordinal (erefl (4 < 7)%N)].

Definition s2 := set_from_seq [::
  Ordinal (erefl (0 < 7)%N);
  Ordinal (erefl (1 < 7)%N);
  Ordinal (erefl (3 < 7)%N);
  Ordinal (erefl (5 < 7)%N)].

Definition ss1 := seq_from_set s1 : hset 7.
Definition ss2 := seq_from_set s2 : hset 7.

Goal ~~ (ordseq_eq ss1 ss2).
Proof.
  Fail by coqeal.
Abort.

Goal (oCard s1) = (oCard s2).
Proof.
  Fail by coqeal.
Abort.

Goal s1 == s2.
Proof.
  eapply refines_eq; eapply refines_goal; tc.
  Fail by coqeal.
Abort.