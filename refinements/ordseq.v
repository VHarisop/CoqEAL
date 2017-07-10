(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)

From mathcomp Require Import all_ssreflect.

From CoqEAL Require Import hrel param refinements.

Import Refinements.Op.

Section Classes.

Definition seq_from_set {m} (I : {set 'I_m}) := [seq val i | i <- enum I].

Class heq_of fset :=
  heq_op : forall n : nat, fset n -> fset n -> bool.
Local Notation "x == y" := (heq_op x y) : hetero_computable_scope.

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
  singl_op : forall n : nat, nat -> fset n.
Class subset_of fset :=
  subset_op : forall n : nat, fset n -> fset n -> bool.

End Classes.

Typeclasses Transparent card_of union_of inter_of compl_of adiff_of.
Typeclasses Transparent empty_of singl_of subset_of.


(** ordseq.v: An implementation of sets of ordinals as sorted sequences
    of nats containing unique elements *)

Section ordseq_op.

(* Number Type *)
Variable N : Type.

(* Set type *)
Variable F : nat -> Type.

Context `{zero_of N, one_of N, add_of N, eq_of N, leq_of N, lt_of N, spec_of N nat}.
Context `{implem_of nat N}.
Context `{forall m, implem_of 'I_m N}.

Definition ordseq {N} := seq N.
Definition hset := fun (_ : nat) => @ordseq nat.

(* Inlining of && should provide lazyness here. *)
Fixpoint eq_seq {T} f (s1 s2 : seq T) :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => f x1 x2 && eq_seq f s1' s2'
  | _, _ => false
  end.

Global Instance ordseq0 : empty_of hset := fun _ => [::].
Global Instance ordseq_eq : eq_of (@ordseq N) := eq_seq eq_op.

Global Instance ordseq_card : card_of hset :=
  fun _ M => seq.size M.

Global Instance ordseq_singleton : singl_of hset :=
  fun _ e => [:: e].

Global Instance ordseq_adiff : adiff_of hset :=
  fix aux _ p q := match q with
  | [::] => p
  | h :: t => aux _ (rem h p) t
  end.

Global Instance ordseq_union : union_of hset :=
  fun _ a b => merge leq a (ordseq_adiff _ b a).

Lemma ordseq_adiff_nil {m} (I : hset m) :
  ordseq_adiff _ I [::] = I.
Proof. by elim: I. Qed.

Lemma ordseq_nil_adiff {m} (I : hset m) :
  ordseq_adiff _ [::] I = [::].
Proof. by elim: I. Qed.

Lemma rem_sorted {m} (I : hset m) (i : nat) :
  sorted leq I -> sorted leq (rem i I).
Proof.
  move: (rem_subseq i I) => Hsub HsI.
  apply: subseq_sorted;
  [ exact: leq_trans |
    exact: Hsub |
    exact: HsI ].
Qed.

Lemma ordseq_adiff_sorted {m} (I J : hset m) :
  sorted leq I -> sorted leq J -> sorted leq (ordseq_adiff _ I J).
Proof.
  elim: J I => [// | j J Hind] [// | i I] //.
  - move => _ _. by rewrite ordseq_nil_adiff.
  - move => HsI HsJ. rewrite /ordseq_adiff.
    have Hs: sorted leq (rem j (i :: I)) by apply: (@rem_sorted m).
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
Admitted.

Lemma ordseq_adiff_is_adiff {m} (I J : hset m) (i : nat) :
  i \in ordseq_adiff _ I J -> i \in I /\ i \notin J.
Proof.
  elim: J I => [// | j J Hind] [// | hi I] //.
  - by rewrite ordseq_nil_adiff //=.
  - admit.
  (* This is too much *)
Admitted.

Lemma ordseq_union_sorted {m} (I J : hset m) :
  sorted leq I -> sorted leq J -> sorted leq (ordseq_union _ I J).
Proof.
  move => Hi Hj. apply: merge_sorted.
  - rewrite /total => x y. case/boolP: (x <= y)%N => //.
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
  sorted leq I -> sorted leq J ->
  forall (i : nat), (i \in ordseq_union _ I J) -> i \in I \/ i \in J.
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

(** Returning if an element is a member of a set *)
Fixpoint ordseq_mem {m} x (p : hset m) : bool := match p with
  | [::] => false
  | h :: t => (h == x) || @ordseq_mem m x t
  end.

Context `{forall m, spec_of nat 'I_m}.
Context `{eq_of nat}.

Global Instance implem_ordseq m : implem_of {set 'I_m} (hset m) :=
  fun s => seq_from_set s.

Global Instance spec_ordseq m : spec_of (@hset m) {set 'I_m} :=
  fun s => let sMapped := map spec s in [set i | i \in sMapped].

Local Open Scope rel_scope.

(* In the spirit of Rseqmx...
   TODO: Need to add elemwise equality! *)
CoInductive Rordseq {m1 m2} (rm : nat_R m1 m2) :
  {set 'I_m1} -> @hset m2 -> Type :=
  Rordseq_spec (I : {set 'I_m1}) (J : hset m2) of
    (forall j, j \in J -> (j < m1)%N) &
    (uniq J) & (sorted leq J) & 
    (eq_seq eq_op J (seq_from_set I)) : Rordseq rm I J.

Lemma in_ordseq_lt {m1 m2} (rm : nat_R m1 m2) I J (j : nat) :
  Rordseq rm I J -> j \in J -> (j < m1)%N.
Proof. case. move => ? ? Hind _ _ ?. by apply: Hind. Qed.

Lemma in_ordseq_uniq {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq rm I J -> uniq J.
Proof. by case. Qed.

Lemma in_ordseq_sorted {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq rm I J -> sorted leq J.
Proof. by case. Qed.

Lemma in_ordseq_eq {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq rm I J -> eq_seq eq_op J (seq_from_set I).
Proof. by case. Qed.

Global Instance Rordseq_sub {m1 m2} (rm : nat_R m1 m2)
(I : {set 'I_m1}) (J : @hset m2) :
  refines (Rordseq rm ==> Rordseq rm ==> Rordseq rm)
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
  - admit.
Admitted.

Global Instance Rordseq_add m1 m2 (rm : nat_R m1 m2)
(I : {set 'I_m1}) (J : (@hset m2)) :
  refines (Rordseq rm ==> Rordseq rm ==> Rordseq rm)
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
  - admit.
Admitted.

Global Instance spec_r m1 m2 (rm : nat_R m1 m2) :
  spec_of (hset m2) {set 'I_m1}.
Proof.
  rewrite [m1](nat_R_eq rm); exact: spec_ordseq.
Qed.

Global Instance implem_r m1 m2 (rm : nat_R m1 m2) :
  implem_of {set 'I_m1} (hset m2).
Proof.
  rewrite [m1](nat_R_eq rm); exact: implem_ordseq.
Qed.


Global Instance Rordseq_spec_l
  m1 m2 (rm : nat_R m1 m2) `{spec_of (hset m2) {set 'I_m1}} :
  refines (Rordseq rm ==> Logic.eq) spec_id spec.
Proof.
  rewrite refinesE=> _ _ [hS lS h1 h2 h3 h4].
  rewrite /spec /spec_id.
  (* TODO : Need elemwise equality to proceed from here! *)
Admitted.

Context (rAC : nat -> nat -> Type).

Definition RordseqC {m1 m2} (rm : nat_R m1 m2) :
  {set 'I_m1} -> hset m2 -> Type :=
  (Rordseq rm \o (list_R nat_R))%rel.

Global Instance RordseqC_sub {m1 m2} (rm : nat_R m1 m2)
 (I : {set 'I_m1}) (J : @hset m2) :
  refines (RordseqC rm ==> RordseqC rm ==> RordseqC rm)
  (@setD (ordinal_finType m1)) (@ordseq_adiff m2).
Proof.
  eapply refines_trans; tc.
  - apply: Rordseq_sub; try by done.
  - rewrite refinesE => // *.
Admitted.

Global Instance refine_ordseq_sub m (J : {set 'I_m}) :
refines (RordseqC (nat_Rxx m) ==> RordseqC (nat_Rxx m) ==> RordseqC (nat_Rxx m))
  (@setD (ordinal_finType m)) (@ordseq_adiff m).
Proof.
  apply: RordseqC_sub; try by done.
  by apply: implem_ordseq.
Qed.

Global Instance RordseqC_add {m1 m2} (rm : nat_R m1 m2)
  (I : {set 'I_m1}) (J : @hset m2) :
  refines (RordseqC rm ==> RordseqC rm ==> RordseqC rm)
  (@setU (ordinal_finType m1)) (@ordseq_union m2).
Proof.
  eapply refines_trans; tc.
  - apply: Rordseq_add; try by done.
  - rewrite refinesE => // *.
Admitted.

Global Instance refine_ordseq_add m (J : {set 'I_m}) :
refines (RordseqC (nat_Rxx m) ==> RordseqC (nat_Rxx m) ==> RordseqC (nat_Rxx m))
  (@setU (ordinal_finType m)) (@ordseq_union m).
Proof.
  apply: RordseqC_add; [ exact: J | by apply: implem_ordseq ].
Qed.

Close Scope rel_scope.

Let set_from_seq {m} := fun (s : seq 'I_m) => [set i | i \in s].

Let s1 := set_from_seq [::
  Ordinal (erefl (0 < 7));
  Ordinal (erefl (1 < 7));
  Ordinal (erefl (3 < 7));
  Ordinal (erefl (4 < 7))].

Let s2 := set_from_seq [::
  Ordinal (erefl (0 < 7));
  Ordinal (erefl (1 < 7));
  Ordinal (erefl (3 < 7));
  Ordinal (erefl (5 < 7))].

Goal s1 == s2.
Proof.
  Fail by coqeal.
Abort.