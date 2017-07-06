(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)

Require Import ZArith.

From mathcomp Require Import all_ssreflect.

From CoqEAL Require Import hrel param refinements.

Import Refinements.Op.

(** ordseq.v: An implementation of sets of ordinals as sorted sequences
    of nats containing unique elements *)
Local Open Scope computable_scope.

Section ordseq_op.

(* Variable A : eqType. *)
Variable N : Type.

Definition ordseq := fun (_ : nat) => seq nat.

Context `{zero_of N, one_of N, add_of N, eq_of N, leq_of N, lt_of N, spec_of N nat}.

Global Instance ordseq0 {m} : zero_of (ordseq m) := [::].
Global Instance eq_ordseq {m} : eq_of (ordseq m) := @eqseq nat_eqType.

Fixpoint ordseq_sublist {m} (p q : ordseq m) : bool :=
  (* mem_aux : returns true/false, plus the remaining list after the match
               in case the element has indeed been found *)
  let fix mem_aux x (p' : ordseq m) : bool * (ordseq m) := match p' with
  | [::] => (false, [::])
  | h :: t =>
      (* If element is found, return true and the rest of the other set *)
      if (h == x) then (true, t)
      else mem_aux x t
  end
  in
  match p with
  | [::] => true
  | h :: t => match mem_aux h q with
    | (false, _) => false
    | (true, t') => ordseq_sublist t t'
    end
  end.

Definition ordseq_sub {m} : sub_of (ordseq m) :=
  let fix aux a b := match b with
  | [::] => a
  | h :: t => aux (rem h a) t
  end in aux.

Lemma ordseq_sub_nil {m} (I : ordseq m) :
  ordseq_sub I [::] = I.
Proof. by elim: I. Qed.

Lemma ordseq_nil_sub {m} (I : ordseq m) :
  ordseq_sub [::] I = [::].
Proof. by elim: I. Qed.

Lemma rem_sorted {m} (I : ordseq m) (i : nat) :
  sorted leq I -> sorted leq (rem i I).
Proof.
  move: (rem_subseq i I) => Hsub HsI.
  apply: subseq_sorted;
  [ exact: leq_trans |
    exact: Hsub |
    exact: HsI ].
Qed.

Lemma ordseq_sub_sorted {m} (I J : ordseq m) :
  sorted leq I -> sorted leq J -> sorted leq (ordseq_sub I J).
Proof.
  elim: J I => [// | j J Hind] [// | i I] //.
  - move => _ _. by rewrite ordseq_nil_sub.
  - move => HsI HsJ. rewrite /ordseq_sub.
    have Hs: sorted leq (rem j (i :: I)) by apply: (@rem_sorted m).
    apply: Hind; first by exact: Hs.
    move: (subseq_cons J j) => Hcons. apply: subseq_sorted;
    [ exact: leq_trans | exact: Hcons | exact: HsJ].
Qed.

Lemma ordseq_sub_uniq {m} (I J : ordseq m) :
  uniq I -> uniq J -> uniq (ordseq_sub I J).
Proof.
  elim: J I => [// | j J Hind] [// | i I] //.
  - move => _ _; by rewrite ordseq_nil_sub.
  - move => HuI. rewrite cons_uniq; move => /andP[_ HuJ].
    have Hu: uniq (rem j (i :: I)) by apply: rem_uniq.
    apply: Hind; first by exact: Hu.
    done.
Qed.

Lemma rem_is_sub {m} (I : ordseq m) :
  forall i, i \in I -> i \notin rem i I.
Proof.
  move => i. elim: I => [// | hi I Hind].
Admitted.

Lemma ordseq_sub_is_sub {m} (I J : ordseq m) (i : nat) :
  i \in ordseq_sub I J -> i \in I /\ i \notin J.
Proof.
  elim: J I => [// | j J Hind] [// | hi I] //.
  - by rewrite ordseq_nil_sub //=.
  - admit.
  (* This is too much *)
Admitted.


(* Union of two ordseqs *)
Definition ordseq_add {m} : add_of (ordseq m) :=
  fun a b => merge leq a (ordseq_sub b a).

Lemma ordseq_add_sorted {m} (I J : ordseq m) :
  sorted leq I -> sorted leq J -> sorted leq (ordseq_add I J).
Proof.
  move => Hi Hj. apply: merge_sorted.
  - rewrite /total => x y. case/boolP: (x <= y)%N => //.
    by rewrite -ltnNge ltn_neqAle => /andP[_ ?].
  - exact: Hi.
  - exact: ordseq_sub_sorted.
Qed.

Lemma ordseq_add_nil {m} (I : ordseq m) :
  ordseq_add I [::] = I.
Proof.
  rewrite /ordseq_add ordseq_nil_sub; by elim: I.
Qed.

Lemma ordseq_nil_add {m} (I : ordseq m) :
  ordseq_add [::] I = I.
Proof.
  rewrite /ordseq_add; by elim: I.
Qed.

Lemma ordseq_add_is_union {m} (I J : ordseq m) :
  sorted leq I -> sorted leq J ->
  forall (i : nat), (i \in ordseq_add I J) -> i \in I \/ i \in J.
Proof.
  move => Hi Hj i; case Icomp: I.
  - rewrite ordseq_nil_add => ?; by apply/orP.
  - rewrite /ordseq_add mem_merge mem_cat.
    move/orP; case => Hin; apply/orP.
    - by rewrite Hin.
    - move: Hin; rewrite -Icomp => Hsub.
      have : i \in J /\ (i \notin I) by exact: ordseq_sub_is_sub.
      move => [Hj' _]; by rewrite Hj' orbT.
Qed.

(** Returning if an element is a member of a set *)
Fixpoint ordseq_mem {m} x (p : ordseq m) : bool := match p with
  | [::] => false
  | h :: t => (h == x) || @ordseq_mem m x t
  end.

Global Instance implem_ordseq {m} : implem_of {set 'I_m} (ordseq m) :=
  fun s => [seq (nat_of_ord i) | i <- enum s].

(* TODO: We need a spec_of nat 'I_m somehow! *)
Global Instance spec_ordseq {m} `{H : spec_of nat 'I_m} :
  spec_of (@ordseq m) {set 'I_m} := fun s =>
  let sMapped := map (@spec _ _ H) s in
  [set i | i \in sMapped].

(** Size of a set *)
Global Instance size_seqset {m} : size_of (ordseq m) N :=
  let fix aux cnt p := match p with
  | [::] => cnt
  | _ :: t => aux (cnt + 1) t
  end
  in aux 0.

Local Open Scope rel_scope.

(* In the spirit of Rseqmx...*)
CoInductive Rordseq {m1 m2} (rm : nat_R m1 m2) :
  {set 'I_m1} -> @ordseq m2 -> Type := Rordseq_spec (I : {set 'I_m1}) (J : ordseq m2) of
  (forall j, j \in J -> (j < m1)%N) &
  (uniq J) & (sorted leq J) : Rordseq rm I J.

Lemma in_ordseq_lt {m1 m2} (rm : nat_R m1 m2) I J (j : nat) :
  Rordseq rm I J -> j \in J -> (j < m1)%N.
Proof. case. move => _ ? Hind _ _ ?. by apply: Hind. Qed.

Lemma in_ordseq_uniq {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq rm I J -> uniq J.
Proof. by case. Qed.

Lemma in_ordseq_sorted {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq rm I J -> sorted leq J.
Proof. by case. Qed.

Instance Rordseq_sub {m1 m2} (rm : nat_R m1 m2)
(I : 'I_m1) (J : (@ordseq m2)) :
  refines (Rordseq rm ==> Rordseq rm ==> Rordseq rm)
  (@setD (ordinal_finType m1)) (@ordseq_sub m2).
Proof.
  rewrite refinesE => I' J' Ho Ialt Jalt Ho' //=; constructor.
  - move => j Hj.
    have : (j \in J') /\ j \notin Jalt. apply: ordseq_sub_is_sub.
    + exact: Hj.
    move => [Hj' _].
    have -> : forall j, j \in J' -> (j < m1)%N. case: Ho => _.
    + move => J0 Hex _ _ j0 Hjex. exact: Hex.
    + rewrite //=.
    + exact: Hj'.
  - apply: ordseq_sub_uniq; [
      exact: in_ordseq_uniq Ho |
      exact: in_ordseq_uniq Ho' ]. 
  - apply: ordseq_sub_sorted; [
      exact: (in_ordseq_sorted rm I' J') |
      exact: (in_ordseq_sorted rm Ialt Jalt) ].
Qed.

Instance Rordseq_add {m1 m2} (rm : nat_R m1 m2)
(I : 'I_m1) (J : (@ordseq m2)) :
  refines (Rordseq rm ==> Rordseq rm ==> Rordseq rm)
  (@setU (ordinal_finType m1)) (@ordseq_add m2).
Proof.
  rewrite refinesE => I' J' Ho Ialt Jalt Ho'; constructor.
  - move => j Hjadd. have : j \in J' \/ j \in Jalt.
    + apply: ordseq_add_is_union.
      * apply: (in_ordseq_sorted _ _ J'); exact: Ho.
      * apply: (in_ordseq_sorted _ _ Jalt); exact: Ho'.
      * exact: Hjadd.
    + case; apply: in_ordseq_lt; [exact: Ho | exact: Ho'].
  - rewrite /ordseq_add merge_uniq cat_uniq; apply/and3P; split.
    + exact: (in_ordseq_uniq rm I' J').
    + apply/hasPn => x Hnot. have [_ ->] : x \in Jalt /\ x \notin J'.
      * by exact: ordseq_sub_is_sub.
      * done.
    + apply: ordseq_sub_uniq; [
      exact: in_ordseq_uniq Ho' | exact: in_ordseq_uniq Ho ].
  - apply: ordseq_add_sorted; apply: in_ordseq_sorted;
    [ exact: Ho | exact: Ho' ].
Qed.