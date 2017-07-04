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

(* Difference of two ordseqs *)
Definition ordseq_sub {m} : sub_of (ordseq m) :=
  let fix aux (a : ordseq m) := match a with
  | [::] => fun _ => [::]
  | h :: t => (fix aux_comp (b : ordseq _) :=
      match b with
      | [::] => a
      | h' :: t' =>
        if (h < h')%N then h :: (aux t b)
        else if (h == h')%N then aux t t'
        else aux_comp t'
      end)
  end
  in aux.

Lemma ordseq_sub_nil {m} (I : ordseq m) :
  ordseq_sub I [::] = I.
Proof. by elim: I. Qed.

Lemma ordseq_nil_sub {m} (I : ordseq m) :
  ordseq_sub [::] I = [::].
Proof. by elim: I. Qed.

Lemma ordseq_sub_is_sub {m} (I J : ordseq m) :
  forall (i : nat), i \in ordseq_sub I J -> i \in I /\ i \notin J.
Proof.
  move => i; elim: J => [| j J Hind] //.
  - rewrite ordseq_sub_nil => Hin; try by done.
  - admit.
  (* This is too much *)
Admitted.

Lemma ordseq_sub_sorted {m} (I J : ordseq m) :
  sorted leq I -> sorted leq J -> sorted leq (ordseq_sub I J).
Proof.
Admitted.

Definition ordcmp {m} := fun (x y : 'I_m) => ((nat_of_ord x) <= (nat_of_ord y))%N.

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
  forall (i : nat), (i \in ordseq_add I J) -> i \in I \/ i \in J.
Proof.
  move => i; elim I.
  - rewrite ordseq_nil_add => Hj; by apply/orP.
  - move => k K Hind. rewrite /ordseq_add mem_merge mem_cat.
    move/orP; case => Hin; apply/orP.
    - by rewrite Hin.
    - have : i \in J /\ (i \notin (k :: K)) by exact: ordseq_sub_is_sub.
      move => [Hj _]; by rewrite Hj orbT.
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
Proof. case. move => _ ? Hind _ _ Hin. by apply: Hind. Qed.

Lemma in_ordseq_uniq {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq rm I J -> uniq J.
Proof. by case. Qed.

Lemma in_ordseq_sorted {m1 m2} (rm : nat_R m1 m2) I J :
  Rordseq rm I J -> sorted leq J.
Proof. by case. Qed.

Instance Rordseq_sub {m1 m2} (rm : nat_R m1 m2)
(I : 'I_m1) (J : (@ordseq m2)) `{Hm: spec_of N 'I_m2} :
  refines (Rordseq rm ==> Rordseq rm ==> Rordseq rm)
  (@setD (ordinal_finType m1)) (@ordseq_sub m2).
Proof.
  rewrite refinesE => I' J' Ho Ialt Jalt Ho' //=; constructor.
  - move => j Hj.
    have : (j \in J') /\ j \notin Jalt by apply: ordseq_sub_is_sub.
    move => [Hj' _].
    have -> : forall j, j \in J' -> (j < m1)%N. case: Ho => _.
    + move => J0 Hex _ _ j0 Hjex. exact: Hex.
    + rewrite //=.
    + exact: Hj'.
  - Search _ (uniq). admit.
  - apply: ordseq_sub_sorted.
    + exact: (in_ordseq_sorted rm I' J').
    + exact: (in_ordseq_sorted rm Ialt Jalt).
Admitted.

Instance Rordseq_add {m1 m2} (rm : nat_R m1 m2)
(I : 'I_m1) (J : (@ordseq m2)) :
  refines (Rordseq rm ==> Rordseq rm ==> Rordseq rm)
  (@setU (ordinal_finType m1)) (@ordseq_add m2).
Proof.
  rewrite refinesE => I' J' Ho Ialt Jalt Ho'; constructor.
  - move => j Hjadd. have : j \in J' \/ j \in Jalt.
    + exact: ordseq_add_is_union.
    + case; apply: in_ordseq_lt; [exact: Ho | exact: Ho'].
  - rewrite /ordseq_add merge_uniq cat_uniq. admit.
  - rewrite /ordseq_add merge_sorted //=.
    + rewrite /total => x1 y1.
      case/boolP: (leq x1 y1) => [// |].
      by rewrite orFb -ltnNge ltn_neqAle => /andP[_ ?] //.
    + by case: Ho.
  - apply: ordseq_sub_sorted; apply: in_ordseq_sorted; [
      exact: Ho' | exact: Ho ].
Admitted.