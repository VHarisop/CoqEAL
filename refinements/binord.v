Require Import ZArith.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.

From CoqEAL Require Import hrel param refinements binnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements zmodp.

Local Open Scope ring_scope.

Section binord_op.

Definition binord := fun (_ : nat) => N.

Global Instance zero_ord n : Op.zero_of (binord n) := N.zero.

Global Instance one_ord n : Op.one_of (binord n.+1) :=
  if (n == 0)%N then N.zero else N.one.

Global Instance opp_ord n : Op.opp_of (binord n) :=
  fun x => (((implem n) - x : N) %% implem n : N)%C.

Global Instance add_ord n : Op.add_of (binord n) :=
  fun x y => ((x + y : N) %% implem n)%C.

Global Instance sub_ord n : Op.sub_of (binord n) :=
  fun x y => (((x : N) + ((implem n - y : N) %% implem n) : N) %% implem n)%C.

Global Instance mul_ord n : Op.mul_of (binord n) :=
  fun x y => ((x * y : N) %% implem n)%C.

Global Instance exp_ord n : Op.exp_of (binord n) N :=
  fun x y => ((x ^ y : N) %% implem n)%C.

Global Instance eq_ord n : Op.eq_of (binord n) := (Op.eq : N -> N -> bool).

Global Instance leq_ord n : Op.leq_of (binord n) := (Op.leq : N -> N -> bool).

Global Instance lt_ord n : Op.lt_of (binord n) := (Op.lt : N -> N -> bool).

Global Instance implem_ord n : Op.implem_of 'I_n (binord n) :=
  fun x => implem (x : nat).

End binord_op.

Section binord_theory.

Local Open Scope rel_scope.

Definition Rord n1 n2 (rn : nat_R n1 n2) : 'I_n1 -> binord n2 -> Type :=
  fun x y => Rnat x y.

Global Instance Rord_0 n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn)) 0%R 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rord_1 n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn)) Zp1 1%C.
Proof.
  rewrite refinesE /Rord /Zp1 /inZp /= modn_def (nat_R_eq rn).
  by case: n2 rn.
Qed.

(* Lemma nat_R_S n1 n2 : nat_R n1 n2 -> nat_R n1.+1 n2.+1. *)
(* Proof. rewrite refinesE; exact: nat_R_S_R. Qed. *)

Local Instance refines_implem_eq A B (R : A -> B -> Type)
      `{Op.implem_of A B, !refines (Logic.eq ==> R) Op.implem_id implem} x y :
  refines eq x y -> refines_rec R x (implem y).
Proof.
  move=> eqxy.
  rewrite -[x]/(Op.implem_id _).
  exact: refines_apply.
Qed.

Local Arguments Rord /.
Local Arguments opp_op /.
Local Arguments opp_ord /.
Local Arguments N.sub : simpl nomatch.

Global Instance Rord_opp n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn)) -%R -%C.
Proof.
move/nat_R_S_R in rn *.
by rewrite refinesE=> x x' hx /=; exact: spec_refines.
Qed.

Local Arguments add_op /.
Local Arguments add_ord /.

Global Instance Rord_add n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn))
          +%R +%C.
Proof.
move/nat_R_S_R in rn *.
rewrite refinesE=> x x' hx y y' hy /=.
exact: spec_refines.
Qed.

Local Arguments sub_op /.
Local Arguments sub_ord /.

Global Instance Rord_sub n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn))
          (fun x y => x - y) sub_op.
Proof.
move/nat_R_S_R in rn *.
rewrite refinesE=> x x' hx y y' hy /=.
exact: spec_refinesP.
Qed.

Local Arguments mul_op /.
Local Arguments mul_ord /.

Global Instance Rord_mul n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn))
          (@Zp_mul n1) *%C.
Proof.
move/nat_R_S_R in rn *.
rewrite refinesE=> x x' hx y y' hy /=.
exact: spec_refines.
Qed.

Local Arguments eq_op /.
Local Arguments eq_ord /.

Global Instance Rord_eq n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> bool_R)
          eqtype.eq_op Op.eq.
Proof.
move/nat_R_S_R in rn *.
rewrite refinesE=> /= x x' hx y y' hy.
have -> /= : (x == y) = (x == y :> nat) by [].
exact: eq_spec_refines.
Qed.

Local Arguments leq_op /.
Local Arguments leq_ord /.

Global Instance Rord_leq n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> bool_R)
          (fun x y => (x <= y)%N) leq_op.
Proof.
move/nat_R_S_R in rn *.
rewrite refinesE=> x x' hx y y' hy /=.
exact: eq_spec_refines.
Qed.

Local Arguments lt_op /.
Local Arguments lt_ord /.
Local Opaque ltn.

Global Instance Rord_lt n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> bool_R)
          (fun x y => ltn x y) lt_op.
Proof.
  rewrite refinesE=> x x' hx y y' hy /=.
  exact: eq_spec_refines.
Qed.

Local Arguments Op.implem_id /.
Local Arguments Op.implem /.
Local Arguments implem_ord /.

Global Instance Rord_implem n1 n2 (rn : nat_R n1 n2) :
  refines (ordinal_R rn ==> Rord rn) Op.implem_id implem.
Proof.
rewrite refinesE=> x y rxy /=.
rewrite -[implem_N]/implem.
have hxy : refines eq (nat_of_ord x) (nat_of_ord y).
  rewrite refinesE.
  case: rxy=> m1 m2 rm _ _ _ /=.
  by rewrite (nat_R_eq rm).
exact: spec_refines.
Qed.

Global Instance Rnat_nat_of_ord n1 n2 (rn : nat_R n1 n2) :
  refines (Rord rn ==> Rnat) (@nat_of_ord n1) id.
Proof. by rewrite refinesE. Qed.

End binord_theory.