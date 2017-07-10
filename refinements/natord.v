From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.

From CoqEAL Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op zmodp.

Local Open Scope ring_scope.

Section natord_op.

Definition natord := fun (_ : nat) => nat.

Global Instance zero_ord n : zero_of (natord n) := 0%N.

Global Instance one_ord n : one_of (natord n.+1) :=
  if (n == 0)%N then 0%N else 1%N.

Global Instance opp_ord n : opp_of (natord n) :=
  fun x => modn (n - x) n.

Global Instance add_ord n : add_of (natord n) :=
  fun x y => modn (x + y) n.

Global Instance sub_ord n : sub_of (natord n) :=
  fun x y => modn (x + (modn (n - y) n)) n.

Global Instance mul_ord n : mul_of (natord n) :=
  fun x y => modn (x * y) n.

Global Instance exp_ord n : exp_of (natord n) nat :=
  fun x y => modn (x ^ y) n.

Global Instance eq_ord n : eq_of (natord n) := fun x y => x == y.

Global Instance leq_ord n : leq_of (natord n) := fun x y => (x <= y)%N.

Global Instance lt_ord n : lt_of (natord n) := fun x y => (x < y)%N.

Global Instance implem_ord n : implem_of 'I_n (natord n) := @nat_of_ord n.

End natord_op.

Section natord_theory.

Local Open Scope rel_scope.

Definition Rid : nat -> nat -> Type := fun_hrel id.

Definition Rord n1 n2 (rn : nat_R n1 n2) : 'I_n1 -> natord n2 -> Type :=
  fun x y => Rid x y.

Global Instance Rord_0 n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn)) 0%R 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rord_1 n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn)) Zp1 1%C.
Proof.
  rewrite refinesE /Rord /Zp1 /inZp /= modn_def (nat_R_eq rn).
  by case: n2 rn.
Qed.

Local Instance refines_nat_R_S n1 n2 :
  refines nat_R n1 n2 -> refines nat_R n1.+1 n2.+1.
Proof. rewrite refinesE; exact: nat_R_S_R. Qed.

Local Instance refines_implem_eq A B (R : A -> B -> Type)
      `{implem_of A B, !refines (eq ==> R) implem_id implem} x y :
  refines eq x y -> refines R x (implem y).
Proof.
  move=> eqxy.
  rewrite -[x]/(implem_id _).
  exact: refines_apply.
Qed.

Local Arguments eq_op /.
Local Arguments eq_ord /.

Lemma RidE x y : refines Rid x y -> x = y.
Proof. by rewrite refinesE. Qed.

Global Instance Rord_eq n1 n2 (rn : nat_R n1 n2) :
  refines (Rord rn ==> Rord rn ==> bool_R)
          eqtype.eq_op eq_op.
Proof.
  rewrite refinesE=> x x' rx y y' ry //=.
  have [Hx Hy] : (nat_of_ord x = x') /\ (nat_of_ord y = y') by move: rx ry.
  rewrite -Hx -Hy. have -> : (x == y) = (x == y :> nat) by [].
  case/boolP: (x == y :> nat)%N => Heq; done.
Qed.

Local Arguments leq_op /.
Local Arguments leq_ord /.

Global Instance Rord_leq n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> bool_R)
          (fun x y => (x <= y)%N) leq_op.
Proof.
  rewrite refinesE=> x x' hx y y' hy /=.
  have [-> ->] : (nat_of_ord x = x') /\ (nat_of_ord y = y') by move: hx hy.
  case/boolP: (x' <= y')%N; done.
Qed.

Local Arguments lt_op /.
Local Arguments lt_ord /.

Global Instance Rord_lt n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> bool_R)
          (fun x y => ltn x y) lt_op.
Proof.
  rewrite refinesE=> x x' hx y y' hy /=.
  have [<- <-] : (nat_of_ord x = x') /\ (nat_of_ord y = y') by move: hx hy.
  case/boolP: (x < y)%N; done.
Qed.

Local Arguments implem_id /.
Local Arguments implem /.
Local Arguments implem_ord /.

Global Instance Rord_implem n1 n2 (rn : nat_R n1 n2) :
  refines (ordinal_R rn ==> Rord rn) implem_id implem.
Proof.
  have Q : 'I_n2 = 'I_n1 by rewrite -(nat_R_eq rn).
  rewrite refinesE => x y rxy //=.
  have hxy : refines eq (nat_of_ord y) (nat_of_ord x).
    rewrite refinesE.
    case: rxy=> m1 m2 rm _ _ _ /=.
    by rewrite (nat_R_eq rm).
  exact: refines_eq.
Qed.

Global Instance Rnat_nat_of_ord n1 n2 (rn : nat_R n1 n2) :
  refines (Rord rn ==> Rid) (@nat_of_ord n1) id.
Proof. by rewrite refinesE. Qed.

Close Scope ring_scope.

End natord_theory.

Local Open Scope nat_scope.

Let p := Ordinal (erefl (0 < 5)).
Let q := Ordinal (erefl (2 < 5)).

Goal p != q.
Proof.
  by coqeal.
Abort.

Goal p < q.
Proof.
  by coqeal.
Abort.

Close Scope nat_scope.