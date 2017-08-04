From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype bigop matrix.

From CoqEAL Require Import hrel param refinements seqmx seqmx_complements.

Section option_refinements.

Global Instance eq_option {T : Type} :
  forall (x y : option T), option_R eq x y -> refines eq x y.
Proof. by rewrite refinesE => x y /=; case => // ? ? ->. Qed.

Global Instance Roption_eq {T : eqType} :
  refines (option_R eq ==> option_R eq ==> bool_R)
          (@eqtype.eq_op (option_eqType T)) eqtype.eq_op.
Proof.
  rewrite refinesE=> x x' /= hx y y' /= hy.
  have -> : eq x x' by apply refinesP; apply: eq_option; exact: hx.
  have -> : eq y y' by apply refinesP; apply: eq_option; exact: hy.
  by case/boolP: (x' == y').
Qed.

Global Instance refines_none {T1 T2 : Type} {R : T1 -> T2 -> Type} :
  refines (option_R R) None None.
Proof. by rewrite refinesE; constructor. Qed.

Global Instance refines_some {T1 T2 : Type} {R : T1 -> T2 -> Type} :
  refines (R ==> option_R R) Some Some.
Proof. rewrite !refinesE /Rord => x y /= Hxy. by constructor. Qed.

End option_refinements.

(** A refinement for the pick operator, focused on its use within
    the Gaussian elimination routine. *)
Section pick_refinement.

Global Instance Roption_Rord m :
  refines (
  option_R (Rord (nat_Rxx m)) ==> option_R (Rord (nat_Rxx m))  ==> bool_R)
          (@eqtype.eq_op (option_eqType (ordinal_finType m))) eqtype.eq_op.
Proof.
  rewrite !refinesE /Rord => x y /= Hxy z w /= Hzw.
  elim: Hxy; elim: Hzw => // a1 _ /= <- b1 _ /= <-.
  rewrite /eqtype.eq_op /=. have <- : (b1 == a1) = (b1 == a1 :> nat) by [].
  by case: (b1 == a1).
Qed.

(* An untyped version of pick. *)
Definition pick_iota {n} f' := ohead (filter f' (iota 0 n)).

Global Instance Rpick (n1 n2: nat) (rn: nat_R n1 n2) f f' :
  refines (Rord rn ==> eq) f f' ->
  refines (option_R (Rord rn)) (@pick _ f) (@pick_iota n2 f').
Proof.
Admitted.

(** XA's version
Global Instance Rpick' (n1 n2: nat) (Rn: nat_R n1 n2) f f'
 `{H : forall x y, refines (Rord Rn) x y ->
               refines eq (f x) (f' y)} :
  refines (option_R (Rord Rn)) (@pick _ f) (@pick_iota n2 f').
Proof.
Admitted.
*)

(** Can we somehow avoid writing a different instance for every
    pred that we want to refine ? *)
Instance refines_Rord_ltn {m : nat} (n : nat) :
  refines (Rord (nat_Rxx n) ==> eq)
  (fun x : 'I_n => x < m) (fun x : nat => x < m).
Proof.
  by rewrite !refinesE /Rord => x y /= ->.
Qed.

Instance refines_Rord_gtn {m : nat} (n : nat) :
  refines (Rord (nat_Rxx n) ==> eq)
  (fun x : 'I_n => x > m) (fun x : nat => x > m).
Proof.
  by rewrite !refinesE /Rord => x y /= ->.
Qed.

Instance refines_Rord_leqn {m : nat} (n : nat) :
  refines (Rord (nat_Rxx n) ==> eq)
  (fun x : 'I_n => x <= m) (fun x : nat => x <= m).
Proof.
  by rewrite !refinesE /Rord => x y /= ->.
Qed.

Goal (@pick (ordinal_finType 5) (fun i => i < 0)) == None.
Proof.
  by coqeal.
Abort.

Goal (@pick (ordinal_finType 5) (fun i => i < 3)) == Some ord0.
Proof.
  by coqeal.
Abort.

Goal (@pick (ordinal_finType 5) (fun i => i > 2)) ==
      Some (Ordinal (erefl (3 < 5)%N)).
Proof.
  by coqeal.
Abort.

End pick_refinement.