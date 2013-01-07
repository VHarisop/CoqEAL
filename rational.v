(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp. 
Require Import path choice fintype tuple finset ssralg bigop ssrint ssrnum rat.
Require Import generic_quotient refinements.

(******************************************************************************)
(* Non-normalized rational numbers refinest SSReflects rational numbers (rat) *) 
(*                                                                            *)
(* ??? == some documentation                                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.
Local Open Scope signature_scope.

Import GRing.Theory.
Import Num.Theory.

(* Non normalized rational numbers *)
Section rational.

Record rational : Set := Rational {
  val_rational : (int * int) ;
  val_rational_gt0 : (0 < val_rational.2)
}.

Canonical rational_subType := Eval hnf in [subType for val_rational].

Lemma val_rational_inj : injective val_rational.
Proof. exact: val_inj. Qed.

(* denormalize = repr *) (* normalize = \pi_rat *)
Definition denormalize (r : rat) : rational := @Rational (valq r) (denq_gt0 r).
Definition normalize (r : rational) : rat := match r with
  | Rational x _ => fracq x
  end.

Lemma normalizeK : cancel denormalize normalize.
Proof.
move=> x.
by rewrite /normalize /denormalize valqK.
Qed.

(* We have a quotient type where rat is the quotients of rat' *)
Definition quotClass := QuotClass normalizeK.
Canonical quotType := QuotType rat quotClass.

(* Zero - Use repr_of to avoid lock on repr *)
Definition zero_rational : rational := repr_of (0 : rat).

Global Program Instance ZeroRational : Zero rational := zero_rational.
Global Program Instance ZeroMorphRational : Morph implem (0 : rat) 0%C.
Obligation 1. by rewrite /implem /implem_op /quot_implem unlock. Qed.

(* Addition *)
(* TODO: Fix the bug! *)
Definition add_rational (a b : rational) : rational.
exists ((val_rational a).1 + (val_rational b).1,
        (val_rational a).2 + (val_rational b).2).
simpl.
case: a => /= a a0.
case: b => /= b b0.
exact: addr_gt0.
Defined.

Global Program Instance AddRational : Add rational := add_rational.

(* This seems to suffice as it implies that both normalize and denormalize are
   morphisms for addition *)
Lemma add_rational_mono : {mono \pi_rat : x y / (x + y)%C >-> repr (x + y) }.
Proof.
move=> x y /=.
admit.
Qed.

(* Adding and then normalizing should be the same as first normalizing and
   then adding *)
Lemma add_rational_correct : {morph \pi_rat : x y / (x + y)%C >-> x + y }.
Proof.
move=> x y.
have _ : normalize ((fun x0 : rational => [eta add_rational x0]) x y) = normalize (add_rational x y) by [].
by rewrite -add_rational_mono reprK.
Qed.

(* We can also prove that denormalize is a morphism for addition *)
Lemma implies_morph :
  {morph (@repr _ [quotType of rat]) : a1 a2 / a1 + a2 >-> (a1 + a2)%C}.
Proof.
move=> x y /=.
by rewrite -add_rational_mono !reprK.
Qed.

(* Now we only need mono... *)
Global Program Instance AddMorph_rat' : Morph (implem ==> implem ==> implem)
        (fun x y : rat => x + y) (fun x y => x + y)%C.
Obligation 1.
rewrite /implem => x _ <- y _ <-.
by rewrite /implem_op /quot_implem implies_morph.
Qed.

End rational.

(* The concrete implementation: Refine rat' to B * B where B refines int *)
Section refines.

(* B is a type that should implement int *)
Variable B : Type.

(* Build a context with proper sharing and the necessary refinements *)
Context `{impl : Implem int B, Add B, One B, Zero B}
        `{!Refines impl,
          zeroE : !Morph implem 0 0%C, oneE : !Morph implem 1 1%C,
          addE : !Morph (implem ==> implem ==> implem) (fun x y : int => x + y) (fun x y => x + y)%C}.

Global Program Instance rat'_implem : Implem rational (B * B) :=
  fun r => match val_rational r with
  | (a,b) => (| a |,| b |)%C
  end.
Global Program Instance rat'_refines : Refines rat'_implem.
Obligation 1.
move=> x y /= h.
apply/val_rational_inj.
move: h.
rewrite /implem_op /rat'_implem /=.
case: (val_rational x) => a b.
case: (val_rational y) => c d.
case => h1 h2.
apply/eqP; rewrite xpair_eqE; apply/andP.
by split; apply/eqP/inj_implem.
Qed.

Global Program Instance Zero_BB : Zero (B * B) := (0%C,1%C).
Global Program Instance ZeroMorph_BB : Morph implem (0 : rational)%C (0 : B*B)%C.
Obligation 1.
rewrite /implem /implem_op /rat'_implem /=.
rewrite /zero /Zero_BB.
rewrite zeroE.
by rewrite oneE.
Qed.

Global Program Instance ZeroMorph_rat : Morph implem (0 : rat) (0 : B*B)%C.
Obligation 1.
exact: (@MorphTrans rat).
Qed.

Global Program Instance Add_BB : Add (B * B) :=
  fun x y => (add x.1 y.1, add x.2 y.2).
(* Morphism from rat' to B * B for addition *)
Global Program Instance AddMorph_BB : Morph (implem ==> implem ==> implem )
  (fun x y : rational => x + y)%C (fun x y : B * B => x + y)%C.
Obligation 1.
rewrite /Morph /implem /= => x _ <- y _ <- /=.
rewrite /implem_op /rat'_implem /=.
case: (val_rational x) => a b.
case: (val_rational y) => c d /=.
(* ARRGH! Why do we have to give these explicitly??? *)
rewrite (@addE _ (| a |)%C _ _ (| c |)%C) //.
by rewrite (@addE _ (| b |)%C _ _ (| d |)%C).
Qed.

Global Instance AddMorph_rat :
  Morph (implem ==> implem ==> implem) (fun x y : rat => x + y) (fun x y : B * B => x + y)%C.
Proof.
(* have := (@MorphTrans rat rat' (B*B) _ rat'_implem _ _ _ _ AddMorph_BB). *)
admit.
Qed.

End refines.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint. *)

(* Eval compute in (0%C + 0%C + 0%C)%C : Z * Z. *)