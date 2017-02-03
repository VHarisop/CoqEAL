From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
From mathcomp Require Import path choice fintype tuple finset bigop poly polydiv.

From CoqEAL Require Import hrel param refinements poly_op.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op Poly.Op.

Local Open Scope ring_scope.
Local Open Scope rel.

Section karatsuba_generic.

Variable polyA N : Type.

Context `{Op.add_of polyA, Op.mul_of polyA, Op.sub_of polyA}.
Context `{shiftp : shift_of polyA N, sizep : Op.size_of polyA N}.
Context `{splitp : split_of polyA N}.
Context `{Op.one_of N, Op.add_of N, Op.mul_of N, Op.leq_of N}.
Context `{spec_of N nat, Op.implem_of nat N}.

Fixpoint karatsuba_rec n (p q : polyA) := match n with
  | 0     => (p * q)%C
  | n'.+1 =>
      let sp := sizep p in let sq := sizep q in
      if (sp <= 1 + 1)%C || (sq <= 1 + 1)%C then (p * q)%C else
        let m       := implem (minn (spec sp)./2 (spec sq)./2) in
        let (p1,p2) := splitp m p in
        let (q1,q2) := splitp m q in
        let p1q1    := karatsuba_rec n' p1 q1 in
        let p2q2    := karatsuba_rec n' p2 q2 in
        let p12     := (p1 + p2)%C in
        let q12     := (q1 + q2)%C in
        let p12q12  := karatsuba_rec n' p12 q12 in
        (shiftp ((1 + 1) * m)%C p1q1 +
         shiftp m (p12q12 - p1q1 - p2q2) +
         p2q2)%C
  end.

Definition karatsuba p q :=
  karatsuba_rec (maxn (spec (sizep p)) (spec (sizep q))) p q.

End karatsuba_generic.

Parametricity karatsuba_rec.
Parametricity karatsuba.

Section karatsuba_correctness.

Local Open Scope rel_scope.

Variable R : ringType.

Instance add_polyR : Op.add_of {poly R} := +%R.
Instance mul_polyR : Op.mul_of {poly R} := *%R.
Instance sub_polyR : Op.sub_of {poly R} := fun x y => (x - y)%R.
Instance size_polyR : Op.size_of {poly R} nat := sizep (R:=R).
Instance shift_polyR : shift_of {poly R} nat := shiftp (R:=R).
Instance split_polyR : split_of {poly R} nat := splitp (R:=R).

Local Instance one_nat    : Op.one_of nat        := 1%N.
Local Instance add_nat    : Op.add_of nat        := addn.
Local Instance mul_nat    : Op.mul_of nat        := muln.
Local Instance leq_nat    : Op.leq_of nat        := ssrnat.leq.
Local Instance spec_nat   : spec_of nat nat   := spec_id.
Local Instance implem_nat : Op.implem_of nat nat := Op.implem_id.

Lemma karatsuba_recE n (p q : {poly R}) : karatsuba_rec (N:=nat) n p q = p * q.
Proof.
elim: n=> //= n ih in p q *; case: ifP=> // _; set m := minn _ _.
rewrite [p in RHS](rdivp_eq (monicXn _ m)) [q in RHS](rdivp_eq (monicXn _ m)).
rewrite /shift_op /shift_polyR /shiftp /implem /implem_nat /Op.implem_id.
simpC.
rewrite !ih !(mulrDl, mulrDr, mulNr) mulnC exprM.
rewrite -addrA -addrA -opprD [X in X + _ - _]addrC addrACA addrK.
by rewrite !(commr_polyXn, mulrA, addrA).
Qed.

Lemma karatsubaE (p q : {poly R}) : karatsuba (N:=nat) p q = p * q.
Proof. exact: karatsuba_recE. Qed.

Section karatsuba_param.

Context (polyC : Type) (RpolyC : {poly R} -> polyC -> Type).
Context (N : Type) (rN : nat -> N -> Type).
Context `{Op.add_of polyC, Op.mul_of polyC, Op.sub_of polyC}.
Context `{Op.one_of N, Op.add_of N, Op.mul_of N, Op.leq_of N}.
Context `{spec_of N nat, Op.implem_of nat N}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) +%R +%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) *%R *%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) (fun x y => x - y)%R sub_op}.
Context `{!refines rN 1%N 1%C}.
Context `{!refines (rN ==> rN ==> rN) addn +%C}.
Context `{!refines (rN ==> rN ==> rN) muln *%C}.
Context `{!refines (rN ==> rN ==> bool_R) ssrnat.leq leq_op}.
Context `{!refines (rN ==> nat_R) spec_id spec,
          !refines (nat_R ==> rN) Op.implem_id implem}.

Context `{!shift_of polyC N}.
Context `{!refines (rN ==> RpolyC ==> RpolyC) shift_op shift_op}.

Context `{!Op.size_of polyC N}.
Context `{!refines (RpolyC ==> rN) size_op size_op}.

Context `{!split_of polyC N}.
Context `{!refines (rN ==> RpolyC ==> prod_R RpolyC RpolyC) split_op split_op}.

Instance ref_RpolyC : 'refinement RpolyC.
Instance ref_rN : 'refinement rN.
Instance ref_nat_R : 'refinement nat_R | 999.

Global Instance RpolyC_karatsuba_rec :
  refines (nat_R ==> RpolyC ==> RpolyC ==> RpolyC)
          (karatsuba_rec (polyA:={poly R}) (N:=nat))
          (karatsuba_rec (polyA:=polyC) (N:=N)).
Proof. by param karatsuba_rec_R. Qed.
  

Global Instance RpolyC_karatsuba :
  refines (RpolyC ==> RpolyC ==> RpolyC)
    (karatsuba (polyA:={poly R}) (N:=nat)) (karatsuba (polyA:=polyC) (N:=N)).
Proof. param karatsuba_R. Qed.

(* Global Instance RpolyC_karatsuba_mul p sp q sq : *)
(*   refines_rec RpolyC p sp -> refines_rec RpolyC q sq ->
  refines RpolyC (p * q) (karatsuba (N:=N) sp sq).
Proof.
  move=> hp hq.
  rewrite refinesE -karatsubaE.
  exact: refinesP.
Qed.
 *)
End karatsuba_param.
End karatsuba_correctness.

Section karatsuba_test.

From mathcomp Require Import ssrint.
From CoqEAL Require Import binnat binint seqpoly.

Local Instance ref_Rnat : 'refinement Rnat.
(* Instance ref_nat_eq : 'refinement (@eq nat) | 99. *)
Local Instance ref_Rpos : 'refinement Rpos.
Local Instance ref_RZNP: 'refinement (RZNP Rnat Rpos).
(* Local Instance ref_seq A B (R : A -> B -> Type) :
 'refinement R -> 'refinement (list_R R).
 *)
(* Local Instance ref_RseqpolyC (P : ringType) C (R : P -> C -> Type) : *)
(*    'refinement R -> 'refinement (RseqpolyC R). *)

Local Instance ref_RseqpolyC :
    'refinement (RseqpolyC (RZNP Rnat Rpos)).

Goal ((1 + 2%:Z *: 'X) * (1 + 2%:Z%:P * 'X) == 1 + 4%:Z *: 'X + 4%:Z%:P * 'X^2).
by coqeal.
Abort.

Goal (Poly [:: 1; 2%:Z] * Poly [:: 1; 2%:Z]) == Poly [:: 1; 4%:Z; 4%:Z].
rewrite /=.
by coqeal.
Abort.

Fixpoint bigseq (x : int) (n : nat) : seq int := match n with
  | 0 => [:: x]
  | n'.+1 => x :: bigseq (x+1) n'
  end.

Fixpoint bigpoly (x : int) (n : nat) : {poly int} :=
  match n with
  | 0 => x%:P
  | n.+1 => x%:P + (bigpoly (x+1) n) * 'X
  end.


(* Local Instance ref_seq A B (R : A -> B -> Type) : *)
(*  'refinement R -> 'refinement (list_R R). *)

(* Local Instance ref_RseqpolyC (P : ringType) C (R : P -> C -> Type) : *)
(*    'refinement R -> 'refinement (RseqpolyC R). *)

Let p1 := Eval compute in bigseq 1 1.
Let p2 := Eval compute in bigseq 2 1.

Let q1 := Eval simpl in bigpoly 1 10.
Let q2 := Eval simpl in bigpoly 2 10.

Typeclasses Opaque karatsuba.
Opaque karatsuba.
(* Set Typeclasses Filtered Unification. *)
(* Set Typeclasses Unique Instances. *)
(* TODO: Translate Poly directly? *)
Goal (Poly p1 * Poly p2 == Poly p2 * Poly p1).
rewrite /=.
(* rewrite -!karatsubaE. *)
Set Typeclasses Debug Verbosity 2.
rewrite [X in X == _](coqeal unify).
by coqeal.
Abort.

Goal (q1 * q2 == q2 * q1).
rewrite /q1 /q2.
coqeal.
Abort.

End karatsuba_test.
