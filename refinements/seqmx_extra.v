From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import finset fintype poly matrix.

From Polyhedra Require Import vector_order.
From CoqEAL Require Import hrel param refinements trivial_seq seqmx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.

Open Scope ring_scope.

Section classes.

(* see vector_order.v *)
Class hlev_of I B := hlev_op : forall n : I, B n 1%N -> B n 1%N  -> bool.
Local Notation "<=m%HC" := hlev_op.
Local Notation "x <=m%HC y" := (hlev_op x y) (at level 0) : hetero_computable_scope.
Local Notation "x >=m%HC y" := (hlev_op y x) (only parsing, at level 0) : hetero_computable_scope.

End classes.

Typeclasses Transparent hlev_of.

Notation "<=m%HC":= hlev_op.
Notation "x <=m y" := (hlev_op x y) (at level 0) : hetero_computable_scope.
Notation "x >=m y" := (hlev_op y x) (only parsing, at level 0) : hetero_computable_scope.

Section seqmx_extra_op.

Variable A : Type.

Variable I : nat -> Type.

Context `{zero_of A, one_of A, add_of A, opp_of A, mul_of A, eq_of A, leq_of A}.
Context `{forall n, implem_of 'I_n (I n)}.

Global Instance lev_seqmx : @hlev_of nat (@hseqmx A) :=
  fun n v u =>
    let v' := map (head 0%C) v in
    let u' := map (head 0%C) u in
    foldl andb true (zipwith leq_op v' u').

End seqmx_extra_op.

Parametricity lev_seqmx.

Section seqmx_extra_refinements.

Variable rF : realFieldType.
Global Instance zeroF : zero_of rF := 0%R.
Local Instance oneF  : one_of rF := 1%R.
Local Instance oppF  : opp_of rF := -%R.
Local Instance addF  : add_of rF := +%R.
Local Instance mulF  : mul_of rF := *%R.
Local Instance leqF  : leq_of rF := fun x y => (x <= y)%R.
Local Instance eqF   : eq_of rF   := eqtype.eq_op.
Local Instance specF_field : spec_of rF rF := spec_id.

Local Instance implem_ord_field : forall n, (implem_of 'I_n 'I_n) :=
  fun _ => implem_id.

Local Open Scope rel_scope.

Global Instance Rseqmx_leq m1 m2 (rm : nat_R m1 m2) :
  refines (Rseqmx rm (nat_Rxx 1) ==> Rseqmx rm (nat_Rxx 1) ==> bool_R)
          (@lev rF m1) (@hlev_op _ _ _ _).
Proof.
  rewrite refinesE => u hu Hu v hv Hv.
  case/boolP: (u) <=m (v) => Hlev.
Admitted.

Context (C : Type) (rFAC : rF -> C -> Type).
Context (I : nat -> Type)
        (F : nat -> nat -> Type)
        (rI : forall n1 n2, nat_R n1 n2 -> 'I_n1 -> I n2 -> Type).
Context `{zero_of C, one_of C, opp_of C, add_of C, mul_of C, eq_of C, leq_of C}.
Context `{spec_of C rF}.
Context `{forall n, implem_of 'I_n (I n)}.
Context `{!refines rFAC 0%R 0%C, !refines rFAC 1%R 1%C}.
Context `{!refines (rFAC ==> rFAC) -%R -%C}.
Context `{!refines (rFAC ==> rFAC ==> rFAC) +%R +%C}.
Context `{!refines (rFAC ==> rFAC ==> rFAC) *%R *%C}.
Context `{!refines (rFAC ==> rFAC ==> bool_R) eqtype.eq_op eq_op}.

(** IMPORTANT: removing this from the context makes the (<=m) goal fail!!! *)
Context `{!refines (rFAC ==> rFAC ==> bool_R) leqF leq_op}.


Context `{!refines (rFAC ==> Logic.eq) spec_id spec}.
Context `{forall n1 n2 (rn : nat_R n1 n2),
             refines (ordinal_R rn ==> rI rn) implem_id implem}.

(* Locally *)
Notation RseqmxC := (RseqmxC rFAC).

Global Instance RseqmxC_lev m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC rm (nat_Rxx 1) ==> RseqmxC rm (nat_Rxx 1) ==> bool_R)
          (@lev rF m1) (@hlev_op _ _ _ _).
Proof.
  param_comp lev_seqmx_R; rewrite refinesE; last by apply: nat_Rxx.
Qed.

Global Instance refine_lev_seqmx m :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx 1) ==> RseqmxC (nat_Rxx m) (nat_Rxx 1)
                   ==> bool_R)
          (@lev rF m) (@hlev_op _ _ _ _).
Proof. exact: RseqmxC_lev. Qed.

Close Scope rel_scope.

End seqmx_extra_refinements.

Section test.

From mathcomp Require Import ssrint poly matrix rat.
From CoqEAL Require Import binint binord rational.

Goal ((3%:~R / 4%:~R) * (20%:~R / 15%:~R) == 1 :> rat).
by coqeal.
Abort.

Definition fN := \matrix_(i,j < 2) 1%:Q.
Definition fP := \matrix_(i,j < 2) 4%:Q.

Goal (col ord0 fN) != (col ord0 fP).
Proof.
  by coqeal.
Qed.

Goal (col ord0 fN) <=m (col ord0 fP).
Proof.
  by coqeal.
Qed.

End test.