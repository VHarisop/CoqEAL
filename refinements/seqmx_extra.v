From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import finset fintype poly matrix.

From Polyhedra Require Import vector_order inner_product.
From CoqEAL Require Import hrel param refinements trivial_seq seqmx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.
Import GRing.Theory Num.Theory.

Open Scope ring_scope.

Section classes.

(* see vector_order.v *)
Class hlev_of I B := hlev_op : forall n : I, B n 1%N -> B n 1%N  -> bool.
Local Notation "<=m%HC" := hlev_op.
Local Notation "x <=m%HC y" := (hlev_op x y) (at level 0) : hetero_computable_scope.
Local Notation "x >=m%HC y" := (hlev_op y x) (only parsing, at level 0) : hetero_computable_scope.

Class hvdot_of A I B := hvdot_op : forall n : I, B n 1%N -> B n 1%N -> A.
Local Notation "''[' u , v ]%HC" := (hvdot_op u v) : hetero_computable_scope.
Local Notation "''[' u ]%HC" := (hvdot_op u u ) : hetero_computable_scope.

End classes.

Typeclasses Transparent hlev_of hvdot_of.

Notation "<=m%HC":= hlev_op.
Notation "x <=m y" := (hlev_op x y) (at level 0) : hetero_computable_scope.
Notation "x >=m y" := (hlev_op y x) (only parsing, at level 0) : hetero_computable_scope.

Notation "''[' u , v ]%HC" := (hvdot_op u v) : hetero_computable_scope.
Notation "''[' u ]%HC" := (hvdot_op u u ) : hetero_computable_scope.

Section seqmx_extra_op.

Variable A : Type.
Variable I : nat -> Type.

Definition hord := fun _ : nat => nat.

Context `{zero_of A, one_of A, add_of A, opp_of A, mul_of A, eq_of A, leq_of A}.
Context `{forall n, implem_of 'I_n (I n)}.

Lemma foldr_true s : foldr andb true s = all (fun x => x == true) s.
Proof.
  elim: s => [// | s S Hind] //=; by case: s => //=.
Qed.

Global Instance lev_seqmx : @hlev_of nat (@hseqmx A) :=
  fun _ v u =>
    let v' := map (head 0%C) v in
    let u' := map (head 0%C) u in
    foldr andb true (zipwith leq_op v' u').

Global Instance vdot_seqmx : @hvdot_of A nat (@hseqmx A) :=
  fun _ v u =>
    let v' := map (head 0%C) v in
    let u' := map (head 0%C) u in
    foldr add_op 0%C (zipwith mul_op v' u').

End seqmx_extra_op.

Parametricity lev_seqmx.
Parametricity vdot_seqmx.

Section seqmx_extra_refinements.

Variable rF : realFieldType.
Global Instance zeroF : zero_of rF := 0%R.
Global Instance oneF  : one_of rF := 1%R.
Global Instance oppF  : opp_of rF := -%R.
Global Instance addF  : add_of rF := +%R.
Global Instance mulF  : mul_of rF := *%R.
Global Instance eqF   : eq_of rF   := eqtype.eq_op.
Global Instance leqF  : leq_of rF := fun x y => (x <= y)%R.
Global Instance specF_field : spec_of rF rF := spec_id.

Global Instance implem_ord_field : forall n, (implem_of 'I_n 'I_n) :=
  fun _ => implem_id.

Local Open Scope rel_scope.

Lemma list_R_eqxx {T} : forall x, list_R (@eq T) x x.
Proof.
  elim => [//= | hP P Hind].
  - exact: list_R_nil_R.
  - apply: list_R_cons_R; [ done | exact : Hind ].
Qed.

Lemma list_R_list_R_eq {T} : forall x, list_R (list_R (@eq T)) x x.
Proof.
  elim => [//= | hp P Pind].
  - exact: list_R_nil_R.
  - apply: list_R_cons_R; last by exact: Pind.
    exact: list_R_eqxx.
Qed.


Lemma foldr_cons (s : rF) (S : seq rF) :
  foldr +%R 0%R (s :: S) = s + foldr +%R 0%R S.
Proof.
  suff -> : s :: S = [:: s] ++ S by rewrite foldr_cat.
  done.
Qed.

Lemma foldr_bigsum (s : seq rF) : foldr +%R 0%R s = \big[+%R/0%R]_(i <- s) i.
Proof.
  elim: s => [//= | s S Hind]; first by rewrite big_nil.
  rewrite big_cons -Hind; exact: foldr_cons.
Qed.

Global Instance Rseqmx_leq m1 m2 (rm : nat_R m1 m2) :
  refines (Rseqmx rm (nat_Rxx 1) ==> Rseqmx rm (nat_Rxx 1) ==> bool_R)
          (@lev rF m1) (@hlev_op _ _ _ _).
Proof.
  rewrite refinesE => u hu Hu v hv Hv.
  case/boolP: (u) <=m (v) => Hlev; rewrite /hlev_op /lev_seqmx foldr_true.
  (* TODO : Use nth for element? *)
Admitted.

Global Instance Rseqmx_vdot m1 m2 (rm : nat_R m1 m2) :
  refines (Rseqmx rm (nat_Rxx 1) ==> Rseqmx rm (nat_Rxx 1) ==> eq)
          (@vdot m1 rF) (@hvdot_op _ _ _ _ _).
Proof.
  rewrite refinesE => u hu Hu v hv Hv.
  rewrite /vdot /hvdot_op /vdot_seqmx.
  have -> : [seq head 0%C i | i <- hu] = [seq u i ord0 | i in 'I_m1].
  - admit.
  have -> : [seq head 0%C i | i <- hv] = [seq v i ord0 | i in 'I_m1].
  - admit.
  rewrite foldr_bigsum.
Admitted.

Context (C : Type) (rFAC : rF -> C -> Type).
Context (I : nat -> Type)
        (rI : forall n1 n2, nat_R n1 n2 -> 'I_n1 -> I n2 -> Type).
Context `{zero_of C, one_of C, opp_of C, add_of C, mul_of C, eq_of C, leq_of C}.
Context `{spec_of C rF}.
Context `{forall n, implem_of 'I_n (I n)}.
Context `{!refines rFAC 0%R 0%C, !refines rFAC 1%R 1%C}.
Context `{!refines (rFAC ==> rFAC) -%R -%C}.
Context `{!refines (rFAC ==> rFAC ==> rFAC) +%R +%C}.
Context `{!refines (rFAC ==> rFAC ==> rFAC) *%R *%C}.
Context `{!refines (rFAC ==> rFAC ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines (eq ==> eq ==> eq) addF addF}.
Context `{!refines (eq ==> eq ==> eq) mulF mulF}.
Context `{!refines eq zeroF zeroF}.

(** IMPORTANT: removing this from the context makes the (<=m) goal fail!!! *)
Context `{!refines (rFAC ==> rFAC ==> bool_R) leqF leq_op}.

Context `{!refines (rFAC ==> eq) spec_id spec}.
Context `{forall n1 n2 (rn : nat_R n1 n2),
             refines (ordinal_R rn ==> rI rn) implem_id implem}.

(* Locally *)
Notation RseqmxC := (RseqmxC rFAC).

Global Instance RseqmxC_lev m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC rm (nat_Rxx 1) ==> RseqmxC rm (nat_Rxx 1) ==> bool_R)
          (@lev rF m1) (@hlev_op _ _ _ _).
Proof.
  param_comp lev_seqmx_R; rewrite refinesE; exact: nat_Rxx.
Qed.

Global Instance refine_lev_seqmx m :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx 1) ==> RseqmxC (nat_Rxx m) (nat_Rxx 1)
                   ==> bool_R)
          (@lev rF m) (@hlev_op _ _ _ _).
Proof. exact: RseqmxC_lev. Qed.

Global Instance RseqmxC_vdot m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC rm (nat_Rxx 1) ==> RseqmxC rm (nat_Rxx 1) ==> rFAC)
          (@vdot m1 rF) (@vdot_seqmx C _ _ _ m2).
Proof.
  param_comp vdot_seqmx_R. rewrite refinesE; exact: nat_Rxx.
Qed.

Global Instance refine_vdot_seqmx m :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx 1) ==> RseqmxC (nat_Rxx m) (nat_Rxx 1)
          ==> rFAC) (@vdot m rF) (@vdot_seqmx C _ _ _ _).
Proof.
  exact: RseqmxC_vdot.
Qed.

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

Definition vN := \matrix_(i < 5, j < 1) 2%:Q.
Definition vP := \matrix_(i < 5, j < 1) 1%:Q.

Goal (col ord0 fN) != (col ord0 fP).
Proof.
  Time by coqeal.
Qed.

Goal (col ord0 fN) <=m (col ord0 fP).
Proof.
  Time by coqeal.
Qed.

Goal vdot vN vP == 10%:Q.
Proof.
  Time by coqeal.
Qed.

Goal '[col ord0 fN, col ord0 fP] == 8%:Q.
Proof.
  Time by coqeal.
Qed.

Set Typeclasses Debug.

Goal vN (Ordinal (erefl (2 < 5)%N)) ord0 == 2%:Q.
Proof.
  Fail by coqeal.
Abort.

End test.
