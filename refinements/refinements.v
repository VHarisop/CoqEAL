From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
Require Import String.
Require Import ssrmatching.

From CoqEAL Require Import hrel param.
From CoqEAL Require Export tclib.
From CoqEAL Require Import ops.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope rel.

(**************************)
(* Linking param and hrel *)
(**************************)

Lemma prod_RE A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  prod_R rA rB x y -> prod_hrel rA rB x y.
Proof. by case; split. Qed.

Lemma prod_RI A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  prod_hrel rA rB x y -> prod_R rA rB x y.
Proof. by move: x y => [x1 x2] [y1 y2] [] /=; constructor. Qed.

(*********************************)
(* Compositionality of relations *)
(*********************************)

Fact composable_lock : unit. Proof. done. Qed.
Class composable A B C
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type) :=
  Composable : locked_with composable_lock (rAB \o rBC <= rAC).
Arguments composable A B C rAB%rel rBC%rel rAC%rel.
Hint Mode composable - - - - - + : typeclass_instances.

Lemma composableE A B C
 (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type) :
  composable rAB rBC rAC = (rAB \o rBC <= rAC).
Proof. by rewrite /composable unlock. Qed.

Global Instance composable_comp A B C (rAB : A -> B -> Type)
  (rBC : B -> C -> Type) : composable rAB rBC (rAB \o rBC).
Proof. by rewrite composableE. Qed.

Global Instance composable_imply A B C A' B' C'
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (R1 : A' -> B' -> Type)
  (R2 : B' -> C' -> Type) (R3 : A' -> C' -> Type) : composable R1 R2 R3 ->
  composable (rAB ==> R1) (rBC ==> R2) (rAB \o rBC ==> R3) | 0.
Proof.
rewrite !composableE => R123 fA fC [fB [RfAB RfBC]] a c [b [rABab rBCbc]].
apply: R123; exists (fB b); split; [ exact: RfAB | exact: RfBC ].
Qed.

Global Instance composable_imply_id1 A B A' B' C'
  (rAB : A -> B -> Type) (R1 : A' -> B' -> Type) (R2 : B' -> C' -> Type)
  (R3 : A' -> C' -> Type) : composable R1 R2 R3 ->
  composable (eq ==> R1) (rAB ==> R2) (rAB ==> R3) | 1.
Proof.
rewrite !composableE => R123 fA fC [fB [RfAB RfBC]] a c rABac.
apply: R123; exists (fB a); split; [ exact: RfAB | exact: RfBC ].
Qed.

Global Instance composable_rid1 A B (R : A -> B -> Type) :
  composable eq R R | 2.
Proof.
rewrite composableE; apply: eq_hrelRL.
by split; [ apply: comp_eql | move=> x y hxy; exists x ].
Qed.

Global Instance composable_bool_id1 B (R : bool -> B -> Type) :
  composable bool_R R R | 1.
Proof. by rewrite composableE => x y [y' [[]]]. Qed.

(* Global Instance composable_nat_id1 B (R : nat -> B -> Type) :
  composable nat_R R R | 1. *)
(* Proof. by rewrite composableE => x y [y' [/nat_R_eq ->]]. Qed. *)

Global Instance composable_prod A A' B B' C C'
  (rAB : A -> B -> Type) (rAB' : A' -> B' -> Type)
  (rBC : B -> C -> Type) (rBC' : B' -> C' -> Type)
  (rAC : A -> C -> Type) (rAC' : A' -> C' -> Type) :
    composable rAB rBC rAC ->
    composable rAB' rBC' rAC' ->
    composable (prod_R rAB rAB') (prod_R rBC rBC')
               (prod_R rAC rAC') | 1.
Proof.
rewrite !composableE=> h1 h2 [a a'] [c c'] [[b b']].
move=> [/prod_RE [/= ??] /prod_RE [/= ??]].
by split; [ apply: h1; exists b | apply: h2; exists b'].
Qed.

(************************)
(* Refinement typeclass *)
(************************)

Module RefinesKeys.
Fact symbol : Key. Proof. done. Qed.
Fact recursive : Key. Proof. done. Qed.
Fact unify : Key -> Key. Proof. done. Qed.
Fact eq : Key. Proof. done. Qed.
(* Fact memoize : Key -> Key. Proof. done. Qed. *)
End RefinesKeys.

Notation "'symbol" := RefinesKeys.symbol : key_scope.
Notation "'recursive" := RefinesKeys.recursive : key_scope.
Notation "'unify key" := (RefinesKeys.unify key) (at level 0) : key_scope.
Notation "'eq" := (RefinesKeys.eq) (at level 0) : key_scope.
(* Notation "'memoize key" := (RefinesKeys.memoize key) (at level 0) : key_scope. *)

Implicit Types (key : Key).

(* Registering the refinement relation *)

Class refinement (P C : Type) (R : P -> C -> Type) := {}.
Arguments refinement P C R : clear implicits.
Hint Mode refinement + - - : typeclass_instances.
Notation "'refinement R" := (refinement _ _ R) (at level 1, only parsing).

Instance refinement_pair (P P' C C' : Type)
  (R : P -> C -> Type) (R' : P' -> C' -> Type) :
  'nobacktrack ('refinement R) -> 'nobacktrack ('refinement R') ->
  'refinement (prod_R R R').

Instance refinement_fun (P P' C C' : Type)
  (R : P -> C -> Type) (R' : P' -> C' -> Type) :
  'nobacktrack ('refinement R) -> 'nobacktrack ('refinement R') -> 'refinement (R ==> R').

(* Refines for a given relation *)

Class refines_ key P C (R : P -> C -> Type) (p : P) (c : C) :=
  refines_rel : (locked_with key R) p c.
Arguments refines_ key%key {P C} R%rel p c%C : simpl never.
Hint Mode refines_ + - + - + - : typeclass_instances.

Lemma refinesE key A B (R : A -> B -> Type) : refines_ key R = R.
Proof. by rewrite /refines_ unlock. Qed.

Section refinements.
Variable key : Key.
Notation refines := (@refines_ key _ _).

Lemma refines_eq_ T (x y : T) : refines eq x y -> x = y.
Proof. by rewrite refinesE. Qed.

Lemma nat_R_eq x y : nat_R x y -> x = y.
Proof. by elim=> // m n _ ->. Qed.

Lemma refinesP_ key2 T T' (R : T -> T' -> Type) (x : T) (y : T') :
  refines R x y -> refines_ key2 R x y.
Proof. by rewrite !refinesE. Qed.

Lemma refines_trans A B C
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type)
  (a : A) (b : B) (c : C) : composable rAB rBC rAC ->
  refines rAB a b -> refines rBC b c -> refines rAC a c.
Proof.
by rewrite !refinesE composableE => rABC rab rbc; apply: rABC; exists b.
Qed.

Lemma trivial_refines T T' (R : T -> T' -> Type) (x : T) (y : T') :
  R x y -> refines R x y.
Proof. by rewrite refinesE. Qed.

Section refines_split.
Context {T} {Y} {Z} {R1 : T -> Y -> Type} {R2 : Y -> Z -> Type} {x : T} {z : Z}.

Lemma refines_split :
  refines (R1 \o R2) x z -> {y : Y & (refines R1 x y * refines R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

Lemma refines_split1 :
  refines (R1 \o R2) x z -> {y : Y & (refines R1 x y * R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

Lemma refines_split2 :
  refines (R1 \o R2) x z -> {y : Y & (R1 x y * refines R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

Lemma refines_split12 :
  refines (R1 \o R2) x z -> {y : Y & (R1 x y * R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

End refines_split.

Lemma refines_apply r1 r2 r3
  A B (R : A -> B -> Type) 
  {R_is_refinement : nobacktrack tt r1 true
   "refines_apply cannot find" ('refinement R)}
  C D (R' : C -> D -> Type) :
  forall (a : A) (b : B), 
  nobacktrack r1 r2 false "" (refines R a b) ->
  forall (c : A -> C) (d : B -> D), 
  nobacktrack r2 r3 false "" (refines (R ==> R') c d) ->
  refines R' (c a) (d b).
Proof.
rewrite !refinesE.
move=> a b; rewrite nobacktrackE => rab.
move=> c d; rewrite nobacktrackE => rcd.
exact: rcd.
Qed.

(* Composable and pairs *)
Lemma refines_prod_R A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  refines rA x.1 y.1 -> refines rB x.2 y.2 -> refines (prod_R rA rB) x y.
Proof. by rewrite !refinesE => *; apply: prod_RI; split. Qed.

Lemma refines_abstr A B C D (R : A -> B -> Type) (R' : C -> D -> Type)
      (c : A -> C) (d : B -> D):
        (forall (a :  A) (b : B), R a b -> refines R' (c a) (d b)) ->
        refines (R ==> R') c d.
Proof. by rewrite !refinesE; apply. Qed.
Ltac refines_abstr1 := eapply refines_abstr=> ???.
Ltac refines_abstr := do ![refines_abstr1].
Ltac refines_abstrE := refines_abstr; rewrite !refinesE.

Lemma refines_abstr2 A B A' B' A'' B''
      (R : A -> B -> Type) (R' : A' -> B' -> Type) (R'' : A'' -> B'' -> Type)
      (f : A -> A' -> A'' ) (g : B -> B' -> B''):
        (forall (a : A)   (b : B), R a b ->
         forall (a' : A') (b' : B'), R' a' b' ->
        refines R'' (f a a') (g b b')) ->
        refines (R ==> R' ==> R'') f g.
Proof. by move=> H; refines_abstr; apply: H. Qed.

End refinements.

Definition refinesP := @refinesP_ 'recursive tt.

(* Definition refines_symbol_apply := @refines_apply 'symbol. *)
(* Global Existing Instance refines_symbol_apply | 99. *)

Definition refines_recursive_apply := @refines_apply 'recursive.
Global Existing Instance refines_recursive_apply | 99.

(* Definition refines_symbol_bool_eq := @refines_bool_eq 'symbol. *)
(* Global Existing Instance refines_symbol_bool_eq. *)

(* Definition refines_symbol_nat_eq := @refines_nat_eq 'symbol. *)
(* Global Existing Instance refines_symbol_nat_eq. *)

Lemma refines_change key2 key1 A B (R : A -> B -> Type) :
  refines_ key1 R = refines_ key2 R.
Proof. by rewrite !refinesE. Qed.

Lemma refines_subst key1 key2 A B (R : A -> B -> Type) x y :
  refines_ key1 R x y -> refines_ key2 R x y.
Proof. by rewrite !refinesE. Qed.

Definition refines_subst_rec := @refines_subst 'recursive.

Ltac refines_symbol :=
(* (once lazymatch goal with |- ?g => idtac "trying " g end); *)
tryif now apply (@refines_subst 'symbol _ _ _ _ _ _ _) then idtac
else (tryif eapply @refines_apply then fail 1 (* "no shortcut" *)
   else (once lazymatch goal with |- ?g
       => idtac "refines_symbol: cannot find refinement for" g end; fail 1)).

Hint Extern 0 (refines_ 'recursive _ _ _)
  => refines_symbol : typeclass_instances.

Hint Extern 0 (refines_ 'symbol _ _ _)
  => apply trivial_refines; eassumption : typeclass_instances.

Global Instance refines_trans_unify key A B (R : A -> B -> Type) x y :
  unify1 (refines_ key R x) y -> refines_ ('unify key) R x y.
Proof. by rewrite unify1E !refinesE. Qed.

Notation refines := (@refines_ 'symbol _ _).
Notation refines_rec := (@refines_ 'recursive _ _).
Notation refines_unify := (@refines_ ('unify 'recursive) _ _).

(* Notation refines_eq := (@refines_eq_ 'eq _ _ _). *)

(* Global Instance refines_bool_eq x y : refines bool_R x y -> refines_ 'eq eq x y. *)
(* Proof. by rewrite !refinesE=> [[]]. Qed. *)

(* Global Instance refines_nat_eq x y : refines nat_R x y -> refines_ 'eq eq x y. *)
(* Proof. rewrite !refinesE; exact: nat_R_eq. Qed. *)

Lemma refines_goal (G G' : Type) :
  refines_rec (fun T T' => T' -> T) G G' -> G' -> G.
Proof. by rewrite refinesE. Qed.

Definition spec_id {A : Type} : A -> A := id.

Module Refinements.

Export ops.

(* Generic spec *)
Module Op.
Class spec_of A B   := spec : A -> B.
Hint Mode spec_of + + : typeclass_instances.
Notation spec_id := spec_id.
Module Exports.
Typeclasses Transparent spec_of.
Arguments spec / A B spec_of _: assert.
End Exports.
Module Compat.
Notation spec := spec.
End Compat.
End Op.
End Refinements.

Import Refinements.
Export Op.Exports.
Export Op.Compat.

Lemma coqeal_eq
   C  {eqC : 'message "coqeal_eq cannot find"
         (strategy_class C)}
   C' {eqC' : 'message "coqeal_eq cannot find"
         (strategy_class C')}
   {T T'} spec (x x' : T) {y y' : T'}
   {R : T -> T' -> Type}
   {R_is_refinement : 'message "coqeal_eq cannot find"
       ('refinement R)}
   {rspec : 'message "coqeal_eq cannot find"
       (refines (R ==> Logic.eq) Op.spec_id spec)}
   {rxy : 'message "coqeal_eq cannot find"
       (refines_unify eq (Op.spec_id x) (spec y))}
   {ry : C _ y y'}
   {rx : C' _ (spec y') x'} : x = x'.
Proof.
rewrite -> nobacktrackE in *.
rewrite (refines_change 'recursive) in rxy.
rewrite eqC in ry; rewrite eqC' in rx; rewrite -rx -ry.
by rewrite -[x]/(Op.spec_id x); apply: refinesP.
Qed.

Notation "'[' 'coqeal'  strategy ,  spec_strategy  'of'  x ']'" :=
  (@coqeal_eq strategy _ spec_strategy _ _ _ _ _ _ x _ _ _ _ _ _).
Notation coqeal strategy := [coqeal strategy ,  unify of _].
Notation coqeal_noop := [coqeal unify ,  unify of _].
Notation coqeal_spec strategy := [coqeal strategy ,  simpl of _].
Notation "'[' 'coqeal'  strategy ,  spec_strategy  'of'  x  'for'  y ']'" :=
  ([coqeal strategy, spec_strategy of x] : y = _).

Ltac coqeal := apply: (refines_goal _ _); vm_compute.
Tactic Notation "coqeal_" tactic3(tac) :=  apply: refines_goal; tac.
Tactic Notation "coqeal" "[" ssrpatternarg(pat) "]" open_constr(strategy) :=
  let H := fresh "H" in let Q := fresh "Q" in let eqQ := fresh "eqQ" in
  ssrpattern pat => H; elim/abstract_context : (H) => Q eqQ;
  rewrite /H {H} [(X in Q X)](coqeal strategy) eqQ {Q eqQ}.

Ltac refines_apply1 := eapply refines_apply; tc.
Ltac refines_apply := do ![refines_apply1].
Ltac refines_trans :=  eapply refines_trans; tc.
Ltac refines_abstr1 := eapply refines_abstr=> ???.
Ltac refines_abstr := do ![refines_abstr1].
Ltac refines_abstrE := refines_abstr; rewrite !refinesE.

Lemma spec_refines_ key A B R a a' b `{Op.spec_of B A} :
  'message "spec_refines_: no spec found"
           (refines_rec (R ==> Logic.eq) Op.spec_id Op.spec) ->
  'message "spec_refines_: cannot refine" (refines_rec R a a') ->
  'message "spec_refines_: cannot refine" 
           (refines_rec R (Op.spec a') b) ->
  refines_ key R a b.
Proof. by rewrite !nobacktrackE !refinesE /= => specP /specP <-. Qed.

Lemma spec_refinesP_ key A B R a a' b `{Op.spec_of B A} :
  'message "spec_refinesP_: no spec found"
           (refines_rec (R ==> Logic.eq) Op.spec_id spec) ->
  'message "spec_refinesP_: cannot refine" (refines_rec R a a') ->
  R (Op.spec a') b -> refines_ key R a b.
Proof. by rewrite !nobacktrackE => *; apply: spec_refines_. Qed.

Lemma eq_spec_refines_ key A B (R : A -> B -> Type) (a : A) (a' b : B) :
  'message "eq_spec_refines_: cannot refine" 
           (refines_rec R a a') -> a' = b -> refines_ key R a b.
Proof. by rewrite !nobacktrackE !refinesE => Raa' <-. Qed.

Definition spec_refines : forall A B R a a' b H, _ -> _ -> _ -> R a b :=
  @spec_refines_ tt.
Definition spec_refinesP : forall A B R a a' b H, _ -> _ -> _ -> R a b :=
  @spec_refinesP_ tt.
Definition eq_spec_refines : forall A B R a a' b, _ -> _ -> R a b :=
  @eq_spec_refines_ tt.

(**************************)
(* Parametric refinements *)
(**************************)

Lemma refines_trans_param A B C
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type)
  (a : A) (b : B) (c : C) : 
  'message "refines_trans_param: cannot find compositionality" 
           (composable rAB rBC rAC) ->
  'message "refines_trans_param: cannot refine" (refines_rec rAB a b) -> 
  rBC b c -> refines rAC a c.
Proof.
by rewrite !nobacktrackE !refinesE composableE => rABC rab rbc; apply: rABC; exists b.
Qed.

Notation "'refines_trans_param" := (@refines_trans_param _ _ _ _ _ _ _ _ _ _ _ _).
(* Tactic for doing parametricity proofs, it takes a parametricity
   theorem generated by the Parametricity plugin as argument *)
Ltac param x := rewrite ?refinesE; do?move=> ?*;
  apply: x; do ?move=> ?*; eapply refinesP; tc.

(* Special tactic when relation is defined using \o *)
Ltac param_comp x := apply: 'refines_trans_param; param x.

(* Bool refinements *)
Global Instance refinement_bool : 'refinement bool_R := {}.

Global Instance refines_pair_R
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (rA ==> rB ==> prod_R rA rB)%rel (@pair _ _) (@pair _ _).
Proof. by rewrite refinesE. Qed.

Global Instance refines_fst_R
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (prod_R rA rB ==> rA)%rel (@fst _ _) (@fst _ _).
Proof. by rewrite !refinesE=> [??] [??]. Qed.

Global Instance refines_snd_R
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (prod_R rA rB ==> rB)%rel (@snd _ _) (@snd _ _).
Proof. by rewrite !refinesE=> [??] [??]. Qed.

Global Instance refines_true : refines bool_R true _ :=
  trivial_refines _ bool_R_true_R.

Global Instance refines_false : refines bool_R false _ :=
  trivial_refines _ bool_R_false_R.

Global Instance refines_negb : refines (bool_R ==> bool_R) negb negb.
Proof. by param negb_R. Qed.

Global Instance refines_implb : refines (bool_R ==> bool_R ==> bool_R) implb implb.
Proof. by param implb_R. Qed.

Global Instance refines_andb : refines (bool_R ==> bool_R ==> bool_R) andb andb.
Proof. by param andb_R. Qed.

Global Instance refines_orb : refines (bool_R ==> bool_R ==> bool_R) orb orb.
Proof. by param orb_R. Qed.

Global Instance refines_addb : refines (bool_R ==> bool_R ==> bool_R) addb addb.
Proof. by param addb_R. Qed.

Global Instance refines_eqb : refines (bool_R ==> bool_R ==> bool_R) eqtype.eq_op eqtype.eq_op.
Proof. by param eqb_R. Qed.

Global Instance refines_leibniz_eq (T : eqType) (x y : T) b :
  refines_rec bool_R (x == y) b -> refines_rec (fun T' T => T -> T') (x = y) b.
Proof. by rewrite !refinesE => eq_xy b_true; apply/eqP; case: eq_xy b_true. Qed.

Global Instance refines_bool_R_spec_id :
  refines (bool_R ==> eq) spec_id id.
Proof. by rewrite refinesE => ??[]. Qed.

Global Instance refines_eq_spec_id (T : Type) (R : T -> T -> Type) :
  refines (R ==> R) spec_id id.
Proof. by rewrite refinesE. Qed.

(* nat refinements *)

Global Instance refines_nat_R_0 : refines nat_R 0%N 0%N.
Proof. by param nat_R_O_R. Qed.

Global Instance refines_nat_R_S : refines (nat_R ==> nat_R) S S.
Proof. by param nat_R_S_R. Qed.

Global Instance refines_predn :  refines (nat_R ==> nat_R) predn predn.
Proof. by param pred_R. Qed.

Global Instance refines_addn :  refines (nat_R ==> nat_R ==> nat_R) addn addn.
Proof. by param addn_R. Qed.

Global Instance refines_subn :  refines (nat_R ==> nat_R ==> nat_R) subn subn.
Proof. by param subn_R. Qed.

Global Instance refines_leq :  refines (nat_R ==> nat_R ==> bool_R) leq leq.
Proof. by param leq_R. Qed.

Global Instance refines_muln :  refines (nat_R ==> nat_R ==> nat_R) muln muln.
Proof. by param muln_R. Qed.

Global Instance refines_expn :  refines (nat_R ==> nat_R ==> nat_R) expn expn.
Proof. by param expn_R. Qed.

Global Instance refines_odd :  refines (nat_R ==> bool_R) odd odd.
Proof. by param odd_R. Qed.

Global Instance refines_double :  refines (nat_R ==> nat_R) double double.
Proof. by param double_R. Qed.

Global Instance refines_eq_nat :
   refines (nat_R ==> nat_R ==> bool_R) eqtype.eq_op eqtype.eq_op.
Proof. by param eqn_R. Qed.

(****************************************)
(* Special case of identity refinements *)
(****************************************)

Record iffT L R := {iffTLR : L -> R; iffTRL : R -> L}.
Hint View iffTLR iffTRL | 2.
Notation is_eq R := (forall x y, iffT (R x y) (x = y)).

Lemma bool_R_is_eq : is_eq bool_R.
Proof. by move=> [] []; constructor=> // -[]. Qed.

Lemma nat_R_is_eq : is_eq nat_R.
Proof.
elim=> [|n IHn] [|m]; constructor;
  do ?by [constructor|inversion 1]; last first.
  by move<-; constructor; apply/IHn.
move eq_Sn: n.+1 => Sn eq_Smn.
by case: eq_Smn eq_Sn IHn => // p q eqpq [->] /(_ q) [->].
Qed.

Global Instance refines_spec_bool_R B (rB : bool -> B -> Type) spec :
  refines (rB ==> eq) spec_id spec ->
  refines (rB ==> bool_R) spec_id spec.
Proof.
by rewrite !refinesE /= => spec_is_id x y /spec_is_id ->; apply/bool_R_is_eq.
Qed.
  
Global Instance refines_spec_nat_R B (rB : nat -> B -> Type) spec :
  refines (rB ==> eq) spec_id spec ->
  refines (rB ==> nat_R) spec_id spec.
Proof.
by rewrite !refinesE /= => spec_is_id x y /spec_is_id ->; apply/nat_R_is_eq.
Qed.
