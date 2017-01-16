From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
(* Require Import path choice fintype tuple finset ssralg bigop poly polydiv. *)
(* Require Import ssrint ZArith. *)

From CoqEAL Require Import hrel param.

Require Import ssrmatching.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic. *)

Delimit Scope computable_scope with C.
Local Open Scope rel.

(* Shortcut for triggering typeclass resolution *)
Ltac tc := do 1?typeclasses eauto.

(**************************)
(* Linking param and hrel *)
(**************************)

Lemma prod_RE A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  prod_R rA rB x y -> prod_hrel rA rB x y.
Proof. by case; split. Qed.

Lemma prod_RI A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  prod_hrel rA rB x y -> prod_R rA rB x y.
Proof. by move: x y => [x1 x2] [y1 y2] [] /=; constructor. Qed.

(*****************************)
(* General unification class *)
(*****************************)

Class unify A (x y : A) := unify_rel : x = y.
Global Instance unifyxx A (x : A) : unify x x := erefl.

(*********************************)
(* Compositionality of relations *)
(*********************************)

Fact composable_lock : unit. Proof. done. Qed.
Class composable A B C
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type) :=
  Composable : locked_with composable_lock (rAB \o rBC <= rAC).
Arguments composable A B C rAB%rel rBC%rel rAC%rel.

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

Module Import RefinesKeys.
Fact symbol : unit. Proof. done. Qed.
Fact recursive : unit. Proof. done. Qed.
End RefinesKeys.

Class refines_ key A B (R : A -> B -> Type) (m : A) (n : B) :=
  refines_rel : (locked_with key R) m n.
Arguments refines_ key {A B} R%rel m n : simpl never.
Hint Mode refines_ + - - - + - : typeclass_instances.

Lemma refinesE key A B (R : A -> B -> Type) : refines_ key R = R.
Proof. by rewrite /refines_ unlock. Qed.

Section refinements.
Variable key : unit.
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

Lemma refines_apply
  A B (R : A -> B -> Type) C D (R' : C -> D -> Type) :
  forall (c : A -> C) (d : B -> D), refines (R ==> R') c d ->
  forall (a : A) (b : B), refines R a b -> refines R' (c a) (d b).
Proof. by rewrite !refinesE => c d rcd a b rab; apply: rcd. Qed.

(* Composable and pairs *)
Lemma refines_prod_R A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  refines rA x.1 y.1 -> refines rB x.2 y.2 -> refines (prod_R rA rB) x y.
Proof. by rewrite !refinesE => *; apply: prod_RI; split. Qed.


Lemma refines_abstr A B C D (R : A -> B -> Type) (R' : C -> D -> Type)
      (c : A -> C) (d : B -> D):
        (forall (a :  A) (b : B), refines R a b -> refines R' (c a) (d b)) ->
        refines (R ==> R') c d.
Proof. by rewrite !refinesE; apply. Qed.

Lemma refines_abstr2 A B A' B' A'' B''
      (R : A -> B -> Type) (R' : A' -> B' -> Type) (R'' : A'' -> B'' -> Type)
      (f : A -> A' -> A'' ) (g : B -> B' -> B''):
        (forall (a : A)   (b : B), refines R a b ->
         forall (a' : A') (b' : B'), refines R' a' b' ->
        refines R'' (f a a') (g b b')) ->
        refines (R ==> R' ==> R'') f g.
Proof. by move=> H; do 2![eapply refines_abstr => *]; apply: H. Qed.

Lemma refines_comp_unify A B (R : A -> B -> Type) x y :
  refines (R \o (@unify B))%rel x y -> refines R x y.
Proof. move=> /refines_split12.
  rewrite !refinesE=> H.
  case: H=> ? h.
  case: h=> ? h2.
  by rewrite -h2.
Qed.

Lemma refines_bool_eq x y : refines bool_R x y -> refines eq x y.
Proof. by rewrite !refinesE=> [[]]. Qed.

Lemma refines_nat_eq x y : refines nat_R x y -> refines eq x y.
Proof. rewrite !refinesE; exact: nat_R_eq. Qed.

End refinements.

Definition refinesP := @refinesP_ recursive tt.

Definition refines_symbol_apply := @refines_apply symbol.
Global Existing Instance refines_symbol_apply | 99.

Definition refines_symbol_bool_eq := @refines_bool_eq symbol. 
Global Existing Instance refines_symbol_bool_eq.

Definition refines_symbol_nat_eq := @refines_nat_eq symbol.
Global Existing Instance refines_symbol_nat_eq.

Lemma refines_change key2 key1 A B (R : A -> B -> Type) :
  refines_ key1 R = refines_ key2 R.
Proof. by rewrite !refinesE. Qed.

Ltac refines_symbol :=
(* (once lazymatch goal with |- ?g => idtac "trying " g end); *)
tryif by [rewrite (@refines_change symbol); typeclasses eauto] then idtac
else (tryif eapply refines_apply then idtac (* "no shortcut" *)
   else (once lazymatch goal with |- ?g
       => idtac "cannot find refinement for" g end; fail 1)).

Hint Extern 0 (refines_ recursive _ _ _) =>
  refines_symbol : typeclass_instances.

Hint Extern 0 (refines_ symbol _ _ _)
  => apply trivial_refines; eassumption : typeclass_instances.

Hint Extern 0 (refines_ recursive (_ \o (@unify _))%rel _ _)
  => eapply refines_trans : typeclass_instances.

(* Tactic for doing parametricity proofs, it takes a parametricity
   theorem generated by the Parametricity plugin as argument *)
Ltac param x :=
  rewrite ?refinesE; do?move=> ?*;
  eapply x=> *; eapply refinesP;
  do ?eapply refines_apply; tc.

(* Special tactic when relation is defined using \o *)
Ltac param_comp x := eapply refines_trans; tc; param x.

Notation refines := (@refines_ symbol _ _).
Notation refines_in := (@refines_ recursive _ _).

Notation refines_eq := (@refines_eq_ recursive _ _ _ _).

Section global_refinements.

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

Global Instance refines_true : refines _ true _ :=
  trivial_refines _ bool_R_true_R.

Global Instance refines_false : refines _ false _ :=
  trivial_refines _ bool_R_false_R.

Global Instance refines_negb : refines (bool_R ==> bool_R) negb negb.
Proof. exact/trivial_refines/negb_R. Qed.

Global Instance refines_implb : refines (bool_R ==> bool_R ==> bool_R) implb implb.
Proof. exact/trivial_refines/implb_R. Qed.

Global Instance refines_andb : refines (bool_R ==> bool_R ==> bool_R) andb andb.
Proof. exact/trivial_refines/andb_R. Qed.

Global Instance refines_orb : refines (bool_R ==> bool_R ==> bool_R) orb orb.
Proof. exact/trivial_refines/orb_R. Qed.

Global Instance refines_addb : refines (bool_R ==> bool_R ==> bool_R) addb addb.
Proof. exact/trivial_refines/addb_R. Qed.

Global Instance refines_eqb : refines (bool_R ==> bool_R ==> bool_R) eqtype.eq_op eqtype.eq_op.
Proof. exact/trivial_refines/eqb_R. Qed.

Lemma refines_goal (G G' : Type) : refines (fun T T' => T' -> T) G G' -> G' -> G.
Proof. by rewrite refinesE. Qed.

Global Instance refines_leibniz_eq (T : eqType) (x y : T) b :
  refines bool_R (x == y) b -> refines (fun T' T => T -> T') (x = y) b.
Proof. by move=> /refines_bool_eq; rewrite !refinesE => <- /eqP. Qed.

End global_refinements.

Module Refinements.

(* Generic operations *)
Module Op.

Class zero_of A := zero : A.
Hint Mode zero_of + : typeclass_instances.
Class one_of A := one : A.
Hint Mode one_of + : typeclass_instances.
Class opp_of A := opp : A -> A.
Hint Mode opp_of + : typeclass_instances.
Class add_of A := add : A -> A -> A.
Hint Mode add_of + : typeclass_instances.
Class sub_of A := sub : A -> A -> A.
Hint Mode sub_of + : typeclass_instances.
Class mul_of A := mul : A -> A -> A.
Hint Mode mul_of + : typeclass_instances.
Class exp_of A B := exp : A -> B -> A.
Hint Mode exp_of + + : typeclass_instances.
Class div_of A := div : A -> A -> A.
Hint Mode div_of + : typeclass_instances.
Class inv_of A := inv : A -> A.
Hint Mode inv_of + : typeclass_instances.
Class mod_of A := mod : A -> A -> A.
Hint Mode mod_of + : typeclass_instances.
Class scale_of A B := scale : A -> B -> B.
Hint Mode scale_of + + : typeclass_instances.

Class eq_of A := eq : A -> A -> bool.
Hint Mode eq_of + : typeclass_instances.
Class leq_of A := leq : A -> A -> bool.
Hint Mode leq_of + : typeclass_instances.
Class lt_of A := lt : A -> A -> bool.
Hint Mode lt_of + : typeclass_instances.
Class size_of A N := size : A -> N.
Hint Mode size_of + + : typeclass_instances.

Class spec_of A B   := spec : A -> B.
Hint Mode spec_of + + : typeclass_instances.
Definition spec_id {A : Type} : spec_of A A := id.
Class implem_of A B := implem : A -> B.
Hint Mode implem_of + + : typeclass_instances.
Definition implem_id {A : Type} : implem_of A A := id.
Class cast_of A B  := cast : A -> B.
Hint Mode cast_of + + : typeclass_instances.

Module Exports.

Typeclasses Transparent zero_of one_of opp_of add_of sub_of mul_of exp_of div_of
            inv_of mod_of scale_of size_of eq_of leq_of lt_of spec_of implem_of cast_of.

Arguments spec / A B spec_of _: assert.

Notation "0"      := zero        : computable_scope.
Notation "1"      := one         : computable_scope.
Notation "-%C"    := opp.
Notation "- x"    := (opp x)     : computable_scope.
Notation "+%C"    := add.
Notation "x + y"  := (add x y)   : computable_scope.
Notation "x - y"  := (sub x y)   : computable_scope.
Notation "*%C"    := mul.
Notation "x * y"  := (mul x y)   : computable_scope.
Notation "x ^ y"  := (exp x y)   : computable_scope.
Notation "x %/ y" := (div x y)   : computable_scope.
Notation "x ^-1"  := (inv x)     : computable_scope.
Notation "x %% y" := (mod x y)   : computable_scope.
Notation "*:%C"   := scale.
Notation "x *: y" := (scale x y) : computable_scope.
Notation "x == y" := (eq x y)    : computable_scope.
Notation "x <= y" := (leq x y)   : computable_scope.
Notation "x < y"  := (lt x y)    : computable_scope.
Notation cast     := (@cast _).

End Exports.

Module Compat.

Notation zero_op := zero.
Notation one_op := one.
Notation opp_op := opp.
Notation add_op := add.
Notation sub_op := sub.
Notation mul_op := mul.
Notation exp_op := exp.
Notation div_op := div.
Notation inv_op := inv.
Notation mod_op := mod.
Notation scale_op := scale.
Notation size_op := size.
Notation eq_op := eq.
Notation leq_op := leq.
Notation lt_op := lt.
Notation spec := spec.
Notation implem := implem.
Notation cast_op := cast.

End Compat.
End Op.
End Refinements.

Import Refinements.
Export Op.Exports.
Export Op.Compat.

Ltac simpC :=
  do ?[ rewrite -[0%C]/0%R
      | rewrite -[1%C]/1%R
      | rewrite -[(_ + _)%C]/(_ + _)%R
      | rewrite -[(_ + _)%C]/(_ + _)%N
      | rewrite -[(- _)%C]/(- _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%N
      | rewrite -[(_ * _)%C]/(_ * _)%R
      | rewrite -[(_ * _)%C]/(_ * _)%N
      | rewrite -[(_ %/ _)%C]/(_ %/ _)%R
      | rewrite -[(_ %% _)%C]/(_ %% _)%R
      | rewrite -[(_ == _)%C]/(_ == _)%bool
      ].


(* Workaround because casts are not retained for hypothesis, so we
design this elimination lemma to abstract the context and vm_compute in the goal *)
Lemma abstract_context T (P : T -> Type) x : (forall Q, Q = P -> Q x) -> P x.
Proof. by move=> /(_ P); apply. Qed.

Tactic Notation  "context" "[" ssrpatternarg(pat) "]" tactic3(tac) :=
  let H := fresh "H" in let Q := fresh "Q" in let eqQ := fresh "eqQ" in
  ssrpattern pat => H;
  elim/abstract_context : (H) => Q eqQ; rewrite /H {H};
  tac; rewrite eqQ {Q eqQ}.

Class strategy_class (C : forall T, T -> T -> Prop) :=
   StrategyClass : C = @eq.
Hint Mode strategy_class + : typeclass_instances.

Class native_compute T (x y : T) := NativeCompute : x = y.
Hint Mode native_compute - + - : typeclass_instances.
Hint Extern 0 (native_compute _ _) =>
  context [(X in native_compute X)] native_compute; reflexivity :
  typeclass_instances.
Instance strategy_class_native_compute : strategy_class native_compute := erefl.

Class vm_compute T (x y : T) := VmCompute : x = y.
Hint Mode vm_compute - + - : typeclass_instances.
Hint Extern 0 (vm_compute _ _) =>
  context [(X in vm_compute X)] vm_compute; reflexivity :
  typeclass_instances.
Instance strategy_class_vm_compute : strategy_class vm_compute := erefl.

Class compute T (x y : T) := Compute : x = y.
Hint Mode compute - + - : typeclass_instances.
Hint Extern 0 (compute _ _) =>
  context [(X in compute X)] compute; reflexivity :
  typeclass_instances.
Instance strategy_class_compute : strategy_class compute := erefl.

Class simpl T (x y : T) := Simpl : x = y.
Hint Mode simpl - + - : typeclass_instances.
Hint Extern 0 (simpl _ _) =>
  context [(X in simpl X)] simpl; reflexivity :
  typeclass_instances.
Instance strategy_class_simpl : strategy_class simpl := erefl.

Lemma coqeal_eq C {eqC : strategy_class C} {T T'} spec (x x' : T) {y y' : T'}
   {rxy : refines_in eq (Op.spec_id x) (spec y)}  {ry : C _ y y'}
   {rx : simpl (spec y') x'} : x = x'.
Proof. by rewrite eqC in ry; rewrite -rx -ry; apply: refines_eq. Qed.

Notation "'[' 'coqeal'  strategy  'of'  x ']'" :=
  (@coqeal_eq strategy _ _ _ _ x _ _ _ _ _ _).
Notation coqeal strategy := [coqeal strategy of _].
Notation "'[' 'coqeal'  strategy  'of'  x  'for'  y ']'" :=
  ([coqeal strategy of x] : y = _).

Ltac coqeal := apply: refines_goal; vm_compute.
Tactic Notation "coqeal_" tactic3(tac) :=  apply: refines_goal; tac.
Tactic Notation "coqeal" "[" ssrpatternarg(pat) "]" open_constr(strategy) :=
  let H := fresh "H" in let Q := fresh "Q" in let eqQ := fresh "eqQ" in
  ssrpattern pat => H; elim/abstract_context : (H) => Q eqQ;
  rewrite /H {H} [(X in Q X)](coqeal strategy) eqQ {Q eqQ}.

Ltac refines_apply1 := eapply refines_apply; tc.
Ltac refines_abstr1 := eapply refines_abstr=> ???; tc.
Ltac refines_apply := do ![refines_apply1].
Ltac refines_abstr := do ![refines_abstr1].
Ltac refines_trans :=  eapply refines_trans; tc.

Lemma spec_refines_ key A B R a a' b `{Op.spec_of B A} :
  refines_in (R ==> Logic.eq) Op.spec_id Op.spec ->
  refines_in R a a' ->
  refines_in R (Op.spec a') b -> refines_ key R a b.
Proof. by rewrite !refinesE /= => specP /specP <-. Qed.

Lemma spec_refinesP_ key A B R a a' b `{Op.spec_of B A} :
  refines_in (R ==> Logic.eq) Op.spec_id spec ->
  refines_in R a a' ->
  R (Op.spec a') b -> refines_ key R a b.
Proof. by move=> *; apply/spec_refines_. Qed.

Lemma eq_spec_refines_ key A B (R : A -> B -> Type) (a : A) (a' b : B) :
  refines_in R a a' -> a' = b -> refines_ key R a b.
Proof. by rewrite !refinesE => Raa' <-. Qed.

Definition spec_refines : forall A B R a a' b H, _ -> _ -> _ -> R a b :=
  @spec_refines_ tt.
Definition spec_refinesP : forall A B R a a' b H, _ -> _ -> _ -> R a b :=
  @spec_refinesP_ tt.
Definition eq_spec_refines : forall A B R a a' b, _ -> _ -> R a b :=
  @eq_spec_refines_ tt.

Ltac refines_abstrE := refines_abstr; rewrite !refinesE.
