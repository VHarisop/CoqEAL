Require Import String.
From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import ssrmatching.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Shortcut for triggering manual typeclass resolution *)
Ltac tc := do 1?(typeclasses eauto).

(* key type with scope *)
Definition Key := unit.
Delimit Scope key_scope with key.
Bind Scope key_scope with Key.

(***************************************)
(* No backtracking with error messages *)
(***************************************)
(* The errormessage typeclass deliberatly cuts typeclass backtracking *)
(* When some class is wrapped by errormessage, its solution is *)
(* independent from the rest of the Goal and an error message *)
(* is displayed in case of failure *)

Fact nobacktrack_key : Key. Proof tt.

Class nobacktrack (input output : unit) (print : bool) (str : string) (class : Type) :=
   nobacktrack_field : locked_with nobacktrack_key class.
Arguments nobacktrack _ _ _ str%string.
Hint Mode nobacktrack + - - - - : typeclass_instances.

Section nobacktrack.
Context (input output : unit) (print : bool) (str : string) (class : Type).
Local Notation nobacktrack := (nobacktrack input output print str class).
Lemma nobacktrackE : nobacktrack = class.
Proof. by rewrite /nobacktrack; case: nobacktrack_key. Qed.
Definition put_nobacktrack : nobacktrack -> class.
Proof. by rewrite nobacktrackE. Qed.
Definition get_nobacktrack : class -> nobacktrack.
Proof. by rewrite nobacktrackE. Qed.

End nobacktrack.

Hint Extern 0 (@nobacktrack tt _ false _ _) =>
  now apply (@get_nobacktrack _ tt _ _ _ _) : typeclass_instances.

Hint Extern 0 (@nobacktrack tt _ true _ _) =>
  tryif now apply (@get_nobacktrack _ tt _ _ _ _) then idtac
       else (once lazymatch goal with |- ?g => idtac g end; fail 1)
  : typeclass_instances.

Notation "'nobacktrack" := (@nobacktrack tt tt false "") (only parsing).
Notation "'message" := (@nobacktrack tt tt true).

(*****************************)
(* General reduction classes *)
(*****************************)

Tactic Notation  "context" "[" ssrpatternarg(pat) "]" tactic3(tac) :=
  let H := fresh "H" in let Q := fresh "Q" in let eqQ := fresh "eqQ" in
  ssrpattern pat => H;
  elim/abstract_context : (H) => Q eqQ; rewrite /H {H};
  tac; rewrite eqQ {Q eqQ}.

Class strategy_class (C : forall T, T -> T -> Prop) :=
   StrategyClass : C = @eq.
Hint Mode strategy_class + : typeclass_instances.

Class unify A (x y : A) := unify_rel : x = y.
Hint Mode unify - + - : typeclass_instances.
Global Instance unifyxx A (x : A) : unify x x := erefl.
Instance strategy_class_unify : strategy_class unify := erefl.

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

Lemma eval_eq C {eqC : strategy_class C} {T} {x x' : T}
   {rx : C _ x x'} : x = x'.
Proof. by rewrite eqC in rx. Qed.

Notation "'[' 'eval'  strategy  'of'  x ']'" :=
  (@eval_eq strategy _ _ x _ _).
Notation eval strategy := [eval strategy of _].
Notation "'[' 'eval'  strategy  'of'  x  'for'  y ']'" :=
  ([eval strategy of x] : y = _).

(******************************************************)
(* Introduces a unification step                      *)
(* between the output of a typeclass and a given term *)
(******************************************************)

Fact unify1_key : Key. Proof tt.
Class unify1 {X : Type} (class : X -> Type) x :=
   unify1_field : locked_with unify1_key (class x).
Lemma unify1E X class (x : X) : unify1 class x = class x.
Proof. by rewrite /unify1; case: unify1_key. Qed.
Global Instance unify_unify1 X class (x x' : X) :
  class x' -> unify x' x -> unify1 class x.
Proof. by rewrite unify1E => ? <-. Qed.
