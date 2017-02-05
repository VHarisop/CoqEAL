From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Delimit Scope computable_scope with C.

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

Class implem_of A B := implem : A -> B.
Hint Mode implem_of + + : typeclass_instances.
Definition implem_id {A : Type} : implem_of A A := id.
Class cast_of A B  := cast : A -> B.
Hint Mode cast_of + + : typeclass_instances.

Module Exports.

Hint Transparent zero_of one_of opp_of add_of sub_of mul_of exp_of div_of
            inv_of mod_of scale_of size_of eq_of leq_of lt_of implem_of cast_of : coqeal.

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

Hint Opaque GRing.zero GRing.one GRing.add GRing.opp GRing.mul : coqeal.
Hint Opaque GRing.exp GRing.inv : coqeal.

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
Notation implem := implem.
Notation cast_op := cast.

End Compat.
End Op.

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