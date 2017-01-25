(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
From CoqEAL Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op GRing.Theory.

Record pos := pos_of {
                  val_of_pos : nat;
                  _ : (val_of_pos > 0)%N
                }.
Canonical pos_subType := [subType for val_of_pos].
Typeclasses Transparent pos_subType.

Definition pos_eqMixin := [eqMixin of pos by <:].
Canonical pos_eqType := EqType pos pos_eqMixin.

Section pos.

Definition posS (n : nat) : pos := @pos_of n.+1 isT.

Global Instance pos1    : Op.one_of pos := posS 0.
Global Instance add_pos : Op.add_of pos := fun m n => insubd pos1 (val m + val n).
Global Instance sub_pos : Op.sub_of pos := fun m n => insubd pos1 (val m - val n).
Global Instance mul_pos : Op.mul_of pos := fun m n => insubd pos1 (val m * val n).
Global Instance exp_pos : Op.exp_of pos pos :=
  fun m n => insubd pos1 (val m ^ val n).
Global Instance leq_pos : Op.leq_of pos := fun m n => val m <= val n.
Global Instance lt_pos  : Op.lt_of pos  := fun m n => val m < val n.
Global Instance eq_pos  : Op.eq_of pos  := eqtype.eq_op.

Global Instance cast_pos_nat : Op.cast_of pos nat := val.
Global Instance cast_nat_pos : Op.cast_of nat pos := insubd 1%C.

Local Open Scope ring_scope.
Definition pos_to_int (p : pos) : int := (val p)%:R.
Definition int_to_nat (z : int) : nat := if z > 0 then `|z|%N else 0%N.
Definition int_to_pos (z : int) : pos := insubd pos1 (int_to_nat z).

End pos.