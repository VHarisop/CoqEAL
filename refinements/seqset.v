(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)

Require Import ZArith.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.

From CoqEAL Require Import hrel param refinements.

Import Refinements.Op.

(** seqset.v: An implementation of sets as sorted sequences
    containing unique elements *)
Local Open Scope computable_scope.

Section seqset_op.

Variable A : Type.
Variable N : Type.

Definition seqset := seq A.

Context `{zero_of A, one_of A, cast_of A}.
Context `{eq_of A}.
Context `{zero_of N, one_of N, add_of N, eq_of N}.
Context `{spec_of N nat}.

Global Instance cast_seqset : cast_of A seqset := fun x => [:: x].

Global Instance seqset0 : zero_of seqset := [::].
Global Instance seqsingleton x : one_of seqset := [:: x].

(** Returning if an element is a member of a set *)
Fixpoint seqset_mem (x : A) (p : seqset) : bool := match p with
  | [::] => false
  | h :: t => (eq_op h x) || seqset_mem x t
  end.

(** Finding if a set is subset of another set *)
Fixpoint seqset_sub_fun (p q : seqset) : bool := match p with
  | [::] => false
  | h :: t => (seqset_mem h q) && seqset_sub_fun t q
  end.

(** Equality on sets *)
Definition eq_seqset_fun (p q : seqset) : bool := 
  (seqset_sub_fun p q) && (seqset_sub_fun q p).
Global Instance eq_seqset : eq_of seqset := eq_seqset_fun.

(** Size of a set *)
Global Instance size_seqset : size_of seqset N :=
  let fix aux cnt p := match p with
  | [::] => cnt
  | _ :: t => aux (cnt + 1) t
  end
  in aux 0.

End seqset_op.

Parametricity cast_seqset.
Parametricity eq_seqset.
Parametricity seqset0.
Parametricity seqsingleton.
Parametricity size_seqset.