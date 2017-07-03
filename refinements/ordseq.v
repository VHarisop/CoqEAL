(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)

Require Import ZArith.

From mathcomp Require Import all_ssreflect.

From CoqEAL Require Import hrel param refinements.

Import Refinements.Op.

(** ordseq.v: An implementation of sets of ordinals as sorted sequences
    of nats containing unique elements *)
Local Open Scope computable_scope.

Section ordseq_op.

Variable A : eqType.
Variable N : Type.

Definition ordseq {A} := seq A.

Context `{zero_of A, one_of A, cast_of A}.
Context `{add_of A, sub_of A, eq_of A, leq_of A, lt_of A}.
(* Note: A is supposed to be a refinement of nat *)
Context `{Hnat: spec_of A nat}.
Context `{zero_of N, one_of N, add_of N, eq_of N, spec_of N nat}.

Global Instance cast_ordseq : cast_of A ordseq := fun x => [:: x].
Global Instance ordseq0 : zero_of (@ordseq A) := [::].
Global Instance ordseq_singleton x : one_of (@ordseq A) := [:: x].
Global Instance eq_ordseq : eq_of ordseq := @eqseq A.

Fixpoint ordseq_sublist (p q : ordseq) : bool :=
  (* mem_aux : returns true/false, plus the remaining list after the match
               in case the element has indeed been found *)
  let fix mem_aux (x : A) (p' : ordseq) : bool * ordseq := match p' with
  | [::] => (false, [::])
  | h :: t =>
      (* If element is found, return true and the rest of the other set *)
      if (h == x) then (true, t)
      else mem_aux x t
  end
  in
  match p with
  | [::] => true
  | h :: t => match mem_aux h q with
    | (false, _) => false
    | (true, t') => ordseq_sublist t t'
    end
  end.

(* Difference of two ordseqs *)
Definition ordseq_sub : sub_of (@ordseq A) :=
  let fix aux (a : ordseq) : ordseq -> ordseq := match a with
  | [::] => fun _ => [::]
  | h :: t => (fix aux_comp (b : ordseq) : ordseq :=
      match b with
      | [::] => a
      | h' :: t' =>
        if (h < h') then h :: (aux t b)
        else if (h == h') then aux t t'
        else aux_comp t'
      end)
  end
  in aux.

(* Union of two ordseqs *)
Definition ordseq_add : add_of (@ordseq A) :=
  fun a b => merge (fun x y => x <= y) a (ordseq_sub a b).

(** Returning if an element is a member of a set *)
Fixpoint ordseq_mem (x : A) (p : ordseq) : bool := match p with
  | [::] => false
  | h :: t => (eq_op h x) || ordseq_mem x t
  end.

(* Make use of spec_of A nat, which is in our context, to map an
   @ordseq A to a seq nat *)
Definition map_spec s := map (@spec A nat _) s.

(* Specification of an ordseq *)
Global Instance spec_ordseq : spec_of (@ordseq A) (seq nat) :=
  fun s => map_spec s.

(** Size of a set *)
Global Instance size_seqset : size_of (@seqset A) N :=
  let fix aux cnt p := match p with
  | [::] => cnt
  | _ :: t => aux (cnt + 1) t
  end
  in aux 0.

(** Adding an element to a set *)
Definition add_elem sset elem := if seqset_mem elem sset then sset else elem :: sset.

(** Adding two seqsets *)
Global Instance union_seqset : add_of seqset :=
  let fix aux p elems := match p with
  | [::] => elems
  | h :: t => aux t (add_elem elems h)
  end
  in aux.

End seqset_op.

Parametricity cast_seqset.
Parametricity eq_seqset.
Parametricity seqset0.
Parametricity seqsingleton.
Parametricity size_seqset.
Parametricity union_seqset.