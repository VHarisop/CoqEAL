From mathcomp Require Import
all_ssreflect ssralg ssrnum matrix fintype.

Require Import hrel param refinements seqmx seqmx_complements.

Import Refinements.Op.

(** Adopted from CoqEAL *)

Section ExtraSeq.

Fixpoint zipall {T1 T2 : Type} (f : T1 -> T2 -> bool)
  (s1 : seq T1) (s2 : seq T2) :=
  (* by convention, this is false if lists have different lengths *)
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then f x1 x2 && (zipall f s1' s2') else false
  else true.

Definition subseq_and_complement {T: Type} (s : seq T) (I : seq nat) :=
  let fix extract_subseq_aux s I acc_index :=
    match s, I with
    | x :: s', i :: I' =>
      if (i == acc_index) then
        let (subsq, compl) := extract_subseq_aux s' I' (acc_index.+1) in
        (x :: subsq, compl)
      else
        let (subsq, compl) := extract_subseq_aux s' I (acc_index.+1) in
        (subsq, x :: compl)
    | _, _ => ([::], s)
    end
  in extract_subseq_aux s I 0%N.

End ExtraSeq.

Section UntrustedInverse.

Variable R : unitRingType.
Variables m n : nat.
Implicit Type T : Type.

Local Open Scope ring_scope.

(** Modify a row of a seqmx, using MathComp's set_nth *)
Definition modify_row {T} (A : @seqmx T) (Ai : seq T) (i : nat) :=
  set_nth [::] A i Ai.

Definition swap_rows {T} (A : @seqmx T) (i j : nat) :=
  let (Ai, Aj) := (nth [::] A i, nth [::] A j) in
  let Amod := modify_row A Ai j in
  modify_row Amod Aj i.

(** A fast, untrusted routine to swap rows *)
Definition swap_rows_fast {T} (A : seq T) (i j : nat) :=
  let (i', j') := (min i j, max i j) in
  let fix aux curr_index (M : seq T) := match M with
  | [::] => [::]
  | h :: t =>
    if (curr_index == i') then let
    (hex, Aex) := (
      let fix extract acc Arem c_index M := match M with
      | [::] => (acc, rev Arem)
      | h' :: t' => if (c_index == j') then
          extract h' (h :: Arem) c_index.+1 t'
        else
          extract acc (h' :: Arem) c_index.+1 t'
      end
      in extract h [::] curr_index.+1 t)
    in hex :: Aex
    else
      h :: (aux curr_index.+1 t)
  end
  in aux 0%N A.

(* Unitary vector *)
Definition unit_vec (sz : nat) (i : nat) : seq R :=
  let zeroes := mkseq (fun _ => 0%R) sz in set_nth 0%R zeroes i 1%R.

Definition unit_seqmx (sz : nat) : @seqmx R :=
  let fix aux (acc_idx : nat) (acc : @seqmx R) := match acc_idx with
  | O => acc
  | idx.+1 => aux idx ((unit_vec sz idx) :: acc)
  end
  in aux sz [::].

(** Dot product between two sequences (vectors) of R *)
Definition vdotQ v u := @foldl _ R +%R 0%R (zipwith *%R v u).

(** Matrix / vector multiplication *)
Definition seqmx_mulvec (A : @seqmx R) (x : seq R) : seq R :=
  map (vdotQ x) A.

(** Find a pivoting element from a square matrix implemented as a sequence of
    sequences, also returning the parts of the matrix "above" and "below" the
    row of the pivoting element, as well as the row itself. The chosen element
    is just the first nonzero encountered element. *)
Definition find_pivot (A : @seqmx R) :=
  let fix find_pivot_aux M :=
      match M with
      | [::] => None
      | row :: M' =>
        if (head 0 row) != 0 then
          Some (row, M')
        else
          omap (fun z => (z.1, row :: z.2)) (find_pivot_aux M')
      end
  in
  find_pivot_aux A.

(* Finds the back pivoting element, returning the normalized pivoting
   row as well as the rest of the matrix *)
Definition find_back_pivot (A : @seqmx R) (index : nat) :=
  let normalize (v : seq R) := let coeff := nth 0%R v index in
    map (fun x => (x / coeff)) v
  in
  let fix find_pivot_aux (M : @seqmx R) :=
      match M with
      | [::] => None
      | row :: M' =>
        if ((nth 0 row index) != 0) then
          Some (normalize row, M')
        else
          omap (fun z => (z.1, row :: z.2)) (find_pivot_aux M')
      end
  in
  find_pivot_aux A.

(** Replace a whole sequence of bigQ numbers after substracting the
    pivoting row. In the case of a leading 0, row `s` is left unchanged. *)
Definition replace_with_pivot (piv_row s : seq R) :=
  let piv_ratio := (head 0 s) / (head 0 piv_row) in
  let f x y := (y - (x * piv_ratio)) in
  behead (zipwith f piv_row s).

Definition replace_with_back_pivot (index : nat) (piv_row s : seq R) :=
  let piv_ratio := (nth 0 s index) / (nth 0 piv_row index) in
  let f x y := y - (x * piv_ratio) in
  zipwith f piv_row s.

(** Performs one step of gauss elimination. Returns a tuple containing:
    1) an option containing `Some piv`, where `piv` is the row used in
       pivoting, or `None` if no pivoting was able to be performed
    2) The part of the matrix whose rows have not yet been used as pivoting
       rows in any phase of the Gaussian elimination *)
Definition gauss_step (A : @seqmx R) :=
  let gauss_step_aux z := (z.1, (map (replace_with_pivot z.1) z.2)) in
  omap gauss_step_aux (find_pivot A).

Definition inv_gauss_step (A : @seqmx R) (index : nat) :=
  let gauss_step_aux z :=
    (z.1, (map (replace_with_back_pivot index z.1) z.2)) in
  omap gauss_step_aux (find_back_pivot A index).

(** The Gaussian elimination routine for the case of linear systems of the
    form Ax = b, forming the augmented matrix [A | b]. *)
Definition gauss_elimination (A : @seqmx R) (b : seq R) : option seqmx :=
  (* Aaug: form augmented matrix [A | b]. *)
  let fix gauss_elim_core dim R (A : seqmx)  :=
      match dim with
      | O => Some R
      | dim'.+1 =>
        match gauss_step A with
        | None => None
        | Some (piv_row, A') => gauss_elim_core dim' (piv_row :: R) A'
        end
      end
  in
  let dim := min (seq.size A) (seq.size (head [::] A)) in
  let Aaug := zipwith (fun row x => rcons row (-x)) A b in
  gauss_elim_core dim [::] Aaug.

Definition prepend_zeros (Aaug : @seqmx R) :=
  let dim := (seq.size Aaug).-1 in
  let mkz := fun x => mkseq (fun _ => 0) x in
  let fix aux_prep M d acc := match M with
  | [::] => acc
  | r :: R =>
    let nRow := cat (mkz d) r in (* new row, with zeros prepended *)
    aux_prep R (d.-1) (nRow :: acc)
  end
  in aux_prep Aaug dim [::].

Definition gauss_elimination_aug (A : seqmx) :=
  let fix gauss_elim_core dim Rs (A : seqmx)  :=
      match dim with
      | O => Some Rs
      | dim'.+1 =>
        match gauss_step A with
        | None => None
        | Some (piv_row, A') => gauss_elim_core dim' (piv_row :: Rs) A'
        end
      end
  in
  (* Gaussian elimination with back-substitution. This is a messy chain
     of calls, since it involves explicitly passing the index where it is
     expected to find the next back-pivoting element. *)
  let fix gauss_elim_back dim Rs (Q : seqmx) :=
    match dim with
      | O => Some Rs
      | dim'.+1 =>
        match inv_gauss_step Q dim' with
        | None => None
        | Some (piv_row, Q') => gauss_elim_back dim' (piv_row :: Rs) Q'
        end
    end
  in
  let dim := min (seq.size A) (seq.size (head [::] A)) in
  let I := unit_seqmx dim in
  let Aaug := zipwith cat A I in
  match gauss_elim_core dim [::] Aaug with
  | None => None
  | Some Ainit =>
    (* Need to reverse the (prepend_zeros Ainit), in order to have the
       "lone" element on the top. *)
    let Acompl := rev (prepend_zeros Ainit) in
    omap (map (drop dim)) (gauss_elim_back dim [::] Acompl)
  end.

(** Performs a back-substitution to solve a linear system in row-echelon
    form. *)
Fixpoint back_substitution acc (Rs: seqmx) :=
  match Rs with
  | [::] => acc
  | row :: R' =>
    let lead_coeff := head 0 row in
    let x := (- (vdotQ acc (behead row)) / lead_coeff) in
    back_substitution (x :: acc) R'
  end.

Fixpoint belast' {T} (s: seq T) :=
  match s with
  | [::] => [::]
  | [:: _] => [::]
  | x :: s' => x :: (belast' s')
  end.

Definition solve_nonhomogeneous (A : @seqmx R) (b : seq R) :=
  omap (belast' \o (back_substitution [:: 1])) (gauss_elimination A b).

(* A variation of the solve_nonhomogeneous function, where the matrix
  inverse is explicitly computed. *)
Definition solve_nonhomogeneous_inv (M : @seqmx R) (b : seq R) :=
  omap (fun x => seqmx_mulvec x b) (gauss_elimination_aug M).

Section FastLup.

Definition find_pivot_lup {T1 T2: Type}  (UL: seq (seq R * T1 * T2)) :=
  let fix find_pivot_aux UL (k : nat) :=
      match UL with
      | [::] => None
      | (row_U, _, _) :: UL' =>
        if (head 0 row_U) != 0 then
          Some k
        else
          find_pivot_aux UL' (k.+1)
      end
  in
  find_pivot_aux UL 0%N.

Definition fast_lup (A: @seqmx R) (b : @seqmx R) :=
  let fix lup_core dim ULP res :=
      match dim with
      | O => Some res
      | dim'.+1 =>
        match find_pivot_lup ULP with
        | None => None
        | Some k =>
          match swap_rows_fast ULP 0 k with
          | ((piv_row_U, _, _) as piv_row) :: UL' =>
            let piv_elt := head 0 piv_row_U in
            let update_UL_row row :=
                match row with
                | (row_U, row_L, row_idx) =>
                  let piv_ratio := ((head 0 row_U) / piv_elt) in
                  let f x y := x - (piv_ratio * y) in
                  (zipwith f (behead row_U) (behead piv_row_U),
                   piv_ratio :: row_L, row_idx)
                end
            in
            let UL'' := map update_UL_row UL' in
            lup_core dim' UL'' (piv_row :: res)
          | _ => None (* impossible *)
          end
        end
      end
  in
  let dim := size A in
  let UL := map (fun row => (row, [::])) A in
  lup_core dim (zip UL b) [::].

Fixpoint backsub_L (ULP: seq (seq R * seq R * seq R)) (res: @seqmx R) :=
  match ULP with
  | [::] => res
  | (_, row_L, row_b) :: ULP' =>
    let backsub_L_aux x b :=
        (b - (vdotQ row_L x)) :: x
    in
    zipwith backsub_L_aux (backsub_L ULP' res) row_b
  end.

Definition backsub_U (res_L: @seqmx R) (ULP: seq (seq R * seq R * seq R)) :=
  let fix backsub_U_aux ULP res row_res_L  :=
      match row_res_L, ULP with
      | [::], _ | _, [::] => res
      | b :: row_res_L', (row_U, _, _) :: ULP' =>
        let lead_coeff := head 0 row_U in
        let res' := ((b - (vdotQ res (behead row_U))) / lead_coeff) :: res in
        backsub_U_aux ULP' res' row_res_L'
      end
  in
  map (backsub_U_aux ULP [::]) res_L.

Definition solve_lup (A: @seqmx R) (b: @seqmx R) : option (@seqmx R) :=
  match fast_lup A b with
  | Some ULP =>
    let res0 := map (fun _ => [::]) b in
    Some (backsub_U (backsub_L ULP res0) ULP)
  | None => None
  end.

End FastLup.

Close Scope ring_scope.

End UntrustedInverse.