Require Import Datatypes List Nat.
Import ListNotations.
Open Scope list_scope.

(* Thank you to Ziteng Yang for providing this definition *)
Inductive vec {T: Type} : nat -> Type :=
  | vec_nil: @vec T 0
  | vec_cons (t: T) {n: nat} (l: @vec T n): @vec T (S n).

Definition bvec (n: nat): Type :=
  @vec bool n.

Definition bmat (m n: nat): Type :=
  @vec (bvec n) m.

Check forall n: nat, bmat n (S n).

Check vec_cons false vec_nil.

Fixpoint veclen {T: Type} {n: nat} (v: @vec T n) :=
  match v with
  | vec_nil => 0
  | vec_cons t v' => S (veclen v')
  end.

Theorem vec_len_n {T: Type} : forall (n: nat), forall v: vec n, (@veclen T n v) = n.
Proof.
  intros n v. induction v as [| t n' v' IHv'].
  - reflexivity.
  - simpl. rewrite IHv'. reflexivity. Qed.

Fixpoint vecapp1 {T: Type} {n: nat} (v: @vec T n) (t: T)
                 : @vec T (S(n)) :=
  match v with
  | vec_nil => vec_cons t vec_nil
  | vec_cons t' v' => vec_cons t' (vecapp1 v' t)
  end.

Fixpoint vecapp {T: Type} {n1: nat} {n2: nat} (v1: @vec T n1) (v2: @vec T n2)
                : @vec T (n1+n2) :=
  match v1 with
  | vec_nil => v2
  | vec_cons t v1' => vec_cons t (vecapp v1' v2)
  end.

(*
Fixpoint vecapp {T: Type} {n1: nat} {n2: nat} (v1: @vec T n1) (v2: @vec T n2)
                : @vec T (n1+n2) :=
  match v2 with
  | vec_nil => v1
  | vec_cons t v2' => vecapp (vecapp1 v1 t) v2'
  end.
*)

Fixpoint vecreverse {T: Type} {n: nat} (v: @vec T n) : @vec T n :=
  match v with
  | vec_nil => vec_nil
  | vec_cons t v' => vecapp1 (vecreverse v') t
  end.

Fixpoint listtovec {T: Type} (l: list T) : vec (length l) :=
  match l with
  | nil => vec_nil
  | cons t l' => vec_cons t (listtovec l')
  end.

Notation "! l" := (listtovec l) (at level 40).

Check ![1; 2; 3].
Check ![![2; 4; 6];
        ![1; 2; 3]].
Fail Check ![![2; 6];
             ![1; 2; 3]].
Fail Check ![![2; 4; 6];
             ![1; false; 3]].
Fail Check ![![2; 4; 6];
           ![true; false; true]].

Fixpoint bvec_all_f {n: nat} (v: bvec n) :=
  match v with
  | vec_nil => true
  | vec_cons t v' => if t
                     then false
                     else bvec_all_f v'
  end.

Example vec_all_f_ex1 : (bvec_all_f (![true; false; false])) = false.
Proof. reflexivity. Qed.

Example vec_all_f_ex2 : (bvec_all_f (![false; false; false])) = true.
Proof. reflexivity. Qed.

Example vec_all_f_ex3 : (bvec_all_f (![])) = true.
Proof. reflexivity. Qed.

Fixpoint bmat_all_f {m n : nat} (mat: bmat m n) : bool :=
  match mat with
  | vec_nil => true
  | vec_cons row mat' =>
      if bvec_all_f row
      then bmat_all_f mat'
      else false
  end.

(* Condition #1 of row echelon form according to Lay, Lay, & McDonald *)
Fixpoint f_rows_at_bottom {m n : nat} (mat: bmat m n) : bool :=
  match mat with
  | vec_nil => true
  | vec_cons row mat' =>
      if bvec_all_f row
      then bmat_all_f mat'
      else f_rows_at_bottom mat'
  end.

Fixpoint leading_entry_idx {n: nat} (row: bvec n) : nat :=
  match row with
  | vec_nil => 0
  | vec_cons e row' =>
      if e then 0
      else S(leading_entry_idx row')
  end.

(* Condition #2 of row echelon form according to Lay, Lay, & McDonald *)
Fixpoint leading_entries_cascade {m n : nat} (mat: bmat m n) : bool :=
  match mat with
  | vec_nil => true
  | vec_cons row mat' =>
      match mat' with
      | vec_nil => true
      | vec_cons row' mat'' =>
          (ltb (leading_entry_idx row) (leading_entry_idx row'))
          && (leading_entries_cascade mat')
      end
  end.

Fixpoint bvec_proj {n: nat} (v: bvec n) (idx: nat) :=
  match v with
  | vec_nil => false
  | vec_cons t v' =>
      match idx with
      | 0 => t
      | _ => bvec_proj v' (pred idx)
      end
  end.

Fixpoint extract_column {m n : nat} (mat: bmat m n) (idx: nat) : (bvec m) :=
  match mat with
  | vec_nil => vec_nil
  | vec_cons row mat' =>
      vec_cons (bvec_proj row idx) (extract_column mat' idx)
  end.

(* Condition #3 of row echelon form according to Lay, Lay, & McDonald *)
Fixpoint leading_entries_above_f {m n : nat} (mat: bmat m n) : bool :=
  match mat with
  | vec_nil => true
  | vec_cons row mat' =>
      ((bvec_all_f row)
       || (bvec_all_f (extract_column mat' (leading_entry_idx row))))
      && (leading_entries_above_f mat')
  end.

Definition bmat_is_ref {m n: nat} (mat: bmat m n) : bool :=
  (f_rows_at_bottom mat)
  && (leading_entries_cascade mat)
  && (leading_entries_above_f mat).

Compute (bmat_is_ref (![![true ; false; true];
                        ![false; false; true]])).

Example bmat_is_ref_ex1 :
  (bmat_is_ref (![![true ; false; true];
                  ![false; false; true]])) = true.
Proof. reflexivity. Qed.

Example bmat_is_ref_ex2 :
  (bmat_is_ref (![![true; false; true];
                  ![true; false; true]])) = false.
Proof. reflexivity. Qed.

Example bmat_is_ref_ex3 :
  (bmat_is_ref (![![false; false; false];
                  ![true ; false; true]])) = false.
Proof. reflexivity. Qed.

(* Condition #5 of reduced row echelon form according to Lay, Lay, & McDonald.
   (Condition #4 is trivially met because this is a matrix of 1s and 0s) *)
Definition leading_entries_below_f {m n : nat} (mat: bmat m n): bool :=
  leading_entries_above_f (vecreverse mat).

Definition bmat_is_rref {m n: nat} (mat: bmat m n) : bool :=
  (bmat_is_ref mat) && (leading_entries_below_f mat).

Example bmat_is_rref_ex1 :
  (bmat_is_rref (![![true ; false; true];
                   ![false; false; true]])) = false.
Proof. reflexivity. Qed.

Example bmat_is_rref_ex2 :
  (bmat_is_rref (![![true ; false; false];
                   ![false; false; true]])) = true.
Proof. reflexivity. Qed.

Example bmat_is_rref_ex3 :
  (bmat_is_rref (![![true ; false; false];
                   ![false; true; true]])) = true.
Proof. reflexivity. Qed.

Fixpoint bmat_has_all_f_row {m n : nat} (mat: bmat m n) : bool :=
  match mat with
  | vec_nil => false
  | vec_cons row mat' =>
      if bvec_all_f row then true
      else bmat_has_all_f_row mat'
  end.

Definition simonmat (m: nat): Type := bmat m (S m).

Definition simon_in_std {m: nat} (mat: simonmat m) :=
  andb (bmat_is_rref mat) (negb (bmat_has_all_f_row mat)).

Fail Compute
  simon_in_std (![![true ; false];
                  ![false; true ]]).

Example simon_in_std_ex1 :
  (simon_in_std (![![true ; false; false];
                   ![false; false; true]])) = true.
Proof. reflexivity. Qed.

Example simon_in_std_ex2 :
  (simon_in_std (![![true ; false; false];
                   ![false; false; false]])) = false.
Proof. reflexivity. Qed.

Example simon_in_std_ex3 :
  (simon_in_std (![![true ; true ; false];
                   ![false; false; true ]])) = true.
Proof. reflexivity. Qed.

Example simon_in_std_ex4 :
  (simon_in_std (![![true ; false; false];
                   ![false; true ; true ]])) = true.
Proof. reflexivity. Qed.

