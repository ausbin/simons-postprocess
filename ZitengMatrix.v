(* This file was graciously provided by Ziteng Yang *)

Require Import Datatypes List.
Import ListNotations.
Open Scope list_scope. 

Inductive listn (T: Type): nat -> Type :=
| listn_nil: listn T 0
| listn_cons (t: T) (n: nat)(ln: listn T n): 
      listn T (S n).

Definition matrix_2d (T: Type) (n m: nat): Type :=
  listn (listn T m) n.

(* matrix of arbitrary dimention *)
Inductive matrix {T: Type}: list nat -> Type :=
| matrix_unit (t: T): matrix [1]
| matrix_listn (n: nat)(l: list nat) (M: listn (matrix l) n ):
      matrix (n :: l)
.

Check matrix [3; 3; 5].



(* 
Definition length{T: Type} {n: nat} (l: listn T n):=
      n.

Fixpoint length'{T: Type}{n: nat} (l: listn T n):nat :=
  match l with
  | listn_nil _ => 0
  | listn_cons _ t n ln => 1 + length' ln
  end.

Lemma listn_length: forall T n (ln: listn T n), length ln = length' ln.
Proof. intros. induction ln. simpl; auto. simpl. Check listn_cons T t n ln. 
  rewrite <- IHln. reflexivity. Qed. *)

