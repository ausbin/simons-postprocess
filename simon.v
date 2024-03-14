Require Import Datatypes.

(* This definition was provided by Ziteng Yang *)
Inductive vec (T: Type): nat -> Type :=
  | vec_nil: vec T 0
  | vec_cons (t: T) (n: nat) (l: vec T n): vec T (S n).

(*
Inductive vec {T: Type} {n: nat}: Type :=
  | vec_nil: @vec T 0
  | vec_cons (t: T) (l: vec n): @vec T (S n).
*)

Definition bmatrix (m n: nat): Type :=
  @vec (@vec bool n) m.

Check forall n: nat, bmatrix n (S n).

Definition simonmat (m: nat): Type :=
  bmatrix m (S m).

Check vec_nil bool.
Check vec_cons bool true 0 (vec_nil bool).

Inductive vec' {T: Type} : nat -> Type :=
  | vec_nil': @vec' T 0
  | vec_cons' (t: T) (n: nat) (l: @vec' T n): @vec' T (S n).

Check vec_cons' false 0 vec_nil'.

Fixpoint veclen {T: Type} (n: nat) (v: @vec' T n) :=
  match v with
  | vec_nil' => 0
  | vec_cons' t n' v' => S (veclen n' v')
  end.

Theorem vec_len_n {T: Type} : forall (n: nat), forall v: vec' n, (@veclen T n v) = n.
Proof.
  intros n v. induction v as [| t n' v' IHv'].
  - reflexivity.
  - simpl. rewrite IHv'. reflexivity. Qed.

Notation "[ [ a ; b ] ; [ c ; d ] ]" := vec_cons bool vec_nil
