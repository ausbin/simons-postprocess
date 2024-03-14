Require Import Datatypes List.
Import ListNotations.
Open Scope list_scope.

(* Thank you to Ziteng Yang for providing this definition *)
Inductive vec {T: Type} : nat -> Type :=
  | vec_nil: @vec T 0
  | vec_cons (t: T) (n: nat) (l: @vec T n): @vec T (S n).

Definition bmatrix (m n: nat): Type :=
  @vec (@vec bool n) m.

Check forall n: nat, bmatrix n (S n).

Definition simonmat (m: nat): Type :=
  bmatrix m (S m).

Check vec_cons false 0 vec_nil.

Fixpoint veclen {T: Type} (n: nat) (v: @vec T n) :=
  match v with
  | vec_nil => 0
  | vec_cons t n' v' => S (veclen n' v')
  end.

Theorem vec_len_n {T: Type} : forall (n: nat), forall v: vec n, (@veclen T n v) = n.
Proof.
  intros n v. induction v as [| t n' v' IHv'].
  - reflexivity.
  - simpl. rewrite IHv'. reflexivity. Qed.

Fixpoint vecapp {T: Type} (n1 n2: nat) (v1: @vec T n1) (v2: @vec T n2)
                : @vec T (n1+n2) :=
  match v1 with
  | vec_nil => v2
  | vec_cons t n1' v1' => vec_cons t (n1' + n2) (vecapp n1' n2 v1' v2)
  end.

Notation "a ++ b" := (vecapp a b)
                     (at level 60, right associativity).

Fixpoint listtovec {T: Type} (l: list T) : vec (length l) :=
  match l with
  | nil => vec_nil
  | cons t l' => vec_cons t (length l') (listtovec l')
  end.

Notation "@ l" := (listtovec l) (at level 40).

Check @[1; 2; 3].
Check @[@[2; 4; 6];
        @[1; 2; 3]].
Fail Check @[@[2; 6];
           @[1; 2; 3]].
Fail Check @[@[2; 4; 6];
           @[1; false; 3]].
Fail Check @[@[2; 4; 6];
           @[true; false; true]].
