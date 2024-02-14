Inductive bit : Type :=
  | zero
  | one.

(* https://rand.cs.uchicago.edu/vqc/Matrix.html *)
Definition simon_matrix (n: nat) := nat -> nat -> bit.

(*
Fixpoint special_helper {n: nat} (k: nat) (M: simon_matrix n) : nat :=
  match (M k k) with
  | zero => k
  | one => special_helper (S k) M
  end.
 *)

  (*Definition special (m: simon_matrix n) :=*)


(*
Inductive bit : Type :=
  | zero
  | one.

   Inductive gg*)
