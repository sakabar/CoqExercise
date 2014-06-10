Module Task11.
Require Import Arith.

Fixpoint sum_odd(n:nat) : nat :=
  match n with
  | O => O
  | S m => 1 + m + m + sum_odd m
  end.

Goal forall n, sum_odd n = n * n.
Proof.
  induction n.
  reflexivity.

  simpl.
  rewrite IHn.
  rewrite mult_succ_r.
  rewrite (plus_comm (n*n) n).
  rewrite plus_assoc.
  reflexivity.
Qed.

End Task11.

Module Task12.
Require Import Lists.List.

Fixpoint sum (xs: list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

(* Goal forall P Q R : Prop, P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R). *)
(* Proof. *)
(*   intros. *)
(*   split; inversion H. *)
(*   left. *)
(*   assumption. *)

(*   right. *)
(*   destruct H0. *)
(*   assumption. *)

(*   left. *)
(*   assumption. *)

(*   destruct H0. *)
(*   right. *)
(*   assumption. *)
(* Qed. *)

Theorem Pigeon_Hole_Principle :
  forall (xs : list nat), length xs < sum xs -> (exists x, 1<x /\ In x xs).
Proof.
  induction xs.
  intros.
  inversion H.

  intros.
  simpl.

Abort.
(* Qed. *)

End Task12.
