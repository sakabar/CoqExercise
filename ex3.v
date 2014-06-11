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
  intros H.
  inversion H.

  intros.
  exists a.

  split.
  simpl in H.



Abort.
(* Qed. *)

End Task12.

Module Task13.
(* コンストラクタの名前は例えば、SOとSにするとよい。 *)
Inductive pos : Set :=
  (* posの定義を書く *)
  | SO : pos
  | S : pos -> pos.

Fixpoint plus(n m:pos) : pos := (* plusの定義を書く *)
  match n with
  | SO => m
  | S n' => S (plus n' m)
  end.

Infix "+" := plus.

Theorem plus_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  generalize n.
  clear n.
  induction n.
  simpl.
  reflexivity.

  simpl.
  rewrite IHn.
  reflexivity.
Qed.

End Task13.

Module Task14.

Theorem FF: ~exists f, forall n, f (f n) = S n.
Proof.
  unfold not.
  intros H.


Abort.
(* Qed. *)

End Task14.

Module Task15.

Inductive Tree:Set :=
  | Node: list Tree -> Tree.

Theorem Tree_dec: forall a b:Tree, {a=b} + {a<>b}.
Proof.
  induction a; induction b.
  induction l; induction l0.
  left.
  reflexivity.

  right.
  unfold not.
  intro H.
  discriminate H.

  right.
  unfold not.
  intro H.
  discriminate H.

  rename a0 into b.
  rename l into tr0.
  rename l0 into tr1.
  inversion IHl.
  right.
  unfold not.
  intro H1.
  rewrite <- H in H1.
Abort.
(* Qed. *)

End Task15.
