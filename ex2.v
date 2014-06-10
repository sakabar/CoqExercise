Require Import Arith.

Goal forall x y, x < y -> x + 10 < y + 10.
Proof.
  intros.
  apply plus_lt_compat_r.
  exact H.
Qed.

Goal forall P Q : nat -> Prop, P 0 -> (forall x, P x -> Q x) -> Q 0.
Proof.
  intros.
  apply H0.
  exact H.
Qed.

Goal forall P : nat -> Prop, P 2 -> (exists y, P (1 + y)).
Proof.
  intros.
  exists 1.
  simpl.
  exact H.
Qed.

Goal forall P : nat -> Prop, (forall n m, P n -> P m) -> (exists p, P p) -> forall q, P q.
Proof.
  intros.
  destruct H0. (* existsに対してdestructできることを覚えておこう *)
  apply (H x).
  exact H0.
Qed.

Goal forall m n : nat, (n * 10) + m = (10 * n) + m.
Proof.
  intros m n.
  rewrite mult_comm.
  reflexivity.
Qed.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  intros.
  apply plus_permute_2_in_4.
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  intros.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_r.
  simpl.
  rewrite <- plus_n_O.
  rewrite mult_plus_distr_r.
  rewrite (plus_comm (n * m) (m * m)).
  rewrite plus_permute_2_in_4.
  rewrite (mult_comm m n).
  reflexivity.
Qed.

Module Task10.
Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).
(* Notation "x / y" := (mult x (inv y)). *) (* 使ってもよい *)

Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.

(* 自力じゃできなかった... *)
(* 群論のサイト見た *)
Lemma inv_r : forall x, x * / x = 1.
Proof.
  intro x.
  rewrite <- (one_unit_l (x * / x)).
  rewrite <- (inv_l (/ x)) at 1.
  rewrite <- (mult_assoc (/ / x) (/ x) (x * / x)).
  rewrite (mult_assoc (/ x) x (/ x)).
  rewrite (inv_l x).
  rewrite one_unit_l.
  rewrite inv_l.
  reflexivity.
Qed.

Lemma one_unit_r : forall x, x * 1 = x.
Proof.
  intros.
  rewrite <- (inv_l x).
  rewrite mult_assoc.
  rewrite (inv_r x).
  rewrite one_unit_l.
  reflexivity.
Qed.

End Task10.
