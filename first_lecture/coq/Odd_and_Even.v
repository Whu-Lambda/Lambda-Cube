Require Import Arith.
Implicit Type m n : nat.

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n, even n -> even (S (S n)).

Inductive odd : nat -> Prop :=
| odd_1 : odd 1
| odd_SS : forall n, odd n -> odd (S (S n)).

Hint Constructors odd even.

Lemma even_add_one : forall n, even n -> odd (S n).
Proof.
  intros.
  induction H.
  - auto.
  - simpl. auto.
Qed.

Hint Resolve even_add_one.

Lemma odd_add_one : forall n, odd n -> even (S n).
Proof. intros; induction H; auto. Qed.

Hint Resolve odd_add_one.

Lemma parity_dec : forall n, {even n} + {odd n}.
Proof.
  induction n.
  - auto.
  - destruct IHn.
    + auto.
    + simpl. auto.
Qed.

Hint Resolve parity_dec.
(* Addition *)

Theorem odd_add_odd : forall n m, odd n -> odd m -> even (n + m).
Proof. intros; induction H; simpl; auto. Qed.

Hint Resolve odd_add_odd.

Theorem odd_add_even : forall n m, odd n -> even m -> odd (n + m).
Proof. intros; induction H; simpl; auto. Qed.

Hint Resolve odd_add_even.

Theorem even_add_odd : forall n m, even n -> odd m -> odd (n + m).
Proof. intros; induction H; simpl; auto. Qed.

Hint Resolve even_add_odd.

Theorem even_add_even : forall n m, even n -> even m -> even (n + m).
Proof. intros; induction H; simpl; auto. Qed.

Hint Resolve even_add_even.

(* Multiplication *)

Theorem even_mul_even : forall n m, even n -> even m -> even (n * m).
Proof. intros; induction H; simpl; auto. Qed.

Hint Resolve even_mul_even.

Theorem even_mul_odd : forall n m, even n -> odd m -> even (n * m).
Proof. intros; induction H; simpl; auto. Qed.

Hint Resolve even_mul_odd.

Theorem odd_mul_even : forall n m, odd n -> even m -> even (n * m).
Proof. intros; induction H; simpl; auto. Qed.

Hint Resolve odd_mul_even.

Theorem odd_mul_odd : forall n m, odd n -> odd m -> odd (n * m).
Proof. intros; induction H; simpl; auto. Qed.

Hint Resolve odd_mul_odd.

Theorem even_mul : forall n m, even n -> even (n * m).
Proof.
  intros.
  destruct (parity_dec m).
  -(*m = even*) auto.
  -(*m=odd*) auto.
Qed.
