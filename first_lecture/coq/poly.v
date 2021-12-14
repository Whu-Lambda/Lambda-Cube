Require Import Arith.
Require Import ArithRing Ring.
Require Import Lia.

Fixpoint sum (n : nat) :=
  match n with
  | 0 => 0
  | S n' => n + sum n'
  end.

Example sum_test : sum 5 = 15.
Proof. auto. Qed.

Theorem sum_formula : forall n : nat,
    2 * sum n = n * (n + 1).
Proof.
  induction n.
  -auto.
  -simpl. ring_simplify.
   rewrite IHn. ring.
Qed.

Fixpoint summation (n : nat) :=
  match n with
  | 0 => 0
  | S n' => n * (2*n-1) + summation n'
  end.

Theorem sum_help : forall n : nat,
    6 * summation (S n) = 6 * summation n + 6 * (S n) * (2 * S n - 1).
Proof.
  induction n.
  -auto.
  -rewrite IHn. simpl.   
   ring.
Qed.

Theorem hardcore : forall n : nat,
    6 * summation n =  n * (n + 1) * (4 * n - 1).
Proof.
  induction n.
  -auto.
  -rewrite sum_help.
   (try destruct n); lia.
Qed.
