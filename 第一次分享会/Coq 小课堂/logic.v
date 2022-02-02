Require Import Arith.
Require Import ArithRing Ring.

Theorem invert : forall a b : nat, a + a = b + b -> a = b.
Proof.
  induction a.
  -intros b H. destruct b.
   +auto.
   +discriminate.
  -intros b H. destruct b.
   +discriminate.
   +inversion H.
    rewrite <- plus_n_Sm in H1.
    rewrite <- plus_n_Sm in H1.
    inversion H1.
    rewrite (IHa b H2).
    auto.
Qed.

(*Tsinghua Class1*)

Definition f := fun x y => x^2+y^2.

Example f_test : f 3 4 = 25.
Proof. auto. Qed.

Fixpoint sum (n : nat) :=
  match n with
  | 0 => 0
  | S n' => n^2 + sum(n')
  end.

Example sum_test : sum 2 = 5.
Proof. auto. Qed.

Lemma Sn_exp : forall n : nat,
    S n = n + 1.
Proof.
  induction n.
-auto.
-simpl.
 rewrite IHn.
 auto.
Qed.
 
Lemma mult_distr_r : forall n m p : nat,
    n * (m + p) = n * m + n * p.
Proof.
  intros n m p.
  induction n.
  -auto.
  -simpl.
   rewrite IHn.
   ring.
Qed.

Lemma sum_helper : forall n : nat,
    sum (S n) = sum n + (n + 1)^2.
Proof.
  induction n.
  -auto.
  -rewrite IHn.
   simpl.
   ring.
Qed.

Lemma n_sum_helper : forall n : nat,
    S n * (S n + 1) * (2 * S n + 1) = n * (n + 1) * (2*n+1) + 6 * (n + 1)^2.
Proof.
  destruct n.
  -auto.
  -simpl. rewrite Sn_exp.
   ring.
Qed.
   
Theorem sum_exp : forall n : nat,
    6 * sum n = n * (n+1) * (2*n+1).
Proof.
  induction n.
  -auto.
  -rewrite sum_helper.
   rewrite mult_distr_r.
   rewrite IHn.
   rewrite n_sum_helper.
   auto.
Qed.
