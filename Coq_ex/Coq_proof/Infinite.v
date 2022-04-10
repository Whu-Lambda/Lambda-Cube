Set Asymmetric Patterns.
Set Implicit Arguments.

Require Import Unicode.Utf8.
Require Import Arith.
Require Import Plus.

Section Examples.

Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

CoFixpoint ones : stream nat := Cons 1 ones.

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
      | Cons h t => Cons (f h) (map t)
    end.
End map.

Definition ones' := map S zeroes.

Section stream_eq.
  Variable A : Type.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : ∀ h t1 t2,
    stream_eq t1 t2
    -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Definition frob A (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem frob_eq : ∀ A (s : stream A), s = frob s.
Proof.
  destruct s; reflexivity.
Qed.

CoFixpoint nats (n:nat) : stream nat := Cons n (nats (n)).

Lemma stream_unfold : ∀ n : nat, nats n = Cons n (nats (n)).
Proof.
  intro;
  change (nats n = match nats n with
                     | Cons x s => Cons x s
                   end).
  case (nats n); reflexivity.
Qed.

Theorem ones_unfold : nats(1) = Cons 1 (nats(1)).
  apply (stream_unfold 1).
Qed.

