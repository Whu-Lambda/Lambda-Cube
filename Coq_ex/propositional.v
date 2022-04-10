Require Import ssreflect.

(* This is a comment line *)

(* This is how we declare propositional variables *)

Variables A B C:Prop.

Theorem A1: A->(B->A).
Proof.
  intros.
  auto.
Qed.

Theorem A2: (A->B->C)->(A->B)->A->C.
Proof.
  move => h1.
  move => h2.
  move => h3.
  apply:h1.
  auto.
  apply:h2.
  auto.
Qed.

Theorem A3: A->~~A.
Proof.
  move => h1.
  move => h2.
  apply:h2.
  apply:h1.
Qed.

Theorem A4: False->A.
Proof.
  move => h1.
  case:h1.
Qed.

Theorem A5: (A->B)->(~B->~A).
Proof.
  move => h1 h2 h3.
  apply: h2.
  apply: h1.
  apply: h3.
Qed.

Theorem A6: A->B->(A/\B).
Proof.
  move => h0 h1.
  split.
  apply h0.
  apply h1.
Qed.

Theorem A7: (A/\B)->A.
Proof.
  move => h0.
  case:h0.
  apply A1.
Qed.

Theorem A8: (A/\B)->B.
Proof.
  move => h0.
  case:h0.
  move => h1.
  move => h2.
  apply:h2.
Qed.

Theorem A9: A->(A\/B).
Proof.
  move => h0.
  left.
  apply:h0.
Qed.

Theorem A10: B->(A\/B).
Proof.
  move => h0.
  right.
  apply:h0.
Qed.

Theorem A11: (A\/B)->(A->C)->(B->C)->C.
Proof.
  move => h0 h1 h2.
  case:h0.
  apply:h1.
  apply:h2.
Qed.


(* Exercises *)

Lemma trans : (A -> B) -> (B -> C) -> A -> C.
Proof.
  move => h0 h1 h2.
  apply: h1.
  apply: h0.
  apply: h2.
Qed.

(* P <-> Q is a shortcut for (P -> Q) /\ (Q -> P): manipulate it like a
   "/\" *)

Lemma and_sym : A /\ B <-> B /\ A.
Proof.
  split.
    move => h0.
    case: h0.
    move => h0 h1.
    split.
      apply: h1.
      apply: h0.
  move => h0.
  case: h0.
  move => h0 h1.
  split.
    apply: h1.
    apply: h0.
Qed.


Lemma or_sym : A \/ B <-> B \/ A.
Proof.
  split.
    move => h0.
    case: h0.
      move => h0.
      right.
      apply: h0.
    move => h0.
    left.
    apply: h0.
  move => h0.
  case: h0.
    move => h0.
    right.
    apply: h0.
  move => h0.
  left.
  apply: h0.
Qed.


Lemma or_not : ~A \/ ~B -> ~ (A /\ B).
Proof.
  move => h0 h1.
  case: h1.
  move => h1 h2.
  case: h0.
    apply.
    apply: h1.
  apply.
  apply: h2.
Qed.


Lemma and_not : ~A /\ ~B <-> ~ (A \/ B).
Proof.
  split.
    move => h0 h1.
    case: h0.
    move => h0 h2.
    case: h1.
      move => h1.
      apply: h0.
      apply h1.
    move => h1.
    apply: h2.
    apply: h1.
  move => h0.
  split.
    move => h1.
    apply: h0.
    left.
    apply: h1.
  move => h1.
  apply: h0.
  right.
  apply: h1.
Qed.


Lemma curry : (A /\ B -> C) <-> (A -> B -> C).
Proof.
  split.
    move => h0 h1 h2.
    apply: h0.
    split.
      apply: h1.
      apply: h2.
  move => h0 h1.
  case: h1.
  move => h1 h2.
  apply: h0.
  apply: h1.
  apply: h2.
Qed.


(* More difficult - remember that "apply" without ":" allow to use an
   hypothesis several times *)

Lemma em : ~~ (A \/ ~A).
Proof.
  move => h0.
  apply:(h0).
  right.
  move => h1.
  apply: h0.
  left.
  apply: h1.
Qed.

Lemma peirce : ~~ (((A -> B) -> A) -> A).
Proof.
  move => h0.
  apply:(h0).
  apply.
  move => h2.
  elim: h0.
  move => h1.
  apply: h2.
Qed.


Lemma absurd : ~~ (~~A -> A).
Proof.
  move => h0.
  apply h0.
  elim.
  move => h1.
  apply: h0.
  move => h2.
  apply: h1.
Qed.
