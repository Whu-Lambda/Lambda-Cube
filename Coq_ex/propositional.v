Require Import ssreflect.

(* This is a comment line *)

(* This is how we declare propositional variables *)

Variables A B C:Prop.

Theorem A1: A->(B->A).
Proof.
  done.
Qed.

Theorem A2: (A->B->C)->(A->B)->A->C.
Proof.
  move => h1.
  move => h2.
  move => h3.
  apply:h1.
  done.
  apply:h2.
  done.
Qed.

Theorem A3: A->~~A.
Proof.
  move => h1.
  move => h2.
  apply:h2.
  done.
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
  done.
Qed.

Theorem A6: A->B->(A/\B).
Proof.
  move => h0 h1.
  split.
  done.
  done.
Qed.

Theorem A7: (A/\B)->A.
Proof.
  move => h0.
  case:h0.
  done.
Qed.

Theorem A8: (A/\B)->B.
Proof.
  move => h0.
  case:h0.
  done.
Qed.

Theorem A9: A->(A\/B).
Proof.
  move => h0.
  left.
  done.
Qed.

Theorem A10: B->(A\/B).
Proof.
  move => h0.
  right.
  done.
Qed.

Theorem A11: (A\/B)->(A->C)->(B->C)->C.
Proof.
  move => h0 h1 h2.
  case:h0.
  done.
  done.
Qed.


(* Exercises *)

Lemma trans : (A -> B) -> (B -> C) -> A -> C.
Proof.
  move => h0 h1 h2.
  apply: h1.
  apply: h0.
  done.
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
      done.
    done.
  move => h0.
  case: h0.
  move => h0 h1.
  split.
    done.
  done.
Qed.


Lemma or_sym : A \/ B <-> B \/ A.
Proof.
  split.
    move => h0.
    case: h0.
      move => h0.
      right.
      done.
    move => h0.
    left.
    done.
  move => h0.
  case: h0.
    move => h0.
    right.
    done.
  move => h0.
  left.
  done.
Qed.


Lemma or_not : ~A \/ ~B -> ~ (A /\ B).
Proof.
  move => h0 h1.
  case: h1.
  move => h1 h2.
  case: h0.
    apply.
    done.
  apply.
  done.
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
      done.
    move => h1.
    apply: h2.
    done.
  move => h0.
  split.
    move => h1.
    apply: h0.
    left.
    done.
  move => h1.
  apply: h0.
  right.
  done.
Qed.


Lemma curry : (A /\ B -> C) <-> (A -> B -> C).
Proof.
  split.
    move => h0 h1 h2.
    apply: h0.
    split.
      done.
    done.
  move => h0 h1.
  case: h1.
  move => h1 h2.
  apply: h0.
    done.
  done.
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
  done.
Qed.

Lemma peirce : ~~ (((A -> B) -> A) -> A).
Proof.
  move => h0.
  apply:(h0).
  apply.
  move => h2.
  elim: h0.
  done.
Qed.


Lemma absurd : ~~ (~~A -> A).
Proof.
  move => h0.
  apply h0.
  elim.
  move => h1.
  apply: h0.
  done.
Qed.
