Require Import Unicode.Utf8.
Require Import List.
Require Import Bool.
Require Import ZArith.

Fixpoint insert (i : nat) (l : list nat) :=
    match l with
    | nil => i :: nil
    | h :: t => if i <=? h
      then i :: h :: t else h :: insert i t
    end.

Fixpoint sort (l : list nat) : list nat :=
    match l with
    | nil => nil
    | h :: t => insert h (sort t)
    end.

Inductive sorted : list nat → Prop :=
  | sorted_nil : sorted nil
  | sorted_one : ∀ (n : nat), sorted (n :: nil)
  | sorted_cons : ∀ x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma lebtop: ∀ x y, (x <=? y) = true -> x <= y.
Proof.
  induction x; destruct y; auto using le_0_n, le_n_S.
  intros H. inversion H.
Qed.

Lemma nlebtop: ∀ x y, (x <=? y) = false -> y <= x.
Proof.
  induction x; destruct y; auto using le_0_n, le_n_S.
  intros H. inversion H.
Qed.

Lemma sorted_inv: ∀ a b l,
  sorted (a :: b :: l) -> sorted (b :: l) /\ a <= b.
Proof.
  intros a b l H. split.
  - inversion H. apply H4.
  - inversion H. apply H2.
Qed.

Lemma insert_sorted: ∀ a l,
  sorted l -> sorted (insert a l).
Proof.
  intros a l H.
  induction l as [| a' l'].
  - simpl. constructor.
  - destruct (a <=? a') eqn: H'.
    + simpl. rewrite H'. constructor.
      * apply lebtop. trivial.
      * apply H.
    + simpl. rewrite H'. 
      destruct l' as [| a'' l''].
      * simpl. apply nlebtop in H'.
        constructor. apply H'.
        constructor.
      * apply sorted_inv in H.
        destruct H. apply IHl' in H.
        destruct (a <=? a'') eqn: H''.
        ** simpl in H. rewrite H'' in H.
           simpl. rewrite H''. constructor.
           apply nlebtop in H'. apply H'.
           apply H.
        ** simpl in H. rewrite H'' in H.
           simpl. rewrite H''. constructor.
           apply H0. apply H.
Qed.

Lemma sort_sorted: ∀ l, sorted (sort l).
Proof.
  intros l. induction l.
  - simpl. constructor.
  - simpl. apply insert_sorted.
    apply IHl.
Qed.

Inductive perm : list nat → list nat → Prop :=
  | perm_nil : ∀ l, perm l l
  | perm_cons : ∀ x l l', perm l l' -> perm (x :: l) (x :: l')
  | perm_swap : ∀ x y l, perm (x :: y :: l) (y :: x :: l)
  | perm_trans : ∀ l l' l'', perm l l' -> perm l' l'' -> perm l l''.

Lemma insert_perm: ∀ x l, perm (x :: l) (insert x l).
Proof.
  intros x l. induction l as [| a' l'].
  - simpl. constructor.
  - destruct (x <=? a') eqn: H.
    + simpl. rewrite H. constructor.
    + simpl. rewrite H.
      assert (H': perm (x :: a' :: l') (a' :: x :: l')).
      constructor.
      apply perm_trans with (a' :: x :: l').
      * apply H'.
      * constructor. apply IHl'.
Qed.

Lemma sort_perm: ∀ l, perm l (sort l).
Proof.
  intros l. induction l.
  - simpl. constructor.
  - simpl. apply (@perm_cons a _ _) in IHl.
    apply perm_trans with (a :: sort l).
    * apply IHl.
    * apply insert_perm.
Qed.

Definition is_a_sorting_algorithm (f: list nat -> list nat) := 
  ∀ l, perm l (f l) /\ sorted (f l).

Theorem insertion_sort_correct: is_a_sorting_algorithm sort.
Proof.
  split. apply sort_perm. apply sort_sorted.
Qed.
