Set Asymmetric Patterns.
Set Implicit Arguments.
Require Import Unicode.Utf8.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Class Monoid (A : Type) :=
  {
    empty : A ;
    append : A -> A -> A ;

    left_neutrality : ∀ x, append empty x = x ;
    right_neutrality : ∀ x, append x empty = x ;
    associativity : ∀ x y z, append x (append y z) = append (append x y) z
  }.

Program
  Instance bool_Monoid : Monoid bool :=
  {
    empty := false ;
    append a b := match a with
                    | true => true
                    | false => b
                  end
  }.

Next Obligation.
  intros.
  reflexivity.
Qed.

Next Obligation.
  intros.
  destruct x.
  reflexivity.
  reflexivity.
Qed.

Next Obligation.
  intros.
  destruct x.
  reflexivity.
  destruct y.
  reflexivity.
  reflexivity.
Qed.