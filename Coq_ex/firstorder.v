Require Import ssreflect.

Variable term:Type.

(* Declaring constant symbol and function symbol of arity 2 *)

Variable a:term.
Variable f:term->term->term.

(* Check that terms are well-formed *)
Check f a a.

(* Declaring predicate symbols, and a propositional variable
   (predicate symbol of arity 0) *)
Variables F: term->Prop.
Variables Rel: term->term->Prop.
Variables G: Prop.

(* PREDICATE LOGIC *)

(* A small example of how to use the forall quantifier. *)

Theorem fa: forall n m, (forall p, Rel p m) -> Rel n m.
Proof.
  move => n.
  move => m.
  move => h.
  apply:h.
Qed.

Theorem b: (forall m, G -> F m) -> G -> forall n, F n.
Proof.
  move => h.
  move => g.
  move => n.
  apply:h.
  apply:g.
Qed.

Theorem c: (forall m, F m) -> F (f a a).
Proof.
  move => h.
  apply:h.
Qed.

(* A small example of how to use the exists quantifier. *)

Theorem ex: forall n, (exists m, F n /\ Rel n m) -> exists p,Rel n p.
Proof.
  move => n h1.
  (* at this point, I would like to say that p should be m,
     but m is just a quantified variable at this point,
     so I use a case to destroy the existential quantifier in h1 *)
  case:h1 => m h2.
  (* at this point, I really want to say that p should be m,
     this is done with exists *)
  exists m.
  (* The rest is easy: finish it as an exercise *)
  case:h2.
  move => h1.
  move => h2.
  apply:h2.
Qed.

Theorem d: F (f a a) -> exists n, F n.
Proof.
  move => h.
  exists (f a a).
  apply:h.
Qed.

Theorem a': (exists n, F n) -> (forall m, F m->G) -> G.
Proof.
  move => h.
  move => h1.
  case:h.
  move => h.
  apply:h1.
Qed.


(* PROVING EQUALITY *)

Theorem Eq1: forall x:term, x=x.
Proof.
  move => x.
  reflexivity.
Qed.

(* USING EQUALITY *)

Theorem Eq_f1: forall x1 x1' x2:term, x1=x1'->f x1 x2 = f x1' x2.
Proof.
  move => x1 x1' x2 h.
  rewrite h.
  reflexivity.
Qed.

Theorem Eq_f2: forall x1 x2 x2':term, x2=x2'->f x1 x2 = f x1 x2'.
Proof.
  move => x1.
  move => x2.
  move => x2'.
  move => h.
  rewrite h.
  reflexivity.
Qed.

Theorem Eq_F: forall x1 x1':term, x1=x1' -> F x1' -> F x1.
Proof.
  move => x1.
  move => x1'.
  move => h.
  rewrite h.
  move => x.
  apply:x.
Qed.

Theorem Eq_sym: forall x1 x1':term, x1=x1' -> x1'=x1.
Proof.
  move => x1.
  move => x1'.
  move => h.
  rewrite h.
  reflexivity.
Qed.

Theorem Eq_trans: forall x1 x1' x1'':term, x1=x1' -> x1'=x1'' -> x1=x1''.
Proof.
  move => x1.
  move => x1'.
  move => x1''.
  move => h1.
  move => h2.
  rewrite h1.
  rewrite h2.
  reflexivity.
Qed.

Theorem Eq_Fback: forall x1 x1':term, x1=x1' -> F x1 -> F x1'.
Proof.
  move => x1.
  move => x1'.
  move => h.
  move => h1.
  rewrite -h.
  apply:h1.
Qed.
