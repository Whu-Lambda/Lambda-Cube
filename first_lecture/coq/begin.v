(* Inductive可以帮助你构造新的类型，比如我们可以这样定义bool类型 *)

Inductive bool : Type :=
  | true
  | false.

(* Definition可以帮助我们定义现有类型的一些操作，例如我们可以定义几个基本的逻辑运算符 *)

Definition and (a : bool) (b : bool) : bool :=
  match a with
  | true => b
  | false => false
  end.

(* match _ with是一个pattern match,它是类型值不同形式的分析 *)

Definition or (a : bool) (b : bool) : bool :=
  match a with
  | true => true
  | false => b
  end.

(*define neq by yourself*)

Definition neq (x : bool) : bool :=
  match x with
  | true => false
  | false => true
  end.

(* 欢迎来到我们的核心主题——定理证明！ *)

(* Coq是一个交互式定理证明器，它的编译器将提示你如何进行下一步证明 *)

(* Theorem, Example, Lemma都代表了Coq中有待证明的命题，对于Coq来说三者没有区别 *)

(* Proof代表一段证明的开始 *)

(* intros用于在证明中引入命题涉及的参数，如果你不给这些参数命名，Coq会自动替你命名 *)

(* destruct是进行分类讨论的策略，Coq会自动为你分配不同的类型值 *)

(* simpl可以对需要证明的结论按照定义进行一次化简 *)

(* reflexivity会检查待证项的两边是否相等，如果相等当前目标完成，如果不等则报错 *)

(* Qed代表证明的结束，如果证明尚未完成，则会报错 *)

Theorem neq_refl : forall n : bool,
    neq (neq n) = n.
Proof.
  intros n.
  destruct n.
  -(* n = true *)
   simpl. reflexivity.
  -(* n = false *)
   simpl. reflexivity.
Qed.

Theorem neq_or : forall n : bool,
    or (neq n) n = true.
Proof.
  intros n.
  destruct n.
  -simpl. reflexivity.
  -simpl. reflexivity.
Qed.

Theorem neq_and : forall n : bool,
    and (neq n) n = false.
Proof.
  destruct n.
  -simpl. reflexivity.
  -simpl. reflexivity.
Qed.

(* 使用Notation可以将原先定义的操作转化为我们熟悉的符号 *)
   
Notation " x && y " := (and x y).
Notation " x || y " := (or x y).
Notation " ~ x " := (neq x).

(* 使用Module可以避免自己的定义与标准库的定义冲突 *)
   
Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Definition pred (n : nat) :=
    match n with
    | O => O
    | S n' => n' 
    end.

  (* Fixpoint用于处理递归定义的操作 *)
  
  Fixpoint plus (n : nat) (m : nat) :=
    match n with
    | O => m
    | S n' => S (plus n' m) 
    end.

  Fixpoint minus (n : nat) (m : nat) : nat :=
    match n, m with
    | O, _ => O
    | (S n'), O => n 
    | (S n'), (S m') => (minus n' m')  
    end.

  Fixpoint mult (n : nat) (m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m) 
    end.

  Fixpoint power (n : nat) (m : nat) : nat :=
    match m with
    | O => S O
    | S m' => mult n (power n m')
    end.

End NatPlayground.

(* rewrite是Coq中极其重要的策略之一，它允许我们用已有定理或归纳假设来改写需要证明的式子 *)

(* induction可以开展归纳证明，Coq会为你自动分析类型值并生成归纳假设 *) 
   
Theorem mult_0_r : forall n : nat,
    n * 0 = 0.
Proof.
  induction n.
  -(* P (0) :  n = 0 *)
    
    simpl. reflexivity.
  (* 0 * 0 = 0 => 0 = 0 => reflexivity *)
    
  -(* 假设P (n)成立，证明P (n + 1)成立 *)
    
    simpl. rewrite IHn. reflexivity.
   (* IHn : n * 0 = 0.
      ---------------- 
      S n * 0 = 0 => 0 + n * 0 = 0 => 0 + 0 = 0 => 0 = 0 => reflexivity *)
Qed.

Theorem plus_0_r : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  induction n.
  -simpl. reflexivity.
  -simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
    n + m + p = n + (m + p).
Proof.
  intros n m p.
  induction n.
  -simpl. reflexivity.
  -simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_Sm_r : forall n m : nat,
    S (n + m) = n + S m.
Proof.
  intros n m.
  induction n.
  -reflexivity.
  -simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.
  induction n.
  -simpl. rewrite plus_0_r. reflexivity.
  -simpl. rewrite IHn. rewrite plus_Sm_r.
   reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  induction n.
  -reflexivity.
  -simpl. rewrite IHn. rewrite plus_Sm_r.
   reflexivity.
Qed.

Lemma mult_Sm_r : forall n m : nat,
    n * S m = n + n * m.
Proof.
  intros n m.
  induction n.
  -simpl. reflexivity.
  -simpl. rewrite IHn.
   rewrite plus_swap.
   reflexivity.
Qed.

Theorem mult_comm : forall n m : nat,
    n * m = m * n.
Proof.
  intros n m.
  induction n.
  -rewrite mult_0_r. reflexivity.
  -simpl. rewrite mult_Sm_r.
   rewrite IHn.
   reflexivity.
Qed.

Lemma mult_distr : forall n m p : nat,
    (n + m) * p = n * p + m * p.
Proof.
  intros n m p.
  induction n.
  -simpl. reflexivity.
  -simpl. rewrite IHn. rewrite plus_assoc. reflexivity.
Qed.


Theorem mult_assoc : forall n m p : nat,
    n * m * p = n * (m * p).
Proof.
  intros n m p.
  induction n.
  -reflexivity.
  -simpl. rewrite mult_distr. rewrite IHn.
   reflexivity.
Qed.



  
