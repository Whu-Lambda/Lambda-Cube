Require Import Arith.
Require Import ArithRing Ring.
Require Import Lia.
Import Nat.

(*
  这一次我们着重介绍如何用Coq证明涉及到多项式的定理;
  首先我们可以定义一个简单的递归函数用于计算∑n.
 *)

Fixpoint sum (n : nat) :=
  match n with
  | 0 => 0
  | S n' => n + sum n' 
  end.

(*想要证明2 * sum n = n * (n + 1)*)

Theorem sum_1 : forall n : nat,
    2 * sum n = n * (n + 1).
Proof.
  induction n.
  - (*n = 0*)
    simpl. reflexivity.
  - simpl. ring_simplify.
    rewrite IHn.
    ring_simplify. reflexivity.
Qed.

(*
  我们可以通过不断使用交换律结合律和分配律来改写待证明的项，
  但这么做是非常繁杂且无趣的。
  那么有什么手段能够帮助我们自动地对待证项使用上述定理改写呢？
  巧合的是，抽象代数中的环结构非常完美地契合我们的要求。
  Coq提供的ring策略能够对所有在环或半环上的多项式命题进行化简,
  那么，什么是环？
  下面的代码给出了一个环或半环结构需要满足的性质。
 *)

Record ring_theory : Prop := mk_rt {
  Radd_0_l    : forall x, 0 + x == x;
  Radd_sym    : forall x y, x + y == y + x;
  Radd_assoc  : forall x y z, x + (y + z) == (x + y) + z;
  Rmul_1_l    : forall x, 1 * x == x;
  Rmul_sym    : forall x y, x * y == y * x;
  Rmul_assoc  : forall x y z, x * (y * z) == (x * y) * z;
  Rdistr_l    : forall x y z, (x + y) * z == (x * z) + (y * z);
  Rsub_def    : forall x y, x - y == x + -y;
  Ropp_def    : forall x, x + (- x) == 0
}.

Record semi_ring_theory : Prop := mk_srt {
  SRadd_0_l   : forall n, 0 + n == n;
  SRadd_sym   : forall n m, n + m == m + n ;
  SRadd_assoc : forall n m p, n + (m + p) == (n + m) + p;
  SRmul_1_l   : forall n, 1*n == n;
  SRmul_0_l   : forall n, 0*n == 0;
  SRmul_sym   : forall n m, n*m == m*n;
  SRmul_assoc : forall n m p, n*(m*p) == (n*m)*p;
  SRdistr_l   : forall n m p, (n + m)*p == n*p + m*p
}.

(*
  ring策略会利用上述的性质对待证项进行化简，
  这个过程是自动化的，而且化简的效果非常好。
 *)

Fixpoint summation (n : nat) :=
  match n with
  | 0 => 0
  | S n' => n ^ 2 + summation n' 
  end.
(*∑ n^2*)

Theorem sum_2 : forall n : nat,
    6 * summation n = n * (2 * n + 1) *  (n + 1).
Proof.
  induction n.
  -simpl. reflexivity.
  -simpl. ring_simplify.
   rewrite IHn. ring.
Qed.

(*
  我们可以再举几个ring应用的例子.
 *)

Fixpoint sum_3 (n : nat) :=
  match n with
  | 0 => 0
  | S n' => n ^ 3 + sum_3 n'
  end.

Theorem sum_three : forall n : nat,
    4 * sum_3 n = n * n * (n + 1) * (n + 1).
Proof.
  induction n.
  -simpl. reflexivity.
  - simpl. ring_simplify.
    rewrite IHn. ring.
Qed.

(*
  然而ring并非是万能的，它只能处理"+"和"*"运算，
  一旦证明式中出现"-"，ring也无可奈何.
 *)

Fixpoint summa (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n * (2 * n - 1) + summa n'
  end.

(*∑n*(2*n-1)*)

Theorem summa_formula : forall n,
  6 * summa n = n * (n + 1) * (4 * n - 1).
Proof.
  induction n.
  -auto.
  -simpl. ring_simplify.
   rewrite IHn. 
   destruct n.
   +lia.
   +lia.
Qed.

