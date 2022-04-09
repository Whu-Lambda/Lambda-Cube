Require Import ssreflect.

Variable P:Prop.

Theorem helloworld: P -> P.
Proof.
  move => P1.
  apply:P1.
Qed.

Check helloworld.
