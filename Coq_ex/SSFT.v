Require Import ssreflect.

Module Lambda.

  Parameter a : Type.
  Parameter z z' : a.
  
  Compute ((fun x => fun x' => x') ((fun y => y) z) ((fun y => y) z')).

  Parameter a' : Type.
  
  Check (fun x => fun y => y x) : a -> (a -> a') -> a' .
  Check (fun x => fun y => x (y x)) : (a' -> a) -> ((a' -> a) -> a') -> a .
  (* Check (fun x => fun y => fun z => z (y x) (x y)) : TO_DO. *)
  
End Lambda.

Module Propositional.

  Lemma fact : forall A:Prop, (A <-> not A) -> False.
  Proof.
    move => A.
    (* intuition. *)
    case.    
    move => H1 H2.  
    have H3: (not A).
    move => H4.
    apply: H1 ; [exact H4 | exact H4].
    apply: (H3).
      by apply: H2.
  Qed.    

End Propositional.

Module Russell.
    
  Parameter V : Type.
  Parameter belongs_to : V -> V -> Prop.
  Notation "x # y" := (belongs_to x y) (at level 30).

  Axiom comprehension : forall (A:V -> Prop), exists c, forall y, (y # c <-> A y).
  Definition NotInSelf y := ~(y # y).

  Theorem R : exists c, forall y, (y # c <-> NotInSelf y).
  Proof.
    apply: comprehension NotInSelf.
  Qed.    

  Theorem Bad: exists r, (r # r <-> ~(r # r)).
  Proof.
    case: R => x H.
    exists x; apply: H x.
  Qed.

  Theorem VeryBad: False.
  Proof.
    case: Bad => x.
    apply: Propositional.fact.
  Qed.    
    
End Russell.


Module CurryHoward.

  Parameter P P1 P2 P3 : Prop.

  Check ((fun x => x) : (P -> P)).
  Check ((fun x => fun u => x): (P1 -> (P2 -> P1))).
  Check ((fun x => fun y => fun z => x z (y z))
         : (P1 -> (P2 -> P3)) -> ((P1 -> P2) -> (P1 -> P3))).

  Check ((P1 /\ P2) -> (P2 /\ P1)).
  Check ((P1 \/ P2) -> (P2 \/ P1)).

  Definition pi1 {A B:Prop} (H:A /\ B) := match H with conj a _ => a end.
  Definition pi2 {A B:Prop} (H:A /\ B) := match H with conj _ a => a end.

  Check ((fun H => conj (pi2 H) (pi1 H)) : (P1 /\ P2) -> (P2 /\ P1)).

  Print or.

  Check ((fun H => 
            match H with
            | or_introl x => or_intror x
            | or_intror x => or_introl x
            end)
         : (P1 \/ P2) -> (P2 \/ P1)).

  Print nat.
  Print Nat.pred.
  Print Nat.add.

  Lemma half: forall x, exists y, x=y+y \/ x=1+y+y.
    elim.
    exists 0.  
      by left.
      move => n [y ih].
      case:ih => ih.
      exists y.
      right.
      simpl.
        by rewrite ih.
        exists (1+y).
        left.
        rewrite ih.
        simpl.
          by rewrite <- plus_n_Sm.
  Defined.

  Check (half 25).
  Compute (half 25).

End CurryHoward.



Module HigherOrder.

  Check ( (fun x f => f x) : forall (x:Prop), (forall y,y) -> x).
  (* Check ( TO_DO : forall (x:Prop), forall (y:Prop), ((x -> y) -> x)). *)
  Parameter a : Type.
  Check (forall (x:a), forall (y:a), (forall z:(a -> Prop), z x -> z y) -> (forall z:(a -> Prop), z y -> z x)).

  Theorem reciprocal :
    forall (x:a), forall (y:a), (forall z:(a -> Prop), z x -> z y) -> (forall z:(a -> Prop), z y -> z x).
  Proof.
    move => x y H z H'.    
    apply: (H (fun i => z i -> z x)).
    move => x'.
    apply: x'.
    apply: H'.
  Qed.

End HigherOrder.



Module InductiveTypes.

  (* We have already seen 2 inductive types *)
  Print nat.
  Print or.

  (* But we can use inductive types for defining enumerated types *)

  Inductive color : Type :=
  | blue : color
  | green : color
  | magenta : color
  | yellow : color.

  Print bool.

  Definition is_blue x :=
    match x with
    | blue => true
    | _ => false
    end.

  (* Conjunction, True and False are also inductive types *)
  Print and.
  Print True.
  Print False.

  Definition abort (A:Prop) (H:False) 
    := match H return A with
      end.

  Check abort.

  (* Even existential quantification *)
  Print ex.
  Print sigT.
  
End InductiveTypes.
  
Notation "{{ p , v }} " := (existT _ p v).



Module InductivePred.

  (* We can also use inductive types for inductively defined predicates *)
  (* Let's prove a theorem about confluence *)
  
  Parameter A : Type.
  Parameter R : A -> A -> Prop.

  Inductive RTClosure : A -> A -> Prop :=
  | RT   {x y}   : R x y -> RTClosure x y
  | RT_R {x}     : RTClosure x x
  | RT_T y {x z} : RTClosure x y -> RTClosure y z -> RTClosure x z
  .

  Notation "x R> y" := (RTClosure x y) (at level 30).

  Inductive RSTClosure : A -> A -> Prop :=
  | RST   {x y}   : R x y -> RSTClosure x y
  | RST_R {x}     : RSTClosure x x
  | RST_T y {x z} : RSTClosure x y -> RSTClosure y z -> RSTClosure x z
  | RST_S {x y}   : RSTClosure x y -> RSTClosure y x
  .

  Notation "x <R> y" := (RSTClosure x y) (at level 30).
    
  Definition Confluent :=
    forall x y z, x R> y -> x R> z -> exists x', y R> x' /\ z R> x'.

  Definition ChurchRosser :=
    forall x y, x <R> y -> exists z, x R> z /\ y R> z.

  Theorem CCR : Confluent -> ChurchRosser.
  Proof.
    move => Conf x y.
    elim; clear x y.
    - move => x y; exists y.
      split.
      * by apply: RT.
      * by apply RT_R.
    - move => x; exists x; split; apply: RT_R.
    - move => y x z H0.
      case => z0.
      case => H1 H2 H3.
      case => z1 ; case => H4 H5.
      move: (Conf y z0 z1).
      case => //.
      move => z2; case => H6 H7.      
      exists z2; split.
      apply: (RT_T z0) => //.
      apply: (RT_T z1) => //.
    - move => x y H0; case => z; case => H1 H2.
      exists z.
      split => //=.
  Qed.

End InductivePred.

(*************************)
(* EQUALITY *)
(*************************)

Module Equal.
  Print eq.

  Lemma Leibniz: forall A (x:A) (P: A -> Prop), P x -> forall y:A, x = y -> P y.
  Proof.
    move => A x P H y Heq.
    rewrite <- Heq.
    exact H.
  Qed.

End Equal.
  
(******************************)
(* Unicity of Identity Proofs *)
(******************************)

Module UnicityIdentityProofs.

  Parameter A: Type.

  Definition UIP_refl :=
    forall (x:A) (p: x=x), p = eq_refl x.

  Definition K :=
    forall (x:A) (P: x=x -> Prop),
      P (eq_refl x) -> forall p:(x=x), P p.

  Definition J :=
    forall (x:A) (P: forall y:A, x=y -> Prop),
      P x (eq_refl x) -> forall p:(x=x), P x p.



  Definition vacuum_cleaner_power_cord (x : A) := {y : A & x=y}.

  (* The trivial power cord with endpoint x itself, together with the
  trivial path from x to x, is in that space *)

  Check ((fun x => {{ x , eq_refl }}) : forall x, vacuum_cleaner_power_cord x).

  (* Every power cord based on a fixed x, is retractable to the
  trivial path *)

  Remark power_cord_retraction :
    forall x:A, forall (z : vacuum_cleaner_power_cord x), z = {{ x , eq_refl }}.
  Proof.
    move=> x z.
    case: z => y p.
    (* The 'destruct' tactic realizes the 'retraction' of the path *)
    destruct p.
    apply: eq_refl.
  Qed.

  (* J becomes an easy corollary *)

  Theorem J_proof: J. 
  Proof.
    rewrite/J.
    intros.
    move:(power_cord_retraction x {{ x, p }}).
    rewrite <- p.
    elim.
    exact H.
  Qed.


End UnicityIdentityProofs.
