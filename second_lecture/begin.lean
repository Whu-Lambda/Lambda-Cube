import tactic.ring 

--C-H isomorphism
constant And : Prop → Prop → Prop
variables p q r : Prop

constant Proof : Prop → Type

constant Or : Prop → Prop → Prop

constant Not : Prop → Prop

#check (or (and p q) (and q r))

#check and p q

#check implies (and p q) (and q p)

--A → B A成立可以推出B成立， 这个时候，我们说B蕴涵了A

variables CCF_is_a_stupid_ass : Prop

axiom CCF_stupid : Π CCF_is_a_stupid_ass : Prop,
  Proof (CCF_is_a_stupid_ass)

#check CCF_stupid

constant andb_comm : Π p q : Prop,
  Proof (implies (and p q) (and q p))

--Π Type (A, B)

--or axiom and_comm : (and p q) ↔ (and q p)

#check andb_comm p q

--theorem poroving

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

/-or theorem t1 : p → q → p :=
     assume hp : p,
     assume hq : q,
     show p, from hp
-/     

--ring tactics

example (R : Type) [comm_ring R] (a b : R) :
  (a+b)^3 = a^3+3*a^2*b+3*a*b^2+b^3 :=
by ring

variables P Q R :  Prop

theorem basic_logic : (P → Q) ∧ (Q → R) → (P → R) :=
begin
intro H, -- H is "P implies Q and Q implies R"
intro HP, -- we want P -> R so let's assume P.
have HQ : Q,
exact H.left HP, -- apply P->Q to P to get Q.
-- now we can get the goal
exact H.right HQ
end

--¬ : Prop → false

example : forall x : nat, x <= x+x :=
begin
intro x,
have H : 0<=x,
apply nat.zero_le,
-- at this point one could say "H is the hypothesis that 0 <= x"
-- but one could also say that H is an object of type 0<=x
-- or in other words a proof that 0<=x.
have H2 : x+0<=x+x,
apply nat.add_le_add_left,
assumption,
have H3 : x+0 = x,
trivial,
rewrite H3 at H2,
assumption
end

