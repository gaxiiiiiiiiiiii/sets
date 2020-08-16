Require Export Relations_Theorems.

Definition isMin (R : Rel) (X y : set) :=
  y ∈ X /\ ~ exists z, z ∈ X /\ <|z,y|> ∈ R.

Definition isMax (R : Rel) (X y : set) :=
  y ∈ X /\ ~ exists z, z ∈ X /\ <|y,z|> ∈ R.

Definition well_found (R : Rel) (A : set) :=
  forall X, X ⊂ A -> X <> ∅ -> exists x, isMin R X x.


    
Definition  well_order (R : Rel) (A : set) :=
  well_found R A /\ total_order R A.


Axiom Belong : set.
Axiom belong :
    forall u, u ∈ Belong <-> exists x y, u = <|x,y|>  /\ x ∈ y.


Definition isOrder (z : set) :
  well_order Belong z /\ forall x y, x ∈ y /\ y ∈ z -> x ∈ z. 


