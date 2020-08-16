Require Export Logics.
Require Export Coq.Setoids.Setoid.

(* Axioms  *)

Axiom set : Type.

Axiom In : set -> set -> Prop.
Notation "x ∈ X" := (In x X)(at level 10).

(*Axioms*)                                                                             
Axiom Existance :                                                                      
  exists x : set, x = x.                                                               
                                                                                       
Axiom Extensionality :
  forall X Y , (forall z, z ∈ X <-> z ∈ Y) -> X = Y.

Axiom Comprehension :
  forall P X, exists Y, forall x, x ∈ Y <-> x ∈ X /\ P x.

Axiom Pair :
  forall X Y, exists U, X ∈ U /\ Y ∈ U.

Axiom Union :
  forall X, exists U, forall Y z, z ∈ Y /\ Y ∈ X -> z ∈ U.

Axiom Replacement :
  forall (P : set -> set -> Prop) (X : set),
  (forall x, x ∈ X -> exists !y, P x y) ->
  exists Y, forall x, x ∈ X -> exists y,y ∈ Y /\  P x y.

Axiom Power :
  forall X, exists U, forall Y, (forall x, x ∈  Y -> x ∈ X)  -> Y ∈ U.
                                           

(* Notations *)
Definition exists_class (P : set -> Prop) :=
  exists X, forall x, x ∈ X <-> P x.

Axiom Class :
  forall P, exists_class P -> set.

Axiom class :
  forall P H x, x ∈ (Class P H) <-> P x.

Theorem separate :
  forall P X, exists_class (fun x => x ∈  X /\ P x).
Proof.
  intros P X.
  apply (Comprehension P X).
Qed.


Definition Separation (X : set) (P : set -> Prop) :=
Class (fun x => x ∈ X  /\ P x) (separate P X ).

Notation "{ X ; P }" := (Separation X P)(at level 10).

Theorem separation {X : set} {P : set -> Prop} :
  forall x, x ∈  ({X ; P}) -> P x.
Proof.
  intros x H.
  apply class in H.
  apply H.
Qed.  
