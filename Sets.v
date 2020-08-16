Require Export Axioms.

(* 空集合 *)
Theorem ex_empty :
  exists !e, forall x, ~ x ∈ e.
Proof.
  induction Existance as [X _].
  specialize (Comprehension (fun x => x <> x) X ) as H.
  induction H as [E H].
  exists E.
  split.
  + intros x notEx.
    specialize (H x).
    apply H in notEx.
    induction notEx as [_ notxx].
    apply notxx.
    reflexivity.
  + intros E' H'.
    apply Extensionality.
    intro z.
    specialize (H z).
    specialize (H' z).
    rewrite H.
    split => [H1 | H1].
    - induction H1 as [_ F].
      case (F (eq_refl z)).
    - case (H' H1).
Qed.

Parameter Empty : set.
Axiom empty :
  forall x, ~ x ∈ Empty.
Notation "∅" := Empty.



(* 包含関係  *)
Definition Subset (X Y : set) := forall x, x ∈ X -> x ∈ Y.
Notation "A ⊂ B" := (Subset A B)(at level 10).

(* 順序対  *)
Theorem uniex_couple :
  forall X Y, exists !U, forall Z, Z ∈ U <-> Z = X \/ Z = Y.
  intros X Y.
  induction (Pair X Y) as [XY HXY].
  induction HXY as [XXY YXY].
  induction (Comprehension (fun x => x = X \/ x = Y) XY) as [U HU].
  exists U.
  split.
  + intro Z.
    specialize (HU Z).
    rewrite HU.
    split => [H | H].
    - apply H.
    - inversion H as [xX | xY].
      * subst X.
        apply (conj XXY H).
      * subst Y.
        apply (conj YXY H).
  + intros U' H'.
    apply Extensionality.
    intro Z.
    specialize (HU Z).
    specialize (H' Z).
    rewrite HU.
    rewrite H'.
    split => [H | H].
    - apply H.
    - inversion H as [xX | xY].
      * subst X.
        apply (conj XXY H).
      * subst Y.
        apply (conj YXY H).
Qed.    


    
Axiom Couple : set -> set -> set.
Axiom couple :
  forall X Y z, z ∈ ( Couple X Y) <-> z = X \/ z = Y.

Definition Single (X : set) := Couple X X.


Definition OrderPair (X Y : set) := Couple (Single X) (Couple X Y).
Notation "<| X , Y |>" := (OrderPair X Y) (at level 10).



(* 差集合  *)
Definition Diff (X Y : set) := {X ; fun x => ~ x ∈ Y}.
Notation "X // Y" := (Diff X Y)(at level 10).
Theorem diff (X Y : set) :
  forall x, x ∈ (X  //     Y ) <-> x ∈ X /\ ~ x ∈ Y.
Proof.
  intro x.
  by rewrite class.
Qed.

(* 和集合  *)
Definition isCups (X : set) := (fun x => exists Y, x ∈ Y /\ Y∈ X).

Theorem exists_cups (X : set):
  exists_class (isCups X).
Proof.
  specialize (Union X) as H.
  induction H as [U H].
  specialize (Comprehension (isCups X) U ) as H1.  
  induction H1 as [U' H1].
  exists U'.
  intro x.
  specialize (H1 x).
  rewrite H1.
  split => [H' | H'].
  + apply H'.
  + inversion H' as [Y H''].
    specialize (H Y x H'').
    apply (conj H H').
Qed.

Definition Cups (X : set) :=  (Class (isCups X) (exists_cups X)).
Notation "⊔ X" := (Cups X)(at level 10).
Theorem cups (X : set) :
  forall x, x ∈ (⊔ X) <-> exists Y, x ∈ Y /\ Y ∈ X.
Proof.
  intro x.
  by rewrite class.
Qed.

Definition Cup X Y := Cups (Couple X Y).
Notation "X ∪ Y" := (Cup X Y)(at level 10).
Theorem cup (X Y : set) :
  forall x, x ∈ (X ∪ Y)  <-> x ∈ X \/ x ∈ Y.
Proof.
  intros x.
  split => [H | H].
  + apply class in H.
    induction H as [U H].
    induction H as [xX UXY].
    apply couple in UXY.
    induction UXY as [UX | UY].
    - by subst; apply or_introl.
    - by subst; apply or_intror.
  + apply class.
    unfold isCups.
    induction H as [xX | xY].
    - exists X.
      apply (conj xX).
      apply couple.
      by apply or_introl.
    - exists Y.
      apply (conj xY).
      apply couple.
      by apply or_intror.
Qed.      

(* 共通部分  *)
Definition Cap X Y := {X ; (fun x => x ∈ Y)}.
Notation "X ∩ Y" := (Cap X Y) (at level 10).  
Theorem cap (X Y : set) :
  forall x, x ∈ (X ∩ Y) <-> x ∈ X /\ x ∈ Y.
Proof.
  intro x.
    by rewrite class.
Qed.    



Definition isCaps (X : set) := fun x => forall Y, Y ∈ X -> x ∈ Y.

Theorem not_empty (X : set) :
  X <> ∅ -> exists x, x ∈ X.
Proof.
  apply contrapositive.
  intro H.
  apply DoubleNegative.
  apply Extensionality.
  intro x.
  move: empty => emp.
  rewrite <- allnot_notexists in H.
  specialize (H x).
  specialize (emp x).
  split => [xX | xE].
  + case (H xX).
  + case (emp xE).
Qed.
    
Theorem exists_caps (X : set) :
  X <> Empty -> exists_class (isCaps X). 
Proof.
  intro H.
  specialize (not_empty X H) as H1.
  induction H1 as [E EX].
  specialize (Comprehension (isCaps X) E) as H'.
  induction H' as [Y H'].
  exists Y.
  intro x.
  specialize (H' x) as H''.
  rewrite H''; clear H''.
  unfold isCaps.
  split => [H1 | H1].
  + apply H1.
  + specialize (H1 E EX) as H2.
    apply (conj H2).
    intros Y' H3.
    apply (H1 Y' H3).
Qed.

Definition Caps (X : set) {H : X <> Empty} := Class (isCaps X) (exists_caps X H).
Notation "⊓ X" := (Caps X) (at level 10).
Theorem caps (X : set) {H : X <> Empty}:
  forall x, x ∈ (@Caps X H) <-> forall Y, Y ∈ X -> x ∈ Y.
Proof.
  intro x.
  by rewrite class.
Qed.       
      


(* 後続者函数  *)
Definition Suc (X : set) := X ∪( Single X).

                    

(* 冪集合  *)

Definition isPowerset (X : set) := fun Y => Y ⊂ X.

Theorem exists_powerset (X : set) :
  exists_class (fun Y => Y ⊂ X).
Proof.
  specialize (Power X) as H0.
  induction H0 as [U0 H0].
  specialize (Comprehension (isPowerset X) U0) as H.
  induction H as [U H].
  exists U.
  intro Y.
  specialize (H Y).
  rewrite H.
  split => [H1 | H1].
  + apply H1.
  + specialize (H0 Y H1).
    done.
Qed.

Definition Powerset (X : set) :=
  Class (isPowerset X) (exists_powerset X).
Notation "P[ X ]" := (Powerset X) (at level 10).

Theorem powerset (X : set) :
  forall x, x ∈( P[X]) <-> x ⊂ X.
Proof.
  intro x.
  by rewrite class.
Qed.    
