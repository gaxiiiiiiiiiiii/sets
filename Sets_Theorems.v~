Require Export Sets.


(* 万有集合の非存在  *)
Theorem notex_universalset :
  ~ exists U, forall x, x ∈ U.
Proof.
  intro H.
  induction H as [U H].
  specialize (Comprehension (fun x => ~ x ∈  x) U)as F.
  induction F as [F HF].
  specialize (HF F).
  specialize (H F).
  case (ExcludedMiddle (F ∈ F)) as [FF |notFF].
  + apply HF in FF as notFF.
    induction notFF as [_ notFF].
    apply (notFF FF).
  + apply notFF.
    apply HF.
    apply (conj H notFF).
Qed.
                                                                                      
(* 順序対の相等 *)

Lemma x_xOPy (x y : set) :
  Single x ∈ <|x,y|>.
Proof.
  apply couple.
  by apply or_introl.
Qed.

Lemma xy_xOPy (x y : set) :
   Couple x y ∈ <|x,y|>.
Proof.
  apply couple.
  by apply or_intror.
Qed.

Lemma single (x : set) :
  forall y, y ∈ (Single x) <-> y = x.
Proof.
  intros y.
  split => [H | H].
  + apply couple in H.
    induction H as [L | R].
    - apply L.
    - apply R.
  + rewrite couple.
    apply (or_intror H) .
Qed.    

Theorem x_xx (x : set) :
  x ∈( Single x).
Proof.
  apply couple.
  by apply or_introl.
Qed.    

Theorem x_xy (x y : set) :
  x ∈ (Couple x y).
Proof.
  apply couple.
  by apply or_introl.
Qed.

Theorem y_xy (x y: set) :
  y ∈ (Couple x y).
Proof.  
  apply couple.
  by apply or_intror.
Qed.

Lemma single_single (x X : set) :
  Single x = Single X <-> x = X.
Proof.
  split => [H | H].
  + specialize (x_xx x) as Hx_xx.
    rewrite H in Hx_xx.
    by  apply single in Hx_xx.
  + by subst x.    
Qed.
    
Lemma single_couple (x X Y : set) :
  Single x = Couple X Y <-> x = X /\ x = Y.
Proof.
  specialize (x_xy X Y) as X_XY.
  specialize (y_xy X Y) as Y_XY.
  split => [H | H].
  + rewrite <- H in X_XY.
    rewrite <- H in Y_XY.
    apply single in X_XY.
    apply single in Y_XY.
    by subst x Y.
  + by induction H; subst X Y.
Qed.


Lemma couple_couple (x y X Y : set) :
  Couple x y = Couple X Y -> (x = X \/ x = Y) /\ (y = X \/ y = Y).
Proof.
  intro H.
  specialize (x_xy x y) as Hx_xy.
  specialize (y_xy x y) as Hy_xy.
  rewrite H in Hx_xy.
  rewrite H in Hy_xy.
  clear H.
  apply couple in Hx_xy.
  apply couple in Hy_xy.
  done.
Qed.  

Lemma couple_single (x y X : set) :
  Couple x y = Single X <-> x = X /\ y = X.
Proof.
  specialize (x_xy x y) as Hx_xy.
  specialize (y_xy x y) as Hy_xy.
  split => [H | H].
  + rewrite H in Hx_xy.
    rewrite H in Hy_xy.
    apply single in Hx_xy.
    apply single in Hy_xy.
    by subst x y.
  + by induction H; subst x y.
Qed.    


    
Theorem eq_OrderPair {x y X Y : set} :
  <|x,y|> = <|X,Y|> <-> x = X /\ y = Y.
Proof.
specialize (xy_xOPy x y) as H1.
specialize (xy_xOPy X Y) as H2.
specialize (x_xOPy x y) as H3.
split => [H | H].
+ rewrite H in H1.
  rewrite <- H in H2.
  rewrite H in H3.
  apply couple in H1.
  apply couple in H2.
  apply couple in H3.
  case (ExcludedMiddle (x = y)) as [xy | notxy].
  - subst y.
    induction H1 as [x_X | x_XY].
    * apply (single_single x X) in x_X.
      subst X.
      induction H2 as [xY_x | xY_x].
        apply couple_single in xY_x.
        by induction xY_x; subst Y.
        apply couple_single in xY_x.
        by induction xY_x; subst Y.
    * by apply single_couple in x_XY.
  - induction H1 as [xy_X | xy_XY].
    * apply couple_single in xy_X.
      induction xy_X; subst x y.
      case (notxy (eq_refl X)).
    * apply couple_couple in xy_XY.
      induction xy_XY as [L R].
      induction H3 as [x_X | x_XY].
        apply (single_single x X) in x_X.
        apply (conj x_X).
        subst X.
        induction R as [yx | yY].
        assert (xy : x = y) by done.
        case (notxy xy).
        done.
        apply single_couple in x_XY.
        induction x_XY; subst X Y.
        apply (conj (eq_refl x)).
        induction R as [yx | yx].
        done.
        done.
+ by  induction H; subst X Y.
Qed.




(* 分配則  *)
Theorem cap_sym  {A B : set} :
    A ∩ B = B ∩ A.
Proof.
  apply Extensionality.
  intro x.
  repeat rewrite cap.
  split => [AB | BA].
  + by induction AB.
  + by induction BA.
Qed.

Theorem cup_sym {A B : set} :
  A ∪ B = B ∪ A.
  Proof.
    apply Extensionality => x.
    repeat rewrite cap .
    unfold isCups.
    repeat rewrite cup.
    split => [H | H].
    + induction H as [a | b].
      apply (or_intror a).
      apply (or_introl b).      
    + induction H as [b | a].
      - apply (or_intror b).
      - apply (or_introl a).
Qed.        


  Theorem cap_dist_cup_l {A B C : set} :
    A ∩ (B ∪ C)  = (A ∩ B) ∪ (A ∩ C).
  Proof.
    apply Extensionality => x.
    repeat rewrite cup.
    rewrite cap.
    rewrite cup.
    repeat rewrite cap.
    split => [H | H].
    + induction H as [a bc].
      induction bc as [b | c].
      - by apply or_introl.
      - by apply or_intror.
    + induction H as [ab | ac].
      - induction ab as [a b].
        apply (conj a (or_introl b)).
      - induction ac as [a c].
        apply (conj a (or_intror c)).
  Qed.

  Theorem cap_dist_cup_r {A B C : set} :
    (B ∪ C) ∩ A = (B ∩ A) ∪ (C ∩ A).
  Proof.
    repeat rewrite [_ ∩ A] cap_sym.
    by apply cap_dist_cup_l.
  Qed.

  Theorem cup_dist_cap_l {A B C : set} :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
  Proof.
    apply Extensionality => x.
    rewrite cup.
    rewrite cap.
    rewrite cap.
    repeat rewrite cup.
    split => [H | H].
    + induction H as [a | bc].
    - apply (conj (or_introl a) (or_introl a)).
    - induction bc as [b c].
      apply (conj (or_intror b) (or_intror c)).
    + induction H as [ab ac].
      induction ab as [a | b].
      apply (or_introl a).
      induction ac as [a | c].
      apply (or_introl a).
      apply (or_intror (conj b c)).
  Qed.

  Theorem cup_dist_cap_r {A B C : set} :
    (B ∩ C) ∪ A = (B ∪ A) ∩ (C ∪ A).
  Admitted.

  
