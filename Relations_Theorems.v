Require Export Relation.



Theorem composition_assoc {f g h : Rel} :
    h ○ (g ○ f) = (h ○ g) ○ f.
Proof.
  apply Extensionality => ad.
  repeat rewrite composition.
  split => [H | H].
  + induction H as [a]; induction H as [c]; induction H as [d].
    induction H as [adad]; induction H as [ac_gf cd_h].
    apply composition in ac_gf.
    induction ac_gf as [x]; induction H as [b]; induction H as [z].
    induction H as [ac_xz]; induction H as [ab_f bc_g].
    apply eq_OrderPair in ac_xz; induction ac_xz; subst x z.
    exists a; exists b; exists d.
    apply (conj adad).
    apply (conj ab_f).
    apply composition.
    exists b; exists c; exists d.
    split.
    - done.
    - apply (conj bc_g cd_h).
  + induction H as [a]; induction H as [b]; induction H as [d].
    induction H as [ad_ad]; induction H as [ab_f bd_hg].
    apply composition in bd_hg.
    induction bd_hg as [b_]; induction H as [c]; induction H as [d_].
    induction H as [bd_bd]; induction H as [bc_g cd_h].
    apply eq_OrderPair in bd_bd; induction bd_bd; subst b_ d_.
    exists a; exists c; exists d.
    apply (conj ad_ad).
    split.
    - rewrite composition.
      exists a; exists b; exists c.
      done.
    - done.
Qed.

Theorem composition_dom {f g A B C : set} :
      f | A → B -> g | B → C -> Dom (g ○ f) = Dom f.
Proof.
  intros fAB gBC.
  induction fAB as [funcf fAB].
  induction fAB as [domf_A ranf_B].
  induction gBC as [funcg gBC].
  induction gBC as [domg_B rang_C].
  apply Extensionality => a.
  split => [H | H].
  + apply dom in H.
    induction H as [c].
    apply composition in H.
    induction H as [a_]; induction H as [b]; induction H as [c_].
    induction H as [acac]; induction H as [ab_f bc_g].
    apply eq_OrderPair in acac; induction acac; subst a_ c_.
    apply dom.
    by exists b.
  + apply dom in H as H0.
    induction H0 as [b ab_f] .
    specialize (ranf_B b).
    move: ranf_B; rewrite ran => ranf_B.
    assert (exists a, (<|a,b|>) ∈ f).
    by exists a.
    specialize (ranf_B H0) as bB  .
    clear H0 ranf_B.
    rewrite <- domg_B in bB.
    apply dom in bB.
    induction bB as [c bc_g].
    apply dom.
    exists c.
    rewrite composition.
    by exists a; exists b; exists c.
Qed.    

Theorem composition_ran {f g A B C : set} :
      f | A → B -> g | B → C -> Ran (g ○ f) ⊂ (Ran g).
Proof.
  intros fAB gBC c H.
  induction fAB as [domf_A ranf_B].
  induction gBC as [domg_B rang_C].
  apply ran in H.
  induction H as [a H].
  apply composition in H.
  induction H as [a_]; induction H as [b]; induction H as [c_].
  induction H as [acac]; induction H as [ab_f bc_g].
  apply eq_OrderPair in acac; induction acac; subst a_ c_.
  apply ran.
  by exists b.
Qed.

Theorem composition_func {f g : set} :
  func f -> func g -> func (g ○ f).
Proof.
  intros funcf funcg.
  intros x H.
  apply dom in H.
  induction H as [z H].
  assert (xz_gf : (<|x,z|> ∈ (g ○ f))) by done.
  apply composition in H.
  induction H as [x_]; induction H as [y]; induction H as [z_].
  induction H as [xyxy]; induction H as [xy_f yz_g].
  apply eq_OrderPair in xyxy; induction xyxy; subst x_ z_.
  exists z.
  apply (conj xz_gf).
  intros z_ H.

  assert (x_domf : x ∈ (Dom f)).
  apply dom.
  by exists y.
  specialize (funcf x x_domf).
  induction funcf as [y0 Hf].
  induction Hf as [xy0f Hf].

  assert (y_domg : y ∈ (Dom g)).
  apply dom.
  by exists z.
  specialize (funcg y y_domg).
  induction funcg as [z0 Hg].
  induction Hg as [yz0g Hg].

  apply composition in H.
  induction H as [x1]; induction H as [y1]; induction H as [z1].
  induction H as [xzxz]; induction H as [xyf yzg].
  apply eq_OrderPair in xzxz; induction xzxz; subst x1 z1.
  apply (Hg z) in yz_g.
  apply (Hf y1) in xyf.
  apply (Hf y) in xy_f.
  subst y0 y1 z0.
  by apply (Hg z_) in yzg.
Qed.  



Theorem composition_map {f g A B C : set} :
     f | A → B -> g | B → C -> g ○ f | A → C.
Proof.
  intros fAB gBC.
  inversion fAB as [funcf fAB_].
  induction  fAB_ as [domf_A ranf_B].
  inversion gBC as [funcg gBC_].
  induction gBC_ as [domf_B ranf_C].
  apply (conj (composition_func funcf funcg)).
  split.
  + rewrite <- domf_A.
    apply (composition_dom fAB gBC).
  + intros c H.
    apply ran in H.
    induction H as [a H]     .
    apply composition in H.
    induction H as [a_]; induction H as [b]; induction H as [c_].
    induction H as [acac]; induction H as [ab_f bc_g].
    apply eq_OrderPair in acac; induction acac; subst a_ c_.
    specialize (ranf_C c).
    move:ranf_C ; rewrite ran => H.
    by apply (H (ex_intro (fun b => (<| b, c |>) ∈ g) b bc_g)).
Qed.

Theorem dom_reverse {f : set} :
    Dom (Reverse f) = Ran f.
Proof.
  apply Extensionality => x.
  rewrite dom; rewrite ran.
  split => [H | H].
  + induction H as [y xy_f'] .
    apply (reverse f) in xy_f'.
    by exists y.
  + induction H as [y yx_f].
    exists y.
    by apply (reverse f).
Qed.

Theorem ran_reverse {f : set} :
    Ran (Reverse f) = Dom f.
Proof.
  apply Extensionality => x.
  rewrite dom; rewrite ran.
  split => [H | H].
  + induction H as [y yx_f'] .
    apply (reverse f) in yx_f'.
    by exists y.
  + induction H as [y xy_f] .
    exists y.
    by apply (reverse f).
Qed.  



Theorem reverse_bijection (f A B : set) :
  Bijection f A B <-> f | A → B /\ Reverse f | B → A.
Proof.    
  split => [H | H].  
  + induction H as [fAB H].
    induction H as [ranf_B inj].
    induction fAB as [funcf fAB].
    induction fAB as [domf_A ranfB].
    split.
    - apply (conj funcf) .
      apply (conj domf_A ranfB).
    - split.
      * intros b b_ranf.
        rewrite dom_reverse in b_ranf.
        apply ran in b_ranf.
        induction b_ranf as [a abf] .
        exists a.
        split.
        by apply reverse.
        intros a_ ab_f.
        apply (reverse f) in ab_f.
        apply inj.
        apply (eq_value funcf) in abf.
        apply (eq_value funcf) in ab_f.
        by subst b.
      * rewrite dom_reverse.
        rewrite ran_reverse.
        apply (conj ranf_B)         .
        by rewrite domf_A.
  + induction H as [fAB f'BA] .
    induction fAB as [funcf fAB].
    induction fAB as [domf_A ranfB].    
    induction f'BA as [funcf' H].
    induction H as [ranf_B domfA].
    rewrite dom_reverse in ranf_B.
    rewrite ran_reverse in domfA.
    split.
    - apply (conj funcf) .
      apply (conj domf_A ranfB).
    - apply (conj ranf_B) .
      intros a a_ H.
      specialize (funcf' (Value f a)).
      assert (H1 : (Value f a) ∈ (Dom (Reverse f))).
      rewrite dom_reverse.
      apply ran.
      exists a.
      apply (value f a funcf).
      apply funcf' in H1.
      induction H1 as [a0 H1].
      induction H1 as [_ H1].
      specialize (value f a funcf) as abf.
      specialize (value f a_ funcf) as a_bf.
      rewrite <- H in a_bf.
      rewrite <- reverse in abf.
      rewrite <- reverse in a_bf.
      apply (H1 a) in abf.
      apply (H1 a_) in a_bf.
      by subst a0.
Qed.

Theorem reverse_ {R : set} :
  forall u, u ∈ (Reverse R) <-> exists x y, u = <|y,x|> /\ <|x,y|> ∈ R.
Proof.
  intros u.
  split => [H | H].
  + apply class in H.
    apply H.
  + inversion H as [x H0]; induction H0 as [y].
    induction H0 as [y_yx xy_R].
    apply class.
    split.
    - apply product.
      exists y; exists x.
      split.
      apply ran.
      by exists x.
      split.
      apply dom.
      by exists y.
      done.
    - by exists x; exists y.
Qed.       




Theorem reverse_composition {f g : set} :
  Reverse (g ○ f) = (Reverse f) ○ (Reverse g).
Proof.
  apply Extensionality => u.
  rewrite composition.
  rewrite reverse_.
  split => [H | H].
  + induction H as [x]; induction H as [z] .
    induction H as [u_yx xy_gf].
    apply composition in xy_gf.
    induction xy_gf as [x_]; induction H as [y]; induction H as [z_].
    induction H as [xzxz]; induction  H as [xy_f yz_g].
    apply eq_OrderPair in xzxz; induction xzxz; subst x_ z_.
    exists z; exists y; exists x.
    by repeat rewrite reverse.
  + induction H as [x]; induction H as [y]; induction H as [z].
    move: H.  repeat rewrite reverse.  intro H.
    induction H as [u_xz]; induction H as [yx_g zy_f].
    exists z; exists x.
    apply (conj u_xz).
    apply composition.
    by exists z; exists y; exists x.
Qed.

Theorem domran {f x y} :
    <|x,y|> ∈ f -> x ∈ (Dom f) /\ y ∈ (Ran f).
Proof.
  intro H.
  split.
  by apply dom; exists y.
  by apply ran; exists x.
Qed.  

Theorem value_composition  {f g A B C : set} :
  f | A → B -> g | B → C -> forall x, Value g (Value f x)  = Value (g ○ f)x.
Proof.
  intros fAB gBC x.

  induction fAB as [funcf  Hf].
  induction Hf as [domf_A ranf_B].
  specialize (value f x funcf) as xfx_f.
  specialize (domran xfx_f) as dom_ran.
  induction dom_ran as [x_domf fx_ranf].
  specialize (funcf x x_domf) as Hf.
  induction Hf as [y0 Hf].
  induction Hf as [xy0_f Hf].
  specialize (Hf (Value f x) xfx_f) as Hf'.
  subst y0.
  specialize (ranf_B (Value f x) fx_ranf).

  induction gBC as [funcg  Hg].
  induction Hg as [domf_B ranf_C].
  rewrite <- domf_B in ranf_B.
  specialize (funcg (Value f x) ranf_B) as Hz.
  induction Hz as [z0 Hz].
  induction Hz as [fxy_g Hz].
  specialize (value g (Value f x) funcg) as fxgfx_g.
  specialize (Hz (Value g (Value f x)) fxgfx_g) as Hz'.
  subst z0.

  specialize (value (g ○ f) x (composition_func funcf funcg)) as H.
  apply composition in H.
  induction H as [x0]; induction H as [y]; induction H as [z].
  induction H as [xzxz H]; induction H as [xy_f yz_g].
  apply eq_OrderPair in xzxz; induction xzxz; subst x0 z.
  apply (Hf y) in xy_f.
  subst y.
  by apply Hz.
Qed.

  



Theorem composition_injection {f g A B C} :
    Injection f A B -> Injection g B C -> Injection (g ○ f) A C.
Proof.
  intros injfAB injgBC.
  induction injfAB as [fAB injf].
  induction injgBC as [gBC injg].
  specialize (value_composition fAB gBC) as H0.
  split.
  + apply (composition_map fAB gBC).
  + intros x x' H.
    apply injf.
    apply injg.
    rewrite (H0 x).
    rewrite (H0 x').
    done.
Qed.   

Theorem composition_surjection {f g A B C} :
    Surjection f A B -> Surjection g B C -> Surjection (g ○ f) A C.
Proof.
  intros Hf Hg.
  induction Hf as [fAB ranf_B].
  induction Hg as [gBC rang_C].
  split.
  + apply (composition_map fAB gBC).
  + apply Extensionality => c.
    rewrite ran.
    split => [H | H].
    - induction H as [a H].
      apply composition in H.
      induction H as [a0]; induction H as [b]; induction H as [c0].
      induction H as [acac]; induction H as [ab_f bc_g].
      apply eq_OrderPair in acac; induction acac; subst a0 c0.
      apply domran in bc_g.
      induction bc_g.
      by subst C.
    - rewrite <- rang_C in H.
      apply ran in H.
      induction H as [b bc_g].
      apply domran in bc_g as dom_ran.
      induction dom_ran as [b_domg _].      
      induction gBC as [_ Hg].
      induction Hg as [domg_B _].
      subst B.
      rewrite domg_B in b_domg.
      apply ran in b_domg.
      induction b_domg as [a ab_f].
      exists a.
      apply composition.
      by exists a; exists b; exists c.
Qed.

Theorem image_subset {f A B P1 P2 : set} 
  {P1_A : P1 ⊂ A} {P2_A : P2 ⊂ A} {fAB : f | A → B}:
  P1 ⊂ P2 -> Image f P1 ⊂ (Image f P2).
Proof.    
  intros H b a_fP1.
  apply image in a_fP1.
  induction a_fP1 as [a H1].
  induction H1 as [a_P1 ab_f].
  specialize (H a a_P1).
  rewrite image.
  by exists a.
Qed.  

Theorem image_cup 
  {f A B P1 P2 : set} {fAB : f | A → B}
  {P1_A : P1 ⊂ A} {P2_A : P2 ⊂ A} {P1P2 : P1 ⊂ P2} :
  Image f (P1 ∪ P2) = (Image f P1) ∪ (Image f P2).
Proof.
  apply Extensionality => b.  
  rewrite cup.
  repeat rewrite image.
  split => [H | H].
  + induction H as [a].
    induction H as [a_P1P2 ab_f].
    apply cup in a_P1P2.
    induction a_P1P2 as [a_P1 | a_P2].
    - by apply or_introl; exists a.
    - by apply or_intror; exists a.
  + induction H as [H | H].
    - induction H as [a]; induction H as [aP abf].
      exists a.
      rewrite cup.
      apply (conj (or_introl aP) abf).
    - induction H as [a]; induction H as [aP abf].
      exists a.
      rewrite cup.
      apply (conj (or_intror aP) abf).
Qed.

Theorem image_cap 
  {f A B P1 P2 : set} {fAB : f | A → B}
  {P1_A : P1 ⊂ A} {P2_A : P2 ⊂ A} {P1P2 : P1 ⊂ P2} :
  Image f (P1 ∩ P2) ⊂ ((Image f P1) ∩ (Image f P2)).
Proof.
  intros b.
  rewrite cap.
  repeat rewrite image.
  intro H.
  induction H as [a]; induction H as [aP1P2 abf].
  apply cap in aP1P2; induction aP1P2 as [aP1 aP2].
  split.
  + by exists a.
  + by exists a.
Qed.

Theorem image_diff 
  {f A B P : set} {fAB : f | A → B} {P_A : P ⊂ A} :
  ((Image f A) // (Image f P)) ⊂ (Image f (A // P)).
Proof.
  intro b.
  rewrite diff.
  repeat rewrite image.
  intro H.
  induction H as [L R].
  induction L as [a]; induction H as [aA abf].
  move : R; rewrite <- allnot_notexists; intro H.
  specialize (H a).
  apply DeMorgan_notand in H.
  induction H as [not_aP | not_abf].
  - exists a.
    split.
    * by apply diff.
    * done.
  - case (not_abf abf).
Qed.





Theorem eqclass_refl {R : Rel} {A : set}  (H : equivalence R A) :
    forall a, a ∈ A -> a ∈ (eqClass H a).
Proof.
  intros a aA.
  apply eqclass.
  induction H as [H _].
  by specialize (H a aA).
Qed.



Theorem eqclass_eq {R A : set} (H : equivalence R A) :
  forall a b, a ∈ A -> b ∈ A -> <|a,b|> ∈ R <-> eqClass H a = eqClass H b.
Proof.
  intros a b aA bA.
  inversion H as [refl_ H0].
  induction H0 as [sym_ trans_].
  split => [H0 | H0].
  + apply Extensionality => i.
    repeat rewrite eqclass.
    split => [H1 | H1].
    - induction H1 as [iA ai_R].
      apply (conj iA).
      apply (sym_ a b aA bA) in H0.
      apply (trans_ b a i bA aA iA H0 ai_R).
    - induction H1 as [iA ai_R].
      apply (conj iA).
      apply (trans_ a b i aA bA iA H0 ai_R).
  + specialize (eqclass_refl H a aA) as H1.    
    rewrite H0 in H1.
    apply eqclass in H1.
    induction H1 as [_ H1].
    by apply (sym_ b a bA aA ) in H1.
Qed.

Theorem eqclass_contra {R A : set} {H : equivalence R A} :
    forall a b, a ∈ A -> b ∈ A ->
    eqClass H a <> eqClass H b -> (eqClass H a ∩ (eqClass H b)) = ∅.
Proof.
  intros a b aA bA H0.
  apply Extensionality => i.
  rewrite cap.
  repeat rewrite eqclass.
  split => [H1 | H1].
  + induction H1 as [l r] .
    induction l as [iA ai_R].
    induction r as [_ bi_R].
    inversion H as [refl_ H2].
    induction H2 as [sym_ trans_].
    apply (sym_ b i bA iA) in bi_R.
    specialize (trans_ a i b aA iA bA ai_R bi_R).
    apply (eqclass_eq H a b aA bA ) in trans_.
    case (H0 trans_).
  + specialize (empty i) as H2.
    case (H2 H1).
Qed.
    
     













    




      

      
      
      
      
      
      
      




