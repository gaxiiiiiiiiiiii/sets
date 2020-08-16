Require Export Order.

Theorem wellorder_subst {R A X} :
  well_order R A -> X ⊂ A -> well_order R X.
Proof.
  intros H XA.
  induction H as [W T].
  unfold well_found in W.
  induction T as [trans_ T].
  induction T as [notrefl tri].
  split.
  + intros Y YX notY.
    apply W.
    - intros y yY.
      apply (XA y (YX y yY)).
    - done.
  + split.
    intros x y z xX yX zX xyR yzR.
    apply (trans_ x y z (XA x xX) (XA y yX) (XA z zX) xyR yzR).
    split.
    * intros x xX H.
      apply ((notrefl x (XA x xX)) H) .
    * intros x y xX yX.
      induction (tri x y (XA x xX) (XA y yX)).
      apply (or_introl H).
      induction H.
      apply (or_intror (or_introl H)).
      apply (or_intror (or_intror H)).
Qed.
      


