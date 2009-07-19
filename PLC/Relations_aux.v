Require Export Relations.

Section Reflexive_Transitive_Closure.
  Variable A : Type.
  Variable R : relation A.

  Inductive clos_rt_n (x:A) : A -> nat -> Prop :=
  | rt_n_step (y:A) : R x y -> clos_rt_n x y 1
  | rt_n_refl : clos_rt_n x x 0
  | rt_n_trans (y z:A) n1 n2:
    clos_rt_n x y n1 -> clos_rt_n y z n2 -> clos_rt_n x z (1 + n1 + n2).

  Lemma clos_rt_n_rt : forall x y n,
    clos_rt_n x y n -> clos_refl_trans A R x y.
  Proof.
    intros x y n H. induction H.
    apply rt_step; auto.
    apply rt_refl.
    eapply rt_trans; eauto.
  Qed.

  Lemma clos_rt_rt_n : forall x y,
    clos_refl_trans A R x y -> exists n, clos_rt_n x y n.
  Proof.
    intros x y H. induction H.
    exists 1; apply rt_n_step; auto.
    exists 0; apply rt_n_refl.
    destruct IHclos_refl_trans1 as [n1 H1].
    destruct IHclos_refl_trans2 as [n2 H2].
    exists (1 + n1 + n2); eapply rt_n_trans; eauto.
  Qed.

  Lemma clos_rt_rt_n_equiv : forall x y,
    clos_refl_trans A R x y <-> exists n, clos_rt_n x y n.
  Proof.
    intros x y.
    split; intro.
    eauto using clos_rt_rt_n.
    destruct H; eauto using clos_rt_n_rt.
  Qed.

  Lemma clos_rt_n_zero : forall x y,
    clos_rt_n x y 0 -> x = y.
  Proof.
    intros x y H; inversion H.
    reflexivity.
  Qed.

End Reflexive_Transitive_Closure.
