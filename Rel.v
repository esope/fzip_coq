Require Import Utf8.
Require Import Relations.

Parameter A : Type.

Implicit Arguments clos_refl_trans [A].
Hint Resolve rt_refl rt_trans rt_step.
Implicit Arguments clos_trans [A].
Hint Resolve t_trans t_step.

Definition concat (R1 R2: relation A) x y :=
  exists z, R1 x z ∧ R2 z y.
Inductive union (R1 R2: relation A) (x y: A): Prop :=
| Left : R1 x y → union R1 R2 x y
| Right : R2 x y → union R1 R2 x y.
Hint Constructors union.
Notation "R ; S" := (concat R S) (at level 30).
Notation "R ∪ S" := (union R S) (at level 30).
Notation "R ⋆" := (clos_refl_trans R) (at level 29).
Notation "R ≡ S" := (forall x y, R x y <-> S x y) (at level 31).

Lemma concat_wf_equiv (R1 R2: relation A):
  well_founded (R1 ; R2) -> well_founded (R2 ; R1).
Proof.
intros R1 R2 H.
intro x.
constructor; intros y [z [Hyz _]].
assert (Acc (R1; R2) z) as H0 by auto; clear H.
generalize dependent y.
induction H0; intros.
constructor; intros z [t [Hzt Hty]].
eapply H0; eauto.
exists y; eauto.
Qed.

Lemma concat_assoc (R1 R2 R3: relation A):
  (R1; R2); R3 ≡ R1; (R2; R3).
Proof.
intros R1 R2 R3 x y; split; intro H.
destruct H as [z [Hxz Hzy]].
destruct Hxz as [t [Hxt Htz]].
exists t; split; auto. exists z; split; auto.
destruct H as [z [Hxz Hzy]].
destruct Hzy as [t [Hzt Hty]].
exists t; split; auto. exists z; split; auto.
Qed.

Lemma concat_star (R: relation A):
  R⋆ ≡ R⋆ ; R⋆.
Proof.
intros; split; intro H.
exists y; split; auto.
destruct H as [z [Hxz Hzy]]; eauto.
Qed.

Lemma concat_star2 (R1 R2: relation A):
  (R1; R2⋆) ≡ (R1; R2⋆) ; R2⋆.
Proof.
intros R1 R2 x y; split; intro H.
exists y; split; auto.
rewrite concat_assoc in H.
destruct H as [z [Hxz Hzy]].
rewrite <- concat_star in Hzy.
exists z; split; auto.
Qed.

Theorem r_u_s_wf (R1 R2: relation A):
  well_founded (R1⋆ ; R2) ->
  well_founded (R2⋆ ; R1) ->
  well_founded (R1 ∪ R2).
Proof.
intros R1 R2 HR1R2 HR2R1.
assert (well_founded (R1 ; (R2)⋆)) as wfR1R2 by auto using concat_wf_equiv.
assert (well_founded (R2 ; (R1)⋆)) as wfR2R1 by auto using concat_wf_equiv.
intro x.
assert (Acc (R1 ; (R2)⋆) x) as Hx1 by auto; induction Hx1.
assert (Acc (R2 ; (R1)⋆) x) as Hx2 by auto; induction Hx2.
constructor; intros y Hy.
destruct Hy as [Hy | Hy].
eapply H0; exists x; split; auto.
eapply H2; auto. exists x; split; auto.
intros z Hz.
eapply H0; eauto. rewrite concat_star2.
exists y; split; auto.
Qed.

