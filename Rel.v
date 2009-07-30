Require Import Utf8.
Require Import Relations.

Parameter A : Type.

Implicit Arguments clos_refl_trans [A].
Implicit Arguments clos_trans [A].
Implicit Arguments transp [A].
Hint Resolve rt_refl rt_trans rt_step.
Hint Resolve t_trans t_step.
Hint Unfold transp.

Definition concat (R1 R2: relation A) x y :=
  ∃ z, R1 x z ∧ R2 z y.
Hint Unfold concat.
Inductive union (R1 R2: relation A) (x y: A): Prop :=
| Left : R1 x y → union R1 R2 x y
| Right : R2 x y → union R1 R2 x y.
Hint Constructors union.
Notation "R ; S" := (concat R S) (at level 30).
Notation "R ∪ S" := (union R S) (at level 30).
Notation "R ⋆" := (clos_refl_trans R) (at level 29).
Notation "R '⁻¹'" := (transp R) (at level 29).
Notation "R ⊆ S" := (forall x y, R x y → S x y) (at level 31).
Notation "R ≡ S" := (forall x y, R x y ↔ S x y) (at level 31).

Definition diamond (R: relation A) := (R⁻¹; R) ⊆ (R; R⁻¹).
Definition confluent (R: relation A) := diamond (R⋆).
Definition weakly_confluent (R: relation A) := (R⁻¹; R) ⊆ (R; R⁻¹⋆).

Lemma transp_concat_commute (R1 R2: relation A):
  (R1; R2)⁻¹ ≡ (R2⁻¹; R1⁻¹).
Proof.
intros R1 R2 x y; split; intro H;
destruct H as [z [Hxz Hzy]]; eauto.
Qed.

Lemma transp_star_commute (R: relation A):
  R⁻¹⋆ ≡ R⋆⁻¹.
Proof.
intro R. split; intro H.
induction H; unfold transp in *; eauto.
unfold transp in H. induction H; eauto.
Qed.

Lemma union_star_equiv (R1 R2: relation A):
  (R1 ∪ R2)⋆ ≡ (R1⋆; R2⋆)⋆.
Proof.
intros R1 R2 x y; split; intro H.
induction H; eauto.
destruct H; apply rt_step; eauto.
induction H; eauto.
destruct H as [z [Hxz Hzy]].
generalize dependent y. induction Hxz; intros; eauto.
apply rt_trans with (y := y); auto.
clear H; induction Hzy; eauto.
induction Hzy; eauto.
Qed.

Lemma concat_star_included1 (R1 R2: relation A):
  R1⋆ ⊆ (R1; R2⋆)⋆.
Proof.
intros R1 R2 x y H.
induction H; eauto.
Qed.

Lemma concat_star_included2 (R1 R2: relation A):
  R2⋆ ⊆ (R1⋆; R2)⋆.
Proof.
intros R1 R2 x y H.
induction H; eauto.
Qed.

Lemma comm_star_included1 (R1 R2: relation A):
  (R1; R2) ⊆ (R2; R1) →
  (R1⋆; R2) ⊆ (R2; R1⋆).
Proof.
intros R1 R2 Hcomm x y H.
destruct H as [z [Hxz Hzy]].
rewrite rt1n_trans_equiv in Hxz.
generalize dependent y; induction Hxz; intros; eauto.
apply IHHxz in Hzy.
destruct Hzy as [t [Hyt Hty0]].
assert ((R2; R1) x t) by eauto.
destruct H0 as [u [Hxu Hut]]. eauto 6.
Qed.

Lemma comm_star_included2 (R1 R2: relation A):
  (R1; R2) ⊆ (R2; R1) →
  (R1; R2⋆) ⊆ (R2⋆; R1).
Proof.
intros R1 R2 Hcomm x y H.
destruct H as [z [Hxz Hzy]].
rewrite rt1n_trans_equiv in Hzy.
generalize dependent x; induction Hzy; intros; eauto.
assert ((R2; R1) x0 y) by eauto.
destruct H0 as [t [Hx0t Hty]].
apply IHHzy in Hty.
destruct Hty as [u [Htu Huz]]; eauto 6.
Qed.

Lemma comm_star_included (R1 R2: relation A):
  (R1; R2) ⊆ (R2; R1) →
  (R1⋆; R2⋆) ⊆ (R2⋆; R1⋆).
Proof.
intros R1 R2 Hcomm x y H.
auto using comm_star_included1, comm_star_included2.
Qed.

(*
Lemma union_star_comm_included (R1 R2: relation A):
  (R1; R2) ⊆ (R2; R1) →
  (R1 ∪ R2)⋆ ⊆ R1⋆; R2⋆.
Proof.
intros R1 R2 Hcomm x y H.
rewrite union_star_equiv in H.
induction H; eauto.
apply comm_star_included in IHclos_refl_trans1; auto.
assert ((R2⋆; (R1⋆; R2⋆)) x z).
destruct IHclos_refl_trans1 as [? [? ?]]. 
destruct IHclos_refl_trans2 as [? [? ?]]. 
eauto 7.
destruct H1 as [? [? ?]].

destruct H1 as [? [? ?]].
*)




Lemma concat_wf_equiv (R1 R2: relation A):
  well_founded (R1 ; R2) → well_founded (R2 ; R1).
Proof.
intros R1 R2 H.
intro x.
constructor; intros y [z [Hyz _]].
assert (Acc (R1; R2) z) as H0 by auto; clear H.
generalize dependent y.
induction H0; intros.
constructor; intros z [t [Hzt Hty]].
eapply H0; eauto.
Qed.

Lemma concat_assoc (R1 R2 R3: relation A):
  (R1; R2); R3 ≡ R1; (R2; R3).
Proof.
intros R1 R2 R3 x y; split; intro H.
destruct H as [z [Hxz Hzy]].
destruct Hxz as [t [Hxt Htz]]; eauto 6.
destruct H as [z [Hxz [t [Hzt Hty]]]]; eauto 6.
Qed.

Lemma star_equiv (R: relation A):
  R⋆ ≡ R⋆ ; R⋆.
Proof.
intros; split; intro H; eauto.
destruct H as [z [Hxz Hzy]]; eauto.
Qed.

Lemma concat_star_equiv (R1 R2: relation A):
  (R1; R2⋆) ≡ (R1; R2⋆) ; R2⋆.
Proof.
intros R1 R2 x y; split; intro H; eauto.
rewrite concat_assoc in H.
destruct H as [z [Hxz Hzy]].
rewrite <- star_equiv in Hzy; eauto.
Qed.

Lemma union_wf (R1 R2: relation A):
  well_founded (R1⋆ ; R2) →
  well_founded (R2⋆ ; R1) →
  well_founded (R1 ∪ R2).
Proof.
intros R1 R2 HR1R2 HR2R1.
assert (well_founded (R1 ; (R2)⋆)) as wfR1R2 by auto using concat_wf_equiv.
assert (well_founded (R2 ; (R1)⋆)) as wfR2R1 by auto using concat_wf_equiv.
intro x.
assert (Acc (R1 ; (R2)⋆) x) as Hx1 by auto; induction Hx1.
assert (Acc (R2 ; (R1)⋆) x) as Hx2 by auto; induction Hx2.
constructor; intros y [Hy | Hy]; eauto.
eapply H2; eauto.
intros z Hz.
eapply H0; eauto. rewrite concat_star_equiv; eauto.
Qed.

(*
Lemma rosen (R1 R2: relation A):
  (R1 ; R2) ⊆ (R2 ; R1) →
  confluent R1 →
  confluent R2 →
  confluent (R1 ∪ R2).
Proof.
intros R1 R2 Hcomm HR1 HR2.
intros y z [x [Hy Hz]]; unfold transp in Hy.
*)


(*
Lemma akamai (R1 R2: relation A):
  (R1 ; R2) ⊆ (R2 ; R1) →
  well_founded R1 →
  well_founded R2 →
  well_founded (R1 ∪ R2).
Proof.
intros R1 R2 Hcomm HR1 HR2.
intro x. generalize dependent R2.
assert (Acc R1 x) as Hx1 by auto; induction Hx1.
intros R2 Hcomm HR2.
assert (Acc R2 x) as Hx2 by auto; induction Hx2.
constructor; intros y [Hy | Hy].
apply H0; auto.
apply H2; auto. intros z Hz R3 Hcomm' HR3. apply H0; auto.
*)