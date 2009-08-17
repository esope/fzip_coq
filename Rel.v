(******************************************************************************)
(*                                                                            *)
(* Copyright (C) Benoît Montagu <benoit.montagu@inria.fr>                     *)
(*                                                                            *)
(* This file is distributed under terms of the GNU Lesser General Public      *)
(* License version 3 or above. http://www.gnu.org/copyleft/lesser.html        *)
(*                                                                            *)
(******************************************************************************)

(** This file provides some proofs of properties on relations (notably
    combination for confluence and well-foundedness) formalized in the
    Coq proof assistant (version 8.2-1).                                       *)
(** Version: August 2009                                                       *)

Require Import Utf8.
Require Import Relations.

Section Rel.
Parameter A : Type.

Implicit Arguments clos_refl_trans [A].
Implicit Arguments clos_trans [A].
Implicit Arguments transp [A].
Hint Resolve rt_refl rt_trans rt_step.
Hint Resolve t_trans t_step.
Hint Unfold transp.

(** * Definitions and notations *)
Inductive union A (R1 R2: relation A) (x y: A): Prop :=
| Left : R1 x y → union A R1 R2 x y
| Right : R2 x y → union A R1 R2 x y.
Hint Constructors union.
Implicit Arguments union [A].
Definition concat A (R1 R2: relation A) x y :=
  ∃ z, R1 x z ∧ R2 z y.
Implicit Arguments concat [A].
Hint Unfold concat.
Definition sub_rel A (R S: relation A) := forall x y, R x y → S x y.
Definition eq_rel A (R S: relation A) := forall x y, R x y ↔ S x y.
Implicit Arguments sub_rel [A].
Implicit Arguments eq_rel [A].
Hint Unfold sub_rel eq_rel.
Notation "R ; S" := (concat R S) (at level 30).
Notation "R ∪ S" := (union R S) (at level 30).
Notation "R '⋆'" := (clos_refl_trans R) (at level 29).
Notation "R '⁺'" := (clos_trans R) (at level 29).
Notation "R '⁻¹'" := (transp R) (at level 29).
Notation "R '?'" := (@eq A ∪ R) (at level 29).
Notation "R ⊆ S" := (sub_rel R S) (at level 31).
Notation "R ≡ S" := (eq_rel R S) (*(forall x y, R x y ↔ S x y)*) (at level 31).

Definition diamond (R: relation A) := (R; R⁻¹) ⊆ (R⁻¹; R).
Definition confluent (R: relation A) := diamond (R ⋆).
Definition weakly_confluent (R: relation A) := (R; R⁻¹) ⊆ (R ⋆ ⁻¹; R ⋆).
Definition commute (R1 R2: relation A) := (R2 ; R1⁻¹) ⊆ (R1⁻¹ ; R2).
Hint Unfold diamond confluent weakly_confluent commute.

(** * Infrastructure  to allow rewriting on relations *)
Lemma eq_rel_refl A (R: relation A): R ≡ R.
Proof.
intros B R x y; tauto.
Qed.

Lemma eq_rel_sym A (R1 R2: relation A): R1 ≡ R2 → R2 ≡ R1.
Proof.
intros B R1 R2 H x y; rewrite (H x y); tauto.
Qed.

Lemma eq_rel_trans A (R1 R2 R3: relation A): R1 ≡ R2 → R2 ≡ R3 → R1 ≡ R3.
Proof.
intros B R1 R2 R3 H1 H2 x y; rewrite (H1 x y); rewrite (H2 x y); tauto.
Qed.

Require Export Setoid.
Add Parametric Relation A : (relation A) (@eq_rel A)
  reflexivity  proved by (eq_rel_refl A)
  symmetry     proved by (eq_rel_sym A)
  transitivity proved by (eq_rel_trans A)
as eq_rel_setoid.

(** Morphisms for relation application *)
Add Parametric Morphism A : (@id (relation A)) with
  signature (@eq_rel A) ==> pointwise_relation A (pointwise_relation A iff) as rel_apply_mor.
Proof.
intros R1 R2 H12 x y.
unfold id in *.
rewrite (H12 _ _). tauto.
Qed.

Add Parametric Morphism A : (fun (R: relation A) (x y: A) => R x y) with
  signature (@eq_rel A) ==> (@eq A) ==> (@eq A) ==> iff as rel_apply2_mor.
Proof.
intros R1 R2 H12 x y.
setoid_rewrite H12. tauto.
Qed.

(** Morphisms for sub_rel *)
Add Parametric Morphism A : (@sub_rel A) with
  signature (@eq_rel A) ==> (@eq_rel A) ==> iff as sub_rel_mor.
Proof.
intros R1 R2 H12 R3 R4 H34.
unfold sub_rel.
split; intros H x y H'.
setoid_rewrite <- H34; apply H; setoid_rewrite H12; auto.
setoid_rewrite H34; apply H; setoid_rewrite <- H12; auto.
Qed.

(** Morphisms for union *)
Add Parametric Morphism A : (@union A) with
  signature (@eq_rel A) ==> (@eq_rel A) ==> (@eq_rel A) as union_mor.
Proof.
intros R1 R2 H12 R3 R4 H34; split; intro H; destruct H.
left; rewrite <- (H12 x y); auto.
right; rewrite <- (H34 x y); auto.
left; rewrite (H12 x y); auto.
right; rewrite (H34 x y); auto.
Qed.

Add Parametric Morphism A : (@union A) with
  signature (@eq_rel A) ==> (@eq_rel A) ==> (@eq A) ==> (@eq A) ==> iff as union_ext_mor.
Proof.
intros R1 R2 H12 R3 R4 H34 x y.
assert (R1 ∪ R3 ≡ R2 ∪ R4). rewrite H12. rewrite H34. reflexivity.
remember (R1 ∪ R3) as R.
setoid_rewrite H.
reflexivity.
Qed.

(** Morphisms for concat *)
Add Parametric Morphism A : (@concat A) with
  signature (@eq_rel A) ==> (@eq_rel A) ==> (@eq_rel A) as concat_mor.
Proof.
intros R1 R2 H12 R3 R4 H34; split; intro H; destruct H as [z [H1 H2]]; exists z; split.
rewrite <- (H12 x z); auto.
rewrite <- (H34 z y); auto.
rewrite (H12 x z); auto.
rewrite (H34 z y); auto.
Qed.

Add Parametric Morphism A : (@concat A) with
  signature (@eq_rel A) ==> (@eq_rel A) ==> (@eq A) ==> (@eq A) ==> iff as concat_ext_mor.
Proof.
intros R1 R2 H12 R3 R4 H34.
assert ((R1;R3) ≡ (R2;R4)). rewrite H12; rewrite H34; reflexivity.
remember (R1;R3) as R.
setoid_rewrite H.
reflexivity.
Qed.

(** Morphisms for clos_refl_trans *)
Add Parametric Morphism A : (@clos_refl_trans A) with
  signature (@eq_rel A) ==> (@eq_rel A) as clos_refl_trans_mor.
Proof.
intros R1 R2 H12; split; intro H; induction H; eauto.
setoid_rewrite H12 in H; auto.
setoid_rewrite <- H12 in H; auto.
Qed.

Add Parametric Morphism A : (@clos_refl_trans A) with
  signature (@eq_rel A) ==> (@eq A) ==> (@eq A) ==> iff as clos_refl_trans_ext_mor.
Proof.
intros R1 R2 H12 x y; split; intro H; induction H; eauto.
setoid_rewrite H12 in H; auto.
setoid_rewrite <- H12 in H; auto.
Qed.

(** Morphisms for clos_trans *)
Add Parametric Morphism A : (@clos_trans A) with
  signature (@eq_rel A) ==> (@eq_rel A) as clos_trans_mor.
Proof.
intros R1 R2 H12; split; intro H; induction H; eauto.
setoid_rewrite H12 in H; auto.
setoid_rewrite <- H12 in H; auto.
Qed.

Add Parametric Morphism A : (@clos_trans A) with
  signature (@eq_rel A) ==> (@eq A) ==> (@eq A) ==> iff as clos_trans_ext_mor.
Proof.
intros R1 R2 H12 x y; split; intro H; induction H; eauto.
setoid_rewrite H12 in H; auto.
setoid_rewrite <- H12 in H; auto.
Qed.

(** Morphisms for transp *)
Add Parametric Morphism A : (@transp A) with
  signature (@eq_rel A) ==> (@eq_rel A) as transp_mor.
Proof.
intros R1 R2 H12; unfold transp; intros x y; setoid_rewrite H12; tauto.
Qed.

Add Parametric Morphism A : (@transp A) with
  signature (@eq_rel A) ==> (@eq A) ==> (@eq A) ==> iff as transp_ext_mor.
Proof.
intros R1 R2 H12 x y; unfold transp; setoid_rewrite H12; tauto.
Qed.

(** Morphisms for Acc *)
Add Parametric Morphism A : (@Acc A) with
  signature (@eq_rel A) ==> (@eq A) ==> iff as acc_mor.
Proof.
intros R1 R2 H12 x; split; intro H.
assert (Acc R1 x) as H0 by auto; induction H0.
constructor; intros. setoid_rewrite <- H12 in H2.
auto.
assert (Acc R2 x) as H0 by auto; induction H0.
constructor; intros. setoid_rewrite H12 in H2.
auto.
Qed.

(** Morphisms for well_founded *)
Add Parametric Morphism A : (@well_founded A) with
  signature (@eq_rel A) ==> iff as wf_mor.
Proof.
intros R1 R2 H12; split; intros H x.
rewrite <- H12; auto.
rewrite H12; auto.
Qed.

(** Morphisms for commute *)
Add Parametric Morphism : commute with
  signature (@eq_rel A) ==> (@eq_rel A) ==> iff as commute_mor.
Proof.
intros R1 R2 H12 R3 R4 H34.
unfold commute.
rewrite H12; rewrite H34; tauto.
Qed.

(** * Some lemmas about operations on relations *)
Lemma star_idempotent (R: relation A):
  R ⋆⋆ ≡ R ⋆.
Proof.
intros R x y; split; intro H; induction H; eauto.
Qed.
Hint Rewrite star_idempotent : rel.
Hint Resolve star_idempotent : rel.

Lemma plus_idempotent (R: relation A):
  R ⁺⁺ ≡ R ⁺.
Proof.
intros R x y; split; intro H; induction H; eauto.
Qed.
Hint Rewrite plus_idempotent : rel.
Hint Resolve plus_idempotent : rel.

Lemma plus_star_equiv (R: relation A):
  R ⋆⁺ ≡ R⁺ ⋆.
Proof.
intros R x y; split; intro H; induction H; eauto; induction H; eauto.
Qed.
Hint Rewrite plus_star_equiv : rel.
Hint Resolve plus_star_equiv : rel.

Lemma star_plus_star_equiv (R: relation A):
  R ⋆⁺ ≡ R ⋆.
Proof.
intros R x y; split; intro H; induction H; eauto.
Qed.
Hint Rewrite star_plus_star_equiv : rel.
Hint Resolve star_plus_star_equiv : rel.

Lemma plus_star_star_equiv (R: relation A):
  R⁺ ⋆ ≡ R ⋆.
Proof.
intro R.
rewrite <- (star_plus_star_equiv R).
symmetry; auto with rel.
Qed.
Hint Rewrite plus_star_star_equiv : rel.
Hint Resolve plus_star_star_equiv : rel.

Lemma plus_star_concat_equiv (R: relation A):
  R⁺ ≡ R ⋆; R.
Proof.
intros R x y; split; intro H.
rewrite tn1_trans_equiv in H; induction H; try rewrite <- tn1_trans_equiv in *|-; eauto.
destruct IHclos_trans_n1 as [? [? ?]].
eauto 6.
destruct H as [? [? ?]]. generalize dependent y.
rewrite rtn1_trans_equiv in H; induction H; try rewrite <- rtn1_trans_equiv in *|-; eauto.
Qed.
Hint Resolve plus_star_concat_equiv : rel.

Lemma plus_star_included (R: relation A):
  R⁺ ⊆ R ⋆.
Proof.
intros R x y H.
induction H; eauto.
Qed.
Hint Resolve plus_star_included : rel.

Lemma concat_assoc (R1 R2 R3: relation A):
  (R1; R2); R3 ≡ R1; (R2; R3).
Proof.
intros R1 R2 R3 x y; split; intro H.
destruct H as [z [Hxz Hzy]].
destruct Hxz as [t [Hxt Htz]]; eauto 6.
destruct H as [z [Hxz [t [Hzt Hty]]]]; eauto 6.
Qed.
Hint Resolve concat_assoc : rel.

Lemma star_equiv (R: relation A):
  R ⋆ ≡ R ⋆ ; R ⋆.
Proof.
intros; split; intro H; eauto.
destruct H as [z [Hxz Hzy]]; eauto.
Qed.
Hint Rewrite <- star_equiv : rel.
Hint Resolve star_equiv : rel.

Lemma transp_involutive (R: relation A):
  R⁻¹⁻¹ ≡ R.
Proof.
intros; split; auto.
Qed.
Hint Rewrite transp_involutive : rel.
Hint Resolve transp_involutive : rel.

Lemma transp_concat_commute (R1 R2: relation A):
  (R1; R2)⁻¹ ≡ (R2⁻¹; R1⁻¹).
Proof.
intros R1 R2 x y; split; intro H;
destruct H as [z [Hxz Hzy]]; eauto.
Qed.
Hint Rewrite transp_concat_commute : rel.
Hint Resolve transp_concat_commute : rel.

Lemma transp_star_commute (R: relation A):
  R⁻¹ ⋆ ≡ R ⋆ ⁻¹.
Proof.
intro R. split; intro H.
induction H; unfold transp in *; eauto.
unfold transp in H. induction H; eauto.
Qed.
Hint Rewrite transp_star_commute : rel.
Hint Resolve transp_star_commute : rel.

Lemma transp_plus_commute (R: relation A):
  R⁻¹⁺ ≡ R⁺ ⁻¹.
Proof.
intro R. split; intro H.
induction H; unfold transp in *; eauto.
unfold transp in H. induction H; eauto.
Qed.
Hint Rewrite transp_plus_commute : rel.
Hint Resolve transp_plus_commute : rel.

Lemma union_star_equiv (R1 R2: relation A):
  (R1 ∪ R2)⋆ ≡ (R1 ⋆; R2 ⋆)⋆.
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
Hint Resolve union_star_equiv : rel.

Lemma concat_star_included1 (R1 R2: relation A):
  R1 ⋆ ⊆ (R1; R2 ⋆)⋆.
Proof.
intros R1 R2 x y H.
induction H; eauto.
Qed.
Hint Resolve concat_star_included1 : rel.

Lemma concat_star_included2 (R1 R2: relation A):
  R2 ⋆ ⊆ (R1 ⋆; R2)⋆.
Proof.
intros R1 R2 x y H.
induction H; eauto.
Qed.
Hint Resolve concat_star_included2 : rel.

Lemma union_star_included1 (R1 R2: relation A):
  R1 ⋆ ⊆ (R1 ∪ R2)⋆.
Proof.
intros R1 R2 x y H. induction H; eauto.
Qed.
Hint Resolve union_star_included1 : rel.

Lemma union_star_included2 (R1 R2: relation A):
  R2 ⋆ ⊆ (R1 ∪ R2)⋆.
Proof.
intros R1 R2 x y H. induction H; eauto.
Qed.
Hint Resolve union_star_included2 : rel.

Lemma union_star_equiv2 (R1 R2: relation A):
  (R1 ∪ R2)⋆ ≡ (R1 ⋆ ∪ R2 ⋆)⋆.
Proof.
intros R1 R2 x y; split; intro H; induction H; eauto.
destruct H; eauto.
destruct H. apply union_star_included1; auto. apply union_star_included2; auto.
Qed.
Hint Resolve union_star_equiv : rel.

Lemma union_plus_included1 (R1 R2: relation A):
  R1⁺ ⊆ (R1 ∪ R2)⁺.
Proof.
intros R1 R2 x y H. induction H; eauto.
Qed.
Hint Resolve union_plus_included1 : rel.

Lemma union_plus_included2 (R1 R2: relation A):
  R2⁺ ⊆ (R1 ∪ R2)⁺.
Proof.
intros R1 R2 x y H. induction H; eauto.
Qed.
Hint Resolve union_plus_included2 : rel.

Lemma union_plus_equiv2 (R1 R2: relation A):
  (R1 ∪ R2)⁺ ≡ (R1⁺ ∪ R2⁺)⁺.
Proof.
intros R1 R2 x y; split; intro H; induction H; eauto.
destruct H; eauto.
destruct H. apply union_plus_included1; auto. apply union_plus_included2; auto.
Qed.
Hint Resolve union_plus_equiv2 : rel.

Lemma concat_star_equiv (R1 R2: relation A):
  (R1; R2 ⋆) ≡ (R1; R2 ⋆) ; R2 ⋆.
Proof.
intros R1 R2.
rewrite concat_assoc.
autorewrite with rel.
reflexivity.
Qed.
Hint Rewrite <- concat_star_equiv : rel.
Hint Resolve concat_star_equiv : rel.

Inductive rt_length_clos (R: relation A) : nat → A → A → Prop :=
| rt_length_refl : forall x, rt_length_clos R 0 x x
| rt_length_trans : forall x y z n,
  rt_length_clos R n x y → R y z → rt_length_clos R (1+n) x z.
Hint Constructors rt_length_clos.

Lemma rt_length_clos_equiv (R: relation A) :
  R ⋆ ≡ (fun x y => exists n, rt_length_clos R n x y).
Proof.
intros R x y; rewrite rtn1_trans_equiv; split; intro H.
induction H; eauto.
  destruct IHclos_refl_trans_n1; eauto.
destruct H as [n H]; induction H; rewrite <- rtn1_trans_equiv in *; eauto.
Qed.

Require Import Omega.
Lemma rt_length_clos_transitivity (R: relation A) : forall n m x y z,
  rt_length_clos R n x y →
  rt_length_clos R m y z →
  rt_length_clos R (n+m) x z.
Proof.
intro R.
assert (forall n x y z, rt_length_clos R n x y → R y z → rt_length_clos R (1+n) x z).
  intros n x y z Hn; induction Hn; intros; eauto.
intros n m x y z Hn Hm.
generalize dependent x. generalize dependent n.
induction Hm; intros.
replace (n+0) with n by auto; auto.
replace (n0+(1+n)) with (1+(n0+n)) by omega; eauto.
Qed.

Lemma rt_length_clos_0_self (R: relation A) :
  forall x y, rt_length_clos R 0 x y → x = y.
Proof.
intros R x y H.
remember 0 as n.
induction H; auto.
assert False by omega; contradiction.
Qed.

(** * Lemmas about [commute] *)
Lemma commute_sym (R1 R2: relation A):
  commute R1 R2 → commute R2 R1.
Proof.
intros R1 R2 Hcomm.
intros x y H.
assert (((R1; R2⁻¹)⁻¹) y x) as H' by auto.
rewrite (transp_concat_commute _ _ _ _) in H'.
autorewrite with rel in H'.
apply Hcomm in H'. destruct H' as [? [? ?]].
eauto.
Qed.

Lemma commute_star1 (R1 R2:relation A):
  commute R1 R2 → commute (R1 ⋆) R2.
Proof.
intros R1 R2 Hcomm x y H.
destruct H as [z [Hxz Hyz]].
unfold transp in Hyz.
rewrite rt1n_trans_equiv in Hyz.
generalize dependent x; induction Hyz; intros; eauto.
apply IHHyz in Hxz. destruct Hxz as [? [? ?]].
assert ((R2; R1⁻¹) x1 x) by eauto. apply Hcomm in H2.
destruct H2 as [? [? ?]]; eauto 7.
Qed.

Lemma commute_star2 (R1 R2:relation A):
  commute R1 R2 → commute R1 (R2 ⋆).
Proof.
intros R1 R2 H.
apply commute_sym. apply commute_sym in H.
auto using commute_star1.
Qed.

Lemma commute_star (R1 R2:relation A):
  commute R1 R2 → commute (R1 ⋆) (R2 ⋆).
Proof.
intros R1 R2 H.
auto using commute_star1, commute_star2.
Qed.

Lemma commute_plus_star (R1 R2: relation A):
  commute (R1⁺) R2 → commute (R1 ⋆) R2.
Proof.
intros R1 R2 H.
apply commute_star1 in H.
intros y z [x [Hyx Hzx]].
unfold transp in Hzx.
rewrite <- (plus_star_star_equiv _ _ _) in Hzx.
assert (((R1 ⁺ ⋆) ⁻¹; R2) y z) as [? [H0 ?]] by eauto.
unfold transp in H0.
rewrite (plus_star_star_equiv _ _ _) in H0.
eauto.
Qed.

Lemma commute_union (R1 R2 R3: relation A):
  commute R1 R2 →
  commute R1 R3 →
  commute R1 (R2 ∪ R3).
Proof.
intros R1 R2 R3 H12 H13 x y H.
destruct H as [z [Hxz Hyz]].
unfold transp in Hyz.
destruct Hxz.
assert ((R2; R1⁻¹) x y) by eauto.
apply H12 in H0.
destruct H0 as [? [? ?]]; eauto.
assert ((R3; R1⁻¹) x y) by eauto.
apply H13 in H0.
destruct H0 as [? [? ?]]; eauto.
Qed.

Lemma commutation_condition (R1 R2: relation A):
  (R1; R2⁻¹) ⊆ (R2 ⋆ ⁻¹; R1?) →
  commute (R1 ⋆) (R2 ⋆).
Proof.
intros R1 R2 Hcomm1.
assert (R1; R2 ⋆ ⁻¹ ⊆ (R2 ⋆) ⁻¹; R1 ⋆) as Hcomm2.
  intros x y [z [Hxz Hyz]]. unfold transp in Hyz.
  generalize dependent x.
  rewrite rtn1_trans_equiv in Hyz; induction Hyz; try rewrite <- rtn1_trans_equiv in *|-; intros.
   eauto 7.
   assert (((R2 ⋆) ⁻¹; R1 ?) x y0) as [t [Htx Hty0]] by eauto.
   destruct Hty0; subst.
     eauto 6.
     apply IHHyz in H0; destruct H0 as [? [? ?]]; eauto 6.
intros x y [z [Hxz Hyz]].
unfold transp in Hyz.
generalize dependent x; rewrite rtn1_trans_equiv in Hyz; induction Hyz; try rewrite <- rtn1_trans_equiv in *|-; intros; eauto.
assert (((R2 ⋆) ⁻¹; R1 ⋆) y0 x) as [t [Hty0 Htx]] by eauto.
apply IHHyz in Hty0. destruct Hty0 as [? [? ?]].
eauto 6.
Qed.

(** * Lemmas about [confluent] *)
Lemma confluent_commute_star_refl_equiv (R: relation A):
  confluent R ↔ commute (R ⋆) (R ⋆).
Proof.
intuition auto.
Qed.

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

Lemma diamond_union (R1 R2: relation A):
  commute R1 R2 →
  diamond R1 →
  diamond R2 →
  diamond (R1 ∪ R2).
Proof.
intros R1 R2 Hcomm HR1 HR2 x y [z [Hxz Hyz]].
destruct Hxz; destruct Hyz.
  assert ((R1⁻¹; R1) x y) as [? [? ?]] by eauto; eauto 7.
  assert (commute R2 R1) as Hcomm' by auto using commute_sym.
    assert ((R2⁻¹; R1) x y) as [? [? ?]] by eauto; eauto 7.
  assert ((R1⁻¹; R2) x y) as [? [? ?]] by eauto; eauto 7.
  assert ((R2⁻¹; R2) x y) as [? [? ?]] by eauto; eauto 7.
Qed.

Lemma diamond_confluent (R: relation A) :
  diamond R → confluent R.
Proof.
intros R Hdiamond.
assert (forall p n m x y z, n ≤ p → m ≤ p →
  rt_length_clos R m x z →
  rt_length_clos R n y z →
  exists t, rt_length_clos R n t x ∧ rt_length_clos R m t y).
intro p; induction p; intros n m x y z Hn Hm Hx Hy.
(* case p = 0 *)
assert (n = 0) by omega; assert (m = 0) by omega; subst.
assert (x = z) by eauto using rt_length_clos_0_self;
assert (y = z) by eauto using rt_length_clos_0_self;
subst; eauto.
(* case p > 0 *)
destruct Hx; eauto.
destruct Hy; eauto.
assert ((R⁻¹; R) y y0) as [t [Htx Hty]] by eauto 7.
assert (exists u, rt_length_clos R 1 u x0 ∧ rt_length_clos R n u t) as [u [Hux0 Hut]].
  destruct n.
  (* n = 0 *)
  assert (x0 = y) by eauto using rt_length_clos_0_self; subst.
  replace 1 with (1+0) by reflexivity; eauto.
  (* n > 0 *)
  apply IHp with (z := y); try omega; eauto.
    replace 1 with (1+0) by reflexivity; eauto.
assert (exists v, rt_length_clos R 1 v x ∧ rt_length_clos R n0 v t) as [v [Hvx Hvt]].
  destruct n0.
  (* n0 = 0 *)
  assert (x = y0) by eauto using rt_length_clos_0_self; subst.
  replace 1 with (1+0) by reflexivity; eauto.
  (* n0 > 0 *)
  apply IHp with (z := y0); try omega; eauto.
    replace 1 with (1+0) by reflexivity; eauto.
assert (exists w, rt_length_clos R n0 w u ∧ rt_length_clos R n w v) as [w [Hwu Hwv]].
  apply IHp with (z := t); try omega; eauto.
exists w; split.
replace (1+n) with (n+1) by omega; eauto using rt_length_clos_transitivity.
replace (1+n0) with (n0+1) by omega; eauto using rt_length_clos_transitivity.
(*
            z
           / \
          1   1
         /     \
        y       y0
       / \     / \
      n   1   1   n0
     /     \ /     \
    x0      t       x
     \     / \     /
      1   n   n0  1
       \ /     \ /
        u       v
         \     /
          n0  n
           \ /
            w
*)
intros x y [z [Hxz Hyz]].
unfold transp in Hyz.
rewrite (rt_length_clos_equiv R x z)  in Hxz.
rewrite (rt_length_clos_equiv R y z)  in Hyz.
destruct Hxz as [n Hxz].
destruct Hyz as [m Hyz].
assert (exists t, rt_length_clos R m t x ∧ rt_length_clos R n t y) as [t [Htx Hty]].
  eapply (H (n+m)); try omega; eauto.
exists t; split; unfold transp; rewrite (rt_length_clos_equiv _ _ _) ; eauto.
Qed.

(** Hindley-Rosen lemma, from 'The λ-calculus, its Syntax and
Semantics', H.P. Barendregt, Ch. 3 § 3 *)
Lemma hindley_rosen1 (R1 R2: relation A):
  commute R1 R2 →
  diamond R1 →
  diamond R2 →
  confluent (R1 ∪ R2).
Proof.
intros R1 R2 Hcomm HR1 HR2.
eauto using diamond_confluent, diamond_union.
Qed.

Lemma hindley_rosen2 (R1 R2: relation A):
  commute (R1 ⋆) (R2 ⋆) →
  confluent R1 →
  confluent R2 →
  confluent (R1 ∪ R2).
Proof.
intros R1 R2 Hcomm HR1 HR2.
apply hindley_rosen1 in Hcomm; auto.
intros x y [z [Hxz Hyz]].
assert (((R1 ⋆∪R2 ⋆)⋆; (R1 ⋆∪R2 ⋆)⋆ ⁻¹) x y).
  unfold transp in Hyz.
  rewrite (union_star_equiv2 _ _ _) in Hxz.
  rewrite (union_star_equiv2 _ _ _) in Hyz.
  eauto.
clear Hxz Hyz z.
apply Hcomm in H.
destruct H as [z [Hzx Hzy]].
unfold transp in Hzx.
rewrite <- (union_star_equiv2 _ _ _) in Hzx.
rewrite <- (union_star_equiv2 _ _ _) in Hzy.
eauto.
Qed.

Lemma newman (R: relation A):
  well_founded R →
  weakly_confluent R →
  confluent R.
Proof.
intros R Hwf Hwc.
intros y1 y2 [x [Hxy1 Hxy2]]. unfold transp in Hxy2.
rewrite rtn1_trans_equiv in * |-.
assert (Acc R x) by auto.
generalize dependent y1; generalize dependent y2.
induction H; intros.
generalize dependent y2.
induction Hxy1; intros; eauto.
rewrite <- rtn1_trans_equiv in * |-; eauto.
generalize dependent y1; generalize dependent y.
induction Hxy2; intros; eauto.
rewrite <- rtn1_trans_equiv in * |-; eauto 7.
assert (((R ⋆) ⁻¹; R ⋆) y y0) as [x [Hxy Hxy0]] by eauto.
unfold transp in Hxy.
assert (((R ⋆) ⁻¹; R ⋆) x y1) as [t [Htx Hty1]].
  apply (H0 y0); auto.
  rewrite <- rtn1_trans_equiv; auto.
assert (((R ⋆) ⁻¹; R ⋆) y2 x) as [u [Huy2 Hux]].
  apply (H0 y); auto.
  rewrite <- rtn1_trans_equiv; auto.
unfold transp in Htx. unfold transp in Huy2.
assert (((R ⋆) ⁻¹; R ⋆) t u) as [v [Hvt Hvu]].
  eapply H0; eauto.
  rewrite <- rtn1_trans_equiv; eauto.
  rewrite <- rtn1_trans_equiv; eauto.
unfold transp in Hvt; eauto 7.
Qed.

(** * Definitions about normal forms *)
Definition nf (R: relation A) (x: A) :=
  forall y, ~(R y x).
Hint Unfold nf.

(** x is a normal form of y *)
Definition is_nf_of (R: relation A) (x y: A) :=
  nf R x ∧ (R ⋆) x y.
Hint Unfold is_nf_of.

Definition nf_unique (R: relation A) :=
  forall x y z, is_nf_of R y x → is_nf_of R z x →
    y = z.
Hint Unfold nf_unique.

(** R1 commutes with R2' normal forms *)
Definition nf_commute (R1 R2: relation A) :=
  forall x y x' y',
    is_nf_of R2 x' x → is_nf_of R2 y' y →
    R1 x y →
    (R1⁺) x' y'.
Hint Unfold nf_commute.

(** R1 preserves R2's normal forms *)
Definition preserves_nf (R1 R2: relation A) :=
  forall x y, nf R2 y → R1 x y → nf R2 x.
Hint Unfold preserves_nf.

(** * Lemmas about [nf], [is_nf_of], [nf_unique], [nf_commute] and [preserve_nf] *)
Lemma nf_star_eq (R: relation A):
  forall x y, nf R x → (R ⋆) y x → y = x.
Proof.
intros R x y Hnf Hyx.
rewrite rtn1_trans_equiv in Hyx; induction Hyx; try rewrite <- rtn1_trans_equiv in *|-; eauto.
edestruct Hnf; eauto.
Qed.

Lemma confluent_nf_unique (R: relation A):
  confluent R → nf_unique R.
Proof.
intros R H x y z Hy Hz.
destruct Hy as [Hy Hyx]; destruct Hz as [Hz Hzx].
assert ((R ⋆ ⁻¹; R ⋆) y z) as [t [Hyt Htz]] by eauto.
unfold transp in Hyt.
rewrite rtn1_trans_equiv in *|-.
assert (t = y).
 destruct Hyt; rewrite <- rtn1_trans_equiv in *|-; auto. edestruct Hy; eauto.
assert (t = z).
 destruct Htz; rewrite <- rtn1_trans_equiv in *|-; auto. edestruct Hz; eauto.
congruence.
Qed.

(** This lemma requires classical logic. *)
Lemma well_founded_nf_exists (R: relation A) (x: A) :
  well_founded R → exists y, is_nf_of R y x.
Proof.
intros R x Hwf.
assert (Acc R x) as Hacc by auto; induction Hacc.
Require Import Classical.
destruct (classic (exists y, R y x)) as [[y Hy] | ?].
assert (exists z, is_nf_of R z y) as [z [Hyz Hz]] by auto; eauto 7.
eauto 8.
Qed.

Lemma preserves_nf_plus (R1 R2: relation A):
  preserves_nf R1 R2 → preserves_nf (R1⁺) R2.
Proof.
intros R1 R2 H x y Hx Hxy.
rewrite tn1_trans_equiv in Hxy; induction Hxy; try rewrite <- tn1_trans_equiv in *|-; eauto.
Qed.

Lemma preserves_nf_star (R1 R2: relation A):
  preserves_nf R1 R2 → preserves_nf (R1 ⋆) R2.
Proof.
intros R1 R2 H x y Hx Hxy.
rewrite rtn1_trans_equiv in Hxy; induction Hxy; try rewrite <- rtn1_trans_equiv in *|-; eauto.
Qed.

Lemma nf_commute_plus (R1 R2: relation A):
  confluent R2 → well_founded R2 →
  nf_commute R1 R2 →
  forall x y z t, is_nf_of R2 z x → is_nf_of R2 t y → ((R1 ∪ R2)⁺) y x →
    (R1 ⋆) t z.
Proof.
intros R1 R2 Hc2 Hwf2 Hnf y x y' x' Hy'y Hx'x Hyx.
generalize dependent y'. generalize dependent x'.
rewrite t1n_trans_equiv in Hyx; induction Hyx; try rewrite <- t1n_trans_equiv in *|-; intros.
destruct H.
  apply plus_star_included; eauto.
  assert (x' = y'); subst; auto.
    destruct Hx'x; destruct Hy'y.
    assert ((R2 ⋆ ⁻¹; R2 ⋆) y' x') as [t [? ?]] by eauto 8.
    unfold transp in *|-.
    assert (t = y') by eauto using nf_star_eq.
    assert (t = x') by eauto using nf_star_eq.
    congruence.
destruct H.
  destruct (well_founded_nf_exists R2 y Hwf2) as [t Hty].
    assert ((R1⁺) x' t) by eauto.
    apply IHHyx with (y' := y') in Hty; auto.
    apply plus_star_included in H0; eauto.
  destruct Hx'x; eauto 6.
Qed.

Lemma nf_commute_star (R1 R2: relation A):
  confluent R2 → well_founded R2 →
  nf_commute R1 R2 →
  forall x y z t, is_nf_of R2 z x → is_nf_of R2 t y → ((R1 ∪ R2)⋆) y x →
    (R1 ⋆) t z.
Proof.
intros R1 R2 Hc2 Hwf2 Hnf y x y' x' Hy'y Hx'x Hyx.
rewrite rtn1_trans_equiv in Hyx; destruct Hyx; try rewrite <- rtn1_trans_equiv in *|-.
assert (y' = x'). eapply confluent_nf_unique; eauto. subst; auto.
eapply nf_commute_plus; eauto. rewrite (plus_star_concat_equiv _ _ _); eauto.
Qed.

(** * Lemmas about [well_founded] *)
Lemma wf_plus_equiv (R: relation A):
  well_founded (R⁺) ↔ well_founded R.
Proof.
intro R; split; intros H x.
(* → *)
assert (Acc (R⁺) x) by auto; induction H0.
constructor; intros; eauto.
(* ← *)
constructor.
assert (Acc R x) as H0 by auto; induction H0.
intros y H2; rewrite tn1_trans_equiv in H2; induction H2; constructor; intros.
  eauto.
  rewrite <- tn1_trans_equiv in H3; eauto.
Qed.

Lemma union_wf (R1 R2: relation A):
  well_founded (R1 ⋆ ; R2) →
  well_founded (R2 ⋆ ; R1) →
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
eapply H0; eauto. rewrite (concat_star_equiv _ _ _); eauto.
Qed.

(** Akama's lemmas, from 'On Mints' Reduction for ccc-Calculus', Yohji Akama, TLCA '93 *)
Lemma akama_well_founded (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  nf_commute R1 R2 →
  well_founded (R1 ∪ R2).
Proof.
intros R1 R2 Hc1 Hc2 Hwf1 Hwf2 Hnf.
rewrite <- wf_plus_equiv in Hwf1.
intro x.
destruct (well_founded_nf_exists R2 x Hwf2) as [x' Hx'].
generalize dependent x.
assert (Acc (R1⁺) x') as Hacc by auto; induction Hacc; intros y Hx.
generalize dependent x.
assert (Acc R2 y) as Hacc by auto; induction Hacc; intros y ? ?.
constructor; intros z Hzy.
destruct Hzy as [Hzy | Hzy].
(* first reduction by R1 *)
destruct (well_founded_nf_exists R2 z Hwf2) as [z' Hz'];
assert ((R1⁺) z' y) by eauto; eauto.
(* first reduction by R2 *)
destruct (well_founded_nf_exists R2 z Hwf2) as [z' Hz'].
eapply H0; intros; eauto.
destruct Hx.
assert ((R2 ⋆ ⁻¹; R2 ⋆) y z) as [t [? ?]] by eauto 7.
assert (t = y) by eauto using nf_star_eq; subst.
assert (y = z'); subst. eapply confluent_nf_unique; eauto.
destruct Hz'; eauto.
Qed.

Lemma akama_confluence (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  nf_commute R1 R2 →
  confluent (R1 ∪ R2).
Proof.
intros R1 R2 Hc1 Hc2 Hwf1 Hwf2 Hnf y z [x [Hyx Hzx]].
destruct (well_founded_nf_exists R2 x Hwf2) as [x' [Hnfx' Hx'x]].
destruct (well_founded_nf_exists R2 y Hwf2) as [y' [Hnfy' Hy'y]].
destruct (well_founded_nf_exists R2 z Hwf2) as [z' [Hnfz' Hz'z]].
assert ((R1 ⋆) y' x') by eauto 6 using nf_commute_star.
assert ((R1 ⋆) z' x') by eauto 6 using nf_commute_star.
assert ((R1 ⋆ ⁻¹; R1 ⋆) y' z') as [t [Hty' Htz']] by eauto.
assert ((((R1 ⋆ ∪ R2 ⋆) ⋆) ⁻¹; (R1 ⋆ ∪ R2 ⋆) ⋆) y z) as [u [Hu1 Hu2]]. exists t; unfold transp; split; eauto 6.
unfold transp in *|-.
rewrite <- (union_star_equiv2 _ _ _) in Hu1.
rewrite <- (union_star_equiv2 _ _ _) in Hu2.
eauto.
Qed.

(** * Results about Di Cosmo-Piperno-Geser's condition *)
(** from 'On the Power of Simple Diagrams', Roberto Di Cosmo, RTA '96 *)
(** Definition of [DPG] and some lemmas about it *)
Definition DPG (R1 R2: relation A) :=
  (R2;R1⁻¹) ⊆ (R1⁺ ⁻¹;R2 ⋆).

Lemma commutation_condition_DPG_plus (R1 R2: relation A):
  well_founded R1 → DPG R1 R2 →
  commute (R1⁺) (R2 ⋆).
Proof.
intros R1 R2 Hwf HDPG y.
rewrite <- wf_plus_equiv in Hwf.
assert (Acc (R1⁺) y) as Hacc by auto; induction Hacc.
rename x into y.
intros z [x [Hyx Hzx]]. unfold transp in Hzx.
generalize dependent z.
rewrite rtn1_trans_equiv in Hyx; induction Hyx; try rewrite <- rtn1_trans_equiv in *|-; intros.
eauto 7.
rewrite tn1_trans_equiv in Hzx; destruct Hzx; try rewrite <- tn1_trans_equiv in *|-; eauto.
assert ((R1⁺ ⁻¹;R2 ⋆) y0 z0) as [t [Hty0 Htz0]] by eauto;
apply IHHyx in Hty0; destruct Hty0 as [? [? ?]]; eauto.
assert ((R1⁺ ⁻¹;R2 ⋆) y0 y1) as [t [Hty0 Hty1]] by eauto.
unfold transp in Hty0.
assert (((R1 ⁺) ⁻¹; R2 ⋆) y t) as [u [Huy Hut]] by auto.
unfold transp in Huy.
assert (((R1 ⁺) ⁻¹; R2 ⋆) u z0) as [v [Hvu Hvz0]]; eauto 6.
Qed.

Lemma commutation_condition_DPG (R1 R2: relation A):
  well_founded R1 → DPG R1 R2 →
  commute (R1 ⋆) (R2 ⋆).
Proof.
intros R1 R2 Hwf HDPG.
auto using commute_plus_star, commutation_condition_DPG_plus.
Qed.

Lemma DPG_diagram1 (R1 R2: relation A):
  well_founded R1 → DPG R1 R2 →
  preserves_nf R1 R2 →
  forall y z, (R2 ⋆; R1 ⋆ ⁻¹) y z → nf R2 y →
    exists t, (R1 ⋆) t y ∧ (R2 ⋆) t z ∧ nf R2 t.
Proof.
intros R1 R2 Hwf HDPG Hnf y z [x [Hyx Hzx]] Hnfy.
assert (commute (R1 ⋆) (R2 ⋆)) by auto using commutation_condition_DPG.
assert (((R1 ⋆)⁻¹; R2 ⋆) y z) as [t [? ?]] by eauto.
exists t; intuition auto.
apply (preserves_nf_star R1 R2 Hnf t y); auto.
Qed.

Lemma DPG_diagram2 (R1 R2: relation A):
  well_founded R1 → DPG R1 R2 →
  nf_unique R2 → preserves_nf R1 R2 →
  nf_commute R1 R2.
Proof.
intros R1 R2 Hwf HDPG Huniq Hnf.
unfold nf_commute.
intros z x t y [Hnft Htz] [Hnfy Hyx] Hxy.
assert (commute (R1⁺) (R2 ⋆)) by auto using commutation_condition_DPG_plus.
assert (((R1⁺)⁻¹; R2 ⋆) y z) as [t' [? ?]] by eauto 7.
assert (nf R2 t'). apply (preserves_nf_star R1 R2 Hnf t' y); apply plus_star_included in H0; auto.
assert (t = t') by eauto 6; subst; auto.
Qed.

(** DPG versions of Hindley-Rosen's ans Akama's lemmas *)
Lemma DPG_hindley_rosen (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → DPG R1 R2 →
  confluent (R1 ∪ R2).
Proof.
auto using hindley_rosen2, commutation_condition_DPG.
Qed.

Lemma DPG_akama_well_founded (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  DPG R1 R2 → preserves_nf R1 R2 →
  well_founded (R1 ∪ R2).
Proof.
auto using akama_well_founded, DPG_diagram2, confluent_nf_unique.
Qed.

Lemma DPG_akama_confluence (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  DPG R1 R2 → preserves_nf R1 R2 →
  confluent (R1 ∪ R2).
Proof.
auto using akama_confluence, DPG_diagram2, confluent_nf_unique.
Qed.

End Rel.
