(*******************************************************************************)
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

Implicit Arguments clos_refl_trans [A].
Implicit Arguments clos_trans [A].
Implicit Arguments transp [A].
Hint Resolve rt_refl rt_trans rt_step : rel.
Hint Resolve t_trans t_step : rel.
Hint Unfold transp.

(** * Definitions and notations *)
Inductive union {A} (R1 R2: relation A) (x y: A): Prop :=
| Left : R1 x y → union R1 R2 x y
| Right : R2 x y → union R1 R2 x y.
Hint Constructors union.
Definition concat {A} (R1 R2: relation A) x y :=
  ∃ z, R1 x z ∧ R2 z y.
Hint Unfold concat.
Definition sub_rel {A} (R S: relation A) := forall x y, R x y → S x y.
Definition eq_rel {A} (R S: relation A) := forall x y, R x y ↔ S x y.
Hint Unfold sub_rel eq_rel.
Notation "R ; S" := (concat R S) (at level 65, right associativity) : rel_scope.
Notation "R ∪ S" := (union R S) (at level 65, right associativity) : rel_scope.
Notation "R '⋆'" := (clos_refl_trans R) (at level 29) : rel_scope.
Notation "R '⁺'" := (clos_trans R) (at level 29) : rel_scope.
Notation "R '⁻¹'" := (transp R) (at level 29) : rel_scope.
Notation "R '?'" := (union (@eq _) R) (at level 29) : rel_scope.
Notation "R ⊆ S" := (sub_rel R S) (at level 66) : rel_scope.
Notation "R ≡ S" := (eq_rel R S) (at level 66) : rel_scope.
Open Scope rel_scope.

Definition diamond {A} (R: relation A) := (R; R⁻¹) ⊆ (R⁻¹; R).
Definition confluent {A} (R: relation A) := diamond (R ⋆).
Definition weakly_confluent {A} (R: relation A) := (R; R⁻¹) ⊆ (R ⋆ ⁻¹; R ⋆).
Definition commute {A} (R1 R2: relation A) := (R2 ; R1⁻¹) ⊆ (R1⁻¹ ; R2).
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
intros R1 R2 H12; split; intro H; induction H; eauto with rel.
setoid_rewrite H12 in H; auto with rel.
setoid_rewrite <- H12 in H; auto with rel.
Qed.

Add Parametric Morphism A : (@clos_refl_trans A) with
  signature (@eq_rel A) ==> (@eq A) ==> (@eq A) ==> iff as clos_refl_trans_ext_mor.
Proof.
intros R1 R2 H12 x y; split; intro H; induction H; eauto with rel.
setoid_rewrite H12 in H; auto with rel.
setoid_rewrite <- H12 in H; auto with rel.
Qed.

(** Morphisms for clos_trans *)
Add Parametric Morphism A : (@clos_trans A) with
  signature (@eq_rel A) ==> (@eq_rel A) as clos_trans_mor.
Proof.
intros R1 R2 H12; split; intro H; induction H; eauto with rel.
setoid_rewrite H12 in H; auto with rel.
setoid_rewrite <- H12 in H; auto with rel.
Qed.

Add Parametric Morphism A : (@clos_trans A) with
  signature (@eq_rel A) ==> (@eq A) ==> (@eq A) ==> iff as clos_trans_ext_mor.
Proof.
intros R1 R2 H12 x y; split; intro H; induction H; eauto with rel.
setoid_rewrite H12 in H; auto with rel.
setoid_rewrite <- H12 in H; auto with rel.
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
Add Parametric Morphism A : (@commute A) with
  signature (@eq_rel A) ==> (@eq_rel A) ==> iff as commute_mor.
Proof.
intros R1 R2 H12 R3 R4 H34.
unfold commute.
rewrite H12; rewrite H34; tauto.
Qed.

(** * Some lemmas about operations on relations *)
Lemma star_idempotent A (R: relation A):
  R ⋆⋆ ≡ R ⋆.
Proof.
intros A R x y; split; intro H; induction H; eauto with rel.
Qed.
Hint Rewrite star_idempotent : rel.
Hint Resolve star_idempotent : rel.
Implicit Arguments star_idempotent [A].

Lemma plus_idempotent A (R: relation A):
  R ⁺⁺ ≡ R ⁺.
Proof.
intros A R x y; split; intro H; induction H; eauto with rel.
Qed.
Hint Rewrite plus_idempotent : rel.
Hint Resolve plus_idempotent : rel.
Implicit Arguments plus_idempotent [A].

Lemma plus_star_equiv A (R: relation A):
  R ⋆⁺ ≡ R⁺ ⋆.
Proof.
intros A R x y; split; intro H; induction H; eauto with rel; induction H; eauto with rel.
Qed.
Hint Rewrite plus_star_equiv : rel.
Hint Resolve plus_star_equiv : rel.
Implicit Arguments plus_star_equiv [A].

Lemma star_plus_star_equiv A (R: relation A):
  R ⋆⁺ ≡ R ⋆.
Proof.
intros A R x y; split; intro H; induction H; eauto with rel.
Qed.
Hint Rewrite star_plus_star_equiv : rel.
Hint Resolve star_plus_star_equiv : rel.
Implicit Arguments star_plus_star_equiv [A].

Lemma plus_star_star_equiv A (R: relation A):
  R⁺ ⋆ ≡ R ⋆.
Proof.
intros A R.
rewrite <- (star_plus_star_equiv R).
symmetry; auto with rel.
Qed.
Hint Rewrite plus_star_star_equiv : rel.
Hint Resolve plus_star_star_equiv : rel.
Implicit Arguments plus_star_star_equiv [A].

Lemma plus_star_concat_equiv A (R: relation A):
  R⁺ ≡ R ⋆; R.
Proof.
intros A R x y; split; intro H.
rewrite tn1_trans_equiv in H; induction H; try rewrite <- tn1_trans_equiv in *|-; eauto with rel.
destruct IHclos_trans_n1 as [? [? ?]].
eauto 6 with rel.
destruct H as [? [? ?]]. generalize dependent y.
rewrite rtn1_trans_equiv in H; induction H; try rewrite <- rtn1_trans_equiv in *|-; eauto with rel.
Qed.
Hint Resolve plus_star_concat_equiv : rel.
Implicit Arguments plus_star_concat_equiv [A].

Lemma plus_star_included A (R: relation A):
  R⁺ ⊆ R ⋆.
Proof.
intros A R x y H.
induction H; eauto with rel.
Qed.
Hint Resolve plus_star_included : rel.
Implicit Arguments plus_star_included [A].

Lemma concat_assoc A (R1 R2 R3: relation A):
  (R1; R2); R3 ≡ R1; (R2; R3).
Proof.
intros A R1 R2 R3 x y; split; intro H.
destruct H as [z [Hxz Hzy]].
destruct Hxz as [t [Hxt Htz]]; eauto 6.
destruct H as [z [Hxz [t [Hzt Hty]]]]; eauto 6.
Qed.
Hint Resolve concat_assoc : rel.
Implicit Arguments concat_assoc [A].

Lemma star_equiv A (R: relation A):
  R ⋆ ≡ R ⋆ ; R ⋆.
Proof.
intros; split; intro H; eauto with rel.
destruct H as [z [Hxz Hzy]]; eauto with rel.
Qed.
Hint Rewrite <- star_equiv : rel.
Hint Resolve star_equiv : rel.
Implicit Arguments star_equiv [A].

Lemma transp_involutive A (R: relation A):
  R⁻¹⁻¹ ≡ R.
Proof.
intros; split; auto.
Qed.
Hint Rewrite transp_involutive : rel.
Hint Resolve transp_involutive : rel.
Implicit Arguments transp_involutive [A].

Lemma transp_concat_commute A (R1 R2: relation A):
  (R1; R2)⁻¹ ≡ (R2⁻¹; R1⁻¹).
Proof.
intros A R1 R2 x y; split; intro H;
destruct H as [z [Hxz Hzy]]; eauto.
Qed.
Hint Rewrite transp_concat_commute : rel.
Hint Resolve transp_concat_commute : rel.
Implicit Arguments transp_concat_commute [A].

Lemma transp_star_commute A (R: relation A):
  R⁻¹ ⋆ ≡ R ⋆ ⁻¹.
Proof.
intros A R. split; intro H.
induction H; unfold transp in *; eauto with rel.
unfold transp in H. induction H; eauto with rel.
Qed.
Hint Rewrite transp_star_commute : rel.
Hint Resolve transp_star_commute : rel.
Implicit Arguments transp_star_commute [A].

Lemma transp_plus_commute A (R: relation A):
  R⁻¹⁺ ≡ R⁺ ⁻¹.
Proof.
intros A R. split; intro H.
induction H; unfold transp in *; eauto with rel.
unfold transp in H. induction H; eauto with rel.
Qed.
Hint Rewrite transp_plus_commute : rel.
Hint Resolve transp_plus_commute : rel.
Implicit Arguments transp_plus_commute [A].

Lemma union_star_equiv A (R1 R2: relation A):
  (R1 ∪ R2)⋆ ≡ (R1 ⋆; R2 ⋆)⋆.
Proof.
intros A R1 R2 x y; split; intro H.
induction H; eauto with rel.
destruct H; apply rt_step; eauto with rel.
induction H; eauto with rel.
destruct H as [z [Hxz Hzy]].
generalize dependent y. induction Hxz; intros; eauto with rel.
apply rt_trans with (y := y); auto with rel.
clear H; induction Hzy; eauto with rel.
induction Hzy; eauto with rel.
Qed.
Hint Resolve union_star_equiv : rel.
Implicit Arguments union_star_equiv [A].

Lemma concat_star_included1 A (R1 R2: relation A):
  R1 ⋆ ⊆ (R1; R2 ⋆)⋆.
Proof.
intros A R1 R2 x y H.
induction H; eauto with rel.
Qed.
Hint Resolve concat_star_included1 : rel.
Implicit Arguments concat_star_included1 [A].

Lemma concat_star_included2 A (R1 R2: relation A):
  R2 ⋆ ⊆ (R1 ⋆; R2)⋆.
Proof.
intros A R1 R2 x y H.
induction H; eauto with rel.
Qed.
Hint Resolve concat_star_included2 : rel.
Implicit Arguments concat_star_included2 [A].

Lemma union_star_included1 A (R1 R2: relation A):
  R1 ⋆ ⊆ (R1 ∪ R2)⋆.
Proof.
intros A R1 R2 x y H. induction H; eauto with rel.
Qed.
Hint Resolve union_star_included1 : rel.
Implicit Arguments union_star_included1 [A].

Lemma union_star_included2 A (R1 R2: relation A):
  R2 ⋆ ⊆ (R1 ∪ R2)⋆.
Proof.
intros A R1 R2 x y H. induction H; eauto with rel.
Qed.
Hint Resolve union_star_included2 : rel.
Implicit Arguments union_star_included2 [A].

Lemma union_star_equiv2 A (R1 R2: relation A):
  (R1 ∪ R2)⋆ ≡ (R1 ⋆ ∪ R2 ⋆)⋆.
Proof.
intros A R1 R2 x y; split; intro H; induction H; eauto with rel.
destruct H; eauto with rel.
destruct H. apply union_star_included1; auto. apply union_star_included2; auto.
Qed.
Hint Resolve union_star_equiv2 : rel.
Implicit Arguments union_star_equiv2 [A].

Lemma union_plus_included1 A (R1 R2: relation A):
  R1⁺ ⊆ (R1 ∪ R2)⁺.
Proof.
intros A R1 R2 x y H. induction H; eauto with rel.
Qed.
Hint Resolve union_plus_included1 : rel.
Implicit Arguments union_plus_included1 [A].

Lemma union_plus_included2 A (R1 R2: relation A):
  R2⁺ ⊆ (R1 ∪ R2)⁺.
Proof.
intros A R1 R2 x y H. induction H; eauto with rel.
Qed.
Hint Resolve union_plus_included2 : rel.
Implicit Arguments union_plus_included2 [A].

Lemma union_plus_equiv2 A (R1 R2: relation A):
  (R1 ∪ R2)⁺ ≡ (R1⁺ ∪ R2⁺)⁺.
Proof.
intros A R1 R2 x y; split; intro H; induction H; eauto with rel.
destruct H; eauto with rel.
destruct H. apply union_plus_included1; auto. apply union_plus_included2; auto.
Qed.
Hint Resolve union_plus_equiv2 : rel.
Implicit Arguments union_plus_equiv2 [A].

Lemma concat_star_equiv A (R1 R2: relation A):
  (R1; R2 ⋆) ≡ (R1; R2 ⋆) ; R2 ⋆.
Proof.
intros A R1 R2.
rewrite concat_assoc.
autorewrite with rel.
reflexivity.
Qed.
Hint Rewrite <- concat_star_equiv : rel.
Hint Resolve concat_star_equiv : rel.
Implicit Arguments concat_star_equiv [A].

Inductive t_length_clos A (R: relation A) : nat → A → A → Prop :=
| t_length_step : forall x y, R x y → t_length_clos A R 1 x y
| t_length_trans : forall x y z n,
  t_length_clos A R n x y → R y z → t_length_clos A R (1+n) x z.
Hint Constructors t_length_clos.
Implicit Arguments t_length_clos [A].

Lemma t_length_clos_equiv A (R: relation A) :
  R ⁺ ≡ (fun x y => exists n, t_length_clos R n x y).
Proof.
intros A R x y; rewrite tn1_trans_equiv; split; intro H.
induction H; eauto.
  destruct IHclos_trans_n1; eauto.
destruct H as [n H]; induction H; rewrite <- tn1_trans_equiv in *; eauto with rel.
Qed.
Implicit Arguments t_length_clos_equiv [A].

Require Import Omega.
Lemma t_length_clos_transitivity A (R: relation A) : forall n m x y z,
  t_length_clos R n x y →
  t_length_clos R m y z →
  t_length_clos R (n+m) x z.
Proof.
intros A R.
assert (forall n x y z, t_length_clos R n x y → R y z → t_length_clos R (1+n) x z).
  intros n x y z Hn; induction Hn; intros; eauto.
intros n m x y z Hn Hm.
generalize dependent x. generalize dependent n.
induction Hm; intros.
replace (n+1) with (1+n) by omega; eauto.
replace (n0+(1+n)) with (1+(n0+n)) by omega; eauto.
Qed.
Implicit Arguments t_length_clos_transitivity [A].

Lemma t_length_clos_1_step A (R: relation A) :
  forall x y, t_length_clos R 1 x y → R x y.
Proof.
intros A R x y H.
remember 1 as n.
induction H; auto.
assert (n=0) by omega; subst; inversion H.
Qed.
Implicit Arguments t_length_clos_1_step [A].

(** * Lemmas about [commute] *)
Lemma commute_sym A (R1 R2: relation A):
  commute R1 R2 → commute R2 R1.
Proof.
intros A R1 R2 Hcomm.
intros x y H.
assert (((R1; R2⁻¹)⁻¹) y x) as H' by auto.
rewrite (transp_concat_commute _ _ _) in H'.
autorewrite with rel in H'.
apply Hcomm in H'. destruct H' as [? [? ?]].
eauto.
Qed.
Implicit Arguments commute_sym [A].

Lemma commute_star1 A (R1 R2:relation A):
  commute R1 R2 → commute (R1 ⋆) R2.
Proof.
intros A R1 R2 Hcomm x y H.
destruct H as [z [Hxz Hyz]].
unfold transp in Hyz.
rewrite rt1n_trans_equiv in Hyz.
generalize dependent x; induction Hyz; intros; eauto with rel.
apply IHHyz in Hxz. destruct Hxz as [? [? ?]].
assert ((R2; R1⁻¹) x1 x) by eauto. apply Hcomm in H2.
destruct H2 as [? [? ?]]; eauto 7 with rel.
Qed.
Implicit Arguments commute_star1 [A].

Lemma commute_star2 A (R1 R2:relation A):
  commute R1 R2 → commute R1 (R2 ⋆).
Proof.
intros A R1 R2 H.
apply commute_sym. apply commute_sym in H.
auto using commute_star1.
Qed.
Implicit Arguments commute_star2 [A].

Lemma commute_star A (R1 R2:relation A):
  commute R1 R2 → commute (R1 ⋆) (R2 ⋆).
Proof.
intros A R1 R2 H.
auto using commute_star1, commute_star2.
Qed.
Implicit Arguments commute_star [A].

Lemma commute_plus_star A (R1 R2: relation A):
  commute (R1⁺) R2 → commute (R1 ⋆) R2.
Proof.
intros A R1 R2 H.
apply commute_star1 in H.
intros y z [x [Hyx Hzx]].
unfold transp in Hzx.
rewrite <- (plus_star_star_equiv _ _) in Hzx.
assert (((R1 ⁺ ⋆) ⁻¹; R2) y z) as [? [H0 ?]] by eauto.
unfold transp in H0.
rewrite (plus_star_star_equiv _ _) in H0.
eauto.
Qed.
Implicit Arguments commute_plus_star [A].

Lemma commute_union A (R1 R2 R3: relation A):
  commute R1 R2 →
  commute R1 R3 →
  commute R1 (R2 ∪ R3).
Proof.
intros A R1 R2 R3 H12 H13 x y H.
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
Implicit Arguments commute_union [A].

Lemma commutation_condition A (R1 R2: relation A):
  (R1; R2⁻¹) ⊆ (R2 ⋆ ⁻¹; R1?) →
  commute (R1 ⋆) (R2 ⋆).
Proof.
intros A R1 R2 Hcomm1.
assert (R1; R2 ⋆ ⁻¹ ⊆ (R2 ⋆) ⁻¹; R1 ⋆) as Hcomm2.
  intros x y [z [Hxz Hyz]]. unfold transp in Hyz.
  generalize dependent x.
  rewrite rtn1_trans_equiv in Hyz; induction Hyz; try rewrite <- rtn1_trans_equiv in *|-; intros.
   eauto 7 with rel.
   assert (((R2 ⋆) ⁻¹; R1 ?) x y0) as [t [Htx Hty0]] by eauto.
   destruct Hty0; subst.
     eauto 6 with rel.
     apply IHHyz in H0; destruct H0 as [? [? ?]]; eauto 6 with rel.
intros x y [z [Hxz Hyz]].
unfold transp in Hyz.
generalize dependent x; rewrite rtn1_trans_equiv in Hyz; induction Hyz; try rewrite <- rtn1_trans_equiv in *|-; intros; eauto with rel.
assert (((R2 ⋆) ⁻¹; R1 ⋆) y0 x) as [t [Hty0 Htx]] by eauto.
apply IHHyz in Hty0. destruct Hty0 as [? [? ?]].
eauto 6 with rel.
Qed.
Implicit Arguments commutation_condition [A].

(** * Lemmas about [confluent] *)
Lemma confluent_commute_star_refl_equiv A (R: relation A):
  confluent R ↔ commute (R ⋆) (R ⋆).
Proof.
intuition auto.
Qed.
Implicit Arguments confluent_commute_star_refl_equiv [A].

Lemma concat_wf_equiv A (R1 R2: relation A):
  well_founded (R1 ; R2) → well_founded (R2 ; R1).
Proof.
intros A R1 R2 H.
intro x.
constructor; intros y [z [Hyz _]].
assert (Acc (R1; R2) z) as H0 by auto; clear H.
generalize dependent y.
induction H0; intros.
constructor; intros z [t [Hzt Hty]].
eapply H0; eauto.
Qed.
Implicit Arguments concat_wf_equiv [A].

Lemma diamond_union A (R1 R2: relation A):
  commute R1 R2 →
  diamond R1 →
  diamond R2 →
  diamond (R1 ∪ R2).
Proof.
intros A R1 R2 Hcomm HR1 HR2 x y [z [Hxz Hyz]].
destruct Hxz; destruct Hyz.
  assert ((R1⁻¹; R1) x y) as [? [? ?]] by eauto; eauto 7.
  assert (commute R2 R1) as Hcomm' by auto using commute_sym.
    assert ((R2⁻¹; R1) x y) as [? [? ?]] by eauto; eauto 7.
  assert ((R1⁻¹; R2) x y) as [? [? ?]] by eauto; eauto 7.
  assert ((R2⁻¹; R2) x y) as [? [? ?]] by eauto; eauto 7.
Qed.
Implicit Arguments diamond_union [A].

Lemma diamond_t_length A (R: relation A) :
  diamond R →
  forall n m x y z, t_length_clos R m x z →
  t_length_clos R n y z →
  exists t, t_length_clos R n t x ∧ t_length_clos R m t y.
Proof.
intros A R Hdiamond.
assert (forall p n m x y z, n + m ≤ p →
  t_length_clos R m x z →
  t_length_clos R n y z →
  exists t, t_length_clos R n t x ∧ t_length_clos R m t y).
intro p; induction p; intros n m x y z Hp Hx Hy.
(* case p = 0 *)
assert (n = 0) by omega; assert (m = 0) by omega; subst.
inversion Hx.
(* case p > 0 *)
destruct Hx; eauto.
(* n0 = 1 *)
destruct Hy; eauto.
(* n = 1 *)
assert ((R⁻¹; R) x x0) as [t [Htx Hty]] by eauto 7.
unfold transp in Htx. apply (t_length_step _ _ _) in Htx.
apply (t_length_step _ _ _) in Hty. eauto.
(* n > 1 *)
assert ((R⁻¹; R) x y) as [t [Htx Hty]] by eauto 7.
assert (exists t0, t_length_clos R n t0 t ∧ t_length_clos R 1 t0 x0) as [? [? ?]].
  apply IHp with (z := y); try omega; eauto.
eauto using t_length_clos_transitivity.
(* n0 > 1 *)
assert (exists t, t_length_clos R n t y0 ∧ t_length_clos R 1 t y) as [t [? ?]].
  apply IHp with (z := z); try omega; eauto.
  inversion Hx; subst; omega.
assert (exists u, t_length_clos R n u x ∧ t_length_clos R n0 u t) as [u [? ?]].
  apply IHp with (z := y0); try omega; eauto.
exists u; split; auto.
replace (1+n0) with (n0+1) by omega; eauto using t_length_clos_transitivity.
intros n m x y z; apply (H (n+m)); auto.
Qed.
Implicit Arguments diamond_t_length [A].

Lemma diamond_plus A (R: relation A) :
  diamond R → diamond (R⁺).
Proof.
intros A R Hdiamond x y [z [Hxz Hyz]].
unfold transp in Hyz.
rewrite (t_length_clos_equiv R x z)  in Hxz.
rewrite (t_length_clos_equiv R y z)  in Hyz.
destruct Hxz as [n Hxz].
destruct Hyz as [m Hyz].
assert (exists t, t_length_clos R m t x ∧ t_length_clos R n t y) as [t [Htx Hty]].
  eapply diamond_t_length; eauto.
exists t; split; unfold transp; rewrite (t_length_clos_equiv _ _ _) ; eauto.
Qed.
Implicit Arguments diamond_plus [A].

Lemma diamond_confluent A (R: relation A) :
  diamond R → confluent R.
Proof.
intros A R Hdiamond x y [z [Hxz Hyz]].
unfold transp in Hyz.
rewrite rtn1_trans_equiv in Hxz; rewrite rtn1_trans_equiv in Hyz;
destruct Hxz; destruct Hyz; try rewrite <- rtn1_trans_equiv in *|-; eauto 7 with rel.
assert ((R⁺) x z). rewrite (plus_star_concat_equiv _ _); eauto.
assert ((R⁺) y z). rewrite (plus_star_concat_equiv _ _); eauto.
destruct (diamond_plus R Hdiamond x y) as [? [? ?]]; eauto using plus_star_included.
unfold transp in *|-; exists x0; split; apply plus_star_included; auto.
Qed.
Implicit Arguments diamond_confluent [A].

(** Hindley-Rosen lemma, from 'The λ-calculus, its Syntax and
Semantics', H.P. Barendregt, Ch. 3 § 3 *)
Lemma hindley_rosen1 A (R1 R2: relation A):
  commute R1 R2 →
  diamond R1 →
  diamond R2 →
  confluent (R1 ∪ R2).
Proof.
intros A R1 R2 Hcomm HR1 HR2.
eauto using diamond_confluent, diamond_union.
Qed.
Implicit Arguments hindley_rosen1 [A].

Lemma hindley_rosen2 A (R1 R2: relation A):
  commute (R1 ⋆) (R2 ⋆) →
  confluent R1 →
  confluent R2 →
  confluent (R1 ∪ R2).
Proof.
intros A R1 R2 Hcomm HR1 HR2.
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
Implicit Arguments hindley_rosen2 [A].

Lemma newman A (R: relation A):
  well_founded R →
  weakly_confluent R →
  confluent R.
Proof.
intros A R Hwf Hwc.
intros y1 y2 [x [Hxy1 Hxy2]]. unfold transp in Hxy2.
rewrite rtn1_trans_equiv in * |-.
assert (Acc R x) by auto.
generalize dependent y1; generalize dependent y2.
induction H; intros.
generalize dependent y2.
induction Hxy1; intros; eauto.
rewrite <- rtn1_trans_equiv in * |-; eauto with rel.
generalize dependent y1; generalize dependent y.
induction Hxy2; intros; eauto.
rewrite <- rtn1_trans_equiv in * |-; eauto 7 with rel.
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
  rewrite <- rtn1_trans_equiv; eauto with rel.
  rewrite <- rtn1_trans_equiv; eauto with rel.
unfold transp in Hvt; eauto 7 with rel.
Qed.
Implicit Arguments newman [A].

(** * Definitions about normal forms *)
Definition nf A (R: relation A) (x: A) :=
  forall y, ~(R y x).
Hint Unfold nf.
Implicit Arguments nf [A].

(** x is a normal form of y *)
Definition is_nf_of A (R: relation A) (x y: A) :=
  nf R x ∧ (R ⋆) x y.
Hint Unfold is_nf_of.
Implicit Arguments is_nf_of [A].

Definition nf_unique A (R: relation A) :=
  forall x y z, is_nf_of R y x → is_nf_of R z x →
    y = z.
Hint Unfold nf_unique.
Implicit Arguments nf_unique [A].

(** R1 commutes with R2' normal forms *)
Definition nf_commute A (R1 R2: relation A) :=
  forall x y x' y',
    is_nf_of R2 x' x → is_nf_of R2 y' y →
    R1 x y →
    (R1⁺) x' y'.
Hint Unfold nf_commute.
Implicit Arguments nf_commute [A].

(** R1 preserves R2's normal forms *)
Definition preserves_nf A (R1 R2: relation A) :=
  forall x y, nf R2 y → R1 x y → nf R2 x.
Hint Unfold preserves_nf.
Implicit Arguments preserves_nf [A].

(** * Lemmas about [nf], [is_nf_of], [nf_unique], [nf_commute] and [preserve_nf] *)
Lemma nf_star_eq A (R: relation A):
  forall x y, nf R x → (R ⋆) y x → y = x.
Proof.
intros A R x y Hnf Hyx.
rewrite rtn1_trans_equiv in Hyx; induction Hyx; try rewrite <- rtn1_trans_equiv in *|-; eauto.
edestruct Hnf; eauto.
Qed.
Implicit Arguments nf_star_eq [A].

Lemma confluent_nf_unique A (R: relation A):
  confluent R → nf_unique R.
Proof.
intros A R H x y z Hy Hz.
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
Implicit Arguments confluent_nf_unique [A].

(** This lemma requires classical logic. *)
Lemma well_founded_nf_exists A (R: relation A) (x: A) :
  well_founded R → exists y, is_nf_of R y x.
Proof.
intros A R x Hwf.
assert (Acc R x) as Hacc by auto; induction Hacc.
Require Import Classical.
destruct (classic (exists y, R y x)) as [[y Hy] | ?].
assert (exists z, is_nf_of R z y) as [z [Hyz Hz]] by auto; eauto 7 with rel.
eauto 8 with rel.
Qed.
Implicit Arguments well_founded_nf_exists [A].

Lemma preserves_nf_plus A (R1 R2: relation A):
  preserves_nf R1 R2 → preserves_nf (R1⁺) R2.
Proof.
intros A R1 R2 H x y Hx Hxy.
rewrite tn1_trans_equiv in Hxy; induction Hxy; try rewrite <- tn1_trans_equiv in *|-; eauto.
Qed.
Implicit Arguments preserves_nf_plus [A].

Lemma preserves_nf_star A (R1 R2: relation A):
  preserves_nf R1 R2 → preserves_nf (R1 ⋆) R2.
Proof.
intros A R1 R2 H x y Hx Hxy.
rewrite rtn1_trans_equiv in Hxy; induction Hxy; try rewrite <- rtn1_trans_equiv in *|-; eauto.
Qed.
Implicit Arguments preserves_nf_star [A].

Lemma nf_commute_plus A (R1 R2: relation A):
  confluent R2 → well_founded R2 →
  nf_commute R1 R2 →
  forall x y z t, is_nf_of R2 z x → is_nf_of R2 t y → ((R1 ∪ R2)⁺) y x →
    (R1 ⋆) t z.
Proof.
intros A R1 R2 Hc2 Hwf2 Hnf y x y' x' Hy'y Hx'x Hyx.
generalize dependent y'. generalize dependent x'.
rewrite t1n_trans_equiv in Hyx; induction Hyx; try rewrite <- t1n_trans_equiv in *|-; intros.
destruct H.
  apply plus_star_included; eauto.
  assert (x' = y'); subst; auto with rel.
    destruct Hx'x; destruct Hy'y.
    assert ((R2 ⋆ ⁻¹; R2 ⋆) y' x') as [t [? ?]] by eauto 8 with rel.
    unfold transp in *|-.
    assert (t = y') by eauto using nf_star_eq.
    assert (t = x') by eauto using nf_star_eq.
    congruence.
destruct H.
  destruct (well_founded_nf_exists R2 y Hwf2) as [t Hty].
    assert ((R1⁺) x' t) by eauto.
    apply IHHyx with (y' := y') in Hty; auto.
    apply plus_star_included in H0; eauto with rel.
  destruct Hx'x; eauto 6 with rel.
Qed.
Implicit Arguments nf_commute_plus [A].

Lemma nf_commute_star A (R1 R2: relation A):
  confluent R2 → well_founded R2 →
  nf_commute R1 R2 →
  forall x y z t, is_nf_of R2 z x → is_nf_of R2 t y → ((R1 ∪ R2)⋆) y x →
    (R1 ⋆) t z.
Proof.
intros A R1 R2 Hc2 Hwf2 Hnf y x y' x' Hy'y Hx'x Hyx.
rewrite rtn1_trans_equiv in Hyx; destruct Hyx; try rewrite <- rtn1_trans_equiv in *|-.
assert (y' = x'). eapply confluent_nf_unique; eauto. subst; auto with rel.
eapply nf_commute_plus; eauto. rewrite (plus_star_concat_equiv _ _ _); eauto.
Qed.
Implicit Arguments nf_commute_star [A].

(** * Lemmas about [well_founded] *)
Lemma wf_plus_equiv A (R: relation A):
  well_founded (R⁺) ↔ well_founded R.
Proof.
intros A R; split; intros H x.
(* → *)
assert (Acc (R⁺) x) by auto; induction H0.
constructor; intros; eauto with rel.
(* ← *)
constructor.
assert (Acc R x) as H0 by auto; induction H0.
intros y H2; rewrite tn1_trans_equiv in H2; induction H2; constructor; intros.
  eauto.
  rewrite <- tn1_trans_equiv in H3; eauto with rel.
Qed.
Implicit Arguments wf_plus_equiv [A].

Lemma union_wf A (R1 R2: relation A):
  well_founded (R1 ⋆ ; R2) →
  well_founded (R2 ⋆ ; R1) →
  well_founded (R1 ∪ R2).
Proof.
intros A R1 R2 HR1R2 HR2R1.
assert (well_founded (R1 ; (R2)⋆)) as wfR1R2 by auto using concat_wf_equiv.
assert (well_founded (R2 ; (R1)⋆)) as wfR2R1 by auto using concat_wf_equiv.
intro x.
assert (Acc (R1 ; (R2)⋆) x) as Hx1 by auto; induction Hx1.
assert (Acc (R2 ; (R1)⋆) x) as Hx2 by auto; induction Hx2.
constructor; intros y [Hy | Hy]; eauto with rel.
eapply H2; eauto with rel.
intros z Hz.
eapply H0; eauto. rewrite (concat_star_equiv _ _ _); eauto with rel.
Qed.
Implicit Arguments union_wf [A].

(** Akama's lemmas, from 'On Mints' Reduction for ccc-Calculus', Yohji Akama, TLCA '93 *)
Lemma akama_well_founded A (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  nf_commute R1 R2 →
  well_founded (R1 ∪ R2).
Proof.
intros A R1 R2 Hc1 Hc2 Hwf1 Hwf2 Hnf.
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
assert ((R2 ⋆ ⁻¹; R2 ⋆) y z) as [t [? ?]] by eauto 7 with rel.
assert (t = y) by eauto using nf_star_eq; subst.
assert (y = z'); subst. eapply confluent_nf_unique; eauto.
destruct Hz'; eauto.
Qed.
Implicit Arguments akama_well_founded [A].

Lemma akama_confluence A (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  nf_commute R1 R2 →
  confluent (R1 ∪ R2).
Proof.
intros A R1 R2 Hc1 Hc2 Hwf1 Hwf2 Hnf y z [x [Hyx Hzx]].
destruct (well_founded_nf_exists R2 x Hwf2) as [x' [Hnfx' Hx'x]].
destruct (well_founded_nf_exists R2 y Hwf2) as [y' [Hnfy' Hy'y]].
destruct (well_founded_nf_exists R2 z Hwf2) as [z' [Hnfz' Hz'z]].
assert ((R1 ⋆) y' x') by eauto 6 using nf_commute_star.
assert ((R1 ⋆) z' x') by eauto 6 using nf_commute_star.
assert ((R1 ⋆ ⁻¹; R1 ⋆) y' z') as [t [Hty' Htz']] by eauto.
assert ((((R1 ⋆ ∪ R2 ⋆) ⋆) ⁻¹; (R1 ⋆ ∪ R2 ⋆) ⋆) y z) as [u [Hu1 Hu2]]. exists t; unfold transp; split; eauto 6 with rel.
unfold transp in *|-.
rewrite <- (union_star_equiv2 _ _ _) in Hu1.
rewrite <- (union_star_equiv2 _ _ _) in Hu2.
eauto.
Qed.
Implicit Arguments akama_confluence [A].

(** * Results about Di Cosmo-Piperno-Geser's condition *)
(** from 'On the Power of Simple Diagrams', Roberto Di Cosmo, RTA '96 *)
(** Definition of [DPG] and some lemmas about it *)
Definition DPG A (R1 R2: relation A) :=
  (R2;R1⁻¹) ⊆ (R1⁺ ⁻¹;R2 ⋆).
Implicit Arguments DPG [A].

Lemma commutation_condition_DPG_plus A (R1 R2: relation A):
  well_founded R1 → DPG R1 R2 →
  commute (R1⁺) (R2 ⋆).
Proof.
intros A R1 R2 Hwf HDPG y.
rewrite <- wf_plus_equiv in Hwf.
assert (Acc (R1⁺) y) as Hacc by auto; induction Hacc.
rename x into y.
intros z [x [Hyx Hzx]]. unfold transp in Hzx.
generalize dependent z.
rewrite rtn1_trans_equiv in Hyx; induction Hyx; try rewrite <- rtn1_trans_equiv in *|-; intros.
eauto 7 with rel.
rewrite tn1_trans_equiv in Hzx; destruct Hzx; try rewrite <- tn1_trans_equiv in *|-; eauto.
assert ((R1⁺ ⁻¹;R2 ⋆) y0 z0) as [t [Hty0 Htz0]] by eauto;
apply IHHyx in Hty0; destruct Hty0 as [? [? ?]]; eauto with rel.
assert ((R1⁺ ⁻¹;R2 ⋆) y0 y1) as [t [Hty0 Hty1]] by eauto.
unfold transp in Hty0.
assert (((R1 ⁺) ⁻¹; R2 ⋆) y t) as [u [Huy Hut]] by auto.
unfold transp in Huy.
assert (((R1 ⁺) ⁻¹; R2 ⋆) u z0) as [v [Hvu Hvz0]]; eauto 6 with rel.
Qed.
Implicit Arguments commutation_condition_DPG_plus [A].

Lemma commutation_condition_DPG A (R1 R2: relation A):
  well_founded R1 → DPG R1 R2 →
  commute (R1 ⋆) (R2 ⋆).
Proof.
intros A R1 R2 Hwf HDPG.
auto using commute_plus_star, commutation_condition_DPG_plus.
Qed.
Implicit Arguments commutation_condition_DPG [A].

Lemma DPG_diagram1 A (R1 R2: relation A):
  well_founded R1 → DPG R1 R2 →
  preserves_nf R1 R2 →
  forall y z, (R2 ⋆; R1 ⋆ ⁻¹) y z → nf R2 y →
    exists t, (R1 ⋆) t y ∧ (R2 ⋆) t z ∧ nf R2 t.
Proof.
intros A R1 R2 Hwf HDPG Hnf y z [x [Hyx Hzx]] Hnfy.
assert (commute (R1 ⋆) (R2 ⋆)) by auto using commutation_condition_DPG.
assert (((R1 ⋆)⁻¹; R2 ⋆) y z) as [t [? ?]] by eauto.
exists t; intuition auto.
apply (preserves_nf_star R1 R2 Hnf t y); auto.
Qed.
Implicit Arguments DPG_diagram1 [A].

Lemma DPG_diagram2 A (R1 R2: relation A):
  well_founded R1 → DPG R1 R2 →
  nf_unique R2 → preserves_nf R1 R2 →
  nf_commute R1 R2.
Proof.
intros A R1 R2 Hwf HDPG Huniq Hnf.
unfold nf_commute.
intros z x t y [Hnft Htz] [Hnfy Hyx] Hxy.
assert (commute (R1⁺) (R2 ⋆)) by auto using commutation_condition_DPG_plus.
assert (((R1⁺)⁻¹; R2 ⋆) y z) as [t' [? ?]] by eauto 7 with rel.
assert (nf R2 t'). apply (preserves_nf_star R1 R2 Hnf t' y); apply plus_star_included in H0; auto.
assert (t = t') by eauto 6; subst; auto.
Qed.
Implicit Arguments DPG_diagram2 [A].

(** DPG versions of Hindley-Rosen's ans Akama's lemmas *)
Lemma DPG_hindley_rosen A (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → DPG R1 R2 →
  confluent (R1 ∪ R2).
Proof.
auto using hindley_rosen2, commutation_condition_DPG.
Qed.
Implicit Arguments DPG_hindley_rosen [A].

Lemma DPG_akama_well_founded A (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  DPG R1 R2 → preserves_nf R1 R2 →
  well_founded (R1 ∪ R2).
Proof.
auto using akama_well_founded, DPG_diagram2, confluent_nf_unique.
Qed.
Implicit Arguments DPG_akama_well_founded [A].

Lemma DPG_akama_confluence A (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  DPG R1 R2 → preserves_nf R1 R2 →
  confluent (R1 ∪ R2).
Proof.
auto using akama_confluence, DPG_diagram2, confluent_nf_unique.
Qed.
Implicit Arguments DPG_akama_confluence [A].
