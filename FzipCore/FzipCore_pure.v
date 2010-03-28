Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_zip.

(** Lemmas about [pure] *)
Lemma pure_T (A: Type) : forall x t, pure (x ~ @T A t).
Proof.
intros A x t y H; analyze_binds H.
Qed.

Lemma pure_U (A: Type) : forall a, pure (a ~ @U A).
Proof.
intros A x y H; analyze_binds H.
Qed.

Lemma pure_Eq (A: Type) : forall a t, pure (a ~ @Eq A t).
Proof.
intros A x t y H; analyze_binds H.
Qed.
Hint Resolve pure_T pure_U pure_Eq: fzip.

Lemma pure_app : forall (Γ₁ Γ₂: typing_env),
  pure Γ₁ → pure Γ₂ → pure (Γ₂ ++ Γ₁).
Proof.
intro Γ₁; induction Γ₁; intros; simpl_env in *; auto.
assert (pure Γ₁). intros y H2; eapply H; eauto.
destruct a. destruct t; intros x H2;
try solve [analyze_binds H2;
  [eapply (IHΓ₁ Γ₂); eauto | eapply H; eauto]].
eapply (H a); auto.
Qed.

Lemma pure_app_inv1 : forall (Γ₁ Γ₂: typing_env),
  pure (Γ₂ ++ Γ₁) → pure Γ₁.
Proof.
intro Γ₁; induction Γ₁; intros; simpl_env in *; auto.
destruct a; destruct t;
intros x H1; eapply (H x); analyze_binds H1.
Qed.

Lemma pure_app_inv2 : forall (Γ₁ Γ₂: typing_env),
  pure (Γ₂ ++ Γ₁) → pure Γ₂.
Proof.
intro Γ₁; induction Γ₁; intros; simpl_env in *; auto.
destruct a; destruct t;
intros x H1; eapply (H x); analyze_binds H1.
Qed.
Hint Resolve pure_app pure_app_inv1 pure_app_inv2: fzip.


Lemma pure_zip : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → pure Γ₁ → pure Γ₂ → pure Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0 H1. induction H; auto.
apply pure_app; eauto using pure_app_inv1; auto with fzip.
apply pure_app; eauto using pure_app_inv1; auto with fzip.
intros x H4; eapply (H0 a); auto.
intros x H4; eapply (H1 a); auto.
apply pure_app; eauto using pure_app_inv1; auto with fzip.
Qed.

Lemma pure_zip_inv1 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → pure Γ₃ → pure Γ₁.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0. induction H; auto;
intros y H4; apply (H0 y); analyze_binds H4; eauto with fzip.
Qed.

Lemma pure_zip_inv2 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → pure Γ₃ → pure Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0. induction H; auto;
intros y H4; apply (H0 y); analyze_binds H4; eauto with fzip.
Qed.
Hint Resolve pure_zip pure_zip_inv1 pure_zip_inv2: fzip.

Lemma zip_self : forall Γ, pure Γ → lc_env Γ → uniq Γ → zip Γ Γ Γ.
Proof.
intros Γ H H0 H1. induction Γ; simpl_env in *; auto.
destruct a; destruct t; auto.
constructor. destruct H0; eauto. solve_uniq. solve_uniq.
  apply IHΓ. eauto with fzip. eauto with lngen. solve_uniq.
constructor. solve_uniq. solve_uniq.
  apply IHΓ. eauto with fzip. eauto with lngen. solve_uniq.
elimtype False; eapply (H a); auto.
constructor. destruct H0; eauto. solve_uniq. solve_uniq.
  apply IHΓ. eauto with fzip. eauto with lngen. solve_uniq.
Qed.


Lemma zip_app_weakening : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ,
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃') →
  zip Γ₁ Γ₂ Γ₃ →
  zip Γ₁' Γ₂' Γ₃' →
  disjoint Γ (Γ₃ ++ Γ₃') →
  pure Γ → lc_env Γ → uniq Γ →
  zip (Γ₁ ++ Γ ++ Γ₁') (Γ₂ ++ Γ ++ Γ₂') (Γ₃ ++ Γ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ H H0 H1 H2 H3 H4 H5.
apply zip_app_weakening_strong; auto.
apply zip_self; auto.
assert (dom Γ₁ [<=] dom Γ₃) by eauto with fzip.
assert (dom Γ₁' [<=] dom Γ₃') by eauto with fzip.
  destruct_uniq.
  assert (disjoint Γ₁ Γ) by solve_uniq.
  assert (disjoint Γ₁' Γ) by solve_uniq.
  solve_uniq.
assert (dom Γ₂ [=] dom Γ₃) by eauto with fzip.
assert (dom Γ₂' [=] dom Γ₃') by eauto with fzip.
  destruct_uniq.
  assert (disjoint Γ₂ Γ) by solve_uniq.
  assert (disjoint Γ₂' Γ) by solve_uniq.
  solve_uniq.
Qed.
