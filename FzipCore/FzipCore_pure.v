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

Lemma pure_subst : forall Γ₁ Γ₂ x (τ: typ),
  pure (Γ₁ ++ x ~ T τ ++ Γ₂) →
  pure (Γ₁ ++ Γ₂).
Proof.
intros Γ₁ Γ₂ x τ H.
intros a H0. eapply (H a). analyze_binds H0.
Qed.

Lemma pure_instantiate : forall Γ₁ Γ₂ a τ,
  lc_typ τ →
  pure (Γ₁ ++ a ~ U ++ Γ₂) →
  pure (Γ₁ ++ a ~ Eq τ ++ Γ₂).
Proof.
intros Γ₁ Γ₂ a τ Hlc H.
intros a0 H0. eapply (H a0). analyze_binds H0.
Qed.

Lemma pure_subst_eq : forall Γ₁ Γ₂ a τ,
  pure (Γ₁ ++ a ~ Eq τ ++ Γ₂) →
  pure (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂).
Proof.
intros Γ₁ Γ₂ a τ H.
unfold env_map.
intros a0 H0.
replace (@E typ) with (tag_map (tsubst_typ τ a) E) in H0 by reflexivity.
eapply (H a0). analyze_binds H0; eauto with lngen.
Qed.

Lemma pure_tsubst : forall Γ₁ Γ₂ a τ,
  lc_typ τ →
  pure (Γ₁ ++ a ~ U ++ Γ₂) →
  pure (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂).
Proof.
intros Γ₁ Γ₂ a τ H H0.
auto using pure_instantiate, pure_subst_eq.
Qed.

Lemma zip_pure_inv1 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → pure Γ₃ → Γ₁ = Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0. induction H; auto.
Case "T". rewrite IHzip; eauto with fzip; subst; auto.
Case "U". rewrite IHzip; eauto with fzip; subst; auto.
Case "E". elimtype False. eapply (H0 a). auto.
Case "EU". elimtype False. eapply (H0 a). auto.
Case "Eq". rewrite IHzip; eauto with fzip; subst; auto.
Qed.

Lemma zip_pure_inv2 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → pure Γ₃ → Γ₂ = Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0. induction H; auto.
Case "T". rewrite IHzip; eauto with fzip; subst; auto.
Case "U". rewrite IHzip; eauto with fzip; subst; auto.
Case "E". elimtype False. eapply (H0 a). auto.
Case "EU". elimtype False. eapply (H0 a). auto.
Case "Eq". rewrite IHzip; eauto with fzip; subst; auto.
Qed.

Lemma zip_pure_eq1 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → pure Γ₁ → Γ₂ = Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0. induction H; auto.
Case "T". f_equal. apply IHzip. intros a Ha. eapply (H0 a); auto.
Case "U". f_equal. apply IHzip. intros b Hb. eapply (H0 b); auto.
Case "UE". elimtype False. eapply (H0 a); auto.
Case "E". f_equal. apply IHzip. intros b Hb. eapply (H0 b); auto.
Case "Eq". f_equal. apply IHzip. intros b Hb. eapply (H0 b); auto.
Qed.

Lemma zip_pure_eq2 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → pure Γ₂ → Γ₁ = Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0. induction H; auto.
Case "T". f_equal. apply IHzip. intros a Ha. eapply (H0 a); auto.
Case "U". f_equal. apply IHzip. intros b Hb. eapply (H0 b); auto.
Case "UE". f_equal. apply IHzip. intros b Hb. eapply (H0 b); auto.
Case "E". elimtype False. eapply (H0 a); auto.
Case "Eq". f_equal. apply IHzip. intros b Hb. eapply (H0 b); auto.
Qed.

Lemma pure_renameU : forall Γ₁ Γ₂ a b,
  pure (Γ₁ ++ a ~ U ++ Γ₂) →
  pure (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ U ++ Γ₂).
Proof.
intros Γ₁ Γ₂ a b H.
unfold env_map.
intros a0 H0.
replace (@U typ) with (tag_map (tsubst_typ (typ_var_f b) a) U) in H0 by reflexivity.
eapply (H a0). analyze_binds H0; eauto with lngen.
Qed.
