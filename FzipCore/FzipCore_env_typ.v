Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_zip.
Require Import FzipCore_pure.
Require Import FzipCore_weakenU.

Scheme wfenv_mut_ind_aux := Induction for wfenv Sort Prop
with   wftyp_mut_ind_aux := Induction for wftyp Sort Prop.
Combined Scheme wfenv_wftyp_mut_ind from
  wfenv_mut_ind_aux, wftyp_mut_ind_aux.

(** Administrative lemmas *)
Lemma wftyp_regular : forall Γ τ, wftyp Γ τ → lc_typ τ.
Proof.
intros Γ τ H.
induction H; eauto.
Qed.
Hint Resolve wftyp_regular : lngen.

Lemma wfenv_wftyp_aux :
  (forall Γ, wfenv Γ → forall Γ₁ x b τ, Γ = x ~ b ++ Γ₁ ->
    (b = T τ ∨ b = Eq τ) → wftyp Γ₁ τ) ∧
  (forall Γ τ, wftyp Γ τ → wfenv Γ).
Proof.
apply wfenv_wftyp_mut_ind; intros; eauto.
inversion H.
inversion H0; destruct H1; congruence.
inversion H0; destruct H1; congruence.
inversion H0; destruct H1; congruence.
inversion H0; destruct H1; congruence.
pick fresh a; assert (a ~ U ++ G ⊢ ok) by auto; inversion H0; subst; auto.
pick fresh a; assert (a ~ U ++ G ⊢ ok) by auto; inversion H0; subst; auto.
Qed.

Lemma wfenv_wftyp_T :
forall Γ₁ Γ₂ x τ, wfenv (Γ₁ ++ x ~ T τ ++ Γ₂) → wftyp Γ₂ τ.
Proof.
destruct wfenv_wftyp_aux as [H1 H2].
intros Γ₁ Γ₂ x τ H0.
generalize dependent Γ₂.
induction Γ₁; intros; simpl_env in H0; eauto.
inversion H0; subst; simpl_env in H5; eauto.
Qed.

Lemma wfenv_wftyp_Eq :
forall Γ₁ Γ₂ x τ, wfenv (Γ₁ ++ x ~ Eq τ ++ Γ₂) → wftyp Γ₂ τ.
Proof.
destruct wfenv_wftyp_aux as [H1 H2].
intros Γ₁ Γ₂ x τ H0.
generalize dependent Γ₂.
induction Γ₁; intros; simpl_env in H0; eauto.
inversion H0; subst; simpl_env in H5; eauto.
Qed.
Hint Resolve wfenv_wftyp_T wfenv_wftyp_Eq: fzip.


Lemma wftyp_wfenv : forall Γ τ, wftyp Γ τ → wfenv Γ.
Proof.
destruct wfenv_wftyp_aux; auto.
Qed.
Hint Resolve wftyp_wfenv: fzip.

Lemma wfenv_wftyp_uniq_aux :
  (forall Γ, wfenv Γ → uniq Γ) ∧ (forall Γ τ, wftyp Γ τ → uniq Γ).
Proof.
apply wfenv_wftyp_mut_ind; intros; auto.
pick fresh a. assert (uniq (a ~ U ++ G)) by auto. destruct_uniq; auto.
pick fresh a. assert (uniq (a ~ U ++ G)) by auto. destruct_uniq; auto.
Qed.

Lemma wfenv_uniq : forall Γ, wfenv Γ → uniq Γ.
Proof.
destruct wfenv_wftyp_uniq_aux; auto.
Qed.
Hint Resolve wfenv_uniq: lngen.

Lemma wftyp_uniq :  forall Γ τ, wftyp Γ τ → uniq Γ.
Proof.
eauto with lngen fzip.
Qed.
Hint Resolve wftyp_uniq: lngen.


(** Lemmas about [wfenv] and [wftyp] *)
Lemma wfenv_wftyp_weakening :
(forall Γ, wfenv Γ → forall Γ₁ Γ₂ Γ₃, Γ = Γ₁ ++ Γ₃ → wfenv (Γ₂ ++ Γ₃) → disjoint Γ₁ Γ₂ → wfenv (Γ₁ ++ Γ₂ ++ Γ₃))
∧
(forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ Γ₃, Γ = Γ₁ ++ Γ₃ → wfenv (Γ₂ ++ Γ₃) → disjoint Γ₁ Γ₂ → wftyp (Γ₁ ++ Γ₂ ++ Γ₃) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; auto.
Case "wfenv_empty".
destruct Γ₁. destruct Γ₃. simpl_env in *; auto.
simpl in H; inversion H.
simpl in H; inversion H.
Case "wfenv_cons_T".
destruct Γ₁; simpl_env in *.
destruct Γ₃; simpl_env in *; auto.
inversion H0; subst.
apply wfenv_cons_T.
simpl in H2; apply disjoint_cons_1 in H2; auto.
apply H; auto.
simpl in H2; apply disjoint_cons_2 in H2; auto.
Case "wfenv_cons_U".
destruct Γ₁; simpl_env in *.
destruct Γ₃; simpl_env in *; auto.
inversion H0; subst.
apply wfenv_cons_U.
simpl in H2; apply disjoint_cons_1 in H2; auto.
apply H; auto.
simpl in H2; apply disjoint_cons_2 in H2; auto.
Case "wfenv_cons_E".
destruct Γ₁; simpl_env in *.
destruct Γ₃; simpl_env in *; auto.
inversion H0; subst.
apply wfenv_cons_E.
simpl in H2; apply disjoint_cons_1 in H2; auto.
apply H; auto.
simpl in H2; apply disjoint_cons_2 in H2; auto.
Case "wfenv_cons_Eq".
destruct Γ₁; simpl_env in *.
destruct Γ₃; simpl_env in *; auto.
inversion H0; subst.
apply wfenv_cons_Eq.
simpl in H2; apply disjoint_cons_1 in H2; auto.
apply H; auto.
simpl in H2; apply disjoint_cons_2 in H2; auto.
Case "wftyp_var".
subst G.
  destruct o. auto.
  destruct H0. auto.
  destruct H0. apply wftyp_var; auto; right; right; eauto.
Case "wftyp_forall".
subst G; apply wftyp_forall with (L := L ∪ dom Γ₂); intros.
rewrite_env ((a~U ++ Γ₁) ++ Γ₂ ++ Γ₃); apply H; eauto.
Case "wftyp_exists".
subst G; apply wftyp_exists with (L := L ∪ dom Γ₂); intros.
rewrite_env ((a~U ++ Γ₁) ++ Γ₂ ++ Γ₃); apply H; eauto.
Qed.

Lemma wfenv_weakening :
forall Γ₁ Γ₂ Γ₃, wfenv (Γ₁ ++ Γ₃) → wfenv (Γ₂ ++ Γ₃) → disjoint Γ₁ Γ₂ → wfenv (Γ₁ ++ Γ₂ ++ Γ₃).
Proof.
destruct wfenv_wftyp_weakening as [H1 H2].
intros; apply (H1 (Γ₁ ++ Γ₃)); auto.
Qed.

Lemma wftyp_weakening :
forall Γ₁ Γ₂ Γ₃ τ, wftyp (Γ₁ ++ Γ₃) τ → wfenv (Γ₂ ++ Γ₃) → disjoint Γ₁ Γ₂ → wftyp (Γ₁ ++ Γ₂ ++ Γ₃) τ.
Proof.
destruct wfenv_wftyp_weakening as [H1 H2].
intros. apply (H2 (Γ₁ ++ Γ₃)); auto.
Qed.
Hint Resolve wfenv_weakening wftyp_weakening: fzip.

Lemma wfenv_wftyp_weakenU :
(forall Γ, wfenv Γ → forall Γ', weakenU Γ' Γ → wfenv Γ')
∧
(forall Γ τ, wftyp Γ τ → forall Γ', weakenU Γ' Γ → wftyp Γ' τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; auto.
Case "nil". induction Γ'; auto; destruct a; destruct t; simpl_env in *;
inversion H; subst; auto.
Case "T". induction Γ'; auto; destruct a; destruct t0; simpl_env in *;
inversion H0; subst; auto.
Case "U". induction Γ'; auto; destruct a0; destruct t; simpl_env in *;
inversion H0; subst; auto.
Case "E". induction Γ'; auto; destruct a0; destruct t; simpl_env in *;
inversion H0; subst; auto.
Case "T". induction Γ'; auto; destruct a0; destruct t0; simpl_env in *;
inversion H0; subst; auto.
Case "var". constructor; auto. intuition eauto with fzip.
destruct H2; eauto with fzip.
Case "forall". pick fresh a and apply wftyp_forall. auto.
Case "exists". pick fresh a and apply wftyp_exists. auto.
Qed.

Lemma wfenv_weakenU : forall Γ Γ',
  wfenv Γ → weakenU Γ' Γ → wfenv Γ'.
Proof.
intros; edestruct wfenv_wftyp_weakenU; eauto.
Qed.

Lemma wftyp_weakenU : forall Γ Γ' τ,
  wftyp Γ τ → weakenU Γ' Γ → wftyp Γ' τ.
Proof.
intros; edestruct wfenv_wftyp_weakenU; eauto.
Qed.

Lemma wfenv_wftyp_T2 :
forall Γ x τ, wfenv Γ → binds x (T τ) Γ → wftyp Γ τ.
Proof.
intro Γ; induction Γ; intros.
analyze_binds H0.
destruct a; destruct t; simpl_env in *; analyze_binds H0.
Case "T =".
replace t with τ in * by congruence.
rewrite_env (nil ++ a ~ T τ ++ Γ).
inversion H; subst.
apply wftyp_weakening; auto.
Case "T ≠".
rewrite_env (nil ++ a ~ T t ++ Γ).
apply wftyp_weakening; auto. simpl.
inversion H; subst. eapply IHΓ; eauto with fzip.
Case "U".
rewrite_env (nil ++ a ~ U ++ Γ).
apply wftyp_weakening; auto.
inversion H; subst. eapply IHΓ; eauto.
Case "E".
rewrite_env (nil ++ a ~ E ++ Γ).
apply wftyp_weakening; auto.
inversion H; subst. eapply IHΓ; eauto.
Case "Eq".
rewrite_env (nil ++ a ~ Eq t ++ Γ).
apply wftyp_weakening; auto. simpl.
inversion H; subst. eapply IHΓ; eauto with fzip.
Qed.

Lemma wfenv_wftyp_Eq2 :
forall Γ x τ, wfenv Γ → binds x (Eq τ) Γ → wftyp Γ τ.
Proof.
intro Γ; induction Γ; intros.
analyze_binds H0.
destruct a; destruct t; simpl_env in *; analyze_binds H0.
Case "T".
rewrite_env (nil ++ a ~ T t ++ Γ).
apply wftyp_weakening; auto. simpl.
inversion H; subst. eapply IHΓ; eauto with fzip.
Case "U".
rewrite_env (nil ++ a ~ U ++ Γ).
apply wftyp_weakening; auto.
inversion H; subst. eapply IHΓ; eauto.
Case "E".
rewrite_env (nil ++ a ~ E ++ Γ).
apply wftyp_weakening; auto.
inversion H; subst. eapply IHΓ; eauto.
Case "Eq =".
replace t with τ in * by congruence.
rewrite_env (nil ++ a ~ Eq τ ++ Γ).
inversion H; subst.
apply wftyp_weakening; auto.
Case "Eq ≠".
rewrite_env (nil ++ a ~ Eq t ++ Γ).
apply wftyp_weakening; auto. simpl.
inversion H; subst. eapply IHΓ; eauto with fzip.
Qed.
Hint Resolve wfenv_wftyp_T2 wfenv_wftyp_Eq2: fzip.

Lemma wfenv_wftyp_T3 :
forall Γ x τ, wfenv (x ~ T τ ++ Γ) → wftyp Γ τ.
Proof.
intros Γ x τ H; inversion H; subst; auto.
Qed.

Lemma wfenv_wftyp_Eq3 :
forall Γ x τ, wfenv (x ~ Eq τ ++ Γ) → wftyp Γ τ.
Proof.
intros Γ x τ H; inversion H; subst; auto.
Qed.
Hint Resolve wfenv_wftyp_T3 wfenv_wftyp_Eq3: fzip.

Lemma wfenv_regular_T :
forall Γ x τ, wfenv Γ → binds x (T τ) Γ → lc_typ τ.
Proof.
intros. induction H; analyze_binds H0.
replace t with τ in * by congruence; eauto with lngen.
eauto with lngen fzip.
eauto with lngen fzip.
Qed.

Lemma wfenv_regular_Eq :
forall Γ x τ, wfenv Γ → binds x (Eq τ) Γ → lc_typ τ.
Proof.
intros. induction H; analyze_binds H0.
eauto with lngen fzip.
replace t with τ in * by congruence; eauto with lngen.
eauto with lngen fzip.
Qed.

Lemma wfenv_lc_env :
forall Γ, wfenv Γ → lc_env Γ.
Proof.
intros. split; intros; eauto using wfenv_regular_T, wfenv_regular_Eq.
Qed.
Hint Resolve wfenv_regular_T wfenv_regular_Eq: lngen.

Lemma wftyp_regular_T2 : forall Γ x τ τ',
  wftyp (x ~ T τ ++ Γ) τ' → lc_typ τ.
Proof.
intros Γ x τ τ' H. eauto with lngen fzip.
Qed.

Lemma wftyp_regular_Eq2 : forall Γ x τ τ',
  wftyp (x ~ Eq τ ++ Γ) τ' → lc_typ τ.
Proof.
intros Γ x τ τ' H. eauto with lngen fzip.
Qed.

Lemma wftyp_lc_env : forall Γ τ,
  wftyp Γ τ → lc_env Γ.
Proof.
intros Γ τ H. apply wfenv_lc_env. eauto with fzip.
Qed.
Hint Resolve wftyp_regular_T2 wftyp_regular_Eq2: lngen.

Lemma wfenv_wftyp_subst :
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ x τ, Γ = Γ₁ ++ x ~ (T τ) ++ Γ₂ → wfenv (Γ₁ ++ Γ₂)) ∧
  (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ x τ', Γ = Γ₁ ++ x ~ (T τ') ++ Γ₂ → wftyp (Γ₁ ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros.
Case "wfenv_empty".
assert (binds x (T τ) nil). rewrite H; auto. analyze_binds H0.
Case "wfenv_T".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto with fzip.
destruct p; destruct t; inversion H0; subst; simpl_env in *;
constructor; eauto.
Case "wfenv_cons_U".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
destruct p; destruct t; inversion H0; subst; simpl_env in *;
constructor; eauto.
Case "wfenv_cons_E".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
destruct p; destruct t; inversion H0; subst; simpl_env in *;
constructor; eauto.
Case "wfenv_Eq".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
destruct p; destruct t; inversion H0; subst; simpl_env in *;
constructor; eauto.
Case "wftyp_var".
subst G. constructor; eauto.
  destruct o. analyze_binds H0.
  destruct H0. analyze_binds H0.
  destruct H0. analyze_binds H0; eauto.
Case "wftyp_arrow".
subst G. constructor; eauto.
Case "wftyp_prod".
subst G. constructor; eauto.
Case "wftyp_forall".
subst G. econstructor; intros.
rewrite_env (([(a, U)] ++ Γ₁) ++ Γ₂). eapply H; simpl_env; eauto.
Case "wftyp_exists".
subst G. econstructor; intros.
rewrite_env (([(a, U)] ++ Γ₁) ++ Γ₂). eapply H; simpl_env; eauto.
Qed.

Lemma wfenv_subst :
forall Γ₁ Γ₂ x τ, wfenv (Γ₁ ++ x ~ (T τ) ++ Γ₂) → wfenv (Γ₁ ++ Γ₂).
Proof.
destruct wfenv_wftyp_subst as [H1 H2].
intros Γ₁ Γ₂ x τ H. eapply H1; eauto.
Qed.

Lemma wftyp_subst :
forall Γ₁ Γ₂ τ x τ', wftyp (Γ₁ ++ x ~ (T τ') ++ Γ₂) τ → wftyp (Γ₁ ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_subst as [H1 H2].
intros. eapply H2; eauto.
Qed.
Hint Resolve wfenv_subst wftyp_subst: fzip.

Lemma wfenv_wftyp_instantiate :
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ a τ, Γ = Γ₁ ++ a ~ U ++ Γ₂ → wftyp Γ₂ τ → wfenv (Γ₁ ++ a ~ Eq τ ++ Γ₂)) ∧
  (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ a τ', Γ = Γ₁ ++ a ~ U ++ Γ₂ → wftyp Γ₂ τ' → wftyp (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros.
Case "wfenv_empty".
assert (binds a (@U typ) nil). rewrite H; auto. analyze_binds H1.
Case "wfenv_cons_T".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
destruct p; destruct t0; inversion H0; subst; auto.
Case "wfenv_cons_U".
destruct Γ₁; simpl_env in *.
inversion H0; subst; auto.
destruct p; destruct t; inversion H0; subst; auto.
Case "wfenv_cons_E".
destruct Γ₁; simpl_env in *.
inversion H0; subst; auto.
destruct p; destruct t; inversion H0; subst; auto.
Case "wfenv_cons_Eq".
destruct Γ₁; simpl_env in *.
inversion H0; subst; auto.
destruct p; destruct t; inversion H0; subst; auto.
Case "wftyp_var".
subst G.
destruct (a == a0); subst.
SCase "a = a0".
constructor; auto.
right; right; eauto.
SCase "a ≠ a0".
constructor; auto.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0.
destruct H0. right; right; exists x. analyze_binds H0.
Case "wftyp_arrow".
subst G. constructor; auto.
Case "wftyp_prod".
subst G. constructor; auto.
Case "wftyp_forall".
subst G. apply wftyp_forall with (L := L ∪ {{a}}); intros.
rewrite_env (([(a0, U)] ++ Γ₁) ++ a ~ Eq τ' ++ Γ₂); auto.
Case "wftyp_exists".
subst G. apply wftyp_exists with (L := L ∪ {{a}}); intros.
rewrite_env (([(a0, U)] ++ Γ₁) ++ a ~ Eq τ' ++ Γ₂); auto.
Qed.

Lemma wfenv_instantiate :
  forall Γ₁ Γ₂ a τ, wfenv (Γ₁ ++ a ~ U ++ Γ₂) → wftyp Γ₂ τ →
    wfenv (Γ₁ ++ a ~ Eq τ ++ Γ₂).
Proof.
destruct wfenv_wftyp_instantiate as [H1 H2].
intros Γ₁ Γ₂ x τ H. eapply H1; eauto.
Qed.

Lemma wftyp_instantiate :
forall Γ₁ Γ₂ τ a τ', wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ →
wftyp Γ₂ τ' → wftyp (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_instantiate as [H1 H2].
intros. eapply H2; eauto.
Qed.
Hint Resolve wfenv_instantiate wftyp_instantiate: fzip.

Lemma wfenv_strip :
forall Γ' Γ, wfenv (Γ' ++ Γ) -> wfenv Γ.
Proof.
intro Γ'; induction Γ'; intros; auto.
apply IHΓ'.
simpl_env in H.
inversion H; subst; auto.
eauto using wftyp_wfenv.
eauto using wftyp_wfenv.
Qed.

Lemma wfenv_wftyp_subst_eq :
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ a τ, Γ = Γ₁ ++ a ~ Eq τ ++ Γ₂ → wfenv ((env_map (tsubst_typ τ a) Γ₁) ++ Γ₂)) ∧
  (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ a τ', Γ = Γ₁ ++ a ~ Eq τ' ++ Γ₂ → wftyp ((env_map (tsubst_typ τ' a) Γ₁) ++ Γ₂) (tsubst_typ τ' a τ)).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst.
Case "wfenv_empty".
assert (binds a (Eq τ) nil). rewrite H; auto. analyze_binds H0.
Case "wfenv_cons_T".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
destruct p; destruct t0; inversion H0; subst; simpl_env in *;
simpl; simpl_env; constructor; auto.
unfold env_map; auto.
Case "wfenv_cons_U".
destruct Γ₁; simpl_env in *.
inversion H0.
destruct p; destruct t; inversion H0; subst; simpl_env in *.
simpl; simpl_env; constructor. unfold env_map; auto. eauto.
Case "wfenv_cons_E".
destruct Γ₁; simpl_env in *.
inversion H0.
destruct p; destruct t; inversion H0; subst; simpl_env in *.
simpl; simpl_env; constructor. unfold env_map; auto. eauto.
Case "wfenv_cons_Eq".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto with fzip.
destruct p; destruct t0; inversion H0; subst; simpl_env in *;
simpl; simpl_env; constructor.
unfold env_map; auto. auto.
Case "wftyp_var". simpl; destruct (a == a0); subst.
SCase "a = a0".
rewrite_env (nil ++ env_map (tsubst_typ τ' a0) Γ₁ ++ Γ₂); apply wftyp_weakening; auto.
simpl_env. apply wfenv_wftyp_Eq3 with (x := a0).
eauto using wfenv_strip.
SCase "a ≠ a0".
constructor; auto.
destruct o.
analyze_binds H0;
replace (@U typ) with (tag_map (tsubst_typ τ' a0) U) by reflexivity;
unfold env_map; auto.
destruct H0.
analyze_binds H0;
replace (@E typ) with (tag_map (tsubst_typ τ' a0) E) by reflexivity;
unfold env_map; auto.
destruct H0.
right; right. analyze_binds H0; eauto.
exists (tsubst_typ τ' a0 x).
replace (Eq (tsubst_typ τ' a0 x)) with (tag_map (tsubst_typ τ' a0) (Eq x)) by reflexivity;
unfold env_map; auto.
Case "wftyp_arrow".
simpl; constructor; auto.
Case "wftyp_prod".
simpl; constructor; auto.
Case "wftyp_forall".
simpl; apply wftyp_forall with (L := L ∪ {{a}}); intros.
rewrite_env (([(a0, U)] ++ env_map (tsubst_typ τ' a) Γ₁) ++ Γ₂).
replace ([(a0, U)] ++ env_map (tsubst_typ τ' a) Γ₁) with (env_map (tsubst_typ τ' a) ([(a0, U)] ++ Γ₁)) by reflexivity.
replace (typ_var_f a0) with (tsubst_typ τ' a (typ_var_f a0)).
rewrite <- tsubst_typ_open_typ_wrt_typ.
eapply H; simpl_env; eauto. eauto with lngen fzip.
autorewrite with lngen; auto.
Case "wftyp_exists".
simpl; apply wftyp_exists with (L := L ∪ {{a}}); intros.
rewrite_env (([(a0, U)] ++ env_map (tsubst_typ τ' a) Γ₁) ++ Γ₂).
replace ([(a0, U)] ++ env_map (tsubst_typ τ' a) Γ₁) with (env_map (tsubst_typ τ' a) ([(a0, U)] ++ Γ₁)) by reflexivity.
replace (typ_var_f a0) with (tsubst_typ τ' a (typ_var_f a0)).
rewrite <- tsubst_typ_open_typ_wrt_typ.
eapply H; simpl_env; eauto. eauto with lngen fzip.
autorewrite with lngen; auto.
Qed.

Lemma wfenv_subst_eq :
  forall Γ₁ Γ₂ a τ, wfenv (Γ₁ ++ a ~ Eq τ ++ Γ₂) →
    wfenv (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂).
Proof.
destruct wfenv_wftyp_subst_eq as [H1 H2]. intros; eauto.
Qed.

Lemma wftyp_subst_eq :
forall Γ₁ Γ₂ τ a τ', wftyp (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ →
wftyp (env_map (tsubst_typ τ' a) Γ₁ ++ Γ₂) (tsubst_typ τ' a τ).
Proof.
destruct wfenv_wftyp_subst_eq as [H1 H2]. intros; eauto.
Qed.
Hint Resolve wfenv_subst_eq wftyp_subst_eq: fzip.

Lemma wfenv_tsubst :
  forall Γ₁ Γ₂ a τ, wfenv (Γ₁ ++ a ~ U ++ Γ₂) → wftyp Γ₂ τ →
    wfenv (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂).
Proof.
intros; auto with fzip.
Qed.

Lemma wftyp_tsubst :
forall Γ₁ Γ₂ τ a τ', wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ →
wftyp Γ₂ τ' → wftyp (env_map (tsubst_typ τ' a) Γ₁ ++ Γ₂) (tsubst_typ τ' a τ).
Proof.
intros; auto with fzip.
Qed.
Hint Resolve wfenv_tsubst wftyp_tsubst: fzip.

Lemma wftyp_ftv : forall Γ τ, wftyp Γ τ → ftv_typ τ [<=] dom Γ.
Proof.
intros Γ τ H. induction H; simpl in *; try fsetdec.
Case "var".
assert (a ∈ dom G).
  destruct H; eauto. destruct H; eauto. destruct H; eauto.
fsetdec.
Case "forall".
pick fresh a.
assert (ftv_typ (open_typ_wrt_typ t (typ_var_f a))[<=]add a (dom G)) by auto.
assert (ftv_typ t [<=] ftv_typ (open_typ_wrt_typ t (typ_var_f a))); auto with lngen.
fsetdec.
Case "exists".
pick fresh a.
assert (ftv_typ (open_typ_wrt_typ t (typ_var_f a))[<=]add a (dom G)) by auto.
assert (ftv_typ t [<=] ftv_typ (open_typ_wrt_typ t (typ_var_f a))); auto with lngen.
fsetdec.
Qed.
Hint Resolve wftyp_ftv: fzip.

Lemma wftyp_T_not_ftv : forall Γ τ x τ',
  wftyp Γ τ → binds x (T τ') Γ → x ∉ ftv_typ τ.
Proof.
intros Γ τ x τ' H H0. induction H; simpl; auto.
Case "var". destruct (a == x); subst; auto.
assert (uniq G) by auto with lngen. elimtype False.
intuition.
  assert (T τ' = U). eapply binds_unique; eauto. congruence.
  assert (T τ' = E). eapply binds_unique; eauto. congruence.
  destruct H. assert (T τ' = Eq x0). eapply binds_unique; eauto. congruence.
Case "forall". pick fresh a.
assert (x ∉ ftv_typ (open_typ_wrt_typ t (typ_var_f a))) by eauto.
assert (ftv_typ t [<=] ftv_typ (open_typ_wrt_typ t (typ_var_f a))) by auto with lngen.
fsetdec.
Case "exists". pick fresh a.
assert (x ∉ ftv_typ (open_typ_wrt_typ t (typ_var_f a))) by eauto.
assert (ftv_typ t [<=] ftv_typ (open_typ_wrt_typ t (typ_var_f a))) by auto with lngen.
fsetdec.
Qed.
Hint Resolve wftyp_T_not_ftv.

Lemma wfenv_wftyp_UE_aux :
  (forall Γ, wfenv Γ ->
    forall Γ₁ a Γ₂, Γ = Γ₁ ++ a ~ U ++ Γ₂ ->
      wfenv (Γ₁ ++ a ~ E ++ Γ₂))
  ∧ (forall Γ τ, wftyp Γ τ ->
    forall Γ₁ a Γ₂, Γ = Γ₁ ++ a ~ U ++ Γ₂ ->
      wftyp (Γ₁ ++ a ~ E ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; auto.
assert (binds a (@U typ) nil). rewrite H; auto.
  analyze_binds H0.
destruct Γ₁; inversion H0; simpl_env in *.
  destruct p; destruct t0; inversion H2; subst.
  auto.
destruct Γ₁; inversion H0; simpl_env in *; subst; auto.
destruct Γ₁; inversion H0; simpl_env in *; subst; auto.
destruct Γ₁; inversion H0; simpl_env in *; subst; auto.
destruct (a == a0); subst.
  auto 7.
  constructor; auto. destruct o. analyze_binds H0.
    destruct H0. analyze_binds H0.
    destruct H0. right; right; exists x. analyze_binds H0.
apply wftyp_forall with (L := L ∪ {{a}}); intros.
  rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ E ++ Γ₂). auto.
apply wftyp_exists with (L := L ∪ {{a}}); intros.
  rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ E ++ Γ₂). auto.
Qed.

Lemma wfenv_wftyp_EU_aux :
  (forall Γ, wfenv Γ ->
    forall Γ₁ a Γ₂, Γ = Γ₁ ++ a ~ E ++ Γ₂ ->
      wfenv (Γ₁ ++ a ~ U ++ Γ₂))
  ∧ (forall Γ τ, wftyp Γ τ ->
    forall Γ₁ a Γ₂, Γ = Γ₁ ++ a ~ E ++ Γ₂ ->
      wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; auto.
assert (binds a (@E typ) nil). rewrite H; auto.
  analyze_binds H0.
destruct Γ₁; inversion H0; simpl_env in *.
  destruct p; destruct t0; inversion H2; subst.
  auto.
destruct Γ₁; inversion H0; simpl_env in *; subst; auto.
destruct Γ₁; inversion H0; simpl_env in *; subst; auto.
destruct Γ₁; inversion H0; simpl_env in *; subst; auto.
destruct (a == a0); subst.
  auto 7.
  constructor; auto. destruct o. analyze_binds H0.
    destruct H0. analyze_binds H0.
    destruct H0. right; right; exists x. analyze_binds H0.
apply wftyp_forall with (L := L ∪ {{a}}); intros.
  rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ U ++ Γ₂). auto.
apply wftyp_exists with (L := L ∪ {{a}}); intros.
  rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ U ++ Γ₂). auto.
Qed.

Lemma wfenv_wftyp_EqU_aux :
  (forall Γ, wfenv Γ ->
    forall Γ₁ a Γ₂ τ', Γ = Γ₁ ++ a ~ Eq τ' ++ Γ₂ ->
      wfenv (Γ₁ ++ a ~ U ++ Γ₂))
  ∧ (forall Γ τ, wftyp Γ τ ->
    forall Γ₁ a Γ₂ τ', Γ = Γ₁ ++ a ~ Eq τ' ++ Γ₂ ->
      wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; eauto.
Case "nil". assert (binds a (Eq τ') nil). rewrite H; auto. analyze_binds H0.
Case "T". destruct Γ₁; inversion H0; simpl_env in *; subst; eauto.
Case "U". destruct Γ₁; inversion H0; simpl_env in *; subst; eauto.
Case "E". destruct Γ₁; inversion H0; simpl_env in *; subst; eauto.
Case "Eq".
destruct Γ₁; inversion H0; simpl_env in *; subst; eauto.
  constructor; eauto with fzip.
Case "var". constructor; eauto.
  destruct o. analyze_binds H0.
  destruct H0. analyze_binds H0.
  destruct H0. analyze_binds H0; eauto 6.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}}); intros.
  rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ U ++ Γ₂). eapply H; simpl_env; eauto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}}); intros.
  rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ U ++ Γ₂). eapply H; simpl_env; eauto.
Qed.

Lemma wfenv_UE :
  forall Γ₁ a Γ₂, wfenv (Γ₁ ++ a ~ U ++ Γ₂) -> wfenv (Γ₁ ++ a ~ E ++ Γ₂).
Proof.
destruct wfenv_wftyp_UE_aux as [H _]. intros; eauto.
Qed.

Lemma wfenv_EU :
  forall Γ₁ a Γ₂, wfenv (Γ₁ ++ a ~ E ++ Γ₂) -> wfenv (Γ₁ ++ a ~ U ++ Γ₂).
Proof.
destruct wfenv_wftyp_EU_aux as [H _]. intros; eauto.
Qed.

Lemma wfenv_EqU :
  forall Γ₁ a Γ₂ τ, wfenv (Γ₁ ++ a ~ Eq τ ++ Γ₂) -> wfenv (Γ₁ ++ a ~ U ++ Γ₂).
Proof.
destruct wfenv_wftyp_EqU_aux as [H _]. intros; eauto.
Qed.

Lemma wftyp_UE :
  forall Γ₁ a Γ₂ τ, wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ -> wftyp (Γ₁ ++ a ~ E ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_UE_aux as [_ H]. intros; eauto.
Qed.

Lemma wftyp_EU :
  forall Γ₁ a Γ₂ τ, wftyp (Γ₁ ++ a ~ E ++ Γ₂) τ -> wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_EU_aux as [_ H]. intros; eauto.
Qed.

Lemma wftyp_EqU :
  forall Γ₁ a Γ₂ τ τ', wftyp (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ -> wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_EqU_aux as [_ H]. intros; eauto.
Qed.
Hint Resolve wfenv_UE wfenv_EU wfenv_EqU wftyp_UE wftyp_EU wftyp_EqU: fzip.

(** Renaming lemmas *)
Lemma wfenv_wftyp_renameU_aux:
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ a b,
    Γ = Γ₁ ++ a ~ U ++ Γ₂ →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wfenv (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ U ++ Γ₂))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ a b,
    Γ = Γ₁ ++ a ~ U ++ Γ₂ →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wftyp (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ U ++ Γ₂) (tsubst_typ (typ_var_f b) a τ)).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; simpl; simpl_env; eauto.
Case "nil".
assert (binds a (@U typ) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *.
constructor. unfold env_map; auto. eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor. unfold env_map; auto. eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor. unfold env_map; auto. eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *.
constructor. unfold env_map; auto. eauto.
Case "var". destruct (a == a0); subst; constructor; simpl_env in *; auto 6.
unfold env_map.
destruct o. replace (@U typ) with (tag_map (tsubst_typ (typ_var_f b) a0) U) by reflexivity.
  analyze_binds H0.
destruct H0. replace (@E typ) with (tag_map (tsubst_typ (typ_var_f b) a0) E) by reflexivity.
  analyze_binds H0.
destruct H0. right; right.
  analyze_binds H0; eauto.
  exists (tsubst_typ (typ_var_f b) a0 x).
  replace (Eq (tsubst_typ (typ_var_f b) a0 x)) with
  (tag_map (tsubst_typ (typ_var_f b) a0) (Eq x)) by reflexivity.
  auto.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}} ∪ {{b}}); intros.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) (a0 ~ U ++ Γ₁)) ++ b ~ U ++ Γ₂). rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}} ∪ {{b}}); intros.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) (a0 ~ U ++ Γ₁)) ++ b ~ U ++ Γ₂). rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
Qed.

Lemma wfenv_renameU:
  forall Γ₁ Γ₂ a b,
    wfenv (Γ₁ ++ a ~ U ++ Γ₂) →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wfenv (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ U ++ Γ₂).
Proof.
destruct wfenv_wftyp_renameU_aux as [H _]. intros. eapply H; eauto.
Qed.

Lemma wftyp_renameU:
  forall Γ₁ Γ₂ τ a b,
    wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wftyp (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ U ++ Γ₂) (tsubst_typ (typ_var_f b) a τ).
Proof.
destruct wfenv_wftyp_renameU_aux as [_ H]. intros. eapply H; eauto.
Qed.

Lemma wfenv_wftyp_renameE_aux:
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ a b,
    Γ = Γ₁ ++ a ~ E ++ Γ₂ →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wfenv (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ E ++ Γ₂))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ a b,
    Γ = Γ₁ ++ a ~ E ++ Γ₂ →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wftyp (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ E ++ Γ₂) (tsubst_typ (typ_var_f b) a τ)).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; simpl; simpl_env; eauto.
Case "nil".
assert (binds a (@E typ) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *.
constructor. unfold env_map; auto. eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *.
constructor. unfold env_map; auto. eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor. unfold env_map; auto. eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *.
constructor. unfold env_map; auto. eauto.
Case "var". destruct (a == a0); subst; constructor; simpl_env in *; auto 6.
unfold env_map.
destruct o. replace (@U typ) with (tag_map (tsubst_typ (typ_var_f b) a0) U) by reflexivity.
  analyze_binds H0.
destruct H0. replace (@E typ) with (tag_map (tsubst_typ (typ_var_f b) a0) E) by reflexivity.
  analyze_binds H0.
destruct H0. right; right.
  analyze_binds H0; eauto.
  exists (tsubst_typ (typ_var_f b) a0 x).
  replace (Eq (tsubst_typ (typ_var_f b) a0 x)) with
  (tag_map (tsubst_typ (typ_var_f b) a0) (Eq x)) by reflexivity.
  auto.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}} ∪ {{b}}); intros.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) (a0 ~ U ++ Γ₁)) ++ b ~ E ++ Γ₂). rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}} ∪ {{b}}); intros.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) (a0 ~ U ++ Γ₁)) ++ b ~ E ++ Γ₂). rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
Qed.

Lemma wfenv_renameE:
  forall Γ₁ Γ₂ a b,
    wfenv (Γ₁ ++ a ~ E ++ Γ₂) →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wfenv (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ E ++ Γ₂).
Proof.
destruct wfenv_wftyp_renameE_aux as [H _]. intros. eapply H; eauto.
Qed.

Lemma wftyp_renameE:
  forall Γ₁ Γ₂ τ a b,
    wftyp (Γ₁ ++ a ~ E ++ Γ₂) τ →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wftyp (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ E ++ Γ₂) (tsubst_typ (typ_var_f b) a τ).
Proof.
destruct wfenv_wftyp_renameE_aux as [_ H]. intros. eapply H; eauto.
Qed.

Lemma wfenv_wftyp_renameEq_aux:
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ a b τ,
    Γ = Γ₁ ++ a ~ Eq τ ++ Γ₂ →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wfenv (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ Eq τ ++ Γ₂))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ a b τ',
    Γ = Γ₁ ++ a ~ Eq τ' ++ Γ₂ →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wftyp (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ Eq τ' ++ Γ₂) (tsubst_typ (typ_var_f b) a τ)).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; simpl; simpl_env; eauto.
Case "nil".
assert (binds a (Eq τ) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *.
constructor. unfold env_map; auto. eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor. unfold env_map; auto. eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor. unfold env_map; auto. eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor. unfold env_map; auto. eauto.
Case "var". destruct (a == a0); subst; constructor; simpl_env in *; eauto 7.
unfold env_map.
destruct o. replace (@U typ) with (tag_map (tsubst_typ (typ_var_f b) a0) U) by reflexivity.
  analyze_binds H0.
destruct H0. replace (@E typ) with (tag_map (tsubst_typ (typ_var_f b) a0) E) by reflexivity.
  analyze_binds H0.
destruct H0. right; right.
  analyze_binds H0; eauto.
  exists (tsubst_typ (typ_var_f b) a0 x).
  replace (Eq (tsubst_typ (typ_var_f b) a0 x)) with
  (tag_map (tsubst_typ (typ_var_f b) a0) (Eq x)) by reflexivity.
  auto.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}} ∪ {{b}}); intros.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) (a0 ~ U ++ Γ₁)) ++ b ~ Eq τ' ++ Γ₂). rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}} ∪ {{b}}); intros.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) (a0 ~ U ++ Γ₁)) ++ b ~ Eq τ' ++ Γ₂). rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
Qed.

Lemma wfenv_renameEq:
  forall Γ₁ Γ₂ a b τ,
    wfenv (Γ₁ ++ a ~ Eq τ ++ Γ₂) →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wfenv (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ Eq τ ++ Γ₂).
Proof.
destruct wfenv_wftyp_renameEq_aux as [H _]. intros. eapply H; eauto.
Qed.

Lemma wftyp_renameEq:
  forall Γ₁ Γ₂ τ a b τ',
    wftyp (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ →
    b ∉ dom (Γ₂ ++ Γ₁) →
    wftyp (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ Eq τ' ++ Γ₂) (tsubst_typ (typ_var_f b) a τ).
Proof.
destruct wfenv_wftyp_renameEq_aux as [_ H]. intros. eapply H; eauto.
Qed.

(** Swapping in the context *)
Lemma wfenv_wftyp_upperE_aux:
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ Γ₃ a,
    Γ = Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃ →
    wfenv (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ Γ₃ a,
    Γ = Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃ →
    wftyp (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; auto.
Case "nil".
assert (binds a (@E typ) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
eapply wfenv_weakening; auto. apply wfenv_strip in w; auto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "var". constructor; simpl_env in *; auto 6.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0; auto 7.
destruct H0. analyze_binds H0; eauto 7.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ Γ₂ ++ a ~ E ++ Γ₃). eauto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ Γ₂ ++ a ~ E ++ Γ₃). eauto.
Qed.

Lemma wfenv_wftyp_lowerE_aux:
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ Γ₃ a,
    Γ = Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃ → a ∉ ftv_env Γ₂ →
    wfenv (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ Γ₃ a,
    Γ = Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃ → a ∉ ftv_env Γ₂ →
    wftyp (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; auto.
Case "nil".
assert (binds a (@E typ) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *; auto.
destruct Γ₂; inversion H0; subst; simpl_env in *.
constructor.
assert (uniq (Γ₂ ++ [(a, E)] ++ Γ₃)) by eauto with lngen. solve_uniq.
constructor; auto.
rewrite ftv_env_app in *|-. unfold ftv_env at 1 in H1; simpl in H1.
rewrite <- tsubst_env_fresh_eq with (G := Γ₂) (a := a) (t := typ_forall (typ_var_b 0)); auto.
rewrite <- tsubst_typ_fresh_eq with (t2 := t) (a1 := a) (t1 := typ_forall (typ_var_b 0)); auto.
apply wftyp_tsubst. apply wftyp_EU; auto.
apply wftyp_forall with (L := dom Γ₃); intros.
unfold open_typ_wrt_typ; simpl; simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ₂ ++ [(a, E)]). simpl_env. eauto with fzip.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *; auto.
destruct Γ₂; inversion H0; subst; simpl_env in *.
constructor.
assert (uniq (Γ₂ ++ [(a0, E)] ++ Γ₃)) by eauto with lngen. solve_uniq.
constructor; auto.
rewrite ftv_env_app in *|-.
rewrite <- tsubst_env_fresh_eq with (G := Γ₂) (a := a0) (t := typ_forall (typ_var_b 0)); auto.
apply wfenv_tsubst. apply wfenv_EU; auto.
apply wftyp_forall with (L := dom Γ₃); intros.
unfold open_typ_wrt_typ; simpl; simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ₂ ++ [(a0, E)]). simpl_env. eauto with fzip.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *; auto.
destruct Γ₂; inversion H0; subst; simpl_env in *; auto.
constructor.
assert (uniq (Γ₂ ++ [(a0, E)] ++ Γ₃)) by eauto with lngen. solve_uniq.
constructor; auto.
rewrite ftv_env_app in *|-.
rewrite <- tsubst_env_fresh_eq with (G := Γ₂) (a := a0) (t := typ_forall (typ_var_b 0)); auto.
apply wfenv_tsubst. apply wfenv_EU; auto.
apply wftyp_forall with (L := dom Γ₃); intros.
unfold open_typ_wrt_typ; simpl; simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ₂ ++ [(a0, E)]). simpl_env. eauto with fzip.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *; auto.
destruct Γ₂; inversion H0; subst; simpl_env in *.
constructor.
assert (uniq (Γ₂ ++ [(a0, E)] ++ Γ₃)) by eauto with lngen. solve_uniq.
constructor; auto.
rewrite ftv_env_app in *|-. unfold ftv_env at 1 in H1; simpl in H1.
rewrite <- tsubst_env_fresh_eq with (G := Γ₂) (a := a0) (t := typ_forall (typ_var_b 0)); auto.
rewrite <- tsubst_typ_fresh_eq with (t2 := t) (a1 := a0) (t1 := typ_forall (typ_var_b 0)); auto.
apply wftyp_tsubst. apply wftyp_EU; auto.
apply wftyp_forall with (L := dom Γ₃); intros.
unfold open_typ_wrt_typ; simpl; simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ₂ ++ [(a0, E)]). simpl_env. eauto with fzip.
Case "var". constructor; simpl_env in *; auto 6.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0; auto 7.
destruct H0. analyze_binds H0; eauto 7.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ E ++ Γ₂ ++ Γ₃). eauto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ E ++ Γ₂ ++ Γ₃). eauto.
Qed.

Lemma wfenv_upperE: forall Γ₁ Γ₂ Γ₃ a,
  wfenv (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃) →
  wfenv (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃).
Proof.
destruct wfenv_wftyp_upperE_aux as [H _]; intros; eapply H; eauto.
Qed.

Lemma wftyp_upperE: forall Γ₁ Γ₂ Γ₃ a τ,
    wftyp (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃) τ →
    wftyp (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃) τ.
Proof.
destruct wfenv_wftyp_upperE_aux as [_ H]; intros; eapply H; eauto.
Qed.

Lemma wfenv_lowerE: forall Γ₁ Γ₂ Γ₃ a,
  wfenv (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃) → a ∉ ftv_env Γ₂ →
  wfenv (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃).
Proof.
destruct wfenv_wftyp_lowerE_aux as [H _]; intros; eapply H; eauto.
Qed.

Lemma wftyp_lowerE: forall Γ₁ Γ₂ Γ₃ a τ,
    wftyp (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃) τ → a ∉ ftv_env Γ₂ →
    wftyp (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃) τ.
Proof.
destruct wfenv_wftyp_lowerE_aux as [_ H]; intros; eapply H; eauto.
Qed.


Lemma wfenv_wftyp_upperU_aux:
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ Γ₃ a,
    Γ = Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃ →
    wfenv (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ Γ₃ a,
    Γ = Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃ →
    wftyp (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; auto.
Case "nil".
assert (binds a (@U typ) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
eapply wfenv_weakening; auto. apply wfenv_strip in w; auto.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "var". constructor; simpl_env in *; auto 6.
destruct o. analyze_binds H0; auto 6.
destruct H0. analyze_binds H0; auto 7.
destruct H0. analyze_binds H0; eauto 7.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ Γ₂ ++ a ~ U ++ Γ₃). eauto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ Γ₂ ++ a ~ U ++ Γ₃). eauto.
Qed.

Lemma wfenv_upperU: forall Γ₁ Γ₂ Γ₃ a,
  wfenv (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃) →
  wfenv (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃).
Proof.
destruct wfenv_wftyp_upperU_aux as [H _]; intros; eapply H; eauto.
Qed.

Lemma wftyp_upperU: forall Γ₁ Γ₂ Γ₃ a τ,
    wftyp (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃) τ →
    wftyp (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃) τ.
Proof.
destruct wfenv_wftyp_upperU_aux as [_ H]; intros; eapply H; eauto.
Qed.


Lemma wfenv_wftyp_lowerU_aux:
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ Γ₃ a,
    Γ = Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃ → a ∉ ftv_env Γ₂ →
    wfenv (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ Γ₃ a,
    Γ = Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃ → a ∉ ftv_env Γ₂ →
    wftyp (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; auto.
Case "nil".
assert (binds a (@U typ) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *; auto.
destruct Γ₂; inversion H0; subst; simpl_env in *.
constructor.
assert (uniq (Γ₂ ++ [(a, U)] ++ Γ₃)) by eauto with lngen. solve_uniq.
constructor; auto.
rewrite ftv_env_app in *|-. unfold ftv_env at 1 in H1; simpl in H1.
rewrite <- tsubst_env_fresh_eq with (G := Γ₂) (a := a) (t := typ_forall (typ_var_b 0)); auto.
rewrite <- tsubst_typ_fresh_eq with (t2 := t) (a1 := a) (t1 := typ_forall (typ_var_b 0)); auto.
apply wftyp_tsubst. auto.
apply wftyp_forall with (L := dom Γ₃); intros.
unfold open_typ_wrt_typ; simpl; simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ₂ ++ [(a, U)]). simpl_env. eauto with fzip.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *; auto.
destruct Γ₂; inversion H0; subst; simpl_env in *; auto.
constructor.
assert (uniq (Γ₂ ++ [(a0, U)] ++ Γ₃)) by eauto with lngen. solve_uniq.
constructor; auto.
rewrite ftv_env_app in *|-.
rewrite <- tsubst_env_fresh_eq with (G := Γ₂) (a := a0) (t := typ_forall (typ_var_b 0)); auto.
apply wfenv_tsubst. auto.
apply wftyp_forall with (L := dom Γ₃); intros.
unfold open_typ_wrt_typ; simpl; simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ₂ ++ [(a0, U)]). simpl_env. eauto with fzip.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *; auto.
destruct Γ₂; inversion H0; subst; simpl_env in *.
constructor.
assert (uniq (Γ₂ ++ [(a0, U)] ++ Γ₃)) by eauto with lngen. solve_uniq.
constructor; auto.
rewrite ftv_env_app in *|-.
rewrite <- tsubst_env_fresh_eq with (G := Γ₂) (a := a0) (t := typ_forall (typ_var_b 0)); auto.
apply wfenv_tsubst. auto.
apply wftyp_forall with (L := dom Γ₃); intros.
unfold open_typ_wrt_typ; simpl; simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ₂ ++ [(a0, U)]). simpl_env. eauto with fzip.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *; auto.
destruct Γ₂; inversion H0; subst; simpl_env in *.
constructor.
assert (uniq (Γ₂ ++ [(a0, U)] ++ Γ₃)) by eauto with lngen. solve_uniq.
constructor; auto.
rewrite ftv_env_app in *|-. unfold ftv_env at 1 in H1; simpl in H1.
rewrite <- tsubst_env_fresh_eq with (G := Γ₂) (a := a0) (t := typ_forall (typ_var_b 0)); auto.
rewrite <- tsubst_typ_fresh_eq with (t2 := t) (a1 := a0) (t1 := typ_forall (typ_var_b 0)); auto.
apply wftyp_tsubst. auto.
apply wftyp_forall with (L := dom Γ₃); intros.
unfold open_typ_wrt_typ; simpl; simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ₂ ++ [(a0, U)]). simpl_env. eauto with fzip.
Case "var". constructor; simpl_env in *; auto 6.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0; auto 7.
destruct H0. analyze_binds H0; eauto 7.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ U ++ Γ₂ ++ Γ₃). eauto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ U ++ Γ₂ ++ Γ₃). eauto.
Qed.

Lemma wfenv_lowerU: forall Γ₁ Γ₂ Γ₃ a,
  wfenv (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃) → a ∉ ftv_env Γ₂ →
  wfenv (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃).
Proof.
destruct wfenv_wftyp_lowerU_aux as [H _]; intros; eapply H; eauto.
Qed.

Lemma wftyp_lowerU: forall Γ₁ Γ₂ Γ₃ a τ,
    wftyp (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃) τ → a ∉ ftv_env Γ₂ →
    wftyp (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃) τ.
Proof.
destruct wfenv_wftyp_lowerU_aux as [_ H]; intros; eapply H; eauto.
Qed.

(** Swapping equations *)
Lemma wfenv_wftyp_swap_Eq:
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ a₁ a₂ τ₁ τ₂,
    Γ = Γ₁ ++ a₁ ~ Eq τ₁ ++ a₂ ~ Eq τ₂ ++ Γ₂ →
    wfenv (Γ₁ ++ a₂ ~ Eq τ₂ ++ a₁ ~ Eq (tsubst_typ τ₂ a₂ τ₁) ++ Γ₂))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ a₁ a₂ τ₁ τ₂,
    Γ = Γ₁ ++ a₁ ~ Eq τ₁ ++ a₂ ~ Eq τ₂ ++ Γ₂ →
    wftyp (Γ₁ ++ a₂ ~ Eq τ₂ ++ a₁ ~ Eq (tsubst_typ τ₂ a₂ τ₁) ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; auto.
Case "nil".
assert (binds a₁ (Eq τ₁) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
eapply wfenv_weakening; auto. eauto with fzip.
rewrite_env (env_map (tsubst_typ τ₂ a₂) (a₁ ~ Eq τ₁) ++ Γ₂).
apply wfenv_subst_eq. auto.
Case "var". constructor; simpl_env in *; auto 6.
destruct o. analyze_binds H0; auto 6.
destruct H0. analyze_binds H0; auto 7.
destruct H0. analyze_binds H0; eauto 7.
inversion BindsTacVal; subst. eauto 8.
Case "forall". apply wftyp_forall with (L := L ∪ {{a₁}} ∪ {{a₂}}); intros.
rewrite_env ((a ~ U ++ Γ₁) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂). eauto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a₁}} ∪ {{a₂}}); intros.
rewrite_env ((a ~ U ++ Γ₁) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂). eauto.
Qed.

Lemma wfenv_swap_Eq: forall Γ₁ Γ₂ a₁ a₂ τ₁ τ₂,
  wfenv (Γ₁ ++ a₁ ~ Eq τ₁ ++ a₂ ~ Eq τ₂ ++ Γ₂) →
  wfenv (Γ₁ ++ a₂ ~ Eq τ₂ ++ a₁ ~ Eq (tsubst_typ τ₂ a₂ τ₁) ++ Γ₂).
Proof.
intros. edestruct wfenv_wftyp_swap_Eq. eauto.
Qed.

Lemma wftyp_swap_Eq: forall Γ₁ Γ₂ a₁ a₂ τ₁ τ₂ τ,
  wftyp (Γ₁ ++ a₁ ~ Eq τ₁ ++ a₂ ~ Eq τ₂ ++ Γ₂) τ →
  wftyp (Γ₁ ++ a₂ ~ Eq τ₂ ++ a₁ ~ Eq (tsubst_typ τ₂ a₂ τ₁) ++ Γ₂) τ.
Proof.
intros. edestruct wfenv_wftyp_swap_Eq. eauto.
Qed.

(** Use with zip *)
Lemma wfenv_wftyp_zip_aux :
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
  (wfenv Γ₁ -> wfenv Γ₂ -> wfenv Γ₃)
  ∧ (forall τ Γ, wftyp (Γ ++ Γ₁) τ -> wftyp (Γ ++ Γ₂) τ ->
    wftyp (Γ ++ Γ₃) τ).
Proof.
intros Γ₁ Γ₂ Γ₃ H; induction H; try destruct IHzip as [IHzip1 IHzip2];
  split; intros; auto.
Case "wfenv_T".
inversion H3; inversion H4; subst; auto.
constructor; auto.
  erewrite <- zip_dom2; eauto.
  rewrite_env (nil ++ G); auto.
Case "wftype_T".
rewrite_env ((Γ ++ [(x, T t)]) ++ G); apply IHzip2; simpl_env; auto.
Case "wfenv_U".
inversion H2; inversion H3; subst; auto.
constructor; auto.
  erewrite <- zip_dom2; eauto.
Case "wftype_U".
rewrite_env ((Γ ++ [(a, U)]) ++ G); apply IHzip2; simpl_env; auto.
Case "wfenv_E".
inversion H2; inversion H3; subst; auto.
constructor; auto.
  erewrite <- zip_dom2; eauto.
Case "wftype_E".
rewrite_env ((Γ ++ [(a, E)]) ++ G); apply IHzip2; simpl_env; auto using wftyp_UE.
Case "wfenv_E".
inversion H3; subst. constructor; auto. erewrite <- zip_dom2; eauto.
Case "wftyp_E".
rewrite_env ((Γ ++ [(a, E)]) ++ G); apply IHzip2; simpl_env; auto.
apply wftyp_weakening; auto.
  constructor; auto. apply wfenv_strip with (Γ' := Γ); auto.
  eauto with fzip.
  apply uniq_app_3; apply uniq_app_1 with (F := G2); simpl_env; eauto with lngen. 
Case "wfenv_Eq".
inversion H3; inversion H4; subst; auto.
constructor; auto.
  erewrite <- zip_dom2; eauto.
  rewrite_env (nil ++ G); auto.
Case "wftype_Eq".
rewrite_env ((Γ ++ [(a, Eq t)]) ++ G); apply IHzip2; simpl_env; auto.
Qed.

Lemma wfenv_zip:
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
    wfenv Γ₁ -> wfenv Γ₂ -> wfenv Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0 H1. edestruct wfenv_wftyp_zip_aux; eauto.
Qed.

Lemma wftyp_zip:
  forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₁ τ -> wftyp Γ₂ τ -> wftyp Γ₃ τ.
Proof.
intros.
edestruct wfenv_wftyp_zip_aux; eauto.
rewrite_env (nil ++ Γ₃). auto.
Qed.
Hint Resolve wfenv_zip wftyp_zip: fzip.

Lemma wftyp_zip12:
  forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₁ τ -> wfenv Γ₂ → wftyp Γ₂ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ τ H H0. generalize dependent Γ₃. generalize dependent Γ₂.
induction H0; intros; eauto.
Case "var". constructor; auto.
destruct H. eauto with fzip.
destruct H. eauto with fzip.
destruct H. eauto with fzip.
Case "forall". apply wftyp_forall with (L := L ∪ dom G ∪ dom Γ₂); intros; auto.
eapply H0; auto. constructor; eauto.
Case "exists". apply wftyp_exists with (L := L ∪ dom G ∪ dom Γ₂); intros; auto.
eapply H0; auto. constructor; eauto.
Qed.

Lemma wftyp_zip13:
  forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₁ τ -> wfenv Γ₂ → wftyp Γ₃ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ τ H H0. generalize dependent Γ₃. generalize dependent Γ₂.
induction H0; intros; eauto.
Case "var". constructor; eauto using wfenv_zip.
destruct H. eauto with fzip.
destruct H. eauto with fzip.
destruct H. eauto with fzip.
Case "forall". apply wftyp_forall with (L := L ∪ dom G ∪ dom Γ₂); intros; auto.
eapply H0 with (Γ₂ := a ~ U ++ Γ₂); auto.
Case "exists". apply wftyp_exists with (L := L ∪ dom G ∪ dom Γ₂); intros; auto.
eapply H0 with (Γ₂ := a ~ U ++ Γ₂); auto.
Qed.

Lemma wftyp_zip23:
  forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₂ τ -> wfenv Γ₁ → wftyp Γ₃ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ τ H H0. generalize dependent Γ₃. generalize dependent Γ₁.
induction H0; intros; eauto.
Case "var". constructor; eauto using wfenv_zip.
destruct H. eapply zip_binds_U23 in H; eauto. tauto.
destruct H. eauto with fzip.
destruct H. eauto with fzip.
Case "forall". apply wftyp_forall with (L := L ∪ dom G ∪ dom Γ₁); intros; auto.
eapply H0 with (Γ₁ := a ~ U ++ Γ₁); auto.
Case "exists". apply wftyp_exists with (L := L ∪ dom G ∪ dom Γ₁); intros; auto.
eapply H0 with (Γ₁ := a ~ U ++ Γ₁); auto.
Qed.
Hint Resolve wftyp_zip12 wftyp_zip13 wftyp_zip23: fzip.

Lemma wfenv_wftyp_zip13_aux :
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
    (wfenv Γ₁ -> wfenv Γ₃)
    ∧ (forall τ Γ, wftyp (Γ ++ Γ₁) τ -> disjoint Γ Γ₃ →
      wftyp (Γ ++ Γ₃) τ).
Proof.
intros Γ₁ Γ₂ Γ₃ H; induction H; try destruct IHzip as [IHzip1 IHzip2];
  split; intros; auto.
Case "wfenv_T".
inversion H3; subst.
constructor; auto.
  assert (dom G2 [=] dom G) by eauto with fzip. fsetdec.
  rewrite_env (nil ++ G). auto.
Case "wftype_T".
rewrite_env ((Γ ++ [(x, T t)]) ++ G); apply IHzip2; simpl_env; auto.
assert (dom G2 [=] dom G) by eauto with fzip.
assert (x ∉ dom G). fsetdec.
solve_uniq.
Case "wfenv_U".
inversion H2; inversion H3; subst; auto.
constructor; auto.
  assert (dom G2 [=] dom G) by eauto with fzip. fsetdec.
Case "wftype_U".
rewrite_env ((Γ ++ [(a, U)]) ++ G); apply IHzip2; simpl_env; auto.
assert (dom G2 [=] dom G) by eauto with fzip.
assert (a ∉ dom G). fsetdec.
solve_uniq.
Case "wfenv_E".
inversion H2; inversion H3; subst; auto.
constructor; auto.
  assert (dom G2 [=] dom G) by eauto with fzip. fsetdec.
Case "wftype_E".
rewrite_env ((Γ ++ [(a, E)]) ++ G); apply IHzip2; simpl_env; auto using wftyp_UE.
assert (dom G2 [=] dom G) by eauto with fzip.
assert (a ∉ dom G). fsetdec.
solve_uniq.
Case "wfenv_E".
constructor; auto.
  assert (dom G2 [=] dom G) by eauto with fzip. fsetdec.
Case "wftyp_E".
rewrite_env ((Γ ++ [(a, E)]) ++ G); apply IHzip2; simpl_env; auto.
apply wftyp_weakening; auto.
  constructor; auto. apply wfenv_strip with (Γ' := Γ); auto.
  eauto with fzip.
  solve_uniq.
assert (dom G2 [=] dom G) by eauto with fzip.
assert (a ∉ dom G). fsetdec.
solve_uniq.
Case "wfenv_Eq".
inversion H3; inversion H4; subst; auto.
constructor; auto.
  assert (dom G2 [=] dom G) by eauto with fzip. fsetdec.
  rewrite_env (nil ++ G); auto.
Case "wftype_Eq".
rewrite_env ((Γ ++ [(a, Eq t)]) ++ G); apply IHzip2; simpl_env; auto.
assert (dom G2 [=] dom G) by eauto with fzip.
assert (a ∉ dom G). fsetdec.
solve_uniq.
Qed.

Lemma wfenv_wftyp_zip12_aux :
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
    (wfenv Γ₁ -> wfenv Γ₂)
    ∧ (forall τ Γ, wftyp (Γ ++ Γ₁) τ -> disjoint Γ Γ₂ →
      wftyp (Γ ++ Γ₂) τ).
Proof.
intros Γ₁ Γ₂ Γ₃ H; induction H; try destruct IHzip as [IHzip1 IHzip2];
  split; intros; auto.
Case "wfenv_T".
inversion H3; subst.
constructor; auto.
  rewrite_env (nil ++ G2). auto.
Case "wftype_T".
rewrite_env ((Γ ++ [(x, T t)]) ++ G2); apply IHzip2; simpl_env; auto.
solve_uniq.
Case "wfenv_U".
inversion H2; subst.
constructor; auto.
Case "wftype_U".
rewrite_env ((Γ ++ [(a, U)]) ++ G2); apply IHzip2; simpl_env; auto.
solve_uniq.
Case "wfenv_E".
inversion H2; inversion H3; subst; auto.
Case "wftype_E".
rewrite_env ((Γ ++ [(a, U)]) ++ G2); apply IHzip2; simpl_env; auto using wftyp_EU.
solve_uniq.
Case "wfenv_E".
rewrite_env ((Γ ++ [(a, E)]) ++ G2); apply IHzip2; simpl_env; auto.
apply wftyp_weakening; auto.
  constructor; auto. apply wfenv_strip with (Γ' := Γ); auto.
  eauto with fzip.
  solve_uniq.
solve_uniq.
Case "wfenv_Eq".
inversion H3; inversion H4; subst; auto.
constructor; auto.
  rewrite_env (nil ++ G2); auto.
Case "wftype_Eq".
rewrite_env ((Γ ++ [(a, Eq t)]) ++ G2); apply IHzip2; simpl_env; auto.
solve_uniq.
Qed.

Lemma wfenv_zip13 : forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
    wfenv Γ₁ -> wfenv Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0. edestruct wfenv_wftyp_zip13_aux; eauto.
Qed.

Lemma wfenv_zip12 : forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
    wfenv Γ₁ -> wfenv Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0. edestruct wfenv_wftyp_zip12_aux; eauto.
Qed.

Lemma wftyp_zip13_bis : forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₁ τ -> wftyp Γ₃ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0 H1.
rewrite_env (nil ++ Γ₃). rewrite_env (nil ++ Γ₁) in H1.
edestruct wfenv_wftyp_zip13_aux; eauto.
Qed.

Lemma wftyp_zip12_bis : forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₁ τ -> wftyp Γ₂ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0 H1.
rewrite_env (nil ++ Γ₂). rewrite_env (nil ++ Γ₁) in H1.
edestruct wfenv_wftyp_zip12_aux; eauto.
Qed.

Lemma wfenv_wftyp_zip21_aux : forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
  (wfenv Γ₂ →
    (forall a, a ∈ ftv_env Γ₂ → not (binds a E Γ₂)) →
    wfenv Γ₁)
  ∧ (forall τ Γ, wftyp (Γ ++ Γ₂) τ ->
    (forall a, a ∈ ftv_env (Γ ++ Γ₂) ∪ ftv_typ τ → not (binds a E (Γ ++ Γ₂))) →
    wftyp (Γ ++ Γ₁) τ).
Proof.
intros Γ₁ Γ₂ Γ₃ H; induction H; try destruct IHzip as [IHzip1 IHzip2];
  split; intros; auto.
Case "wfenv_T".
inversion H3; subst.
constructor; auto.
  rewrite_env (nil ++ G1). apply IHzip2; auto.
intros. intro. eapply H4; eauto. rewrite ftv_env_app in *.
unfold ftv_env at 1; simpl; fsetdec.
Case "wftype_T".
rewrite_env ((Γ ++ [(x, T t)]) ++ G1); apply IHzip2; simpl_env; auto.
Case "wfenv_U".
inversion H2; subst.
constructor; auto. apply IHzip1; auto.
intros. intro. eapply H3; eauto.
Case "wftype_U".
rewrite_env ((Γ ++ [(a, U)]) ++ G1); apply IHzip2; simpl_env; auto.
Case "wfenv_UE".
inversion H2; subst. constructor; auto.
apply IHzip1; auto.
intros. intro. eapply H3; eauto.
Case "wftype_UE".
apply wftyp_UE.
rewrite_env ((Γ ++ [(a, U)]) ++ G1); apply IHzip2; simpl_env; auto using wftyp_UE.
apply IHzip1; auto. eauto using wfenv_strip.
intros. intro. eapply H3; eauto.
Case "wfenv_E".
apply IHzip2; auto.
assert (a ∉ ftv_env Γ ∪ ftv_typ τ). intro. eapply (H3 a); auto.
  rewrite ftv_env_app; fsetdec.
rewrite <- tsubst_env_fresh_eq with (G := Γ)
  (t := typ_forall (typ_var_b 0)) (a := a); auto.
rewrite <- tsubst_typ_fresh_eq with (t2 := τ)
  (t1 := typ_forall (typ_var_b 0)) (a1 := a); auto.
apply wftyp_tsubst. apply wftyp_EU; auto.
pick fresh c and apply wftyp_forall. unfold open_typ_wrt_typ; simpl.
  simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ ++ a ~ E); simpl_env.
  eapply wftyp_wfenv; eauto.
intros. intro. eapply (H3 a0); auto. repeat rewrite ftv_env_app in *. fsetdec.
Case "wfenv_Eq".
inversion H3; subst.
constructor; auto.
  rewrite_env (nil ++ G1); apply IHzip2; auto.
intros. intro. eapply H4; eauto. rewrite ftv_env_app.
unfold ftv_env at 1; simpl; fsetdec.
Case "wftype_Eq".
rewrite_env ((Γ ++ [(a, Eq t)]) ++ G1); apply IHzip2; simpl_env; auto.
Qed.

Lemma wfenv_zip21 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ ->
  (forall a, a ∈ ftv_env Γ₂ → not (binds a E Γ₂)) →
  wfenv Γ₂ → wfenv Γ₁.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0 H1. edestruct wfenv_wftyp_zip21_aux; eauto.
Qed.

Lemma wftyp_zip21 : forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
  wftyp Γ₂ τ ->
  (forall a, a ∈ ftv_env Γ₂ ∪ ftv_typ τ → not (binds a E Γ₂)) →
  wftyp Γ₁ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ τ H H0 H1.
rewrite_env (nil ++ Γ₁). rewrite_env (nil ++ Γ₂) in H0.
rewrite_env (nil ++ Γ₂) in H1.
edestruct wfenv_wftyp_zip21_aux; eauto.
Qed.

Lemma wfenv_wftyp_zip31_aux : forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
  (wfenv Γ₃ →
    (forall a, a ∈ ftv_env Γ₃ → not (binds a E Γ₃)) →
    wfenv Γ₁)
  ∧ (forall τ Γ, wftyp (Γ ++ Γ₃) τ ->
    (forall a, a ∈ ftv_env (Γ ++ Γ₃) ∪ ftv_typ τ → not (binds a E (Γ ++ Γ₃))) →
    wftyp (Γ ++ Γ₁) τ).
Proof.
intros Γ₁ Γ₂ Γ₃ H; induction H; try destruct IHzip as [IHzip1 IHzip2];
  split; intros; auto.
Case "wfenv_T".
inversion H3; subst.
constructor; auto.
  rewrite_env (nil ++ G1). apply IHzip2; auto.
intros. intro. eapply H4; eauto. rewrite ftv_env_app in *.
unfold ftv_env at 1; simpl; fsetdec.
Case "wftype_T".
rewrite_env ((Γ ++ [(x, T t)]) ++ G1); apply IHzip2; simpl_env; auto.
Case "wfenv_U".
inversion H2; subst.
constructor; auto. apply IHzip1; auto.
intros. intro. eapply H3; eauto.
Case "wftype_U".
rewrite_env ((Γ ++ [(a, U)]) ++ G1); apply IHzip2; simpl_env; auto.
Case "wfenv_UE".
inversion H2; subst. constructor; auto.
apply IHzip1; auto.
intros. intro. eapply H3; eauto.
Case "wftype_UE".
rewrite_env ((Γ ++ [(a, E)]) ++ G1); apply IHzip2; simpl_env; auto using wftyp_UE.
apply IHzip1; auto. eauto using wfenv_strip.
intros. intro. eapply H3; eauto.
Case "wfenv_E".
apply IHzip2; auto.
assert (a ∉ ftv_env Γ ∪ ftv_typ τ). intro. eapply (H3 a); auto.
  rewrite ftv_env_app; fsetdec.
rewrite <- tsubst_env_fresh_eq with (G := Γ)
  (t := typ_forall (typ_var_b 0)) (a := a); auto.
rewrite <- tsubst_typ_fresh_eq with (t2 := τ)
  (t1 := typ_forall (typ_var_b 0)) (a1 := a); auto.
apply wftyp_tsubst. apply wftyp_EU; auto.
pick fresh c and apply wftyp_forall. unfold open_typ_wrt_typ; simpl.
  simpl_env. constructor; auto. constructor; auto.
  apply wfenv_strip with (Γ' := Γ ++ a ~ E); simpl_env.
  eapply wftyp_wfenv; eauto.
intros. intro. eapply (H3 a0); auto. repeat rewrite ftv_env_app in *. fsetdec.
Case "wfenv_Eq".
inversion H3; subst.
constructor; auto.
  rewrite_env (nil ++ G1); apply IHzip2; auto.
intros. intro. eapply H4; eauto. rewrite ftv_env_app.
unfold ftv_env at 1; simpl; fsetdec.
Case "wftype_Eq".
rewrite_env ((Γ ++ [(a, Eq t)]) ++ G1); apply IHzip2; simpl_env; auto.
Qed.

Lemma wfenv_zip31 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ ->
  (forall a, a ∈ ftv_env Γ₃ → not (binds a E Γ₃)) →
  wfenv Γ₃ → wfenv Γ₁.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0 H1. edestruct wfenv_wftyp_zip31_aux; eauto.
Qed.

Lemma wftyp_zip31 : forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
  wftyp Γ₃ τ ->
  (forall a, a ∈ ftv_env Γ₃ ∪ ftv_typ τ → not (binds a E Γ₃)) →
  wftyp Γ₁ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ τ H H0 H1.
rewrite_env (nil ++ Γ₁). rewrite_env (nil ++ Γ₃) in H0.
rewrite_env (nil ++ Γ₃) in H1.
edestruct wfenv_wftyp_zip31_aux; eauto.
Qed.

Lemma wfenv_wftyp_zip_inv_aux :
  (forall Γ, wfenv Γ →
    (forall a, a ∈ ftv_env Γ → not (binds a E Γ)) →
    forall Γ' Γ'', Γ = Γ'' ++ Γ' →
      forall Γ₁' Γ₂', zip Γ₁' Γ₂' Γ' →
        wfenv (Γ'' ++ Γ₁') ∧ wfenv (Γ'' ++ Γ₂')) ∧
  (forall Γ τ, wftyp Γ τ →
    (forall a, a ∈ ftv_env Γ ∪ ftv_typ τ → not (binds a E Γ)) →
    forall Γ' Γ'', Γ = Γ'' ++ Γ' →
      forall Γ₁' Γ₂', zip Γ₁' Γ₂' Γ' →
        wftyp (Γ'' ++ Γ₁') τ ∧ wftyp (Γ'' ++ Γ₂') τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst.
Case "nil".
destruct Γ''; try solve [inversion H0].
simpl in *; subst. inversion H1; subst. auto.
Case "T".
destruct Γ''; simpl_env in *. destruct Γ'; inversion H1; subst.
inversion H2; subst.
edestruct H with (Γ'' := nil) (Γ'0 := Γ'); intros; eauto.
  intro; eapply (H0 a); auto. rewrite ftv_env_app.
  unfold ftv_env at 1. simpl. fsetdec.
inversion H1; subst.
edestruct H with (Γ''0 := Γ'') (Γ'0 := Γ'); intros; eauto.
  intro; eapply (H0 a); auto. rewrite ftv_env_app.
  unfold ftv_env at 1. simpl. fsetdec.
split; constructor; auto; simpl_env in *.
  assert (dom Γ₁' [<=] dom Γ') by eauto with fzip. fsetdec.
  assert (dom Γ₂' [=] dom Γ') by eauto with fzip. fsetdec.
Case "U".
destruct Γ''; simpl_env in *. destruct Γ'; inversion H1; subst.
inversion H2; subst.
edestruct H with (Γ'' := nil) (Γ'0 := Γ'); intros; eauto.
  intro; eapply (H0 a0); auto.
inversion H1; subst.
edestruct H with (Γ''0 := Γ'') (Γ'0 := Γ'); intros; eauto.
  intro; eapply (H0 a0); auto. 
split; constructor; auto; simpl_env in *.
  assert (dom Γ₁' [<=] dom Γ') by eauto with fzip. fsetdec.
  assert (dom Γ₂' [=] dom Γ') by eauto with fzip. fsetdec.
Case "E".
destruct Γ''; simpl_env in *. destruct Γ'; inversion H1; subst.
inversion H2; subst.
SCase "EU".
edestruct H with (Γ'' := nil) (Γ'0 := Γ'); intros; eauto.
  intro; eapply (H0 a0); auto.
SCase "E".
edestruct H with (Γ'' := nil) (Γ'0 := Γ'); intros; eauto.
  intro; eapply (H0 a0); auto.
inversion H1; subst.
edestruct H with (Γ''0 := Γ'') (Γ'0 := Γ'); intros; eauto.
  intro; eapply (H0 a0); auto. 
split; constructor; auto; simpl_env in *.
  assert (dom Γ₁' [<=] dom Γ') by eauto with fzip. fsetdec.
  assert (dom Γ₂' [=] dom Γ') by eauto with fzip. fsetdec.
Case "Eq".
destruct Γ''; simpl_env in *. destruct Γ'; inversion H1; subst.
inversion H2; subst.
edestruct H with (Γ'' := nil) (Γ'0 := Γ'); intros; eauto.
  intro; eapply (H0 a0); auto. rewrite ftv_env_app.
  unfold ftv_env at 1. simpl. fsetdec.
inversion H1; subst.
edestruct H with (Γ''0 := Γ'') (Γ'0 := Γ'); intros; eauto.
  intro; eapply (H0 a0); auto. rewrite ftv_env_app.
  unfold ftv_env at 1. simpl. fsetdec.
split; constructor; auto; simpl_env in *.
  assert (dom Γ₁' [<=] dom Γ') by eauto with fzip. fsetdec.
  assert (dom Γ₂' [=] dom Γ') by eauto with fzip. fsetdec.
Case "var". edestruct H; eauto.
split; constructor; auto.
destruct o; [left|right]. analyze_binds H4; eauto with fzip.
destruct H4; [left|right]. elimtype False. eapply (H0 a); simpl; auto.
destruct H4. analyze_binds H4; eauto with fzip.
destruct o; [left|right]. analyze_binds H4; eauto with fzip.
destruct H4; [left|right]. elimtype False. eapply (H0 a); simpl; auto.
destruct H4. analyze_binds H4; eauto with fzip.
Case "arrow".
edestruct H; intros; eauto.
  intro; eapply (H1 a); auto. simpl; fsetdec.
edestruct H0; intros; eauto.
  intro; eapply (H1 a); auto. simpl; fsetdec.
Case "prod".
edestruct H; intros; eauto.
  intro; eapply (H1 a); auto. simpl; fsetdec.
edestruct H0; intros; eauto.
  intro; eapply (H1 a); auto. simpl; fsetdec.
Case "forall".
split; apply wftyp_forall with (L := L); intros; auto.
edestruct H with (Γ''0 := a ~ U ++ Γ''); intros; eauto.
  intro; eapply (H0 a0); auto.
  rewrite ftv_env_app in H3. simpl.
  assert (ftv_typ (open_typ_wrt_typ t (typ_var_f a)) [<=]
ftv_typ (typ_var_f a) ∪ ftv_typ t) by auto with lngen.
  simpl in H5.
  analyze_binds_uniq H4. eauto with lngen.
    simpl_env in *. fsetdec.
    simpl_env in *. fsetdec.
  analyze_binds H4.
  simpl_env. auto.
edestruct H with (Γ''0 := a ~ U ++ Γ''); intros; eauto.
  intro; eapply (H0 a0); auto.
  rewrite ftv_env_app in H3. simpl.
  assert (ftv_typ (open_typ_wrt_typ t (typ_var_f a)) [<=]
ftv_typ (typ_var_f a) ∪ ftv_typ t) by auto with lngen.
  simpl in H5.
  analyze_binds_uniq H4. eauto with lngen.
    simpl_env in *. fsetdec.
    simpl_env in *. fsetdec.
  analyze_binds H4.
  simpl_env. auto.
Case "exists".
split; apply wftyp_exists with (L := L); intros; auto.
edestruct H with (Γ''0 := a ~ U ++ Γ''); intros; eauto.
  intro; eapply (H0 a0); auto.
  rewrite ftv_env_app in H3. simpl.
  assert (ftv_typ (open_typ_wrt_typ t (typ_var_f a)) [<=]
ftv_typ (typ_var_f a) ∪ ftv_typ t) by auto with lngen.
  simpl in H5.
  analyze_binds_uniq H4. eauto with lngen.
    simpl_env in *. fsetdec.
    simpl_env in *. fsetdec.
  analyze_binds H4.
  simpl_env. auto.
edestruct H with (Γ''0 := a ~ U ++ Γ''); intros; eauto.
  intro; eapply (H0 a0); auto.
  rewrite ftv_env_app in H3. simpl.
  assert (ftv_typ (open_typ_wrt_typ t (typ_var_f a)) [<=]
ftv_typ (typ_var_f a) ∪ ftv_typ t) by auto with lngen.
  simpl in H5.
  analyze_binds_uniq H4. eauto with lngen.
    simpl_env in *. fsetdec.
    simpl_env in *. fsetdec.
  analyze_binds H4.
  simpl_env. auto.
Qed.

Lemma wfenv_zip_inv1 : forall Γ' Γ'', wfenv (Γ'' ++ Γ') →
  (forall a, a ∈ ftv_env (Γ'' ++ Γ') → not (binds a E (Γ'' ++ Γ'))) →
  forall Γ₁' Γ₂', zip Γ₁' Γ₂' Γ' →
    wfenv (Γ'' ++ Γ₁').
Proof.
edestruct wfenv_wftyp_zip_inv_aux as [? _].
intros Γ' Γ'' H0 H1 Γ₁' Γ₂' H2.
edestruct (H (Γ'' ++ Γ')) as [? _]; eauto.
Qed.

Lemma wfenv_zip_inv2 : forall Γ' Γ'', wfenv (Γ'' ++ Γ') →
  (forall a, a ∈ ftv_env (Γ'' ++ Γ') → not (binds a E (Γ'' ++ Γ'))) →
  forall Γ₁' Γ₂', zip Γ₁' Γ₂' Γ' →
    wfenv (Γ'' ++ Γ₂').
Proof.
edestruct wfenv_wftyp_zip_inv_aux as [? _].
intros Γ' Γ'' H0 H1 Γ₁' Γ₂' H2.
edestruct (H (Γ'' ++ Γ')) as [_ ?]; eauto.
Qed.

Lemma wftyp_zip_inv1 : forall Γ' Γ'' τ, wftyp (Γ'' ++ Γ') τ →
  (forall a, a ∈ ftv_env (Γ'' ++ Γ') ∪ ftv_typ τ →
    not (binds a E (Γ'' ++ Γ'))) →
  forall Γ₁' Γ₂', zip Γ₁' Γ₂' Γ' →
    wftyp (Γ'' ++ Γ₁') τ.
Proof.
edestruct wfenv_wftyp_zip_inv_aux as [_ ?].
intros Γ' Γ'' τ H0 H1 Γ₁' Γ₂' H2.
edestruct (H (Γ'' ++ Γ')) as [? _]; eauto.
Qed.

Lemma wftyp_zip_inv2 : forall Γ' Γ'' τ, wftyp (Γ'' ++ Γ') τ →
  (forall a, a ∈ ftv_env (Γ'' ++ Γ') ∪ ftv_typ τ →
    not (binds a E (Γ'' ++ Γ'))) →
  forall Γ₁' Γ₂', zip Γ₁' Γ₂' Γ' →
    wftyp (Γ'' ++ Γ₂') τ.
Proof.
edestruct wfenv_wftyp_zip_inv_aux as [_ ?].
intros Γ' Γ'' τ H0 H1 Γ₁' Γ₂' H2.
edestruct (H (Γ'' ++ Γ')) as [_ ?]; eauto.
Qed.
