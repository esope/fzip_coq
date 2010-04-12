Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_zip.
Require Import FzipCore_pure.
Require Import FzipCore_env_typ.
Require Import FzipCore_weakenU.


(** Lemmas about [wfeq] *)
Lemma wftypeq_wfenv : forall Γ τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → wfenv Γ.
Proof.
intros Γ τ₁ τ₂ H; induction H; auto; try solve [pick fresh a; eauto using wfenv_strip].
Qed.

Lemma wftypeq_wftyp : forall Γ τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → wftyp Γ τ₁ ∧ wftyp Γ τ₂.
Proof.
intros Γ τ₁ τ₂ H; induction H; split; intuition; eauto.
eauto using wfenv_wftyp_Eq2.
apply wftyp_forall with (L := L); firstorder.
apply wftyp_forall with (L := L); firstorder.
apply wftyp_exists with (L := L); firstorder.
apply wftyp_exists with (L := L); firstorder.
Qed.

Lemma wftypeq_wftyp1 : forall Γ τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → wftyp Γ τ₁.
Proof.
intros Γ τ₁ τ₂ H. edestruct wftypeq_wftyp; eauto.
Qed.

Lemma wftypeq_wftyp2 : forall Γ τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → wftyp Γ τ₂.
Proof.
intros Γ τ₁ τ₂ H. edestruct wftypeq_wftyp; eauto.
Qed.
Hint Resolve wftypeq_wfenv wftypeq_wftyp1 wftypeq_wftyp2: fzip.

Lemma wftypeq_refl : forall Γ τ, wftyp Γ τ →
  wftypeq Γ τ τ.
Proof.
intros Γ τ H; induction H; eauto.
Qed.
Hint Resolve wftypeq_refl: fzip.

Lemma wftypeq_UE : forall Γ₁ a Γ₂ τ₁ τ₂,
  wftypeq (Γ₂ ++ a ~ U ++ Γ₁) τ₁ τ₂ →
  wftypeq (Γ₂ ++ a ~ E ++ Γ₁) τ₁ τ₂.
Proof.
intros Γ₁ a Γ₂ τ₁ τ₂ H. dependent induction H; eauto.
Case "var". destruct (a == a0); subst; constructor; auto 6 with fzip.
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto 6.
Case "eq". constructor; auto with fzip. analyze_binds H.
Case "forall". apply wftypeq_forall with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₂) ++ a ~ E ++ Γ₁). auto.
Case "exists". apply wftypeq_exists with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₂) ++ a ~ E ++ Γ₁). auto.
Qed.

Lemma wftypeq_EU : forall Γ₁ a Γ₂ τ₁ τ₂,
  wftypeq (Γ₂ ++ a ~ E ++ Γ₁) τ₁ τ₂ →
  wftypeq (Γ₂ ++ a ~ U ++ Γ₁) τ₁ τ₂.
Proof.
intros Γ₁ a Γ₂ τ₁ τ₂ H. dependent induction H; eauto.
Case "var". destruct (a == a0); subst; constructor; auto 6 with fzip.
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto 6.
Case "eq". constructor; auto with fzip.
analyze_binds H.
Case "forall". apply wftypeq_forall with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₂) ++ a ~ U ++ Γ₁). auto.
Case "exists". apply wftypeq_exists with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₂) ++ a ~ U ++ Γ₁). auto.
Qed.
Hint Resolve wftypeq_EU wftypeq_UE: fzip.

Lemma wftypeq_instantiate :
  forall Γ₁ Γ₂ τ₁ τ₂ a τ, wftypeq (Γ₁ ++ a ~ U ++ Γ₂) τ₁ τ₂ →
    wftyp Γ₂ τ → wftypeq (Γ₁ ++ a ~ Eq τ ++ Γ₂) τ₁ τ₂.
Proof.
intros Γ₁ Γ₂ τ₁ τ₂ a τ H. dependent induction H; intros; eauto.
Case "var". constructor; auto with fzip.
destruct H. analyze_binds H; eauto 7.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto 7.
Case "eq". analyze_binds H; constructor; auto with fzip.
Case "forall". apply wftypeq_forall with (L := L); intros; auto.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ ++ Γ₂). auto.
Case "exists". apply wftypeq_exists with (L := L); intros; auto.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ ++ Γ₂). auto.
Qed.

Lemma wftypeq_subst_eq :
  forall Γ₁ Γ₂ τ₁ τ₂ a τ, wftypeq (Γ₁ ++ a ~ Eq τ ++ Γ₂) τ₁ τ₂ →
    wftypeq (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂)
    ((tsubst_typ τ a) τ₁) ((tsubst_typ τ a) τ₂).
Proof.
intros Γ₁ Γ₂ τ₁ τ₂ a τ H.
dependent induction H; intros; try solve [simpl; eauto].
Case "var". destruct (a == a0); subst.
SCase "a = a0". auto with fzip.
SCase "a ≠ a0". simpl; destruct (a == a0). contradiction.
destruct H. analyze_binds H; constructor; auto with fzip.
replace (@U typ) with (tag_map (tsubst_typ τ a0) U) by reflexivity.
  unfold env_map. auto.
destruct H. analyze_binds H; constructor; auto with fzip.
replace (@E typ) with (tag_map (tsubst_typ τ a0) E) by reflexivity.
  unfold env_map. auto.
destruct H. analyze_binds H.
  constructor; auto with fzip.
  right; right; exists (tsubst_typ τ a0 x).
replace (Eq (tsubst_typ τ a0 x)) with (tag_map (tsubst_typ τ a0) (Eq x))
  by reflexivity.
  unfold env_map. auto.
  constructor; auto with fzip. eauto.
Case "eq". assert (uniq (Γ₁ ++ [(a0, Eq τ)] ++ Γ₂)) by auto with lngen.
analyze_binds_uniq H.
SCase "binds a Γ₁". assert (a ≠ a0) by auto. simpl; destruct (a == a0); try contradiction.
constructor; auto with fzip.
replace (Eq (tsubst_typ τ a0 t)) with (tag_map (tsubst_typ τ a0) (Eq t)) by reflexivity.
unfold env_map. auto.
SCase "a = a0". assert (t = τ) by congruence; subst.
assert (a0 ∉ ftv_typ τ).
  apply wfenv_strip in H0. inversion H0; subst. apply wftyp_ftv in H7. auto.
  assert (wftypeq (env_map (tsubst_typ τ a0) Γ₁ ++ Γ₂) (tsubst_typ τ a0 τ) (tsubst_typ τ a0 τ)).
  apply wftypeq_refl; apply wftyp_subst_eq; apply wfenv_wftyp_Eq2 with (x := a0); auto.
  autorewrite with lngen in *; auto.
SCase "binds a Γ₂". assert (a ≠ a0) by auto. simpl; destruct (a == a0); try contradiction.
constructor; auto with fzip.
assert (a0 ∉ ftv_typ t).
assert (ftv_typ t [<=] dom Γ₂) by eauto with fzip.
solve_uniq.
autorewrite with lngen. auto.
Case "forall". simpl. apply wftypeq_forall with (L := L ∪ {{a}}); intros; auto.
replace (typ_var_f a0) with (tsubst_typ τ a (typ_var_f a0)).
assert (lc_typ τ) by eauto with lngen fzip.
repeat rewrite <- tsubst_typ_open_typ_wrt_typ; auto.
rewrite_env (env_map (tsubst_typ τ a) (a0 ~ U ++ Γ₁) ++ Γ₂). auto.
assert (a0 ≠ a) by auto.
simpl; unfold typvar. destruct (a0 == a); congruence.
Case "exists". simpl. apply wftypeq_exists with (L := L ∪ {{a}}); intros; auto.
replace (typ_var_f a0) with (tsubst_typ τ a (typ_var_f a0)).
 assert (lc_typ τ) by eauto with lngen fzip.
 repeat rewrite <- tsubst_typ_open_typ_wrt_typ; auto.
 rewrite_env (env_map (tsubst_typ τ a) (a0 ~ U ++ Γ₁) ++ Γ₂). auto.
 assert (a0 ≠ a) by auto.
 simpl; unfold typvar. destruct (a0 == a); congruence.
Qed.

Lemma wftypeq_tsubst :
  forall Γ₁ Γ₂ τ₁ τ₂ a τ, wftypeq (Γ₁ ++ a ~ U ++ Γ₂) τ₁ τ₂ →
    wftyp Γ₂ τ →
    wftypeq (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂)
    ((tsubst_typ τ a) τ₁) ((tsubst_typ τ a) τ₂).
Proof.
auto using wftypeq_instantiate, wftypeq_subst_eq.
Qed.
Hint Resolve wftypeq_instantiate wftypeq_subst_eq wftypeq_tsubst: fzip.

Lemma wftypeq_subst :
  forall Γ₁ Γ₂ τ₁ τ₂ x τ, wftypeq (Γ₁ ++ x ~ T τ ++ Γ₂) τ₁ τ₂ →
    wftypeq (Γ₁ ++ Γ₂) τ₁ τ₂.
Proof.
intros Γ₁ Γ₂ τ₁ τ₂ x τ H. dependent induction H; eauto.
Case "var". constructor.
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto.
eauto with fzip.
Case "eq". constructor.
analyze_binds H. eapply wfenv_subst; eauto.
Case "forall". apply wftypeq_forall with (L := L); intros.
rewrite_env ((a ~ U ++ Γ₁) ++ Γ₂).
 eapply H0; simpl_env; auto.
Case "exists". apply wftypeq_exists with (L := L); intros.
rewrite_env ((a ~ U ++ Γ₁) ++ Γ₂).
 eapply H0; simpl_env; auto.
Qed.
Hint Resolve wftypeq_subst.

Lemma wfenv_wftyp_wftypeq_T_aux :
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ x τ₁ τ₂,
    Γ = Γ₁ ++ x ~ T τ₁ ++ Γ₂ →
    wftypeq Γ₂ τ₁ τ₂ →
    wfenv (Γ₁ ++ x ~ T τ₂ ++ Γ₂))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ x τ₁ τ₂,
    Γ = Γ₁ ++ x ~ T τ₁ ++ Γ₂ →
    wftypeq Γ₂ τ₁ τ₂ →
    wftyp (Γ₁ ++ x ~ T τ₂ ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; eauto.
Case "nil".
assert (binds x (T τ₁) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
constructor; auto. eauto with fzip.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "var". constructor; eauto.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0.
destruct H0. analyze_binds H0; eauto 6.
Case "forall". apply wftyp_forall with (L := L); intros.
rewrite_env ((a ~ U ++ Γ₁) ++ x ~ T τ₂ ++ Γ₂). eapply H; simpl_env; auto.
Case "exists". apply wftyp_exists with (L := L); intros.
rewrite_env ((a ~ U ++ Γ₁) ++ x ~ T τ₂ ++ Γ₂). eapply H; simpl_env; auto.
Qed.

Lemma wfenv_wftypeq_T :
  forall Γ₁ Γ₂ x τ₁ τ₂,
    wfenv (Γ₁ ++ x ~ T τ₁ ++ Γ₂) →
    wftypeq Γ₂ τ₁ τ₂ →
    wfenv (Γ₁ ++ x ~ T τ₂ ++ Γ₂).
Proof.
destruct wfenv_wftyp_wftypeq_T_aux as [H _]; intros; eapply H; eauto.
Qed.

Lemma wftyp_wftypeq_T :
  forall Γ₁ Γ₂ x τ₁ τ₂ τ,
    wftyp (Γ₁ ++ x ~ T τ₁ ++ Γ₂) τ →
    wftypeq Γ₂ τ₁ τ₂ →
    wftyp (Γ₁ ++ x ~ T τ₂ ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_wftypeq_T_aux as [_ H]; intros; eapply H; eauto.
Qed.
Hint Resolve wfenv_wftypeq_T wftyp_wftypeq_T: fzip.

Lemma wfenv_wftyp_wftypeq_Eq_aux :
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ a τ₁ τ₂,
    Γ = Γ₁ ++ a ~ Eq τ₁ ++ Γ₂ →
    wftypeq Γ₂ τ₁ τ₂ →
    wfenv (Γ₁ ++ a ~ Eq τ₂ ++ Γ₂))
  ∧ (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ a τ₁ τ₂,
    Γ = Γ₁ ++ a ~ Eq τ₁ ++ Γ₂ →
    wftypeq Γ₂ τ₁ τ₂ →
    wftyp (Γ₁ ++ a ~ Eq τ₂ ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; eauto.
Case "nil".
assert (binds a (Eq τ₁) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *; eauto.
constructor; auto. eauto with fzip.
Case "var". constructor; eauto.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0.
destruct H0. analyze_binds H0; eauto 7.
Case "forall". apply wftyp_forall with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ₂ ++ Γ₂). eapply H; simpl_env; auto.
Case "exists". apply wftyp_exists with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ₂ ++ Γ₂). eapply H; simpl_env; auto.
Qed.

Lemma wfenv_wftypeq_Eq :
  forall Γ₁ Γ₂ a τ₁ τ₂,
    wfenv (Γ₁ ++ a ~ Eq τ₁ ++ Γ₂) →
    wftypeq Γ₂ τ₁ τ₂ →
    wfenv (Γ₁ ++ a ~ Eq τ₂ ++ Γ₂).
Proof.
destruct wfenv_wftyp_wftypeq_Eq_aux as [H _]; intros; eapply H; eauto.
Qed.

Lemma wftyp_wftypeq_Eq :
  forall Γ₁ Γ₂ a τ₁ τ₂ τ,
    wftyp (Γ₁ ++ a ~ Eq τ₁ ++ Γ₂) τ →
    wftypeq Γ₂ τ₁ τ₂ →
    wftyp (Γ₁ ++ a ~ Eq τ₂ ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_wftypeq_Eq_aux as [_ H]; intros; eapply H; eauto.
Qed.
Hint Resolve wfenv_wftypeq_Eq wftyp_wftypeq_Eq: fzip.

Lemma wftypeq_weakening :
  forall Γ₁ Γ₂ Γ₃ τ₁ τ₂, wftypeq (Γ₁ ++ Γ₃) τ₁ τ₂ →
    wfenv (Γ₂ ++ Γ₃) → disjoint Γ₁ Γ₂ →
    wftypeq (Γ₁ ++ Γ₂ ++ Γ₃) τ₁ τ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ τ₁ τ₂ H H0 H1. dependent induction H; auto using wfenv_weakening.
Case "var".
constructor; auto using wfenv_weakening.
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto 6.
Case "forall".
apply wftypeq_forall with (L := L ∪ dom Γ₂); intros.
rewrite_env ((a~U ++ Γ₁) ++ Γ₂ ++ Γ₃); eauto.
Case "exists".
apply wftypeq_exists with (L := L ∪ dom Γ₂); intros.
rewrite_env ((a~U ++ Γ₁) ++ Γ₂ ++ Γ₃); eauto.
Case "trans". eauto.
Qed.
Hint Resolve wftypeq_weakening: fzip.

Lemma wftypeq_weakenU : forall Γ Γ' τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → weakenU Γ' Γ → wftypeq Γ' τ₁ τ₂.
Proof.
intros Γ Γ' τ₁ τ₂ H H0. generalize dependent Γ'.
induction H; intros; auto.
Case "var". constructor.
intuition eauto with fzip. destruct H; eauto with fzip.
eauto using wfenv_weakenU.
Case "eq". constructor. eauto with fzip. eauto using wfenv_weakenU.
Case "forall". pick fresh a and apply wftypeq_forall; auto.
Case "exists". pick fresh a and apply wftypeq_exists; auto.
Case "trans". eauto.
Qed.

Lemma wftypeq_wftypeq :
  forall Γ₁ Γ₂ τ₁ τ₂ a τ τ', wftypeq (Γ₁ ++ a ~ Eq τ ++ Γ₂) τ₁ τ₂ →
    wftypeq Γ₂ τ τ' →
    wftypeq (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ₁ τ₂.
Proof.
intros Γ₁ Γ₂ τ₁ τ₂ a τ τ' H H0. dependent induction H; eauto.
Case "var". constructor; eauto using wfenv_wftypeq_Eq.
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto 7.
Case "eq". analyze_binds H; eauto using wfenv_wftypeq_Eq.
replace t with τ by congruence.
apply wftypeq_trans with (t2 := τ').
constructor; eauto using wfenv_wftypeq_Eq. apply wftypeq_sym.
rewrite_env (nil ++ (Γ₁ ++ a0 ~ Eq τ') ++ Γ₂). apply wftypeq_weakening; simpl_env in *; 
eauto using wfenv_wftypeq_Eq.
Case "forall". apply wftypeq_forall with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ' ++ Γ₂). eauto.
Case "exists". apply wftypeq_exists with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ' ++ Γ₂). eauto.
Qed.
Hint Resolve wftypeq_wftypeq: fzip.

Lemma wftypeq_renameU : forall Γ₁ a Γ₂ τ τ' b,
  wftypeq (Γ₁ ++ a ~ U ++ Γ₂) τ τ' →
  b ∉ dom (Γ₁ ++ Γ₂) →
  wftypeq (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ U ++ Γ₂)
    (tsubst_typ (typ_var_f b) a τ)
    (tsubst_typ (typ_var_f b) a τ').
Proof.
intros Γ₁ a Γ₂ τ τ' b H H0. dependent induction H; simpl; simpl_env; eauto.
Case "var". destruct (a == a0); subst.
SCase "a = a0". constructor. auto 6. auto using wfenv_renameU.
SCase "a ≠ a0". constructor.
destruct H. analyze_binds H.
  replace (@U typ) with (tag_map (tsubst_typ (typ_var_f b) a0) U) by reflexivity.
    unfold env_map. auto.
destruct H. analyze_binds H.
  replace (@E typ) with (tag_map (tsubst_typ (typ_var_f b) a0) E) by reflexivity.
    unfold env_map. auto.
destruct H. right; right. unfold env_map. analyze_binds H; eauto.
  exists (tsubst_typ (typ_var_f b) a0 x).
    replace (Eq (tsubst_typ (typ_var_f b) a0 x)) with (tag_map (tsubst_typ (typ_var_f b) a0) (Eq x)) by reflexivity.
    auto.
auto using wfenv_renameU.
Case "eq". destruct (a == a0); subst.
SCase "a = a0 (absurd)".
assert (Eq t = U). eapply binds_unique; eauto. auto with lngen. congruence.
SCase "a ≠ a0". constructor.
analyze_binds H.
replace (Eq (tsubst_typ (typ_var_f b) a0 t)) with (tag_map (tsubst_typ (typ_var_f b) a0) (Eq t)) by reflexivity.
unfold env_map. auto.
rewrite tsubst_typ_fresh_eq. auto.
assert (ftv_typ t [<=] dom Γ₂).
  apply wftyp_ftv. eapply wfenv_wftyp_Eq2; eauto.
  apply wfenv_strip with (Γ' := Γ₁ ++ [(a0, U)]). simpl_env; auto.
assert (uniq (Γ₁ ++ [(a0, U)] ++ Γ₂)) by auto with lngen.
destruct_uniq; fsetdec.
auto using wfenv_renameU.
Case "forall". pick fresh c and apply wftypeq_forall.
repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, U)] ++ Γ₂).
auto.
Case "exists". pick fresh c and apply wftypeq_exists.
repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, U)] ++ Γ₂).
auto.
Qed.

Lemma wftypeq_renameE : forall Γ₁ a Γ₂ τ τ' b,
  wftypeq (Γ₁ ++ a ~ E ++ Γ₂) τ τ' →
  b ∉ dom (Γ₁ ++ Γ₂) →
  wftypeq (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ E ++ Γ₂)
    (tsubst_typ (typ_var_f b) a τ)
    (tsubst_typ (typ_var_f b) a τ').
Proof.
intros Γ₁ a Γ₂ τ τ' b H H0. dependent induction H; simpl; simpl_env; eauto.
Case "var". destruct (a == a0); subst.
SCase "a = a0". constructor. auto 6. auto using wfenv_renameE.
SCase "a ≠ a0". constructor.
destruct H. analyze_binds H.
  replace (@U typ) with (tag_map (tsubst_typ (typ_var_f b) a0) U) by reflexivity.
    unfold env_map. auto.
destruct H. analyze_binds H.
  replace (@E typ) with (tag_map (tsubst_typ (typ_var_f b) a0) E) by reflexivity.
    unfold env_map. auto.
destruct H. right; right. unfold env_map. analyze_binds H; eauto.
  exists (tsubst_typ (typ_var_f b) a0 x).
    replace (Eq (tsubst_typ (typ_var_f b) a0 x)) with (tag_map (tsubst_typ (typ_var_f b) a0) (Eq x)) by reflexivity.
    auto.
auto using wfenv_renameE.
Case "eq". destruct (a == a0); subst.
SCase "a = a0 (absurd)".
assert (Eq t = E). eapply binds_unique; eauto. auto with lngen. congruence.
SCase "a ≠ a0". constructor.
analyze_binds H.
replace (Eq (tsubst_typ (typ_var_f b) a0 t)) with (tag_map (tsubst_typ (typ_var_f b) a0) (Eq t)) by reflexivity.
unfold env_map. auto.
rewrite tsubst_typ_fresh_eq. auto.
assert (ftv_typ t [<=] dom Γ₂).
  apply wftyp_ftv. eapply wfenv_wftyp_Eq2; eauto.
  apply wfenv_strip with (Γ' := Γ₁ ++ [(a0, E)]). simpl_env; auto.
assert (uniq (Γ₁ ++ [(a0, E)] ++ Γ₂)) by auto with lngen.
destruct_uniq; fsetdec.
auto using wfenv_renameE.
Case "forall". pick fresh c and apply wftypeq_forall.
repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, E)] ++ Γ₂).
auto.
Case "exists". pick fresh c and apply wftypeq_exists.
repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, E)] ++ Γ₂).
auto.
Qed.

Lemma wftypeq_renameEq : forall Γ₁ a Γ₂ τ τ' b τ₀,
  wftypeq (Γ₁ ++ a ~ Eq τ₀ ++ Γ₂) τ τ' →
  b ∉ dom (Γ₁ ++ Γ₂) →
  wftypeq (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ Eq τ₀ ++ Γ₂)
    (tsubst_typ (typ_var_f b) a τ)
    (tsubst_typ (typ_var_f b) a τ').
Proof.
intros Γ₁ a Γ₂ τ τ' b τ₀ H H0. dependent induction H; simpl; simpl_env; eauto.
Case "var". destruct (a == a0); subst.
SCase "a = a0". constructor. eauto 7. auto using wfenv_renameEq.
SCase "a ≠ a0". constructor.
destruct H. analyze_binds H.
  replace (@U typ) with (tag_map (tsubst_typ (typ_var_f b) a0) U) by reflexivity.
    unfold env_map. auto.
destruct H. analyze_binds H.
  replace (@E typ) with (tag_map (tsubst_typ (typ_var_f b) a0) E) by reflexivity.
    unfold env_map. auto.
destruct H. right; right. unfold env_map. analyze_binds H; eauto.
  exists (tsubst_typ (typ_var_f b) a0 x).
    replace (Eq (tsubst_typ (typ_var_f b) a0 x)) with (tag_map (tsubst_typ (typ_var_f b) a0) (Eq x)) by reflexivity.
    auto.
auto using wfenv_renameEq.
Case "eq". destruct (a == a0); subst.
SCase "a = a0".
assert (t = τ₀). assert (Eq t = Eq τ₀). eapply binds_unique; eauto with lngen. congruence.
subst.
rewrite tsubst_typ_fresh_eq. constructor; auto using wfenv_renameEq.
assert (ftv_typ τ₀ [<=] dom Γ₂).
  apply wftyp_ftv. apply wfenv_wftyp_Eq3 with (x := a0). eauto using wfenv_strip.
assert (uniq (Γ₁ ++ [(a0, Eq τ₀)] ++ Γ₂)) by eauto with lngen.
solve_uniq.
SCase "a ≠ a0". constructor.
analyze_binds H.
replace (Eq (tsubst_typ (typ_var_f b) a0 t)) with (tag_map (tsubst_typ (typ_var_f b) a0) (Eq t)) by reflexivity.
unfold env_map. auto.
rewrite tsubst_typ_fresh_eq. auto.
assert (ftv_typ t [<=] dom Γ₂).
  apply wftyp_ftv. eapply wfenv_wftyp_Eq2; eauto.
  apply wfenv_strip with (Γ' := Γ₁ ++ a0 ~ Eq τ₀). simpl_env; auto.
assert (uniq (Γ₁ ++ a0 ~ Eq τ₀ ++ Γ₂)) by auto with lngen.
solve_uniq.
auto using wfenv_renameEq.
Case "forall". pick fresh c and apply wftypeq_forall.
repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, Eq τ₀)] ++ Γ₂).
auto.
Case "exists". pick fresh c and apply wftypeq_exists.
repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, Eq τ₀)] ++ Γ₂).
auto.
Qed.

Lemma wftypeq_upperE: forall Γ₁ Γ₂ Γ₃ a τ τ',
    wftypeq (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃) τ τ' →
    wftypeq (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃) τ τ'.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ τ' H. dependent induction H; auto.
Case "var". constructor.
destruct H. analyze_binds H; auto.
destruct H. analyze_binds H; auto 7.
destruct H. analyze_binds H; eauto 7.
auto using wfenv_upperE.
Case "eq". constructor.
analyze_binds H; auto.
auto using wfenv_upperE.
Case "forall". pick fresh b and apply wftypeq_forall.
rewrite_env (([(b, U)] ++ Γ₁) ++ Γ₂ ++ [(a, E)] ++ Γ₃). auto.
Case "exists". pick fresh b and apply wftypeq_exists.
rewrite_env (([(b, U)] ++ Γ₁) ++ Γ₂ ++ [(a, E)] ++ Γ₃). auto.
Case "trans". eauto.
Qed.

Lemma wftypeq_lowerE: forall Γ₁ Γ₂ Γ₃ a τ τ',
    wftypeq (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃) τ τ' → a ∉ ftv_env Γ₂ →
    wftypeq (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃) τ τ'.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ τ' H Ha. dependent induction H; auto.
Case "var". constructor.
destruct H. analyze_binds H; auto.
destruct H. analyze_binds H; auto 7.
destruct H. analyze_binds H; eauto 7.
auto using wfenv_lowerE.
Case "eq". constructor.
analyze_binds H; auto.
auto using wfenv_lowerE.
Case "forall". pick fresh b and apply wftypeq_forall.
rewrite_env (([(b, U)] ++ Γ₁) ++ [(a, E)] ++ Γ₂ ++ Γ₃). auto.
Case "exists". pick fresh b and apply wftypeq_exists.
rewrite_env (([(b, U)] ++ Γ₁) ++ [(a, E)] ++ Γ₂ ++ Γ₃). auto.
Case "trans". eauto.
Qed.

Lemma wftypeq_upperU: forall Γ₁ Γ₂ Γ₃ a τ τ',
    wftypeq (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃) τ τ' →
    wftypeq (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃) τ τ'.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ τ' H. dependent induction H; auto.
Case "var". constructor.
destruct H. analyze_binds H; auto 6.
destruct H. analyze_binds H; auto 7.
destruct H. analyze_binds H; eauto 7.
auto using wfenv_upperU.
Case "eq". constructor.
analyze_binds H; auto.
auto using wfenv_upperU.
Case "forall". pick fresh b and apply wftypeq_forall.
rewrite_env (([(b, U)] ++ Γ₁) ++ Γ₂ ++ [(a, U)] ++ Γ₃). auto.
Case "exists". pick fresh b and apply wftypeq_exists.
rewrite_env (([(b, U)] ++ Γ₁) ++ Γ₂ ++ [(a, U)] ++ Γ₃). auto.
Case "trans". eauto.
Qed.

Lemma wftypeq_lowerU: forall Γ₁ Γ₂ Γ₃ a τ τ',
    wftypeq (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃) τ τ' → a ∉ ftv_env Γ₂ →
    wftypeq (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃) τ τ'.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ τ' H Ha. dependent induction H; auto.
Case "var". constructor.
destruct H. analyze_binds H; auto.
destruct H. analyze_binds H; auto 7.
destruct H. analyze_binds H; eauto 7.
auto using wfenv_lowerU.
Case "eq". constructor.
analyze_binds H; auto.
auto using wfenv_lowerU.
Case "forall". pick fresh b and apply wftypeq_forall.
rewrite_env (([(b, U)] ++ Γ₁) ++ [(a, U)] ++ Γ₂ ++ Γ₃). auto.
Case "exists". pick fresh b and apply wftypeq_exists.
rewrite_env (([(b, U)] ++ Γ₁) ++ [(a, U)] ++ Γ₂ ++ Γ₃). auto.
Case "trans". eauto.
Qed.

Lemma wftypeq_unfold_eq : forall Γ τ a τ',
  wftyp Γ τ → binds a (Eq τ') Γ →
  wftypeq Γ τ (tsubst_typ τ' a τ).
Proof.
intros Γ τ a τ' H H0. induction H; simpl; auto.
Case "var". unfold typvar in *; destruct (a0 == a); subst; auto.
Case "forall". pick fresh b and apply wftypeq_forall.
assert (b ≠ a) by fsetdec.
replace (typ_var_f b) with (tsubst_typ τ' a (typ_var_f b)).
rewrite <- tsubst_typ_open_typ_wrt_typ.
simpl; unfold typvar in *; destruct (b == a); subst; simpl_env; auto; try congruence.
apply wftyp_regular with (Γ := b ~ U ++ G).
  apply wfenv_wftyp_Eq2 with (x := a); auto. eapply wftyp_wfenv; eauto.
simpl; unfold typvar in *; destruct (b == a); subst; auto; try congruence.
Case "exists". pick fresh b and apply wftypeq_exists.
assert (b ≠ a) by fsetdec.
replace (typ_var_f b) with (tsubst_typ τ' a (typ_var_f b)).
rewrite <- tsubst_typ_open_typ_wrt_typ.
simpl; unfold typvar in *; destruct (b == a); subst; simpl_env; auto; try congruence.
apply wftyp_regular with (Γ := b ~ U ++ G).
  apply wfenv_wftyp_Eq2 with (x := a); auto. eapply wftyp_wfenv; eauto.
simpl; unfold typvar in *; destruct (b == a); subst; auto; try congruence.
Qed.

Lemma wftypeq_swap_Eq : forall Γ₁ Γ₂ a₁ a₂ τ₁ τ₂ τ τ',
    wftypeq (Γ₁ ++ a₁ ~ Eq τ₁ ++ a₂ ~ Eq τ₂ ++ Γ₂) τ τ' →
    wftypeq (Γ₁ ++ a₂ ~ Eq τ₂ ++ a₁ ~ Eq (tsubst_typ τ₂ a₂ τ₁) ++ Γ₂) τ τ'.
Proof.
intros Γ₁ Γ₂ a₁ a₂ τ₁ τ₂ τ τ' H. dependent induction H; auto.
Case "var". constructor.
destruct H. analyze_binds H; eauto.
destruct H. analyze_binds H; eauto 6.
destruct H. analyze_binds H; eauto 7.
inversion BindsTacVal; subst. eauto 8.
auto using wfenv_swap_Eq.
Case "eq". analyze_binds H; auto using wfenv_swap_Eq.
inversion BindsTacVal; subst.
apply wftypeq_trans with (t2 := tsubst_typ τ₂ a₂ τ₁).
auto 6 using wfenv_swap_Eq.
apply wftypeq_sym. apply wftypeq_unfold_eq; auto. apply wftyp_swap_Eq.
apply wfenv_wftyp_Eq2 with (x := a₁); auto.
Case "forall". pick fresh a and apply wftypeq_forall.
rewrite_env ((a ~ U ++ Γ₁) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂). auto.
Case "exists". pick fresh a and apply wftypeq_exists.
rewrite_env ((a ~ U ++ Γ₁) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂). auto.
Case "trans". eauto.
Qed.

Lemma wftypeq_zip12 : forall Γ₁ Γ₂ Γ₃ τ τ',
  zip Γ₁ Γ₂ Γ₃ → wftypeq Γ₁ τ τ' → wftypeq Γ₂ τ τ'.
Proof.
intros Γ₁ Γ₂ Γ₃ τ τ' H H0.
generalize dependent Γ₃. generalize dependent Γ₂. induction H0; intros; eauto.
Case "var".
destruct H. constructor. eauto with fzip. eauto using wfenv_zip12.
destruct H. constructor. eauto with fzip. eauto using wfenv_zip12.
destruct H. constructor. eauto with fzip. eauto using wfenv_zip12.
Case "eq". constructor. eauto with fzip. eauto using wfenv_zip12.
Case "forall". pick fresh a and apply wftypeq_forall; intros.
apply H0 with (Γ₃ := a ~ U ++ Γ₃); auto.
Case "exists". pick fresh a and apply wftypeq_exists; intros.
apply H0 with (Γ₃ := a ~ U ++ Γ₃); auto.
Qed.

Lemma wftypeq_zip13 : forall Γ₁ Γ₂ Γ₃ τ τ',
  zip Γ₁ Γ₂ Γ₃ → wftypeq Γ₁ τ τ' → wftypeq Γ₃ τ τ'.
Proof.
intros Γ₁ Γ₂ Γ₃ τ τ' H H0.
generalize dependent Γ₃. generalize dependent Γ₂. induction H0; intros; eauto.
Case "var".
destruct H. constructor. eauto with fzip. eauto using wfenv_zip13.
destruct H. constructor. eauto with fzip. eauto using wfenv_zip13.
destruct H. constructor. eauto with fzip. eauto using wfenv_zip13.
Case "eq". constructor. eauto with fzip. eauto using wfenv_zip13.
Case "forall". pick fresh a and apply wftypeq_forall; intros.
apply H0 with (Γ₂ := a ~ U ++ Γ₂); auto.
Case "exists". pick fresh a and apply wftypeq_exists; intros.
apply H0 with (Γ₂ := a ~ U ++ Γ₂); auto.
Qed.

Inductive typeq_unfold : typing_env → typ → typ → Prop :=
| typeq_unfold_var : forall Γ a,
    wfenv Γ → (binds a U Γ ∨ binds a E Γ) →
    typeq_unfold Γ (typ_var_f a) (typ_var_f a)
| typeq_unfold_eq : forall Γ a τ τ',
    binds a (Eq τ) Γ → typeq_unfold Γ τ τ' →
    typeq_unfold Γ (typ_var_f a) τ'
| typeq_unfold_arrow : forall Γ τ₁ τ₂ τ₁' τ₂',
    typeq_unfold Γ τ₁ τ₁' → typeq_unfold Γ τ₂ τ₂' →
    typeq_unfold Γ (typ_arrow τ₁ τ₂) (typ_arrow τ₁' τ₂')
| typeq_unfold_prod : forall Γ τ₁ τ₂ τ₁' τ₂',
    typeq_unfold Γ τ₁ τ₁' → typeq_unfold Γ τ₂ τ₂' →
    typeq_unfold Γ (typ_prod τ₁ τ₂) (typ_prod τ₁' τ₂')
| typeq_unfold_forall : forall L Γ τ τ',
    (forall a, a ∉ L →
      typeq_unfold (a ~ U ++ Γ)
                   (open_typ_wrt_typ τ  (typ_var_f a))
                   (open_typ_wrt_typ τ' (typ_var_f a))) →
    typeq_unfold Γ (typ_forall τ) (typ_forall τ')
| typeq_unfold_exists : forall L Γ τ τ',
    (forall a, a ∉ L →
      typeq_unfold (a ~ U ++ Γ)
                   (open_typ_wrt_typ τ  (typ_var_f a))
                   (open_typ_wrt_typ τ' (typ_var_f a))) →
    typeq_unfold Γ (typ_exists τ) (typ_exists τ').
Hint Constructors typeq_unfold.

Lemma typeq_unfold_wfenv : forall Γ τ τ',
  typeq_unfold Γ τ τ' → wfenv Γ.
Proof.
intros Γ τ τ' H. induction H; auto.
Case "forall". pick fresh a; apply wfenv_strip with (Γ' := a ~ U); eauto.
Case "exists". pick fresh a; apply wfenv_strip with (Γ' := a ~ U); eauto.
Qed.

Lemma typeq_unfold_weakening : forall Γ₁ Γ₂ Γ₃ τ τ',
  typeq_unfold (Γ₁ ++ Γ₃) τ τ' →
  wfenv (Γ₁ ++ Γ₂ ++ Γ₃) →
  typeq_unfold (Γ₁ ++ Γ₂ ++ Γ₃) τ τ'.
Proof.
intros Γ₁ Γ₂ Γ₃ τ τ' H H0. dependent induction H; eauto.
Case "var". constructor; auto.
destruct H0; analyze_binds H0.
Case "forall". pick fresh b and apply typeq_unfold_forall; intros.
rewrite_env ((b ~ U ++ Γ₁) ++ Γ₂ ++ Γ₃). apply H0; simpl_env; auto.
Case "exists". pick fresh b and apply typeq_unfold_exists; intros.
rewrite_env ((b ~ U ++ Γ₁) ++ Γ₂ ++ Γ₃). apply H0; simpl_env; auto.
Qed.

Lemma typeq_unfold_unique : forall Γ τ τ₁ τ₂,
  typeq_unfold Γ τ τ₁ → typeq_unfold Γ τ τ₂ → τ₁ = τ₂.
Proof.
intros Γ τ τ₁ τ₂ H H0. generalize dependent τ₂.
induction H; intros τ₀ H₀; inversion H₀; subst; auto.
Case "var eq".
elimtype False. destruct H0.
assert (Eq τ = U). eapply binds_unique; eauto with lngen.
  congruence.
assert (Eq τ = E). eapply binds_unique; eauto with lngen.
  congruence.
Case "eq var".
elimtype False. destruct H4.
assert (Eq τ = U). eapply binds_unique; eauto with lngen.
  congruence.
assert (Eq τ = E). eapply binds_unique; eauto with lngen.
  congruence.
Case "eq eq".
assert (Eq τ = Eq τ0). eapply binds_unique; eauto using typeq_unfold_wfenv with lngen.
replace τ0 with τ in * by congruence. auto.
Case "arrow". f_equal; auto.
Case "prod". f_equal; auto.
Case "forall". f_equal. pick fresh a.
apply open_typ_wrt_typ_inj with (a1 := a); auto.
Case "exists". f_equal. pick fresh a.
apply open_typ_wrt_typ_inj with (a1 := a); auto.
Qed.

Lemma typeq_unfold_wftypeq : forall Γ τ τ',
  typeq_unfold Γ τ τ' → wftypeq Γ τ τ'.
Proof.
intros Γ τ τ' H. induction H; eauto.
Case "var". constructor; auto. tauto.
Case "eq". assert (wfenv Γ) by eauto using typeq_unfold_wfenv.
eauto.
Qed.

Lemma typeq_unfold_renameU : forall Γ₁ a Γ₂ τ τ' b,
  typeq_unfold (Γ₁ ++ a ~ U ++ Γ₂) τ τ' → b ∉ dom (Γ₁ ++ Γ₂) →
  typeq_unfold
    (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ U ++ Γ₂)
    (tsubst_typ (typ_var_f b) a τ)
    (tsubst_typ (typ_var_f b) a τ').
Proof.
intros Γ₁ a Γ₂ τ τ' b H H0. dependent induction H; simpl; simpl_env; auto.
Case "var". unfold typvar; destruct (a == a0); subst.
SCase "a = a0". constructor. auto using wfenv_renameU.
destruct H0; analyze_binds H0.
SCase "a ≠ a0". constructor. auto using wfenv_renameU.
destruct H0; analyze_binds H0.
SSCase "binds a U Γ₁".
replace (@U typ) with (tag_map (tsubst_typ (typ_var_f b) a0) U) by reflexivity.
unfold env_map. auto.
SSCase "binds a E Γ₁".
replace (@E typ) with (tag_map (tsubst_typ (typ_var_f b) a0) E) by reflexivity.
unfold env_map. auto.
Case "eq". unfold typvar; destruct (a == a0); subst.
SCase "a = a0 (absurd)". elimtype False.
analyze_binds_uniq H. eauto using typeq_unfold_wfenv with lngen.
SCase "a ≠ a0". analyze_binds H.
SSCase "a binds in Γ₁". apply typeq_unfold_eq with (τ := (tsubst_typ (typ_var_f b) a0 τ)); auto.
replace (Eq (tsubst_typ (typ_var_f b) a0 τ)) with
(tag_map (tsubst_typ (typ_var_f b) a0) (Eq τ)) by reflexivity.
unfold env_map; auto.
SSCase "a binds in Γ₂". apply typeq_unfold_eq with (τ := τ); auto.
rewrite <- tsubst_typ_fresh_eq with (t2 := τ) (a1 := a0) (t1 := typ_var_f b); auto.
assert (ftv_typ τ [<=] dom Γ₂). apply wftyp_ftv. eapply wfenv_wftyp_Eq2; eauto. apply wfenv_strip with (Γ' := Γ₁ ++ a0 ~ U). eapply typeq_unfold_wfenv; simpl_env; eauto.
assert (uniq (Γ₁ ++ [(a0, U)] ++ Γ₂)). eauto using typeq_unfold_wfenv with lngen.
destruct_uniq; fsetdec.
Case "forall". pick fresh c and apply typeq_unfold_forall; intros.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, U)] ++ Γ₂).
repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
Case "exists". pick fresh c and apply typeq_unfold_exists; intros.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, U)] ++ Γ₂).
repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
Qed.

Lemma typeq_unfold_defined_aux :
  (forall Γ, wfenv Γ → forall Γ₁ a τ Γ₂,
    Γ = Γ₁ ++ a ~ Eq τ ++ Γ₂ → exists τ', typeq_unfold Γ₂ τ τ')
  ∧ (forall Γ τ, wftyp Γ τ →
    (forall Γ₁ a τ Γ₂,
      Γ = Γ₁ ++ a ~ Eq τ ++ Γ₂ → exists τ', typeq_unfold Γ₂ τ τ')
    ∧ exists τ', typeq_unfold Γ τ τ').
Proof.
apply wfenv_wftyp_mut_ind; intros.
Case "nil". destruct Γ₁; inversion H.
Case "T". destruct Γ₁; inversion H0; subst.
destruct H. destruct (H Γ₁ a τ Γ₂). simpl_env; auto. eauto.
Case "U". destruct Γ₁; inversion H0; subst.
destruct (H Γ₁ a0 τ Γ₂). simpl_env; auto. eauto.
Case "E". destruct Γ₁; inversion H0; subst.
destruct (H Γ₁ a0 τ Γ₂). simpl_env; auto. eauto.
Case "Eq". destruct H. destruct Γ₁; inversion H0; subst.
destruct H1; eauto.
destruct (H Γ₁ a0 τ Γ₂). simpl_env; auto. eauto.
Case "var". split; intros; eauto.
destruct o; eauto. destruct H0; eauto.
destruct H0.
destruct (binds_decomp G a (Eq x)) as [? [? ?]]; auto; subst.
destruct (H x0 a x x1); auto.
exists x2. apply typeq_unfold_eq with (τ := x); auto.
rewrite_env (nil ++ (x0 ++ a ~ Eq x) ++ x1).
apply typeq_unfold_weakening; simpl_env; auto.
Case "arrow". destruct H. destruct H0. split; intros; subst.
edestruct H; eauto.
destruct H1; destruct H2; eauto.
Case "prod". destruct H. destruct H0. split; intros; subst.
edestruct H; eauto.
destruct H1; destruct H2; eauto.
Case "forall". pick fresh b. edestruct H; eauto. clear H. split; intros; subst.
destruct (H0 (b ~ U ++ Γ₁) a τ Γ₂); simpl_env; eauto.
destruct H1.
rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (t1 := x) (a1 := b) in H.
exists (typ_forall (close_typ_wrt_typ b x)).
apply typeq_unfold_forall with (L := L ∪ dom G); intros.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ a ~ U ++ G).
replace (open_typ_wrt_typ t (typ_var_f a)) with (tsubst_typ (typ_var_f a) b (open_typ_wrt_typ t (typ_var_f b))).
replace (open_typ_wrt_typ (close_typ_wrt_typ b x) (typ_var_f a)) with (tsubst_typ (typ_var_f a) b (open_typ_wrt_typ (close_typ_wrt_typ b x) (typ_var_f b))).
apply typeq_unfold_renameU; simpl_env; auto.
autorewrite with lngen. apply tsubst_typ_spec.
rewrite tsubst_typ_open_typ_wrt_typ; auto. simpl.
unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_typ_fresh_eq; auto.
Case "exists". pick fresh b. edestruct H; eauto. clear H. split; intros; subst.
destruct (H0 (b ~ U ++ Γ₁) a τ Γ₂); simpl_env; eauto.
destruct H1.
rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (t1 := x) (a1 := b) in H.
exists (typ_exists (close_typ_wrt_typ b x)).
apply typeq_unfold_exists with (L := L ∪ dom G); intros.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ a ~ U ++ G).
replace (open_typ_wrt_typ t (typ_var_f a)) with (tsubst_typ (typ_var_f a) b (open_typ_wrt_typ t (typ_var_f b))).
replace (open_typ_wrt_typ (close_typ_wrt_typ b x) (typ_var_f a)) with (tsubst_typ (typ_var_f a) b (open_typ_wrt_typ (close_typ_wrt_typ b x) (typ_var_f b))).
apply typeq_unfold_renameU; simpl_env; auto.
autorewrite with lngen. apply tsubst_typ_spec.
rewrite tsubst_typ_open_typ_wrt_typ; auto. simpl.
unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_typ_fresh_eq; auto.
Qed.

Lemma typeq_unfold_defined : forall Γ τ,
  wftyp Γ τ → exists τ', typeq_unfold Γ τ τ'.
Proof.
intros Γ τ H. destruct typeq_unfold_defined_aux as [_ H0].
edestruct H0 as [_ ?]; eauto.
Qed.

Definition algtypeq Γ τ₁ τ₂ := exists τ₀,
  typeq_unfold Γ τ₁ τ₀ ∧ typeq_unfold Γ τ₂ τ₀.
Hint Unfold algtypeq.

Lemma algtypeq_refl : forall Γ τ, wftyp Γ τ → algtypeq Γ τ τ.
Proof.
intros Γ τ H. apply typeq_unfold_defined in H. destruct H; eauto.
Qed.

Lemma algtypeq_sym : forall Γ τ₁ τ₂,
  algtypeq Γ τ₁ τ₂ → algtypeq Γ τ₂ τ₁.
Proof.
intros Γ τ₁ τ₂ H. destruct H as [? [? ?]]; eauto.
Qed.

Lemma algtypeq_trans : forall Γ τ₁ τ₂ τ₃,
  algtypeq Γ τ₁ τ₂ → algtypeq Γ τ₂ τ₃ → algtypeq Γ τ₁ τ₃.
Proof.
intros Γ τ₁ τ₂ τ₃ H H0.
destruct H as [τ₁₂ [? ?]]. destruct H0 as [τ₂₃ [? ?]].
assert (τ₁₂ = τ₂₃) by eauto using typeq_unfold_unique. subst.
eauto.
Qed.

Lemma algtypeq_wftypeq : forall Γ τ₁ τ₂,
  algtypeq Γ τ₁ τ₂ → wftypeq Γ τ₁ τ₂.
Proof.
intros Γ τ₁ τ₂ H. destruct H as [τ₃ [? ?]].
eauto using typeq_unfold_wftypeq.
Qed.

Lemma wftypeq_algtypeq : forall Γ τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → algtypeq Γ τ₁ τ₂.
Proof.
intros Γ τ₁ τ₂ H. induction H.
Case "var". destruct H. eauto 8. destruct H. eauto 8.
destruct H. assert (exists τ, typeq_unfold G x τ) as [? ?].
apply typeq_unfold_defined. eapply wfenv_wftyp_Eq2; eauto.
eauto 6.
Case "eq". assert (exists τ, typeq_unfold G t τ) as [? ?].
apply typeq_unfold_defined. eapply wfenv_wftyp_Eq2; eauto.
eauto 6.
Case "arrow". destruct IHwftypeq1 as [? [? ?]]; destruct IHwftypeq2 as [? [? ?]].
eauto 6.
Case "prod". destruct IHwftypeq1 as [? [? ?]]; destruct IHwftypeq2 as [? [? ?]].
eauto 6.
Case "forall". pick fresh a.
edestruct H0 as [? [? ?]]; eauto. clear H0.
rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (a1 := a) (t1 := x) in H1.
rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (a1 := a) (t1 := x) in H2.
exists (typ_forall (close_typ_wrt_typ a x)). split.
SCase "left part". clear H2.
apply typeq_unfold_forall with (L := L ∪ {{a}} ∪ ftv_typ t1 ∪ ftv_typ x ∪ dom G); intros.
rewrite_env (nil ++ a ~ U ++ G) in H1.
apply typeq_unfold_renameU with (b := a0) in H1; auto.
rewrite tsubst_typ_open_typ_wrt_typ in H1; auto.
simpl in H1.
unfold typvar in *; destruct (a == a); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ in H1; auto.
simpl in H1.
unfold typvar in *; destruct (a == a); try congruence.
rewrite tsubst_typ_fresh_eq with (t2 := t1) in H1; auto.
rewrite tsubst_typ_fresh_eq with (t2 := close_typ_wrt_typ a x) in H1; auto.
autorewrite with lngen. fsetdec.
SCase "right part". clear H1.
apply typeq_unfold_forall with (L := L ∪ {{a}} ∪ ftv_typ t2 ∪ ftv_typ x ∪ dom G); intros.
rewrite_env (nil ++ a ~ U ++ G) in H2.
apply typeq_unfold_renameU with (b := a0) in H2; auto.
rewrite tsubst_typ_open_typ_wrt_typ in H2; auto.
simpl in H2.
unfold typvar in *; destruct (a == a); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ in H2; auto.
simpl in H2.
unfold typvar in *; destruct (a == a); try congruence.
rewrite tsubst_typ_fresh_eq with (t2 := t2) in H2; auto.
rewrite tsubst_typ_fresh_eq with (t2 := close_typ_wrt_typ a x) in H2; auto.
autorewrite with lngen. fsetdec.
Case "exists". pick fresh a.
edestruct H0 as [? [? ?]]; eauto. clear H0.
rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (a1 := a) (t1 := x) in H1.
rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (a1 := a) (t1 := x) in H2.
exists (typ_exists (close_typ_wrt_typ a x)). split.
SCase "left part". clear H2.
apply typeq_unfold_exists with (L := L ∪ {{a}} ∪ ftv_typ t1 ∪ ftv_typ x ∪ dom G); intros.
rewrite_env (nil ++ a ~ U ++ G) in H1.
apply typeq_unfold_renameU with (b := a0) in H1; auto.
rewrite tsubst_typ_open_typ_wrt_typ in H1; auto.
simpl in H1.
unfold typvar in *; destruct (a == a); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ in H1; auto.
simpl in H1.
unfold typvar in *; destruct (a == a); try congruence.
rewrite tsubst_typ_fresh_eq with (t2 := t1) in H1; auto.
rewrite tsubst_typ_fresh_eq with (t2 := close_typ_wrt_typ a x) in H1; auto.
autorewrite with lngen. fsetdec.
SCase "right part". clear H1.
apply typeq_unfold_exists with (L := L ∪ {{a}} ∪ ftv_typ t2 ∪ ftv_typ x ∪ dom G); intros.
rewrite_env (nil ++ a ~ U ++ G) in H2.
apply typeq_unfold_renameU with (b := a0) in H2; auto.
rewrite tsubst_typ_open_typ_wrt_typ in H2; auto.
simpl in H2.
unfold typvar in *; destruct (a == a); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ in H2; auto.
simpl in H2.
unfold typvar in *; destruct (a == a); try congruence.
rewrite tsubst_typ_fresh_eq with (t2 := t2) in H2; auto.
rewrite tsubst_typ_fresh_eq with (t2 := close_typ_wrt_typ a x) in H2; auto.
autorewrite with lngen. fsetdec.
Case "sym". auto using algtypeq_sym.
Case "trans". eauto using algtypeq_trans.
Qed.

Lemma wftypeq_arrow_inv1 : forall Γ τ₁ τ₂ τ₁' τ₂',
  wftypeq Γ (typ_arrow τ₁ τ₂) (typ_arrow τ₁' τ₂') →
  wftypeq Γ τ₁ τ₁'.
Proof.
intros Γ τ₁ τ₂ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
apply algtypeq_wftypeq. eauto.
Qed.

Lemma wftypeq_arrow_inv2 : forall Γ τ₁ τ₂ τ₁' τ₂',
  wftypeq Γ (typ_arrow τ₁ τ₂) (typ_arrow τ₁' τ₂') →
  wftypeq Γ τ₂ τ₂'.
Proof.
intros Γ τ₁ τ₂ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
apply algtypeq_wftypeq. eauto.
Qed.

Lemma wftypeq_prod_inv1 : forall Γ τ₁ τ₂ τ₁' τ₂',
  wftypeq Γ (typ_prod τ₁ τ₂) (typ_prod τ₁' τ₂') →
  wftypeq Γ τ₁ τ₁'.
Proof.
intros Γ τ₁ τ₂ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
apply algtypeq_wftypeq. eauto.
Qed.

Lemma wftypeq_prod_inv2 : forall Γ τ₁ τ₂ τ₁' τ₂',
  wftypeq Γ (typ_prod τ₁ τ₂) (typ_prod τ₁' τ₂') →
  wftypeq Γ τ₂ τ₂'.
Proof.
intros Γ τ₁ τ₂ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
apply algtypeq_wftypeq. eauto.
Qed.

Lemma wftypeq_forall_inv : forall Γ τ τ' a,
  wftypeq Γ (typ_forall τ) (typ_forall τ') →
  a ∉ dom Γ →
  wftypeq (a ~ U ++ Γ)
          (open_typ_wrt_typ τ (typ_var_f a))
          (open_typ_wrt_typ τ' (typ_var_f a)).
Proof.
intros Γ τ τ' a H Ha.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst. clear H H0.
apply algtypeq_wftypeq.
pick fresh b.
assert (typeq_unfold ([(b, U)] ++ Γ)
  (open_typ_wrt_typ τ (typ_var_f b))
  (open_typ_wrt_typ τ'0 (typ_var_f b))) by auto; clear H3.
rewrite_env (nil ++ b ~ U ++ Γ) in H.
apply typeq_unfold_renameU with (b := a) in H; auto.
rewrite tsubst_typ_open_typ_wrt_typ in H; auto.
simpl in H. unfold typvar in *; destruct (b == b); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ in H; auto.
simpl in H. unfold typvar in *; destruct (b == b); try congruence.
rewrite tsubst_typ_fresh_eq in H; auto.
rewrite tsubst_typ_fresh_eq in H; auto.
simpl_env in H.
assert (typeq_unfold ([(b, U)] ++ Γ)
  (open_typ_wrt_typ τ' (typ_var_f b))
  (open_typ_wrt_typ τ'0 (typ_var_f b))) by auto; clear H5.
rewrite_env (nil ++ b ~ U ++ Γ) in H0.
apply typeq_unfold_renameU with (b := a) in H0; auto.
rewrite tsubst_typ_open_typ_wrt_typ in H0; auto.
simpl in H0. unfold typvar in *; destruct (b == b); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ in H0; auto.
simpl in H0. unfold typvar in *; destruct (b == b); try congruence.
rewrite tsubst_typ_fresh_eq in H0; auto.
rewrite tsubst_typ_fresh_eq in H0; auto.
simpl_env in H0.
eauto.
Qed.

Lemma wftypeq_exists_inv : forall Γ τ τ' a,
  wftypeq Γ (typ_exists τ) (typ_exists τ') →
  a ∉ dom Γ →
  wftypeq (a ~ U ++ Γ)
          (open_typ_wrt_typ τ (typ_var_f a))
          (open_typ_wrt_typ τ' (typ_var_f a)).
Proof.
intros Γ τ τ' a H Ha.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst. clear H H0.
apply algtypeq_wftypeq.
pick fresh b.
assert (typeq_unfold ([(b, U)] ++ Γ)
  (open_typ_wrt_typ τ (typ_var_f b))
  (open_typ_wrt_typ τ'0 (typ_var_f b))) by auto; clear H3.
rewrite_env (nil ++ b ~ U ++ Γ) in H.
apply typeq_unfold_renameU with (b := a) in H; auto.
rewrite tsubst_typ_open_typ_wrt_typ in H; auto.
simpl in H. unfold typvar in *; destruct (b == b); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ in H; auto.
simpl in H. unfold typvar in *; destruct (b == b); try congruence.
rewrite tsubst_typ_fresh_eq in H; auto.
rewrite tsubst_typ_fresh_eq in H; auto.
simpl_env in H.
assert (typeq_unfold ([(b, U)] ++ Γ)
  (open_typ_wrt_typ τ' (typ_var_f b))
  (open_typ_wrt_typ τ'0 (typ_var_f b))) by auto; clear H5.
rewrite_env (nil ++ b ~ U ++ Γ) in H0.
apply typeq_unfold_renameU with (b := a) in H0; auto.
rewrite tsubst_typ_open_typ_wrt_typ in H0; auto.
simpl in H0. unfold typvar in *; destruct (b == b); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ in H0; auto.
simpl in H0. unfold typvar in *; destruct (b == b); try congruence.
rewrite tsubst_typ_fresh_eq in H0; auto.
rewrite tsubst_typ_fresh_eq in H0; auto.
simpl_env in H0.
eauto.
Qed.

Lemma wftypeq_arrow_prod_absurd : forall Γ τ₁ τ₂ τ₁' τ₂',
  wftypeq Γ (typ_arrow τ₁ τ₂) (typ_prod τ₁' τ₂') → False.
Proof.
intros Γ τ₁ τ₂ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_arrow_forall_absurd : forall Γ τ₁ τ₂ τ',
  wftypeq Γ (typ_arrow τ₁ τ₂) (typ_forall τ') → False.
Proof.
intros Γ τ₁ τ₂ τ' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_arrow_exists_absurd : forall Γ τ₁ τ₂ τ',
  wftypeq Γ (typ_arrow τ₁ τ₂) (typ_exists τ') → False.
Proof.
intros Γ τ₁ τ₂ τ' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_prod_arrow_absurd : forall Γ τ₁ τ₂ τ₁' τ₂',
  wftypeq Γ (typ_prod τ₁ τ₂) (typ_arrow τ₁' τ₂') → False.
Proof.
intros Γ τ₁ τ₂ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_prod_forall_absurd : forall Γ τ₁ τ₂ τ',
  wftypeq Γ (typ_prod τ₁ τ₂) (typ_forall τ') → False.
Proof.
intros Γ τ₁ τ₂ τ' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_prod_exists_absurd : forall Γ τ₁ τ₂ τ',
  wftypeq Γ (typ_prod τ₁ τ₂) (typ_exists τ') → False.
Proof.
intros Γ τ₁ τ₂ τ' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_forall_arrow_absurd : forall Γ τ τ₁' τ₂',
  wftypeq Γ (typ_forall τ) (typ_arrow τ₁' τ₂') → False.
Proof.
intros Γ τ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_forall_prod_absurd : forall Γ τ τ₁' τ₂',
  wftypeq Γ (typ_forall τ) (typ_prod τ₁' τ₂') → False.
Proof.
intros Γ τ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_forall_exists_absurd : forall Γ τ τ',
  wftypeq Γ (typ_forall τ) (typ_exists τ') → False.
Proof.
intros Γ τ τ' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_exists_arrow_absurd : forall Γ τ τ₁' τ₂',
  wftypeq Γ (typ_exists τ) (typ_arrow τ₁' τ₂') → False.
Proof.
intros Γ τ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_exists_prod_absurd : forall Γ τ τ₁' τ₂',
  wftypeq Γ (typ_exists τ) (typ_prod τ₁' τ₂') → False.
Proof.
intros Γ τ τ₁' τ₂' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.

Lemma wftypeq_exists_forall_absurd : forall Γ τ τ',
  wftypeq Γ (typ_exists τ) (typ_forall τ') → False.
Proof.
intros Γ τ τ' H.
apply wftypeq_algtypeq in H. destruct H as [? [? ?]].
inversion H; subst. inversion H0; subst.
Qed.
