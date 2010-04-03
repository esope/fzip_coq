Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_zip.
Require Import FzipCore_pure.
Require Import FzipCore_env_typ.


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
