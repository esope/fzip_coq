Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_pure.
Require Import FzipCore_zip.
Require Import FzipCore_env_typ.
Require Import FzipCore_term.

Lemma pure_renameT : forall Γ₁ Γ₂ x y (τ: typ),
  pure (Γ₁ ++ x ~ T τ ++ Γ₂) →
  pure (Γ₁ ++ y ~ T τ ++ Γ₂).
Proof.
intros Γ₁ Γ₂ x y τ H.
unfold env_map.
intros a0 H0.
eapply (H a0). analyze_binds H0. 
Qed.

Lemma zip_renameT : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' x y τ,
  y ∉ dom (Γ₁ ++ Γ₁') ∪ dom (Γ₂ ++ Γ₂') ∪ dom (Γ₃ ++ Γ₃') →
  zip (Γ₁ ++ x ~ T τ ++ Γ₁') (Γ₂ ++ x ~ T τ ++ Γ₂') (Γ₃ ++ x ~ T τ ++ Γ₃') →
  zip (Γ₁ ++ y ~ T τ ++ Γ₁')
      (Γ₂ ++ y ~ T τ ++ Γ₂')
      (Γ₃ ++ y ~ T τ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' x y τ Hb H.
assert (uniq (Γ₁ ++ [(x, T τ)] ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ [(x, T τ)] ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ [(x, T τ)] ++ Γ₃')) by eauto with lngen.
simpl_env in *.
apply zip_app_inv in H. decompose record H; clear H; simpl_env in *.
inversion H7; subst.
apply uniq_app_inv in H3; auto.
apply uniq_app_inv in H4; auto.
destruct H3; destruct H4; subst; auto.
apply zip_app; auto.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
Qed.

(* begin hide *)
Lemma wfenv_wftyp_renameT_aux:
  (forall Γ, Γ ⊢ ok → forall Γ₁ Γ₂ a b τ,
    Γ = Γ₁ ++ a ~ T τ ++ Γ₂ →
    b ∉ dom (Γ₂ ++ Γ₁) → Γ₁ ++ b ~ T τ ++ Γ₂ ⊢ ok)
  ∧ (forall Γ τ, Γ ⊢ τ ok → forall Γ₁ Γ₂ a b τ',
    Γ = Γ₁ ++ a ~ T τ' ++ Γ₂ →
    b ∉ dom (Γ₂ ++ Γ₁) → Γ₁ ++ b ~ T τ' ++ Γ₂ ⊢ τ ok).
Proof.
apply wfenv_wftyp_mut_ind; intros; subst; simpl; simpl_env; eauto.
Case "nil".
assert (binds a (T τ) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor; eauto. 
Case "U". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor; eauto. 
Case "E". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor; eauto. 
Case "Eq". destruct Γ₁; inversion H0; subst; simpl; simpl_env in *; auto.
constructor; eauto. 
Case "var". constructor; eauto.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0.
destruct H0. right; right. analyze_binds H0; eauto.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}} ∪ {{b}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ b ~ T τ' ++ Γ₂). eapply H; simpl_env; eauto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}} ∪ {{b}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ b ~ T τ' ++ Γ₂). eapply H; simpl_env; eauto.
Qed.
(* end hide *)

Lemma wfenv_renameT:
  forall Γ₁ Γ₂ x y τ,
    Γ₁ ++ x ~ T τ ++ Γ₂ ⊢ ok →
    y ∉ dom (Γ₂ ++ Γ₁) →
    Γ₁ ++ y ~ T τ ++ Γ₂ ⊢ ok.
Proof.
intros. edestruct wfenv_wftyp_renameT_aux. eauto.
Qed.

Lemma wftyp_renameT:
  forall Γ₁ Γ₂ τ x y τ',
    Γ₁ ++ x ~ T τ' ++ Γ₂ ⊢ τ ok →
    y ∉ dom (Γ₂ ++ Γ₁) →
    Γ₁ ++ y ~ T τ' ++ Γ₂ ⊢ τ ok.
Proof.
intros. edestruct wfenv_wftyp_renameT_aux. eauto.
Qed.

Lemma wftypeq_renameT:
  forall Γ₁ Γ₂ x y τ₀ τ τ',
    Γ₁ ++ x ~ T τ₀ ++ Γ₂ ⊢ τ ≡ τ' →
    y ∉ dom (Γ₂ ++ Γ₁) →
    Γ₁ ++ y ~ T τ₀ ++ Γ₂ ⊢ τ ≡ τ'.
Proof.
intros Γ₁ Γ₂ x y τ₀ τ τ' H H0.
dependent induction H; try solve [constructor; eauto].
Case "var". constructor; eauto using wfenv_renameT.
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto 6.
Case "eq". constructor; eauto using wfenv_renameT. analyze_binds H.
Case "forall". pick fresh a and apply wftypeq_forall.
rewrite_env ((a ~ U ++ Γ₁) ++ y ~ T τ₀ ++ Γ₂).
eapply H0; simpl_env; eauto.
Case "exists". pick fresh a and apply wftypeq_exists.
rewrite_env ((a ~ U ++ Γ₁) ++ y ~ T τ₀ ++ Γ₂).
eapply H0; simpl_env; eauto.
Qed.

Lemma wfterm_renameT : forall Γ₁ Γ₂ x y e τ τ₀,
  Γ₁ ++ x ~ T τ₀ ++ Γ₂ ⊢ e ~: τ →
  y ∉ dom (Γ₁ ++ Γ₂) →
  Γ₁ ++ y ~ T τ₀ ++ Γ₂ ⊢
  subst_term (term_var_f y) x e ~: τ.
Proof.
intros Γ₁ Γ₂ x y e τ τ₀ H H0. dependent induction H; simpl; simpl_env.
Case "var". destruct (x == x0).
SCase "x = x0". constructor.
apply pure_app; eauto with fzip.
eauto using wfenv_renameT.
subst. analyze_binds_uniq H1. eauto with lngen.
SCase "x ≠ x0". constructor.
apply pure_app; eauto with fzip.
eauto using wfenv_renameT.
analyze_binds H1.
Case "app".
assert (uniq G1) by eauto with lngen.
assert (uniq G2) by eauto with lngen.
assert (uniq (Γ₁ ++ [(x, T τ₀)] ++ Γ₂)) by eauto with lngen.
destruct (zip_app_inv G1 G2 Γ₁ ([(x, T τ₀)] ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H9; subst.
simpl_env in *.
assert (dom x0 [<=] dom Γ₁) by eauto with fzip.
assert (dom x2 [=] dom Γ₁) by eauto with fzip.
assert (dom G1 [<=] dom Γ₂) by eauto with fzip.
assert (dom G2 [=] dom Γ₂) by eauto with fzip.
apply wfterm_app with
  (G1 := x0 ++ [(y, T τ₀)] ++ G1)
  (G2 := x2 ++ [(y, T τ₀)] ++ G2)
  (t2 := t2).
eapply zip_renameT; eauto. simpl_env. fsetdec.
apply IHwfterm1; auto. simpl_env; fsetdec.
apply IHwfterm2; auto. simpl_env; fsetdec.
Case "abs".
pick fresh z and apply wfterm_abs. eauto using pure_renameT.
rewrite subst_term_open_term_wrt_term_var; auto.
rewrite_env ((z ~ T t1 ++ Γ₁) ++ [(y, T τ₀)] ++ Γ₂).
auto.
Case "let".
assert (uniq G1) by eauto with lngen.
assert (uniq G2) by eauto with lngen.
assert (uniq (Γ₁ ++ [(x, T τ₀)] ++ Γ₂)) by eauto with lngen.
destruct (zip_app_inv G1 G2 Γ₁ ([(x, T τ₀)] ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H10; subst.
simpl_env in *.
assert (dom x0 [<=] dom Γ₁) by eauto with fzip.
assert (dom x2 [=] dom Γ₁) by eauto with fzip.
assert (dom G1 [<=] dom Γ₂) by eauto with fzip.
assert (dom G2 [=] dom Γ₂) by eauto with fzip.
apply wfterm_let with (L := L ∪ {{x}} ∪ {{y}})
  (G1 := x0 ++ [(y, T τ₀)] ++ G1)
  (G2 := x2 ++ [(y, T τ₀)] ++ G2)
  (t1 := t1); intros.
eapply zip_renameT; eauto. simpl_env. fsetdec.
apply IHwfterm; auto. simpl_env; fsetdec.
rewrite_env ((x1 ~ T t1 ++ x2) ++ [(y, T τ₀)] ++ G2).
rewrite subst_term_open_term_wrt_term_var; auto.
apply H2; auto. simpl_env; fsetdec.
Case "pair".
assert (uniq G1) by eauto with lngen.
assert (uniq G2) by eauto with lngen.
assert (uniq (Γ₁ ++ [(x, T τ₀)] ++ Γ₂)) by eauto with lngen.
destruct (zip_app_inv G1 G2 Γ₁ ([(x, T τ₀)] ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H9; subst.
simpl_env in *.
assert (dom x0 [<=] dom Γ₁) by eauto with fzip.
assert (dom x2 [=] dom Γ₁) by eauto with fzip.
assert (dom G1 [<=] dom Γ₂) by eauto with fzip.
assert (dom G2 [=] dom Γ₂) by eauto with fzip.
apply wfterm_pair with
  (G1 := x0 ++ [(y, T τ₀)] ++ G1)
  (G2 := x2 ++ [(y, T τ₀)] ++ G2).
eapply zip_renameT; eauto. simpl_env. fsetdec.
apply IHwfterm1; auto. simpl_env; fsetdec.
apply IHwfterm2; auto. simpl_env; fsetdec.
Case "fst".
apply wfterm_fst with (t2 := t2). apply IHwfterm; auto.
Case "snd".
apply wfterm_snd with (t1 := t1). apply IHwfterm; auto.
Case "inst". apply wfterm_inst.
eauto using wftyp_renameT.
apply IHwfterm; auto.
Case "gen".
pick fresh c and apply wfterm_gen. eauto using pure_renameT.
rewrite subst_term_open_term_wrt_typ_var; auto.
rewrite_env ((c ~ U ++ Γ₁) ++ [(y, T τ₀)] ++ Γ₂). auto.
Case "exists".
pick fresh c and apply wfterm_exists.
rewrite subst_term_open_term_wrt_typ_var; auto.
rewrite_env ((c ~ E ++ Γ₁) ++ [(y, T τ₀)] ++ Γ₂). auto.
Case "open".
assert (binds b E (Γ₁ ++ (x, T τ₀) :: Γ₂)). rewrite <- H2; auto.
analyze_binds H3.
SSCase "b binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
simpl_env in H2.
apply uniq_app_inv in H2. destruct H2; subst. simpl_env.
apply wfterm_open. auto.
rewrite_env ((x0 ++ x1) ++ [(y, T τ₀)] ++ Γ₂).
apply IHwfterm; simpl_env; auto.
assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
SSCase "b0 binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in H2.
rewrite_env ((Γ₁ ++ [(x, T τ₀)] ++ x0) ++ [(b, E)] ++ x1) in H2.
apply uniq_app_inv in H2. destruct H2; subst.
rewrite_env ((Γ₁ ++ [(y, T τ₀)] ++ x0) ++ [(b, E)] ++ x1).
apply wfterm_open. auto.
simpl_env. apply IHwfterm; simpl_env; auto.
assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
Case "nu".
pick fresh c and apply wfterm_nu.
rewrite subst_term_open_term_wrt_typ_var; auto.
rewrite_env ((c ~ E ++ Γ₁) ++ [(y, T τ₀)] ++ Γ₂). auto.
Case "sigma".
assert (binds b E (Γ₁ ++ (x, T τ₀) :: Γ₂)). rewrite <- H3; auto.
analyze_binds H4.
SSCase "b binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
simpl_env in H3.
apply uniq_app_inv in H3. destruct H3; subst. simpl_env.
pick fresh c and apply wfterm_sigma. auto.
rewrite_env ((c ~ Eq t' ++ x0 ++ x1) ++ [(y, T τ₀)] ++ Γ₂).
rewrite subst_term_open_term_wrt_typ_var; auto.
apply H1; simpl_env; auto.
pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
SSCase "b binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in H3.
rewrite_env ((Γ₁ ++ [(x, T τ₀)] ++ x0) ++ [(b, E)] ++ x1) in H3.
apply uniq_app_inv in H3. destruct H3; subst.
rewrite_env ((Γ₁ ++ [(y, T τ₀)] ++ x0) ++ [(b, E)] ++ x1).
pick fresh c and apply wfterm_sigma. auto.
rewrite subst_term_open_term_wrt_typ_var; auto.
rewrite_env ((c ~ Eq t' ++ Γ₁) ++ [(y, T τ₀)] ++ x0 ++ x1).
apply H1; simpl_env; auto.
pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
Case "coerce".
apply wfterm_coerce with (t' := t').
eauto using wftypeq_renameT. auto.
Qed.

