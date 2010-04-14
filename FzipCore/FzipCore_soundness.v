Add LoadPath "../metatheory".
Require Export FzipCore_init.
Require Import FzipCore_val.
Require Import FzipCore_red.
Require Import FzipCore_zip.
Require Import FzipCore_pure.
Require Import FzipCore_env_typ.
Require Import FzipCore_typeq.
Require Import FzipCore_term.

(** Soundness *)
Lemma sr0 :  forall Γ e e' τ,
  wfterm Γ e τ → red0 e e' → wfterm Γ e' τ.
Proof.
intros Γ e e' τ H H0. destruct H0; inversion H; subst.
Case "beta_v_red".
assert (pure G2) by eauto using val_pure.
inversion H7; subst.
assert (pure Γ) by eauto using pure_zip.
assert (G1 = Γ) by eauto using zip_pure_inv1.
assert (G2 = Γ) by eauto using zip_pure_inv2.
subst. eauto.
Case "beta_v_let".
pick fresh x. rewrite subst_term_intro with (x1 := x); auto.
assert (pure G1) by eauto using val_pure.
rewrite_env (nil ++ Γ). eapply wfterm_subst; eauto. simpl_env; auto.
Case "proj fst".
assert (pure Γ) by eauto using val_pure.
inversion H3; subst.
assert (G1 = Γ) by eauto using zip_pure_inv1.
subst. auto.
Case "proj snd".
assert (pure Γ) by eauto using val_pure.
inversion H3; subst.
assert (G2 = Γ) by eauto using zip_pure_inv2.
subst. auto.
Case "beta_t".
inversion H7; subst.
pick fresh a.
rewrite tsubst_term_intro with (a1 := a); auto.
rewrite tsubst_typ_intro with (a1 := a); auto.
rewrite_env (env_map (tsubst_typ t a) nil ++ Γ).
eapply wfterm_tsubst; simpl_env; eauto.
Case "open exists".
inversion H6; subst.
rewrite_env (nil ++ G2 ++ [(b, E)] ++ G1). apply wfterm_upperE.
pick fresh a.
replace (typ_var_f b) with (tsubst_typ (typ_var_f b) a (typ_var_f a)).
rewrite <- tsubst_env_fresh_eq with (G := nil) (a := a) (t := typ_var_f b); auto.
rewrite <- tsubst_term_fresh_eq with (e1 := e) (a1 := a) (t1 := typ_var_f b); auto.
rewrite <- tsubst_typ_fresh_eq with (t2 := t) (a1 := a) (t1 := typ_var_f b); auto.
rewrite <- tsubst_term_open_term_wrt_typ; auto.
rewrite <- tsubst_typ_open_typ_wrt_typ; auto.
apply wfterm_renameE; auto.
simpl_env; auto.
simpl; unfold typvar; destruct (a == a); congruence.
Case "nu_sigma".
pick fresh b.
assert (wfterm (b ~ E ++ Γ) (open_term_wrt_typ (term_sigma (typ_var_b 0) t e) (typ_var_f b)) τ) by auto.
assert (uniq (b ~ E ++ Γ)) by eauto with lngen.
unfold open_term_wrt_typ in H5; simpl in H5; simpl_env in H5.
inversion H5; subst.
simpl_env in H8; rewrite_env (nil ++ b ~ E ++ Γ) in H8.
symmetry in H8; apply uniq_app_inv in H8. destruct H8; subst; simpl_env in *.
pick fresh a.
erewrite H4 with (b := b) (a := a)
(e1 := open_term_wrt_typ_rec 1 (typ_var_f b) e); try reflexivity; auto.
rewrite <- tsubst_typ_fresh_eq with (t1 := open_typ_wrt_typ_rec 0 (typ_var_f b) t) (a1 := a) (t2 := τ); auto.
rewrite_env (env_map (tsubst_typ (open_typ_wrt_typ_rec 0 (typ_var_f b) t) a) nil ++ G1).
apply wfterm_subst_eq. simpl_env.
rewrite <- tsubst_typ_fresh_eq with (t1 := typ_var_f a) (a1 := b) (t2 := τ); auto.
solve_uniq.
Case "coerce_app".
inversion H9; subst. inversion H14; subst.
assert (wftypeq G1 t2' t3) by eauto using wftypeq_arrow_inv1.
assert (wftypeq G1 t2 τ) by eauto using wftypeq_arrow_inv2.
apply wfterm_coerce with (t' := t2); auto.
eauto using wftypeq_zip13.
apply wfterm_app with (G1 := G1) (G2 := G2) (t2 := t2'); auto.
apply wfterm_coerce with (t' := t3); auto. apply wftypeq_sym.
eauto using wftypeq_zip12.
Case "coerce_fst".
inversion H5; subst.
inversion H10; subst.
assert (wftypeq Γ t1 τ) by eauto using wftypeq_prod_inv1.
apply wfterm_coerce with (t' := t1); eauto.
Case "coerce_snd".
inversion H5; subst.
inversion H10; subst.
assert (wftypeq Γ t2 τ) by eauto using wftypeq_prod_inv2.
apply wfterm_coerce with (t' := t2); eauto.
Case "coerce_inst".
inversion H8; subst.
inversion H10; subst.
assert (forall a, a ∉ dom Γ →
  wftypeq (a ~ U ++ Γ)
  (open_typ_wrt_typ t (typ_var_f a))
  (open_typ_wrt_typ t' (typ_var_f a))) by eauto using wftypeq_forall_inv.
apply wfterm_coerce with (t' := open_typ_wrt_typ t t2); auto.
pick fresh a.
rewrite tsubst_typ_intro with (a1 := a) (t1 := t); auto.
rewrite tsubst_typ_intro with (a1 := a) (t1 := t'); auto.
rewrite_env (env_map (tsubst_typ t2 a) nil ++ Γ).
apply wftypeq_tsubst; simpl_env; auto.
Case "coerce_open".
inversion H7; subst.
inversion H9; subst.
assert (forall a, a ∉ dom (G2 ++ G1) →
  wftypeq (a ~ U ++ G2 ++ G1)
  (open_typ_wrt_typ t (typ_var_f a))
  (open_typ_wrt_typ t0 (typ_var_f a))) by eauto using wftypeq_exists_inv.
apply wfterm_coerce with (t' := open_typ_wrt_typ t (typ_var_f b)).
rewrite_env (nil ++ G2 ++ [(b, E)] ++ G1). apply wftypeq_upperE. apply wftypeq_UE. simpl_env; auto.
pick fresh a.
replace (typ_var_f b) with (tsubst_typ (typ_var_f b) a (typ_var_f a)).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) nil ++ G2 ++ [(b, E)] ++ G1).
rewrite <- tsubst_typ_fresh_eq with (t1 := typ_var_f b) (a1 := a) (t2 := t); auto.
rewrite <- tsubst_term_fresh_eq with (t1 := typ_var_f b) (a1 := a) (e1 := e); auto.
rewrite <- tsubst_typ_open_typ_wrt_typ; auto.
apply wfterm_upperE.
replace (term_open (tsubst_typ (typ_var_f b) a (typ_var_f a))
       (term_exists (tsubst_term (typ_var_f b) a e)))
with (tsubst_term (typ_var_f b) a (term_open (typ_var_f a) (term_exists e)))
by reflexivity.
apply wfterm_renameE; auto.
simpl; unfold typvar; destruct (a == a); congruence.
Case "coerce_coerce". inversion H7; subst. eauto.
Case "sigma_appL". inversion H7; subst.
assert (binds b U G2) by eauto with fzip.
assert (binds b E Γ) by eauto with fzip.
apply binds_decomp in H3. destruct H3 as [? [? ?]]; subst.
apply binds_decomp in H4. destruct H4 as [? [? ?]]; subst.
pick fresh a and apply wfterm_sigma.
assert (uniq (x1 ++ [(b, E)] ++ x2)) by eauto with lngen. solve_uniq.
assert (lc_typ t).
  assert (lc_term (term_sigma (typ_var_f b) t e1))
    by eauto with lngen. inversion H3; subst; auto.
replace (open_term_wrt_typ (term_app e1 e2') (typ_var_f a)) with
  (term_app (open_term_wrt_typ e1 (typ_var_f a)) (open_term_wrt_typ e2' (typ_var_f a))) by reflexivity.
rewrite H2; auto.
apply wfterm_app with
  (G1 := a ~ Eq t ++ G3 ++ G0)
  (G2 := a ~ Eq t ++ x ++ x0) (t2 := tsubst_typ (typ_var_f a) b t2).
constructor; eauto using zip_remove_EU.
apply H12; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ a ~ Eq t ++ x ++ x0).
apply wfterm_instantiate.
apply wfterm_renameU; auto.
apply wfterm_lowerU; auto.
intro H4. apply ftv_env_binds in H4. destruct H4 as [? [? [? [? | ?]]]].
  assert (binds x3 (T x4) (x ++ b ~ U ++ x0)) by auto.
    eapply zip_binds_T23 in H8; eauto. eapply zip_binds_T31 in H8; eauto.
    assert (ftv_typ x4 [<=] dom (G3 ++ G0)). apply wftyp_ftv.
    apply wfenv_wftyp_T2 with (x := x3); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv. eauto with fzip.
    analyze_binds H8.
    clear Fr. assert (b ∉ ftv_typ x4) by fsetdec. contradiction.
  assert (binds x3 (Eq x4) (x ++ b ~ U ++ x0)) by auto.
    eapply zip_binds_Eq23 in H8; eauto. eapply zip_binds_Eq31 in H8; eauto.
    assert (ftv_typ x4 [<=] dom (G3 ++ G0)). apply wftyp_ftv.
    apply wfenv_wftyp_Eq2 with (x := x3); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv; eauto.
    analyze_binds H8.
    clear Fr. assert (b ∉ ftv_typ x4) by fsetdec. contradiction.
apply zip_remove_EU in H5. eapply wftyp_zip12; eauto. apply wfenv_wftyp_Eq3 with (x := a).
eapply wfterm_wfenv; eauto.
eapply wfenv_zip12; eauto. apply wfenv_strip with (Γ' := a ~ Eq t).
eapply wfterm_wfenv; eauto.
apply zip_remove_EU in H5.
intros.
assert (a0 ∈ dom (G3 ++ G0)).
assert (ftv_typ t [<=] dom (G3 ++ G0)). apply wftyp_ftv. apply wfenv_wftyp_Eq3 with (x := a). eapply wfterm_wfenv; eauto. auto.
apply binds_In_inv in H6. destruct H6. destruct x3.
eapply zip_binds_T12 in H6; eauto. intro.
  assert (E = T t0). eapply binds_unique; eauto with lngen. congruence.
eapply zip_binds_U12 in H6; eauto. intro.
  assert (@E typ = U). eapply binds_unique; eauto with lngen. congruence.
eapply zip_binds_E12 in H6; eauto. intro.
  assert (@E typ = U). eapply binds_unique; eauto with lngen. congruence.
eapply zip_binds_Eq12 in H6; eauto. intro.
  assert (@E typ = Eq t0). eapply binds_unique; eauto with lngen. congruence.
Case "sigma_appR". inversion H9; subst.
assert (binds b E Γ) by eauto with fzip.
assert (b ∉ dom G1).
  eapply zip_binds_E3_inv in H3; eauto. destruct H3 as [[? ?] | [? ?]]; auto.
  analyze_binds_uniq H4; eauto with lngen.
apply binds_decomp in H3. destruct H3 as [? [? ?]]; subst.
pick fresh a and apply wfterm_sigma.
assert (uniq (x ++ [(b, E)] ++ x0)) by eauto with lngen. solve_uniq.
assert (lc_typ t).
  assert (lc_term (term_sigma (typ_var_f b) t e2))
    by eauto with lngen. inversion H3; subst; auto.
replace (open_term_wrt_typ (term_app e1' e2) (typ_var_f a)) with
  (term_app (open_term_wrt_typ e1' (typ_var_f a)) (open_term_wrt_typ e2 (typ_var_f a))) by reflexivity.
rewrite H2; auto.
apply wfterm_app with
  (G1 := a ~ Eq t ++ G1)
  (G2 := a ~ Eq t ++ G3 ++ G0) (t2 := tsubst_typ (typ_var_f a) b t2); eauto.
constructor; auto.
rewrite_env (nil ++ G1) in H5. rewrite_env (nil ++ G1). eauto using zip_remove_E.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ a ~ Eq t ++ G1).
apply wfterm_instantiate.
replace (typ_arrow (tsubst_typ (typ_var_f a) b t2) (tsubst_typ (typ_var_f a) b τ))
with (tsubst_typ (typ_var_f a) b (typ_arrow t2 τ)) by reflexivity.
apply wfterm_renameU; auto.
apply wfterm_weakening; auto. constructor; auto.
  eapply wfterm_wfenv; eauto. apply pure_U.
  intros. unfold ftv_env in H6; simpl in H6. intro. clear Fr. fsetdec.
apply wfenv_wftyp_Eq3 with (x := a).
apply wfenv_zip21 with (Γ₂ := a ~ Eq t ++ G3 ++ G0) (Γ₃ := a ~ Eq t ++ x ++ x0).
constructor; auto. rewrite_env (nil ++ G1).
  rewrite_env (nil ++ G1) in H5. eapply zip_remove_E; eauto.
intros. apply ftv_env_binds in H6. destruct H6 as [? [? [? [? | ?]]]].
eapply wfterm_T_not_E; eauto.
eapply wfterm_Eq_not_E; eauto.
eapply wfterm_wfenv; eauto.
intros. eapply val_pure; eauto.
Case "sigma_letL". inversion H7; subst.
assert (binds b U G2) by eauto with fzip.
assert (binds b E Γ) by eauto with fzip.
apply binds_decomp in H3. destruct H3 as [? [? ?]]; subst.
apply binds_decomp in H4. destruct H4 as [? [? ?]]; subst.
pick fresh a and apply wfterm_sigma.
assert (uniq (x1 ++ [(b, E)] ++ x2)) by eauto with lngen. solve_uniq.
assert (lc_typ t).
  assert (lc_term (term_sigma (typ_var_f b) t e1))
    by eauto with lngen. inversion H3; subst; auto.
replace (open_term_wrt_typ (term_let e1 e2') (typ_var_f a)) with
  (term_let (open_term_wrt_typ e1 (typ_var_f a)) (open_term_wrt_typ e2' (typ_var_f a))) by reflexivity.
rewrite H2; auto.
apply wfterm_let with (L := L ∪ L0 ∪ {{a}})
  (G1 := a ~ Eq t ++ G3 ++ G0)
  (G2 := a ~ Eq t ++ x ++ x0) (t1 := tsubst_typ (typ_var_f a) b t1); intros.
constructor; eauto using zip_remove_EU.
apply H12; auto.
apply wfterm_instantiate.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) (x3 ~ T t1) ++ a ~ U ++ x ++ x0).
rewrite tsubst_term_open_term_wrt_term_var.
apply wfterm_renameU; auto.
apply wfterm_lowerU; auto.
intro H6. apply ftv_env_binds in H6. destruct H6 as [? [? [? [? | ?]]]].
  assert (binds x4 (T x5) (x ++ b ~ U ++ x0)) by auto.
    eapply zip_binds_T23 in H10; eauto. eapply zip_binds_T31 in H10; eauto.
    assert (ftv_typ x5 [<=] dom (G3 ++ G0)). apply wftyp_ftv.
    apply wfenv_wftyp_T2 with (x := x4); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv. eauto with fzip.
    analyze_binds H10.
    clear Fr. assert (b ∉ ftv_typ x5) by fsetdec. contradiction.
  assert (binds x4 (Eq x5) (x ++ b ~ U ++ x0)) by auto.
    eapply zip_binds_Eq23 in H10; eauto. eapply zip_binds_Eq31 in H10; eauto.
    assert (ftv_typ x5 [<=] dom (G3 ++ G0)). apply wftyp_ftv.
    apply wfenv_wftyp_Eq2 with (x := x4); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv; eauto.
    analyze_binds H10.
    clear Fr. assert (b ∉ ftv_typ x5) by fsetdec. contradiction.
apply zip_remove_EU in H5. eapply wftyp_zip12; eauto. apply wfenv_wftyp_Eq3 with (x := a).
eapply wfterm_wfenv; eauto.
eapply wfenv_zip12; eauto. apply wfenv_strip with (Γ' := a ~ Eq t).
eapply wfterm_wfenv; eauto.
apply zip_remove_EU in H5.
intros.
assert (a0 ∈ dom (G3 ++ G0)).
assert (ftv_typ t [<=] dom (G3 ++ G0)). apply wftyp_ftv. apply wfenv_wftyp_Eq3 with (x := a). eapply wfterm_wfenv; eauto. auto.
apply binds_In_inv in H8. destruct H8. destruct x4.
eapply zip_binds_T12 in H8; eauto. intro.
  assert (E = T t0). eapply binds_unique; eauto with lngen. congruence.
eapply zip_binds_U12 in H8; eauto. intro.
  assert (@E typ = U). eapply binds_unique; eauto with lngen. congruence.
eapply zip_binds_E12 in H8; eauto. intro.
  assert (@E typ = U). eapply binds_unique; eauto with lngen. congruence.
eapply zip_binds_Eq12 in H8; eauto. intro.
  assert (@E typ = Eq t0). eapply binds_unique; eauto with lngen. congruence.
Case "sigma_pairL". inversion H7; subst.
assert (binds b U G2) by eauto with fzip.
assert (binds b E Γ) by eauto with fzip.
apply binds_decomp in H3. destruct H3 as [? [? ?]]; subst.
apply binds_decomp in H4. destruct H4 as [? [? ?]]; subst.
pick fresh a and apply wfterm_sigma.
assert (uniq (x1 ++ [(b, E)] ++ x2)) by eauto with lngen. solve_uniq.
assert (lc_typ t).
  assert (lc_term (term_sigma (typ_var_f b) t e1))
    by eauto with lngen. inversion H3; subst; auto.
replace (open_term_wrt_typ (term_pair e1 e2') (typ_var_f a)) with
  (term_pair (open_term_wrt_typ e1 (typ_var_f a)) (open_term_wrt_typ e2' (typ_var_f a))) by reflexivity.
simpl. simpl_env.
rewrite H2; auto.
apply wfterm_pair with
  (G1 := a ~ Eq t ++ G3 ++ G0)
  (G2 := a ~ Eq t ++ x ++ x0).
constructor; eauto using zip_remove_EU.
apply H12; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ a ~ Eq t ++ x ++ x0).
apply wfterm_instantiate.
apply wfterm_renameU; auto.
apply wfterm_lowerU; auto.
intro H4. apply ftv_env_binds in H4. destruct H4 as [? [? [? [? | ?]]]].
  assert (binds x3 (T x4) (x ++ b ~ U ++ x0)) by auto.
    eapply zip_binds_T23 in H8; eauto. eapply zip_binds_T31 in H8; eauto.
    assert (ftv_typ x4 [<=] dom (G3 ++ G0)). apply wftyp_ftv.
    apply wfenv_wftyp_T2 with (x := x3); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv. eauto with fzip.
    analyze_binds H8.
    clear Fr. assert (b ∉ ftv_typ x4) by fsetdec. contradiction.
  assert (binds x3 (Eq x4) (x ++ b ~ U ++ x0)) by auto.
    eapply zip_binds_Eq23 in H8; eauto. eapply zip_binds_Eq31 in H8; eauto.
    assert (ftv_typ x4 [<=] dom (G3 ++ G0)). apply wftyp_ftv.
    apply wfenv_wftyp_Eq2 with (x := x3); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv; eauto.
    analyze_binds H8.
    clear Fr. assert (b ∉ ftv_typ x4) by fsetdec. contradiction.
apply zip_remove_EU in H5. eapply wftyp_zip12; eauto. apply wfenv_wftyp_Eq3 with (x := a).
eapply wfterm_wfenv; eauto.
eapply wfenv_zip12; eauto. apply wfenv_strip with (Γ' := a ~ Eq t).
eapply wfterm_wfenv; eauto.
apply zip_remove_EU in H5.
intros.
assert (a0 ∈ dom (G3 ++ G0)).
assert (ftv_typ t [<=] dom (G3 ++ G0)). apply wftyp_ftv. apply wfenv_wftyp_Eq3 with (x := a). eapply wfterm_wfenv; eauto. auto.
apply binds_In_inv in H6. destruct H6. destruct x3.
eapply zip_binds_T12 in H6; eauto. intro.
  assert (E = T t0). eapply binds_unique; eauto with lngen. congruence.
eapply zip_binds_U12 in H6; eauto. intro.
  assert (@E typ = U). eapply binds_unique; eauto with lngen. congruence.
eapply zip_binds_E12 in H6; eauto. intro.
  assert (@E typ = U). eapply binds_unique; eauto with lngen. congruence.
eapply zip_binds_Eq12 in H6; eauto. intro.
  assert (@E typ = Eq t0). eapply binds_unique; eauto with lngen. congruence.
Case "sigma_pairR". inversion H9; subst.
assert (binds b E Γ) by eauto with fzip.
assert (b ∉ dom G1).
  eapply zip_binds_E3_inv in H3; eauto. destruct H3 as [[? ?] | [? ?]]; auto.
  analyze_binds_uniq H4; eauto with lngen.
apply binds_decomp in H3. destruct H3 as [? [? ?]]; subst.
pick fresh a and apply wfterm_sigma.
assert (uniq (x ++ [(b, E)] ++ x0)) by eauto with lngen. solve_uniq.
assert (lc_typ t).
  assert (lc_term (term_sigma (typ_var_f b) t e2))
    by eauto with lngen. inversion H3; subst; auto.
replace (open_term_wrt_typ (term_pair e1' e2) (typ_var_f a)) with
  (term_pair (open_term_wrt_typ e1' (typ_var_f a)) (open_term_wrt_typ e2 (typ_var_f a))) by reflexivity.
simpl. simpl_env.
rewrite H2; auto.
apply wfterm_pair with
  (G1 := a ~ Eq t ++ G1)
  (G2 := a ~ Eq t ++ G3 ++ G0); eauto.
constructor; auto.
rewrite_env (nil ++ G1) in H5. rewrite_env (nil ++ G1). eauto using zip_remove_E.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ a ~ Eq t ++ G1).
apply wfterm_instantiate.
apply wfterm_renameU; auto.
apply wfterm_weakening; auto. constructor; auto.
  eapply wfterm_wfenv; eauto. apply pure_U.
  intros. unfold ftv_env in H6; simpl in H6. intro. clear Fr. fsetdec.
apply wfenv_wftyp_Eq3 with (x := a).
apply wfenv_zip21 with (Γ₂ := a ~ Eq t ++ G3 ++ G0) (Γ₃ := a ~ Eq t ++ x ++ x0).
constructor; auto. rewrite_env (nil ++ G1).
  rewrite_env (nil ++ G1) in H5. eapply zip_remove_E; eauto.
intros. apply ftv_env_binds in H6. destruct H6 as [? [? [? [? | ?]]]].
eapply wfterm_T_not_E; eauto.
eapply wfterm_Eq_not_E; eauto.
eapply wfterm_wfenv; eauto.
intros. eapply val_pure; eauto.
Case "sigma_fst". inversion H3; subst.
pick fresh a and apply wfterm_sigma; auto.
replace (open_term_wrt_typ (term_fst e) (typ_var_f a)) with
(term_fst (open_term_wrt_typ e (typ_var_f a))) by reflexivity.
apply wfterm_fst with (t2 := tsubst_typ (typ_var_f a) b t2).
replace (typ_prod (tsubst_typ (typ_var_f a) b τ) (tsubst_typ (typ_var_f a) b t2))
with (tsubst_typ (typ_var_f a) b (typ_prod τ t2)) by reflexivity.
auto.
Case "sigma_snd". inversion H3; subst.
pick fresh a and apply wfterm_sigma; auto.
replace (open_term_wrt_typ (term_snd e) (typ_var_f a)) with
(term_snd (open_term_wrt_typ e (typ_var_f a))) by reflexivity.
apply wfterm_snd with (t1 := tsubst_typ (typ_var_f a) b t1).
replace (typ_prod (tsubst_typ (typ_var_f a) b t1) (tsubst_typ (typ_var_f a) b τ))
with (tsubst_typ (typ_var_f a) b (typ_prod t1 τ)) by reflexivity.
auto.
Case "sigma_inst". inversion H8; subst.
pick fresh a and apply wfterm_sigma; auto.
replace (open_term_wrt_typ (term_inst e t'') (typ_var_f a))
with (term_inst (open_term_wrt_typ e (typ_var_f a)) (open_typ_wrt_typ t'' (typ_var_f a)))
by reflexivity.
rewrite tsubst_typ_open_typ_wrt_typ; auto.
rewrite H2; auto.
apply wfterm_inst.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ a ~ Eq t ++ G2 ++ G1).
apply wftyp_instantiate. apply wftyp_renameU; auto.
apply wftyp_EU. apply wftyp_lowerE; auto.
intro. apply ftv_env_binds in H3. destruct H3 as [? [? [? [? | ?]]]].
  assert (ftv_typ x0 [<=] dom (G2 ++ G1)).
    apply wftyp_ftv. apply wfenv_wftyp_T2 with (x := x); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv; eauto.
    clear Fr. fsetdec.
  assert (ftv_typ x0 [<=] dom (G2 ++ G1)).
    apply wftyp_ftv. apply wfenv_wftyp_Eq2 with (x := x); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv; eauto.
    clear Fr. fsetdec.
apply wfenv_wftyp_Eq3 with (x := a). eapply wfterm_wfenv; eauto.
apply H11; auto.
Case "sigma_open".
assert (uniq (G2 ++ c ~ E ++ G1)) by eauto with lngen.
inversion H6; subst.
assert (binds b E (G2 ++ G1)). rewrite <- H2. auto.
analyze_binds H3; apply binds_decomp in BindsTac;
destruct BindsTac as [? [? ?]]; subst.
SCase "b binds in G2".
simpl_env in H2.
symmetry in H2. apply uniq_app_inv in H2. destruct H2; subst. simpl_env.
pick fresh a and apply wfterm_sigma; auto.
replace (open_term_wrt_typ (term_open (typ_var_f c) e) (typ_var_f a))
with (term_open (typ_var_f c) (open_term_wrt_typ e (typ_var_f a)))
by reflexivity.
rewrite tsubst_typ_open_typ_wrt_typ; auto.
simpl. destruct (c == b); subst.
SSSCase "c = b (absurd)". elimtype False. clear Fr.
  simpl_env in *. fsetdec.
SSSCase "c ≠ b".
rewrite_env (([(a, Eq t)] ++ G3 ++ x0) ++ [(c, E)] ++ G1).
apply wfterm_open. solve_uniq. simpl_env; apply H10; auto.
solve_uniq.
SCase "b binds in G1".
simpl_env in H2. rewrite_env ((G2 ++ x) ++ [(b, E)] ++ x0) in H2.
symmetry in H2. apply uniq_app_inv in H2. destruct H2; subst. simpl_env.
rewrite_env ((G2 ++ [(c, E)] ++ x) ++ [(b, E)] ++ G0).
pick fresh a and apply wfterm_sigma; auto.
replace (open_term_wrt_typ (term_open (typ_var_f c) e) (typ_var_f a))
with (term_open (typ_var_f c) (open_term_wrt_typ e (typ_var_f a)))
by reflexivity.
rewrite tsubst_typ_open_typ_wrt_typ; auto.
simpl. destruct (c == b); subst.
SSSCase "c = b (absurd)". elimtype False. clear Fr.
  simpl_env in *. fsetdec.
SSSCase "c ≠ b".
rewrite_env (([(a, Eq t)] ++ G2) ++ [(c, E)] ++ x ++ G0).
apply wfterm_open. solve_uniq.
rewrite_env ([(a, Eq t)] ++ (G2 ++ x) ++ G0). apply H10; auto.
solve_uniq.
Case "sigma sigma".
assert (uniq (G2 ++ b1 ~ E ++ G1)) by eauto with lngen.
assert (binds b2 E (G2 ++ G1)).
  pick fresh a1. pick fresh a2.
  assert (wfterm (a1 ~ Eq t1 ++ G2 ++ G1)
  (open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e) (typ_var_f a1))
  (tsubst_typ (typ_var_f a1) b1 τ)) by auto.
  unfold open_term_wrt_typ in H5; simpl open_term_wrt_typ_rec in H5;
    inversion H5; subst.
  destruct G3; inversion H6; subst. auto.
analyze_binds H5; apply binds_decomp in BindsTac;
destruct BindsTac as [? [? ?]]; subst.
SCase "b binds in G2".
simpl_env in *.
pick fresh a2 and apply wfterm_sigma. solve_uniq.
unfold open_term_wrt_typ; simpl open_term_wrt_typ_rec.
rewrite_env ((a2 ~ Eq (open_typ_wrt_typ t2 t1) ++ x ++ x0) ++ [(b1, E)] ++ G1).
pick fresh a1 and apply wfterm_sigma. solve_uniq.
assert (wfterm ([(a1, Eq t1)] ++ x ++ [(b2, E)] ++ x0 ++ G1)
(open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e) (typ_var_f a1))
(tsubst_typ (typ_var_f a1) b1 τ)) by auto.
inversion H5; subst.
simpl_env in H6. rewrite_env ((a1 ~ Eq t1 ++ x) ++ [(b2, E)] ++ x0 ++ G1) in H6.
symmetry in H6. apply uniq_app_inv in H6. destruct H6; subst.
assert (wfterm ([(a2, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a1) t2))] ++
          ([(a1, Eq t1)] ++ x) ++ x0 ++ G1)
(open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a1) e) (typ_var_f a2))
(tsubst_typ (typ_var_f a2) b2 (tsubst_typ (typ_var_f a1) b1 τ))).
  pick fresh c.
  rewrite_env (env_map (tsubst_typ (typ_var_f a2) c) nil ++
    [(a2, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a1) t2))] ++
    ([(a1, Eq t1)] ++ x) ++ x0 ++ G1).
  replace (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a1) e)
       (typ_var_f a2))
    with (tsubst_term (typ_var_f a2) c
      (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a1) e)
       (typ_var_f c))).
  replace (tsubst_typ (typ_var_f a2) b2 (tsubst_typ (typ_var_f a1) b1 τ))
    with (tsubst_typ (typ_var_f a2) c
      (tsubst_typ (typ_var_f c) b2 (tsubst_typ (typ_var_f a1) b1 τ))).
  apply wfterm_renameEq; simpl_env; auto.
  rewrite tsubst_typ_tsubst_typ; simpl; auto.
    unfold typvar; destruct (c == c); try congruence.
    f_equal. apply tsubst_typ_fresh_eq.
    assert (ftv_typ (tsubst_typ (typ_var_f a1) b1 τ) [<=]
      ftv_typ (typ_var_f a1) `union` remove b1 (ftv_typ τ)) by auto with lngen.
    simpl in H6. clear H4 Fr Fr0 H13. fsetdec.
  rewrite tsubst_term_open_term_wrt_typ; auto.
  rewrite tsubst_term_open_term_wrt_typ_rec; auto.
  autorewrite with lngen. auto.
unfold open_term_wrt_typ; rewrite <- H3; auto.
rewrite tsubst_typ_tsubst_typ; auto.
rewrite tsubst_typ_fresh_eq with (t2 := typ_var_f a2); auto.
replace (open_typ_wrt_typ_rec 0 (typ_var_f a2) t1') with
(open_typ_wrt_typ t1' (typ_var_f a2)) by reflexivity.
rewrite <- H2; auto. rewrite tsubst_typ_intro with (a1 := a1); auto.
rewrite_env (nil ++ [(a1, Eq t1)] ++
  [(a2, Eq (tsubst_typ t1 a1 (open_typ_wrt_typ t2 (typ_var_f a1))))]
 ++ x ++ x0 ++ G1).
apply wfterm_swap_Eq. apply H6.
solve_uniq.
SCase "b binds in G1".
simpl_env in *.
rewrite_env ((G2 ++ [(b1, E)] ++ x) ++ [(b2, E)] ++ x0).
pick fresh a2 and apply wfterm_sigma. solve_uniq.
unfold open_term_wrt_typ; simpl open_term_wrt_typ_rec.
rewrite_env ((a2 ~ Eq (open_typ_wrt_typ t2 t1) ++ G2) ++ [(b1, E)] ++ x ++ x0).
pick fresh a1 and apply wfterm_sigma. solve_uniq.
assert (wfterm ([(a1, Eq t1)] ++ G2 ++ x ++ [(b2, E)] ++ x0)
(open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e) (typ_var_f a1))
(tsubst_typ (typ_var_f a1) b1 τ)) by auto.
inversion H5; subst.
simpl_env in H6. rewrite_env ((a1 ~ Eq t1 ++ G2 ++ x) ++ [(b2, E)] ++ x0) in H6.
symmetry in H6. apply uniq_app_inv in H6. destruct H6; subst.
assert (wfterm ([(a2, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a1) t2))] ++
          ([(a1, Eq t1)] ++ G2 ++ x) ++ G1)
(open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a1) e) (typ_var_f a2))
(tsubst_typ (typ_var_f a2) b2 (tsubst_typ (typ_var_f a1) b1 τ))).
  pick fresh c.
  rewrite_env (env_map (tsubst_typ (typ_var_f a2) c) nil ++
    [(a2, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a1) t2))] ++
    ([(a1, Eq t1)] ++ G2++ x) ++ G1).
  replace (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a1) e)
       (typ_var_f a2))
    with (tsubst_term (typ_var_f a2) c
      (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a1) e)
       (typ_var_f c))).
  replace (tsubst_typ (typ_var_f a2) b2 (tsubst_typ (typ_var_f a1) b1 τ))
    with (tsubst_typ (typ_var_f a2) c
      (tsubst_typ (typ_var_f c) b2 (tsubst_typ (typ_var_f a1) b1 τ))).
  apply wfterm_renameEq. apply H14; auto. simpl_env; auto.
  rewrite tsubst_typ_tsubst_typ; simpl; auto.
    unfold typvar; destruct (c == c); try congruence.
    f_equal. apply tsubst_typ_fresh_eq.
    assert (ftv_typ (tsubst_typ (typ_var_f a1) b1 τ) [<=]
      ftv_typ (typ_var_f a1) `union` remove b1 (ftv_typ τ)) by auto with lngen.
    simpl in H6. clear H4 Fr Fr0 H13. fsetdec.
  rewrite tsubst_term_open_term_wrt_typ; auto.
  rewrite tsubst_term_open_term_wrt_typ_rec; auto.
  autorewrite with lngen. auto.
unfold open_term_wrt_typ; rewrite <- H3; auto.
rewrite tsubst_typ_tsubst_typ; auto.
rewrite tsubst_typ_fresh_eq with (t2 := typ_var_f a2); auto.
replace (open_typ_wrt_typ_rec 0 (typ_var_f a2) t1') with
(open_typ_wrt_typ t1' (typ_var_f a2)) by reflexivity.
rewrite <- H2; auto. rewrite tsubst_typ_intro with (a1 := a1); auto.
rewrite_env (nil ++ [(a1, Eq t1)] ++
  [(a2, Eq (tsubst_typ t1 a1 (open_typ_wrt_typ t2 (typ_var_f a1))))]
 ++ G2 ++ x ++ G1).
apply wfterm_swap_Eq. simpl_env in H6. apply H6.
simpl_env. solve_uniq.
Qed.

Theorem subject_reduction : forall Γ e e' τ,
  wfterm Γ e τ → e ⇝ e' → wfterm Γ e' τ.
Proof.
intros Γ e e' τ H. generalize dependent e'.
induction H; intros e' Hred; inversion Hred; subst; eauto;
try solve [ inversion H2 | eapply sr0; eauto ].
Case "exists". pick fresh a and apply wfterm_exists; eauto.
Case "nu". pick fresh a and apply wfterm_nu; eauto.
Case "sigma". pick fresh a and apply wfterm_sigma; eauto.
Qed.

Theorem progress : forall Γ e τ,
  (forall x τ, not (binds x (T τ) Γ)) →
  wfterm Γ e τ →
  (exists e', e ⇝ e') ∨ result e.
Proof with eauto with lngen.
intros Γ e τ Henv H. induction H; simpl.
Case "var". elimtype False. intuition eauto.
Case "app".
destruct IHwfterm1 as [[? ?] | ?]... intuition eauto with fzip.
destruct IHwfterm2 as [[? ?] | ?]... intuition eauto with fzip.
destruct H2.
  SCase "e val". destruct H3; subst.
    SSCase "e0 val". destruct H2; subst; eauto; try solve [inversion H0].
      SSSCase "e coerce". inversion H0; subst. destruct H4; subst.
        SSSSCase "coerce lam". inversion H2; subst. eauto.
        SSSSCase "coerce gen (absurd)". elimtype False.
          inversion H11; subst. eapply wftypeq_arrow_forall_absurd; eauto.
        SSSSCase "coerce pair (absurd)". elimtype False.
          inversion H11; subst. eapply wftypeq_prod_arrow_absurd; eauto.
        SSSSCase "coerce coerce (absurd)". elimtype False. eapply H5; eauto.
        SSSSCase "coerce exists (absurd)". elimtype False.
          inversion H11; subst. eapply wftypeq_arrow_exists_absurd; eauto.
    SSCase "e0 result". left.
      exists (term_sigma (typ_var_f b) t (term_app (close_term_wrt_typ b e) e0)).
      constructor. apply red0_sigma_appR with (L := ftv_term e); eauto; auto with lngen.
  SCase "e result". left.
    exists (term_sigma (typ_var_f b) t (term_app e (close_term_wrt_typ b e2))).
    constructor. apply red0_sigma_appL with (L := ftv_term e2); eauto; auto with lngen.
Case "abs". pick fresh x.
assert (lc_typ t1). eapply wftyp_regular. eapply wfenv_wftyp_T3.
  eapply wfterm_wfenv. eauto.
eauto 6 with lngen.
Case "let". pick fresh x.
assert (lc_term (term_let e1 e2)). constructor; intros; eauto with lngen.
destruct IHwfterm as [[? ?] | ?]... intuition eauto with fzip.
destruct H4; eauto.
SCase "e result". pick fresh a. left.
exists (term_sigma (typ_var_f b) t (term_let e
  (close_term_wrt_typ a (tsubst_term (typ_var_f a) b e2)))).
constructor. apply red0_sigma_letL with (L := L ∪ {{b}}); intros...
rewrite <- tsubst_term_spec. rewrite tsubst_term_tsubst_term; auto.
simpl. unfold typvar; destruct (a == a); try congruence.
rewrite tsubst_term_fresh_eq with (a1 := a)...
Case "pair".
destruct IHwfterm1 as [[? ?] | ?]... intuition eauto with fzip.
destruct IHwfterm2 as [[? ?] | ?]... intuition eauto with fzip.
destruct H2.
  SCase "e val". destruct H3; subst; auto.
    SSCase "e0 result". left.
      exists (term_sigma (typ_var_f b) t (term_pair (close_term_wrt_typ b e) e0)).
      constructor. apply red0_sigma_pairR with (L := ftv_term e); eauto; auto with lngen.
  SCase "e result". left.
    exists (term_sigma (typ_var_f b) t (term_pair e (close_term_wrt_typ b e2))).
    constructor. apply red0_sigma_pairL with (L := ftv_term e2); eauto; auto with lngen.
Case "fst". destruct IHwfterm as [[? ?] | ?]... destruct H0; subst.
  SSCase "e val". destruct H0; subst; try solve [inversion H]; eauto 6.
    SSSCase "coerce". inversion H; subst. destruct H1; subst.
      SSSSCase "coerce abs (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_arrow_prod_absurd; eauto.
      SSSSCase "coerce gen (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_prod_forall_absurd; eauto.
      SSSSCase "coerce pair". inversion H0; subst. eauto 6.
      SSSSCase "coerce coerce (absurd)". elimtype False. intuition eauto.
      SSSSCase "coerce exists (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_prod_exists_absurd; eauto.
  SSCase "e result". eauto 6.
Case "snd". destruct IHwfterm as [[? ?] | ?]... destruct H0; subst.
  SSCase "e val". destruct H0; subst; try solve [inversion H]; eauto 6.
    SSSCase "coerce". inversion H; subst. destruct H1; subst.
      SSSSCase "coerce abs (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_arrow_prod_absurd; eauto.
      SSSSCase "coerce gen (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_prod_forall_absurd; eauto.
      SSSSCase "coerce pair". inversion H0; subst. eauto 6.
      SSSSCase "coerce coerce (absurd)". elimtype False. intuition eauto.
      SSSSCase "coerce exists (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_prod_exists_absurd; eauto.
  SSCase "e result". eauto 6.
Case "inst". destruct IHwfterm as [[? ?] | ?]... destruct H1; subst.
  SCase "e val". destruct H1; subst; try solve [inversion H0]...
    SSCase "gen". eauto 6 with lngen.
    SSCase "coerce". inversion H0; subst. destruct H2; subst.
      SSSCase "abs (absurd)". elimtype False. inversion H9; subst.
        eapply wftypeq_arrow_forall_absurd; eauto.
      SSSCase "gen". eauto 6 with lngen.
      SSSCase "pair (absurd)". elimtype False. inversion H9; subst.
        eapply wftypeq_prod_forall_absurd; eauto.
      SSSCase "coerce (absurd)". elimtype False. intuition eauto.
      SSSCase "exists (absurd)". elimtype False. inversion H9; subst.
        eapply wftypeq_exists_forall_absurd; eauto.
  SCase "e result". left.
    exists (term_sigma (typ_var_f b) t0 (term_inst e (close_typ_wrt_typ b t))).
    constructor. apply red0_sigma_inst with (L := ftv_typ t); eauto with lngen.
Case "gen". pick fresh a. eauto 6 with lngen.
Case "exists". pick fresh a. destruct (H0 a) as [[? ?] | ?]...
  intros. intro. eapply (Henv x τ). analyze_binds H1.
  SCase "e reduces". left. exists (term_exists (close_term_wrt_typ a x)).
  pick fresh b and apply red1_exists.
  rewrite <- tsubst_term_spec.
  replace (open_term_wrt_typ e (typ_var_f b)) with
    (tsubst_term (typ_var_f b) a (open_term_wrt_typ e (typ_var_f a))).
  apply red1_trenaming; auto.
  assert (ftv_term (open_term_wrt_typ e (typ_var_f a))
    [<=] ftv_typ (typ_var_f a) ∪ ftv_term e) by auto with lngen.
  simpl in H2. fsetdec.
  rewrite tsubst_term_open_term_wrt_typ; auto. autorewrite with lngen. auto.
  SCase "e result". admit.
Case "open". destruct IHwfterm as [[? ?] | ?]...
  intros. intro. eapply (Henv x τ). analyze_binds H1. destruct H1; subst.
  SCase "e val".  destruct H1; subst; try solve [inversion H0]...
    SSCase "coerce". inversion H0; subst. destruct H2; subst.
      SSSCase "abs (absurd)". elimtype False. inversion H9; subst.
        eapply wftypeq_arrow_exists_absurd; eauto.
      SSSCase "gen (absurd)". elimtype False. inversion H9; subst.
        eapply wftypeq_forall_exists_absurd; eauto.
      SSSCase "pair (absurd)". elimtype False. inversion H9; subst.
        eapply wftypeq_prod_exists_absurd; eauto.
      SSSCase "coerce (absurd)". elimtype False. intuition eauto.
      SSSCase "exists". eauto 6 with lngen.
    SSCase "exists". left.
    exists (open_term_wrt_typ (term_sigma (typ_var_b 0) t' e') (typ_var_f b)).
    constructor. pick fresh a and apply red0_open_exists.
    unfold open_term_wrt_typ; simpl. pick fresh c and apply result_sigma.
    apply H2...
    unfold open_term_wrt_typ; simpl. constructor.
    eapply H3 with (b := a) (a := c)...
    unfold close_term_wrt_typ.
    rewrite close_term_wrt_typ_rec_open_term_wrt_typ_rec. reflexivity.
    assert (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f a) e') [<=]
    ftv_typ (typ_var_f a) ∪ ftv_term e') by auto with lngen. simpl in H1.
    clear Fr. fsetdec.
  SCase "e result". eauto 6.
Case "nu".




ICI (needs renaming lemma for reduction)

Qed.
