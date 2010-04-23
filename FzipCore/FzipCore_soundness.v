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
Lemma sr0 :  forall A Γ e e' τ,
  Γ ⊢ e ~: τ → red0 e A e' → Γ ⊢ e' ~: τ.
Proof.
intros A Γ e e' τ H H0. destruct H0; inversion H; subst.
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
Case "nu_sigma". pick fresh b.
assert (b ~ E ++ Γ ⊢ open_term_wrt_typ (term_sigma (typ_var_b 0) t e) (typ_var_f b) ~: τ) by auto.
assert (uniq (b ~ E ++ Γ)) by eauto with lngen.
unfold open_term_wrt_typ in H4; simpl in H4; simpl_env in H4.
inversion H4; subst.
simpl_env in H7; rewrite_env (nil ++ b ~ E ++ Γ) in H7.
symmetry in H7; apply uniq_app_inv in H7. destruct H7; subst; simpl_env in *.
pick fresh a.
erewrite H3 with (b := b) (a := a)
(e1 := open_term_wrt_typ_rec 1 (typ_var_f b) e); try reflexivity; auto.
rewrite tsubst_term_tsubst_term; auto. rewrite tvar_tsubst.
rewrite <- tsubst_typ_fresh_eq with
  (t1 := open_typ_wrt_typ_rec 0 (typ_var_f b) t) (a1 := b) (t2 := τ); auto.
rewrite_env (env_map (tsubst_typ (open_typ_wrt_typ_rec 0 (typ_var_f b) t) b) nil ++ G1).
apply wfterm_subst_eq.
apply wfterm_weakening; intros; auto with fzip.
rewrite <- tsubst_typ_fresh_eq with
  (t1 := open_typ_wrt_typ_rec 0 (typ_var_f b) t) (a1 := a) (t2 := τ); auto.
rewrite_env (env_map (tsubst_typ (open_typ_wrt_typ_rec 0 (typ_var_f b) t) a) nil ++ G1).
apply wfterm_subst_eq. simpl_env.
rewrite <- tsubst_typ_fresh_eq with
  (t1 := typ_var_f a) (a1 := b) (t2 := τ); auto.
constructor; auto. apply wfenv_wftyp_Eq3 with (x := a).
  eapply wfterm_wfenv. eauto.
intro.
assert (not (binds a0 E
  (a ~ Eq (open_typ_wrt_typ_rec 0 (typ_var_f b) t) ++ G1))).
eapply wfterm_Eq_not_E; eauto.
unfold ftv_env in H7; simpl in H7. clear Fr Fr0. fsetdec.
intuition eauto.
solve_uniq.
Case "coerce_app".
inversion H9; subst. inversion H14; subst.
assert (G1 ⊢ t2' ≡ t3) by eauto using wftypeq_arrow_inv1.
assert (G1 ⊢ t2  ≡ τ) by eauto using wftypeq_arrow_inv2.
apply wfterm_coerce with (t' := t2); auto.
eauto using wftypeq_zip13.
apply wfterm_app with (G1 := G1) (G2 := G2) (t2 := t2'); auto.
apply wfterm_coerce with (t' := t3); auto. apply wftypeq_sym.
eauto using wftypeq_zip12.
Case "coerce_fst".
inversion H5; subst.
inversion H10; subst.
assert (Γ ⊢ t1 ≡ τ) by eauto using wftypeq_prod_inv1.
apply wfterm_coerce with (t' := t1); eauto.
Case "coerce_snd".
inversion H5; subst.
inversion H10; subst.
assert (Γ ⊢ t2 ≡ τ) by eauto using wftypeq_prod_inv2.
apply wfterm_coerce with (t' := t2); eauto.
Case "coerce_inst".
inversion H8; subst.
inversion H10; subst.
assert (forall a, a ∉ dom Γ →
  a ~ U ++ Γ ⊢
  open_typ_wrt_typ t (typ_var_f a) ≡ open_typ_wrt_typ t' (typ_var_f a))
by eauto using wftypeq_forall_inv.
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
  a ~ U ++ G2 ++ G1 ⊢
  open_typ_wrt_typ t (typ_var_f a) ≡ open_typ_wrt_typ t0 (typ_var_f a))
by eauto using wftypeq_exists_inv.
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
Case "sigma exists".
pick fresh a.
assert ([(a, E)] ++ Γ ⊢
  open_term_wrt_typ (term_sigma (typ_var_f b) t e) (typ_var_f a) ~:
  open_typ_wrt_typ t0 (typ_var_f a)) by auto.
unfold open_term_wrt_typ in H5; inversion H5; subst.
assert (binds b E ((a, E) :: Γ)). rewrite <- H6. auto. analyze_binds H8.
apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
simpl_env in H6. rewrite_env (([(a, E)] ++ x) ++ [(b, E)] ++ x0) in H6.
symmetry in H6. apply uniq_app_inv in H6. destruct H6; subst.
pick fresh c and apply wfterm_sigma.
simpl_env in H12. auto.
unfold open_term_wrt_typ; simpl; simpl_env.
pick fresh d and apply wfterm_exists.
rewrite_env (env_map (tsubst_typ (typ_var_f d) a) nil ++
  [(d, E)] ++ [(c, Eq t')] ++ x ++ G1).
replace (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f c) e')
       (typ_var_f d)) with (tsubst_term (typ_var_f d) a
       (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f c) e')
       (typ_var_f a))).
replace (open_typ_wrt_typ (tsubst_typ (typ_var_f c) b t0) (typ_var_f d)) with
  (tsubst_typ (typ_var_f d) a
    (open_typ_wrt_typ (tsubst_typ (typ_var_f c) b t0) (typ_var_f a))).
apply wfterm_renameE.
apply wfterm_lowerE.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite <- H4; auto. rewrite (H3 a); auto. apply H13; auto.
unfold ftv_env; simpl. auto.
simpl; auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto. f_equal.
apply tsubst_typ_fresh_eq.
assert (ftv_typ (tsubst_typ (typ_var_f c) b t0) [<=]
  ftv_typ (typ_var_f c) ∪ remove b (ftv_typ t0)) by auto with lngen.
simpl in H6. assert (a ≠ c) by auto. assert (a ∉ ftv_typ t0) by auto.
clear Fr Fr0 Fr1. fsetdec.
autorewrite with lngen. auto.
rewrite tsubst_term_open_term_wrt_typ; auto. f_equal.
apply tsubst_term_fresh_eq.
assert (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f c) e') [<=]
  ftv_typ (typ_var_f c) ∪ ftv_term e') by auto with lngen.
simpl in H6. assert (a ≠ c) by auto. assert (a ∉ ftv_term e') by auto.
clear Fr Fr0 Fr1. fsetdec.
autorewrite with lngen. auto.
simpl_env. eauto with lngen.
Case "sigma coerce". inversion H8; subst.
pick fresh a and apply wfterm_sigma; auto.
replace (open_term_wrt_typ (term_coerce e t'') (typ_var_f a))
with (term_coerce (open_term_wrt_typ e (typ_var_f a)) (open_typ_wrt_typ t'' (typ_var_f a)))
by reflexivity.
rewrite H2; auto.
apply wfterm_coerce with (t' := tsubst_typ (typ_var_f a) b t'0).
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ a ~ Eq t ++ G2 ++ G1).
apply wftypeq_instantiate. apply wftypeq_renameU; auto.
apply wftypeq_EU. apply wftypeq_lowerE; auto.
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
Case "sigma sigma".
assert (uniq (G2 ++ b1 ~ E ++ G1)) by eauto with lngen.
assert (binds b2 E (G2 ++ G1)).
  pick fresh a1. pick fresh a2.
  assert (a1 ~ Eq t1 ++ G2 ++ G1 ⊢
  open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e) (typ_var_f a1) ~:
  tsubst_typ (typ_var_f a1) b1 τ) by auto.
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
assert ([(a1, Eq t1)] ++ x ++ [(b2, E)] ++ x0 ++ G1 ⊢
open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e) (typ_var_f a1) ~:
tsubst_typ (typ_var_f a1) b1 τ) by auto.
inversion H5; subst.
simpl_env in H6. rewrite_env ((a1 ~ Eq t1 ++ x) ++ [(b2, E)] ++ x0 ++ G1) in H6.
symmetry in H6. apply uniq_app_inv in H6. destruct H6; subst.
assert ([(a2, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a1) t2))] ++
          ([(a1, Eq t1)] ++ x) ++ x0 ++ G1 ⊢
open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a1) e) (typ_var_f a2) ~:
tsubst_typ (typ_var_f a2) b2 (tsubst_typ (typ_var_f a1) b1 τ)).
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
assert ([(a1, Eq t1)] ++ G2 ++ x ++ [(b2, E)] ++ x0 ⊢
open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e) (typ_var_f a1) ~:
tsubst_typ (typ_var_f a1) b1 τ) by auto.
inversion H5; subst.
simpl_env in H6. rewrite_env ((a1 ~ Eq t1 ++ G2 ++ x) ++ [(b2, E)] ++ x0) in H6.
symmetry in H6. apply uniq_app_inv in H6. destruct H6; subst.
assert ([(a2, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a1) t2))] ++
          ([(a1, Eq t1)] ++ G2 ++ x) ++ G1 ⊢
open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a1) e) (typ_var_f a2) ~:
tsubst_typ (typ_var_f a2) b2 (tsubst_typ (typ_var_f a1) b1 τ)).
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

Theorem subject_reduction : forall A Γ e e' τ,
  Γ ⊢ e ~: τ → e ⇝[A] e' → Γ ⊢ e' ~: τ.
Proof.
intros A Γ e e' τ H. generalize dependent e'.
induction H; intros e' Hred; inversion Hred; subst; eauto;
try solve [ inversion H2 | eapply sr0; eauto ].
Case "exists". pick fresh a and apply wfterm_exists; eauto.
Case "nu". pick fresh a and apply wfterm_nu; eauto.
Case "sigma". pick fresh a and apply wfterm_sigma; eauto.
Qed.

Lemma result_redn_Eps : forall Γ₁ Γ₂ b e τ,
  result e → Γ₁ ++ b ~ E ++ Γ₂ ⊢ e ~: τ →
  exists τ', exists e',
    e ⇝⋆[Eps] (term_sigma (typ_var_f b) τ' e') ∧ b ∉ ftv_typ τ'.
Proof.
intros Γ₁ Γ₂ b e τ H H0. generalize dependent τ.
generalize dependent Γ₂. generalize dependent Γ₁.
induction H; intros.
Case "val". elimtype False.
assert (pure (Γ₁ ++ [(b, E)] ++ Γ₂)) by eauto using val_pure.
eapply (H1 b); auto.
Case "sigma". destruct (b0 == b); subst.
SCase "b0 = b".
exists t. exists e. split. auto with clos_refl_trans.
intros. inversion H2; subst.
symmetry in H3. simpl_env in H3. apply uniq_app_inv in H3.
destruct H3; subst. pick fresh c.
assert ([(c, Eq t)] ++ G2 ++ G1 ⊢
  open_term_wrt_typ e (typ_var_f c) ~:
  tsubst_typ (typ_var_f c) b τ) by auto.
apply wfterm_wfenv in H3. apply wfenv_wftyp_Eq3 in H3.
apply wftyp_ftv in H3. clear Fr. fsetdec.
eauto with lngen.
SCase "b0 ≠ b". inversion H2; subst.
assert (binds b E (G2 ++ (b0, E) :: G1)). rewrite H3. auto.
analyze_binds H4.
SSCase "b binds in G2".
apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
simpl_env in H3. apply uniq_app_inv in H3. destruct H3; subst.
simpl_env in *.
pick fresh a. edestruct H1 with (a := a)
 (Γ₁ := [(a, Eq t)] ++ Γ₁) (Γ₂ := x0 ++ G1) as [τ' [e' [? ?]]];
 simpl_env; auto. clear H1.
apply redn_context_sigma with (b := b0) (a := a) (τ := t) in H3; auto.
rewrite close_term_wrt_typ_open_term_wrt_typ in H3; auto.
unfold close_term_wrt_typ in H3; simpl in H3.
assert (a ≠ b) by auto.
unfold typvar in *; destruct (a == b); try congruence.
assert (exists e'', red0 (term_sigma (typ_var_f b0) t (term_sigma
  (typ_var_f b) (close_typ_wrt_typ_rec 0 a τ') (close_term_wrt_typ_rec
  1 a e'))) Eps e'') as [e'' He''].
  apply red0_sigma_sigma_defined.
  apply result_redn_Eps_result
    with (e := term_sigma (typ_var_f b0) t e); auto.
  pick fresh c and apply result_sigma; auto.
assert ((term_sigma (typ_var_f b0) t (term_sigma (typ_var_f b)
         (close_typ_wrt_typ_rec 0 a τ') (close_term_wrt_typ_rec 1 a
         e'))) ⇝⋆[ Eps] e''). eauto with clos_refl_trans.
inversion He''; subst.
exists (open_typ_wrt_typ (close_typ_wrt_typ_rec 0 a τ') t).
exists (term_sigma (typ_var_f b0) t1' e'0). split.
eauto with clos_refl_trans.
unfold open_typ_wrt_typ. rewrite <- tsubst_typ_spec_rec.
assert (b ∉ ftv_typ t).
  assert ([(a, Eq t)] ++ Γ₁ ++ [(b, E)] ++ x0 ++ G1 ⊢
open_term_wrt_typ e (typ_var_f a) ~: tsubst_typ (typ_var_f a) b0 τ)
by auto.
  intro.
  apply wfterm_Eq_not_E with (a := a) (b := b) (τ₁ := t) in H6.
  eapply H6. auto. auto. auto.
assert (ftv_typ (tsubst_typ t a τ') [<=]
  ftv_typ t ∪ remove a (ftv_typ τ')) by auto with lngen.
clear Fr. fsetdec.
rewrite H3. eauto with lngen.
SSCase "b binds in G1".
apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in H3.
rewrite_env ((G2 ++ [(b0, E)] ++ x) ++ [(b, E)] ++ x0) in H3.
apply uniq_app_inv in H3. destruct H3; subst.
simpl_env in *.
pick fresh a. edestruct H1 with (a := a)
 (Γ₁ := [(a, Eq t)] ++ G2 ++ x) (Γ₂ := Γ₂) as [τ' [e' [? ?]]];
 simpl_env; auto. clear H1.
apply redn_context_sigma with (b := b0) (a := a) (τ := t) in H3; auto.
rewrite close_term_wrt_typ_open_term_wrt_typ in H3; auto.
unfold close_term_wrt_typ in H3; simpl in H3.
assert (a ≠ b) by auto.
unfold typvar in *; destruct (a == b); try congruence.
assert (exists e'', red0 (term_sigma (typ_var_f b0) t (term_sigma
  (typ_var_f b) (close_typ_wrt_typ_rec 0 a τ') (close_term_wrt_typ_rec
  1 a e'))) Eps e'') as [e'' He''].
  apply red0_sigma_sigma_defined.
  apply result_redn_Eps_result
    with (e := term_sigma (typ_var_f b0) t e); auto.
  pick fresh c and apply result_sigma; auto.
assert ((term_sigma (typ_var_f b0) t (term_sigma (typ_var_f b)
         (close_typ_wrt_typ_rec 0 a τ') (close_term_wrt_typ_rec 1 a
         e'))) ⇝⋆[ Eps] e''). eauto with clos_refl_trans.
inversion He''; subst.
exists (open_typ_wrt_typ (close_typ_wrt_typ_rec 0 a τ') t).
exists (term_sigma (typ_var_f b0) t1' e'0).
split. eauto with clos_refl_trans.
unfold open_typ_wrt_typ. rewrite <- tsubst_typ_spec_rec.
assert (b ∉ ftv_typ t).
  assert ([(a, Eq t)] ++ G2 ++ x ++ [(b, E)] ++ Γ₂ ⊢
open_term_wrt_typ e (typ_var_f a) ~: tsubst_typ (typ_var_f a) b0 τ)
by auto.
  intro.
  apply wfterm_Eq_not_E with (a := a) (b := b) (τ₁ := t) in H6.
  eapply H6. auto 6. auto. auto.
assert (ftv_typ (tsubst_typ t a τ') [<=]
  ftv_typ t ∪ remove a (ftv_typ τ')) by auto with lngen.
clear Fr. fsetdec.
rewrite H3; eauto with lngen.
Qed.

Theorem progress : forall Γ e τ,
  (forall x τ, not (binds x (T τ) Γ)) →
  Γ ⊢ e ~: τ →
  (exists e', exists e'', e ⇝⋆[Eps] e' ∧ e' ⇝[NoEps] e'') ∨ result e.
Proof with eauto 9 with lngen clos_refl_trans redn_context.
intros Γ e τ Henv H. induction H; simpl.
Case "var". elimtype False. intuition eauto.
Case "app".
destruct IHwfterm1 as [[? [? [? ?]]] | ?]... intuition eauto with fzip.
destruct IHwfterm2 as [[? [? [? ?]]] | ?]... intuition eauto with fzip.
destruct H2.
  SCase "e val". destruct H3; subst.
    SSCase "e0 val". destruct H2; subst; eauto 9 with clos_refl_trans;
    try solve [inversion H0].
      SSSCase "e coerce". inversion H0; subst. destruct H4; subst.
        SSSSCase "coerce lam". inversion H2; subst...
        SSSSCase "coerce gen (absurd)". elimtype False.
          inversion H11; subst. eapply wftypeq_arrow_forall_absurd; eauto.
        SSSSCase "coerce pair (absurd)". elimtype False.
          inversion H11; subst. eapply wftypeq_prod_arrow_absurd; eauto.
        SSSSCase "coerce coerce (absurd)". elimtype False. eapply H5; eauto.
        SSSSCase "coerce exists (absurd)". elimtype False.
          inversion H11; subst. eapply wftypeq_arrow_exists_absurd; eauto.
    SSCase "e0 result".
    destruct red0_sigma_appR_defined with (t := t) (b := b)
      (e1 := e) (e2 := e0); auto.
    pick fresh a. apply result_sigma_exists with (a := a); auto.
    left; eauto with clos_refl_trans.
  SCase "e result".
  destruct red0_sigma_appL_defined with (t := t) (b := b)
    (e1 := e) (e2 := e2); auto.
  pick fresh a. apply result_sigma_exists with (a := a); auto.
  left; eauto with clos_refl_trans.
Case "abs". pick fresh x.
assert (lc_typ t1). eapply wftyp_regular. eapply wfenv_wftyp_T3.
  eapply wfterm_wfenv. eauto.
idtac...
Case "let". pick fresh x.
assert (lc_term (term_let e1 e2)). idtac...
inversion H3; subst.
destruct IHwfterm as [[? [? [? ?]]] | ?]. intuition eauto with fzip.
SCase "e1 reduces". left.
exists (term_let x0 e2). exists (term_let x1 e2). split.
apply redn_context_letL with (x := x); auto.
eauto with lngen.
SCase "e1 result". inversion H4; subst.
SSCase "e1 val". idtac...
SSCase "e1 result".
destruct red0_sigma_letL_defined with (b := b) (t := t) (e1 := e) (e2 := e2); auto.
left. eauto with clos_refl_trans.
Case "pair".
destruct IHwfterm1 as [[? [? [? ?]]] | ?]... intuition eauto with fzip.
destruct IHwfterm2 as [[? [? [? ?]]] | ?]... intuition eauto with fzip.
inversion H2; subst.
  SCase "e1 val". inversion H3; subst; auto.
    SSCase "e2 result".
    destruct red0_sigma_pairR_defined
      with (b := b) (t := t) (e1 := e1) (e2 := e); auto. left.
    eauto with clos_refl_trans.
  SCase "e1 result".
  destruct red0_sigma_pairL_defined
    with (b := b) (t := t) (e1 := e) (e2 := e2); auto. left.
  eauto with clos_refl_trans.
Case "fst". destruct IHwfterm as [[? [? [? ?]]] | ?]... destruct H0; subst...
  SSCase "e val". destruct H0; subst; try solve [inversion H]...
    SSSCase "coerce". inversion H; subst. destruct H1; subst.
      SSSSCase "coerce abs (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_arrow_prod_absurd; eauto.
      SSSSCase "coerce gen (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_prod_forall_absurd; eauto.
      SSSSCase "coerce pair". inversion H0; subst...
      SSSSCase "coerce coerce (absurd)". elimtype False. intuition eauto.
      SSSSCase "coerce exists (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_prod_exists_absurd; eauto.
Case "snd". destruct IHwfterm as [[? [? [? ?]]] | ?]... destruct H0; subst...
  SSCase "e val". destruct H0; subst; try solve [inversion H]...
    SSSCase "coerce". inversion H; subst. destruct H1; subst.
      SSSSCase "coerce abs (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_arrow_prod_absurd; eauto.
      SSSSCase "coerce gen (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_prod_forall_absurd; eauto.
      SSSSCase "coerce pair". inversion H0; subst...
      SSSSCase "coerce coerce (absurd)". elimtype False. intuition eauto.
      SSSSCase "coerce exists (absurd)". elimtype False.
        inversion H8; subst. eapply wftypeq_prod_exists_absurd; eauto.
Case "inst". destruct IHwfterm as [[? [? [? ?]]] | ?]... destruct H1; subst.
  SCase "e val". destruct H1; subst; try solve [inversion H0]...
    SSCase "coerce". inversion H0; subst. destruct H2; subst...
      SSSCase "abs (absurd)". elimtype False. inversion H9; subst.
        eapply wftypeq_arrow_forall_absurd; eauto.
      SSSCase "pair (absurd)". elimtype False. inversion H9; subst.
        eapply wftypeq_prod_forall_absurd; eauto.
      SSSCase "coerce (absurd)". elimtype False. intuition eauto.
      SSSCase "exists (absurd)". elimtype False. inversion H9; subst.
        eapply wftypeq_exists_forall_absurd; eauto.
  SCase "e result".
  destruct red0_sigma_inst_defined
    with (b := b) (t := t0) (t' := t) (e := e); auto.
  eauto with lngen.
  pick fresh a. apply result_sigma_exists with (a := a); auto.
  left. eauto with clos_refl_trans.
Case "gen". pick fresh a...
Case "exists". pick fresh a. destruct (H0 a) as [[? [? [? ?]]] | ?]; clear H0...
  intros. intro. eapply (Henv x τ). analyze_binds H0.
  SCase "e reduces". left.
    exists (term_exists (close_term_wrt_typ a x)).
    exists (term_exists (close_term_wrt_typ a x0)). split.
    SSCase "redn Eps".
    rewrite <- close_term_wrt_typ_open_term_wrt_typ with (e1 := e) (a1 := a)...
    SSCase "red1 NoEps".
    pick fresh b and apply red1_exists.
    repeat rewrite <- tsubst_term_spec. apply red1_trenaming; auto.
  SCase "e result". inversion H1; subst.
    SSCase "e val". elimtype False. eapply val_pure; eauto.
    SSCase "e result".
    unfold open_term_wrt_typ in H0; destruct e; inversion H0; subst.
    assert (uniq (a ~ E ++ G)) by eauto with lngen.
    assert ([(a, E)] ++ G ⊢ open_term_wrt_typ (term_sigma t1
         t2 e) (typ_var_f a) ~: open_typ_wrt_typ t (typ_var_f a)) by
         auto. clear H.
    unfold open_term_wrt_typ in H6; simpl in H6. inversion H6; subst. clear H6.
    assert (b0 = b) by congruence. subst.
    assert (binds b E ((a, E) :: G)). rewrite <- H; auto. analyze_binds_uniq H6.
    SSSCase "b = a". destruct t1; inversion H7; subst.
    destruct (lt_eq_lt_dec n 0); try congruence.
    destruct s; try congruence; subst.
    SSSSCase "t1 = typ_var_b 0". clear H5 H7 H0 H9.
    unfold open_term_wrt_typ in H1; inversion H1; subst.
    inversion H0. inversion H5.
    pick fresh a0.
    assert (result (open_term_wrt_typ (open_term_wrt_typ_rec 1
           (typ_var_f a) e) (typ_var_f a0))) by auto.
    unfold open_term_wrt_typ in H0; inversion H0; subst.
    (* e is a value : we have a value *)
    right. apply result_val.
    apply val_exists_exists with (a := a0) (b := a); auto.
    (* e is a sigma : we can reduce *) left.
    destruct e; inversion H5; subst. clear H5.
    destruct t1; inversion H14.
    destruct (lt_eq_lt_dec n 1); try congruence.
    destruct s; try congruence; subst.
    (* t3 = typ_var_b 0 : absurd *) assert (n = 0) by omega; subst.
    assert (wfterm ([(a0, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a)
          t2))] ++ G2 ++ G1) (open_term_wrt_typ (open_term_wrt_typ_rec
          1 (typ_var_f a) (term_sigma (typ_var_b 0) t3 e)) (typ_var_f
          a0)) (tsubst_typ (typ_var_f a0) a (open_typ_wrt_typ t
          (typ_var_f a)))) by auto.
    unfold open_term_wrt_typ in H5; simpl in H5. inversion H5; subst.
    assert (E = Eq (open_typ_wrt_typ_rec 0 (typ_var_f a) t2)).
    apply binds_unique with (x := a0) (E := (a0, Eq
    (open_typ_wrt_typ_rec 0 (typ_var_f a) t2)) :: G2 ++ G1).
    rewrite <- H15. auto. auto. eauto with lngen.
    congruence.
    (* t3 = typ_var_b 1 : absurd *)
    assert (wfterm ([(a0, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a)
          t2))] ++ G2 ++ G1) (open_term_wrt_typ (open_term_wrt_typ_rec
          1 (typ_var_f a) (term_sigma (typ_var_b 1) t3 e)) (typ_var_f
          a0)) (tsubst_typ (typ_var_f a0) a (open_typ_wrt_typ t
          (typ_var_f a)))) by auto.
    unfold open_term_wrt_typ in H5; simpl in H5. inversion H5; subst.
    assert (a ∈ dom (G2 ++ G1)).
    assert (binds a E ((a0, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a)
    t2)) :: G2 ++ G1)). rewrite <- H15; auto.
    analyze_binds H16; eapply binds_In; eauto.
    contradiction.
    (* t3 = typ_var_b n with n > 1 : absurd *)
    simpl in H13. destruct (lt_eq_lt_dec (n-1) 0); try congruence.
    destruct s; try congruence. absurdity with omega.
    (* t3 = typ_var_f b : we can reduce *) subst t0. clear H14.
    (* Eps reduction *)
    assert (exists e', red0 (term_sigma (typ_var_f a)
      (open_typ_wrt_typ t2 (typ_var_f a)) (term_sigma (typ_var_f b)
      (open_typ_wrt_typ_rec 1 (typ_var_f a) t3)
      (open_term_wrt_typ_rec 2 (typ_var_f a) e))) Eps e') as [e' He'].
      apply red0_sigma_sigma_defined.
      apply result_sigma_exists with (a := a0); auto.
    assert (term_exists (term_sigma (typ_var_b 0) t2 (term_sigma
    (typ_var_f b) t3 e)) ⇝⋆[Eps] term_exists (close_term_wrt_typ a
    e')).
    rewrite <- close_term_wrt_typ_open_term_wrt_typ
      with (a1 := a)
        (e1 := term_sigma (typ_var_b 0) t2 (term_sigma (typ_var_f b) t3 e)). 
    apply redn_context_exists. auto with clos_refl_trans.
    simpl in Fr; simpl; auto.
    (* NoEps reduction *)
    assert (exists e'', term_exists (close_term_wrt_typ a e')
    ⇝[NoEps]e'') as [e'' He''].
      assert (exists e'', red0 (term_exists (close_term_wrt_typ a e'))
        NoEps e'') as [e'' He''].
      inversion He'; subst. unfold close_term_wrt_typ; simpl.
      unfold typvar; destruct (a == a); try congruence.
      assert (a ≠ b). simpl in Fr; auto.
      unfold typvar; destruct (a == b); try congruence.
      apply red0_sigma_exists_defined with (c := a) (a := a0). auto.
      (* freshness proof 1 *)
      pick fresh d1.
      rewrite <- close_typ_wrt_typ_open_typ_wrt_typ
        with (a1 := d1) (t1 := t1'); auto.
      rewrite <- H21; auto.
      pick fresh d2.
      rewrite <- close_term_wrt_typ_rec_open_term_wrt_typ_rec
        with (n1 := 1) (a1 := d2) (e1 := e'0); auto.
      rewrite <- close_term_wrt_typ_rec_open_term_wrt_typ_rec
        with (n1 := 0) (a1 := d1)
          (e1 := open_term_wrt_typ_rec 1 (typ_var_f d2) e'0).
      rewrite <- H22; auto.
      simpl.
      repeat rewrite ftv_term_close_term_wrt_typ_rec.
      unfold close_typ_wrt_typ.
      repeat rewrite ftv_typ_close_typ_wrt_typ_rec.
      clear H2 H4 H11 H H8 H6 H10 H7 H3 H12 H1 H9 H0 H17 H20 H21 H22 He' H5.
      assert (a0 ∉ remove a (remove d1
        (ftv_typ (open_typ_wrt_typ t2 (typ_var_f a))))).
        assert (a0 ≠ a) by auto. assert (a0 ∉ ftv_typ t2) by auto.
        clear Fr Fr0 Fr1 Fr2.
        assert (remove a (remove d1 (ftv_typ (open_typ_wrt_typ t2 (typ_var_f a))))
        [<=] ftv_typ (open_typ_wrt_typ t2 (typ_var_f a))). fsetdec.
        assert (ftv_typ (open_typ_wrt_typ t2 (typ_var_f a)) [<=]
        ftv_typ (typ_var_f a) ∪ ftv_typ t2) by auto with lngen.
        simpl in H2. fsetdec.
      assert (a0 ∉ remove a
        (remove d2
          (remove d1
            (ftv_term
              (open_term_wrt_typ_rec 0 (typ_var_f d2)
                (open_term_wrt_typ_rec 1 (typ_var_f d1)
                  (open_term_wrt_typ_rec 2 (typ_var_f a) e))))))).
        assert (a0 ≠ d1) by auto. assert (a0 ≠ d2) by auto. simpl in Fr0.
        assert (a0 ∉ ftv_term e) by auto. assert (a0 ≠ a) by auto.
        clear Fr Fr0 Fr1 Fr2.
        assert (remove a
          (remove d2
            (remove d1
              (ftv_term
                (open_term_wrt_typ_rec 0 (typ_var_f d2)
                  (open_term_wrt_typ_rec 1 (typ_var_f d1)
                    (open_term_wrt_typ_rec 2 (typ_var_f a) e))))))
          [<=]
          ftv_typ (typ_var_f d2) ∪ ftv_typ (typ_var_f d1) ∪
          ftv_typ (typ_var_f a) ∪ ftv_term e).
        transitivity (ftv_term
          (open_term_wrt_typ_rec 0 (typ_var_f d2)
            (open_term_wrt_typ_rec 1 (typ_var_f d1)
              (open_term_wrt_typ_rec 2 (typ_var_f a) e)))).
        clear H H0 H1 n H13. fsetdec.
        transitivity (ftv_typ (typ_var_f d2) ∪ ftv_typ (typ_var_f d1) ∪
        ftv_term (open_term_wrt_typ_rec 2 (typ_var_f a) e)); auto with lngen.
        transitivity (ftv_typ (typ_var_f d2) ∪ ftv_term
        (open_term_wrt_typ_rec 1 (typ_var_f d1) (open_term_wrt_typ_rec 2
        (typ_var_f a) e))); auto with lngen.
        simpl in H4. clear Henv BindsTacSideCond H13 n H.
        assert (a0 ∉ singleton d2∪singleton d1∪singleton a∪ftv_term e)
          by auto. clear H0 H1 H2 H3. auto.
      clear Fr Fr0 Fr1 Fr2 BindsTacSideCond Henv e0 H13 n. solve_notin.
      assert (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f d2) e'0)
        [<=] ftv_typ (typ_var_f d2) ∪ ftv_term e'0) by auto with lngen.
      clear Fr Fr0. assert (d1 ≠ d2) by auto. clear Fr2.
      assert (d1 ∉ ftv_term e'0) by auto. clear Fr1.
      simpl in H14. fsetdec.
      (* freshness proof 2 *)
      pick fresh d1.
      rewrite <- close_typ_wrt_typ_open_typ_wrt_typ
        with (a1 := d1) (t1 := t1'); auto.
      rewrite <- H21; auto.
      pick fresh d2.
      rewrite <- close_term_wrt_typ_rec_open_term_wrt_typ_rec
        with (n1 := 1) (a1 := d2) (e1 := e'0); auto.
      rewrite <- close_term_wrt_typ_rec_open_term_wrt_typ_rec
        with (n1 := 0) (a1 := d1)
          (e1 := open_term_wrt_typ_rec 1 (typ_var_f d2) e'0).
      rewrite <- H22; auto.
      simpl.
      repeat rewrite ftv_term_close_term_wrt_typ_rec.
      unfold close_typ_wrt_typ.
      repeat rewrite ftv_typ_close_typ_wrt_typ_rec.
      clear Fr Fr0 Fr1 Fr2. auto.
      assert (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f d2) e'0)
        [<=] ftv_typ (typ_var_f d2) ∪ ftv_term e'0) by auto with lngen.
      clear Fr Fr0. assert (d1 ≠ d2) by auto. clear Fr2.
      assert (d1 ∉ ftv_term e'0) by auto. clear Fr1.
      simpl in H14. fsetdec.
      (* freshness proof 3 *)
      unfold open_typ_wrt_typ.
      rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec.
      assert (a ∉ ftv_typ (open_typ_wrt_typ_rec 1 (typ_var_f a) t3)).
        assert (wfterm ([(a0, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a)
          t2))] ++ G2 ++ G1) (open_term_wrt_typ (open_term_wrt_typ_rec
          1 (typ_var_f a) (term_sigma (typ_var_f b) t3 e)) (typ_var_f
          a0)) (tsubst_typ (typ_var_f a0) a (open_typ_wrt_typ t
          (typ_var_f a)))) by auto.
        unfold open_term_wrt_typ in H14; simpl in H14.
        apply wfterm_ftv in H14. simpl in H14.
        assert (a ∉ ftv_typ (open_typ_wrt_typ_rec 0 (typ_var_f a0)
               (open_typ_wrt_typ_rec 1 (typ_var_f a) t3))).
          assert (a ≠ a0) by auto. clear Fr Fr0. fsetdec.
        assert (ftv_typ (open_typ_wrt_typ_rec 1 (typ_var_f a) t3)
          [<=] ftv_typ
              (open_typ_wrt_typ_rec 0 (typ_var_f a0)
                 (open_typ_wrt_typ_rec 1 (typ_var_f a) t3)))
        by auto with lngen.
        clear Fr Fr0. fsetdec.
      assert (a ∉ ftv_typ (open_typ_wrt_typ_rec 0 (typ_var_f a) t2)).
        assert (wfterm ([(a0, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a)
          t2))] ++ G2 ++ G1) (open_term_wrt_typ (open_term_wrt_typ_rec
          1 (typ_var_f a) (term_sigma (typ_var_f b) t3 e)) (typ_var_f
          a0)) (tsubst_typ (typ_var_f a0) a (open_typ_wrt_typ t
          (typ_var_f a)))) by auto.
        unfold open_term_wrt_typ in H15; simpl in H15.
        apply wfterm_wfenv in H15. simpl_env in H15.
        apply wfenv_wftyp_Eq3 in H15.
        apply wftyp_ftv in H15. clear Fr Fr0. fsetdec.
        clear Fr Fr0.
        assert (ftv_typ (open_typ_wrt_typ_rec 0 (open_typ_wrt_typ_rec
       0 (typ_var_f a) t2) (open_typ_wrt_typ_rec 1 (typ_var_f a) t3))
       [<=] ftv_typ (open_typ_wrt_typ_rec 0 (typ_var_f a) t2) ∪
       ftv_typ (open_typ_wrt_typ_rec 1 (typ_var_f a) t3)) by auto with
       lngen.
        fsetdec.
        (* result proof *)
        apply result_red0_Eps_result in He'; auto.
        unfold open_term_wrt_typ; simpl.
        repeat rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec.
        rewrite <- tsubst_term_spec_rec. rewrite tsubst_term_var_self.
        inversion He'; subst. inversion H14; try congruence.
        pick fresh d. apply result_sigma_exists with (a := d); auto.
      eauto.
    eauto.
    SSSSCase "t1 = typ_var_f t0 (absurd)".
    simpl in Fr. assert (t0 ≠ t0) by auto. congruence.
    SSSCase "a ≠ b". destruct t1; inversion H7; subst.
    destruct (lt_eq_lt_dec n 0); try congruence. destruct s; try congruence.
    assert (b ≠ a) by auto. inversion H9; congruence. clear H0 H5 H7.
    (* we can reduce *) left.
    assert (exists e'', red0 (term_exists (term_sigma (typ_var_f t0)
    t2 e)) NoEps e'') as [e'' He''].
    apply red0_sigma_exists_defined with (c := a) (a := t0). auto.
    SSSSCase "freshness proof 1". pick fresh a0.
    assert (wfterm ([(a0, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a)
          t2))] ++ G2 ++ G1) (open_term_wrt_typ (open_term_wrt_typ_rec
          1 (typ_var_f a) e) (typ_var_f a0)) (tsubst_typ (typ_var_f
          a0) t0 (open_typ_wrt_typ t (typ_var_f a)))) by auto. clear H12.
    apply wfterm_ftv in H0; simpl in H0.
    assert (ftv_term e [<=] ftv_term (open_term_wrt_typ
         (open_term_wrt_typ_rec 1 (typ_var_f a) e) (typ_var_f a0))).
      transitivity (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f a) e));
        auto with lngen.
    assert (t0 ≠ a0) by auto. clear Fr Fr0. fsetdec.
    SSSSCase "freshness proof 2". simpl in Fr; auto.
    SSSSCase "freshness proof 3". pick fresh a0.
    assert (wfterm ([(a0, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a)
          t2))] ++ G2 ++ G1) (open_term_wrt_typ (open_term_wrt_typ_rec
          1 (typ_var_f a) e) (typ_var_f a0)) (tsubst_typ (typ_var_f
          a0) t0 (open_typ_wrt_typ t (typ_var_f a)))) by auto. clear H12.
    intro.
    eapply wfterm_Eq_not_E with
      (Γ := [(a0, Eq (open_typ_wrt_typ_rec 0 (typ_var_f a) t2))] ++ G2 ++ G1)
      (τ₁ := open_typ_wrt_typ_rec 0 (typ_var_f a) t2)
      (a := a0) (b := a); eauto.
    assert (binds a E (G2 ++ (t0, E) :: G1)). rewrite H. auto.
    analyze_binds H6.
    SSSSCase "result proof". unfold open_term_wrt_typ; simpl.
    pick fresh a0. apply result_sigma_exists with (a := a0); auto.
    eauto with clos_refl_trans.
Case "open". destruct IHwfterm as [[? [? [? ?]]] | ?]...
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
      SSSCase "exists". idtac...
    SSCase "exists". left.
    exists (term_open (typ_var_f b) (term_exists (term_sigma
    (typ_var_b 0) t' e'))).
    exists (open_term_wrt_typ (term_sigma (typ_var_b 0) t' e') (typ_var_f b)).
    split. idtac...
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
  SCase "e result". idtac...
Case "nu". pick fresh b. destruct (H0 b) as [[? [? [? ?]]] | ?]...
  intros. intro. eapply (Henv x τ). analyze_binds H1. 
  SCase "e reduces.". left.
    exists (term_nu (close_term_wrt_typ b x)).
    exists (term_nu (close_term_wrt_typ b x0)). split.
    SSCase "redn Eps".
    rewrite <- close_term_wrt_typ_open_term_wrt_typ with (e1 := e) (a1 := b)...
    SSCase "red1 NoEps". pick fresh a and apply red1_nu.
    repeat rewrite <- tsubst_term_spec. apply red1_trenaming; auto.
  SCase "e result". clear H0.
  assert (wfterm ([(b, E)] ++ G) (open_term_wrt_typ e (typ_var_f b)) t) by auto.
  clear H. inversion H1; subst.
  SSCase "e val". elimtype False. eapply val_pure; eauto.
  SSCase "e result". left. unfold open_term_wrt_typ in H; inversion H; subst.
  clear H H5.
  rewrite_env (nil ++ b ~ E ++ G) in H0.
  apply result_redn_Eps in H0; eauto. destruct H0 as [t'0 [e'0 [He'0 Ht'0]]].
  exists (term_nu (close_term_wrt_typ b (term_sigma (typ_var_f b) t'0 e'0))).
  assert (exists e'', red0 (term_nu (close_term_wrt_typ b (term_sigma (typ_var_f b) t'0 e'0)))
 NoEps e'') as [e'' He''].
    SSSCase "NoEps reduction". unfold close_term_wrt_typ; simpl.
    unfold typvar; destruct (b == b); try congruence.
    pick fresh a.
    apply red0_nu_sigma_defined with (b := b). 
    unfold open_typ_wrt_typ.
    rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec; auto.
    apply result_redn_Eps_result in He'0; auto. inversion He'0; subst.
    inversion H; try congruence.
    unfold open_term_wrt_typ; simpl. pick fresh c.
    apply result_sigma_exists with (a := c).
    rewrite <- tsubst_typ_spec_rec. auto with lngen.
    rewrite <- tsubst_term_spec_rec. rewrite tsubst_term_var_self. auto.
    exists e''. split; auto.
    rewrite <- close_term_wrt_typ_open_term_wrt_typ with (e1 := e) (a1 := b)...
Case "sigma". pick fresh a. destruct (H1 a) as [[? [? [? ?]]] | ?]; auto.
  intros. intro. eapply (Henv x τ). analyze_binds H2.
  SCase "e reduces.". left.
  exists (term_sigma (typ_var_f b) t' (close_term_wrt_typ a x)).
  exists (term_sigma (typ_var_f b) t' (close_term_wrt_typ a x0)).
  assert (lc_typ t').
    assert (wfterm ([(a, Eq t')] ++ G2 ++ G1) (open_term_wrt_typ e
    (typ_var_f a)) (tsubst_typ (typ_var_f a) b t)) by auto.
    apply wfterm_wfenv in H4. apply wfenv_wftyp_Eq3 in H4.
    apply wftyp_regular in H4. auto.
  split.
  SSCase "Eps reduction".
  rewrite <- close_term_wrt_typ_open_term_wrt_typ with (e1 := e) (a1 := a); auto.
  apply redn_context_sigma; auto.
  SSCase "NoEps reduction". pick fresh c and apply red1_sigma; auto.
  repeat rewrite <- tsubst_term_spec. auto using red1_trenaming.
  SCase "e result". right.
  apply result_sigma with (L := L ∪ ftv_term e); intros.
  assert (wfterm ([(a, Eq t')] ++ G2 ++ G1) (open_term_wrt_typ e
    (typ_var_f a)) (tsubst_typ (typ_var_f a) b t)) by auto.
    apply wfterm_wfenv in H3. apply wfenv_wftyp_Eq3 in H3.
    apply wftyp_regular in H3. auto.
  apply result_trenaming_inv with (a := a0) (b := a).
    rewrite tsubst_term_open_term_wrt_typ; auto.
    autorewrite with lngen; auto.
Case "coerce". destruct IHwfterm as [[? [? [? ?]]] | ?].
  intros. intro. eapply (Henv x τ). analyze_binds H2.
  SCase "e reduces.". left.
  assert (lc_typ t) by eauto with lngen. idtac...
  SCase "e result". assert (lc_typ t) by eauto with lngen.
  assert (lc_term e) by eauto with lngen.
  inversion H1; subst.
  SSCase "e val". inversion H4; subst;
  try solve [right; constructor; constructor; auto; intros; congruence].
  SSSCase "e coerce". left...
  SSCase "e result". left.
  destruct red0_sigma_coerce_defined
    with (b := b) (t := t0) (e := e0) (t' := t); auto.
  eauto with clos_refl_trans.
Qed.
