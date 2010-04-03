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
Case "beta_v".
inversion H7; subst.
pick fresh x. rewrite subst_term_intro with (x1 := x); auto.
assert (pure G2) by eauto using val_pure.
assert (pure Γ) by eauto using pure_zip.
assert (G1 = Γ) by eauto using zip_pure_inv1.
assert (G2 = Γ) by eauto using zip_pure_inv2.
subst.
rewrite_env (nil ++ Γ). eapply wfterm_subst; simpl_env; eauto.
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
assert (wftypeq G1 t2' t3) by admit.
assert (wftypeq G1 t2 τ) by admit. (* wftypeq_arrow_inv *)
apply wfterm_coerce with (t' := t2); auto.
admit. (* wftypeq_zip13 *)
apply wfterm_app with (G1 := G1) (G2 := G2) (t2 := t2'); auto.
apply wfterm_coerce with (t' := t3); auto. apply wftypeq_sym.
admit. (* wftypeq_zip12 *)
Case "coerce_fst".
inversion H5; subst.
inversion H10; subst.
assert (wftypeq Γ t1 τ) by admit. (* wftypeq_prod_inv1 *)
apply wfterm_coerce with (t' := t1); eauto.
Case "coerce_snd".
inversion H5; subst.
inversion H10; subst.
assert (wftypeq Γ t2 τ) by admit. (* wftypeq_prod_inv2 *)
apply wfterm_coerce with (t' := t2); eauto.
Case "coerce_inst".
inversion H8; subst.
inversion H10; subst.
assert (forall a, a ∉ dom Γ →
  wftypeq (a ~ U ++ Γ)
  (open_typ_wrt_typ t (typ_var_f a))
  (open_typ_wrt_typ t' (typ_var_f a))) by admit. (* wftypeq_forall_inv *)
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
  (open_typ_wrt_typ t0 (typ_var_f a))) by admit. (* wftypeq_forall_exists *)
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
replace (open_term_wrt_typ (term_app e1 e2') (typ_var_f a)) with
  (term_app (open_term_wrt_typ e1 (typ_var_f a)) (open_term_wrt_typ e2' (typ_var_f a))) by reflexivity.
rewrite H2; auto.
apply zip_remove_EU in H5.
apply wfterm_app with
  (G1 := a ~ Eq t ++ G3 ++ G0)
  (G2 := a ~ Eq t ++ x ++ x0) (t2 := tsubst_typ (typ_var_f a) b t2).
assert (lc_term (term_sigma (typ_var_f b) t e1)) by eauto with lngen. inversion H3; subst.
constructor; auto.
apply H12; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ a ~ Eq t ++ x ++ x0).
apply wfterm_instantiate.
apply wfterm_renameU; auto.
apply wfterm_lowerU; auto.
intro H3. apply ftv_env_binds in H3. destruct H3 as [? [? [? [? | ?]]]].
  assert (binds x3 (T x4) (x ++ x0)) by auto.
    eapply zip_binds_T23 in H6; eauto. eapply zip_binds_T31 in H6; eauto.
    assert (ftv_typ x4 [<=] dom (G3 ++ G0)). apply wftyp_ftv.
    apply wfenv_wftyp_T2 with (x := x3); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv. eauto with fzip.
    clear Fr. assert (b ∉ ftv_typ x4) by fsetdec. contradiction.
  assert (binds x3 (Eq x4) (x ++ x0)) by auto.
    eapply zip_binds_Eq23 in H6; eauto. eapply zip_binds_Eq31 in H6; eauto.
    assert (ftv_typ x4 [<=] dom (G3 ++ G0)). apply wftyp_ftv.
    apply wfenv_wftyp_Eq2 with (x := x3); auto.
    apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv; eauto.
    clear Fr. assert (b ∉ ftv_typ x4) by fsetdec. contradiction.

ICI

eapply wftyp_zip12; eauto.
  apply wfenv_wftyp_Eq3 with (x := a). eapply wfterm_wfenv; eauto.

  apply wfenv_strip with (Γ' := a ~ Eq t). eapply wfterm_wfenv; eauto.


Case "sigma_appR".
Case "sigma_pairL".
Case "sigma_pairR".
Case "sigma_fset".
Case "sigma_snd".
Case "sigma_inst".
Case "sigma_open".
Case "sigma_sigma".


ICI

Theorem subject_reduction : forall Γ e e' τ,
  wfterm Γ e τ → e ⇝ e' → wfterm Γ e' τ.
Proof with eauto.
  intros Γ e e' τ H. generalize dependent e'.
  dependent induction H.
  Case "var".
    intros e' J; inversion J; subst; inversion H1.
  Case "app".
    intros e' J; inversion J; subst...
    inversion H; subst; inversion H1; subst.
    pick fresh z.
    rewrite (subst_term_intro z)...
    eapply wfterm_subst with (Γ₁ := nil); simpl_env...
  Case "abs".
    intros e' J; inversion J; subst.
    inversion H1.
    pick fresh z and apply wfterm_abs...
  Case "inst".
    intros e' J; inversion J; subst; auto.
    inversion H1; subst.
    inversion H0; subst.
    pick fresh a.
    rewrite (tsubst_term_intro a)...
    rewrite (tsubst_typ_intro a)...
    rewrite_env (env_map (tsubst_typ t a) nil ++ G).
    eapply wfterm_tsubst; simpl_env...
  Case "gen".
    intros e' J; inversion J; subst.
    inversion H1.
    pick fresh a and apply wfterm_gen...
Qed.

Theorem progress : forall Γ e τ,
  wfterm Γ e τ →
  (exists e', e ⇝ e') ∨ val e.
Proof with eauto.
  intros Γ e τ H.
  dependent induction H; simpl...
  Case "typing_app".
    destruct IHwfterm1 as [[e1' ?] | ?]...
    destruct IHwfterm2 as [[e2' ?] | ?]...
    destruct e1; simpl in H1; inversion H1; subst; try solve [inversion H]; eauto 7.
  Case "abs".
    pick fresh z. edestruct (H0 z) as [[e1 ?] | ?]...
    left.
      exists (term_abs t1 (close_term_wrt_term z e1)).
      apply red1_abs with (L := L `union` {{z}}); intros...
      rewrite <- subst_term_spec.
      rewrite (subst_term_intro z)...
    right.
      apply val_abs with (L := L `union` {{z}}); intros...
      rewrite (subst_term_intro z)...
  Case "inst".
    destruct IHwfterm as [[e' ? ] | ? ]...
    destruct e; simpl in H1; inversion H1; subst; eauto.
    inversion H0.
    eauto 7.
  Case "gen".
    pick fresh a. edestruct (H0 a) as [[e1 ?] | ?]...
    left.
      exists (term_gen (close_term_wrt_typ a e1)).
      apply red1_gen with (L := L `union` {{a}}); intros.
      rewrite <- tsubst_term_spec.
      rewrite (tsubst_term_intro a)...
    right.
      apply val_gen with (L := L `union` {{a}}); intros.
      rewrite (tsubst_term_intro a)...
Qed.
