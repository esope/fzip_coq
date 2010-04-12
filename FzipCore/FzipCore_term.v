Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_zip.
Require Import FzipCore_pure.
Require Import FzipCore_env_typ.
Require Import FzipCore_typeq.
Require Import FzipCore_weakenU.


(** Lemmas about [wfterm] *)
Lemma wfterm_wfenv : forall Γ e τ,
  wfterm Γ e τ → wfenv Γ.
Proof.
intros Γ e τ H.
induction H; auto; try solve [eapply wfenv_zip; eauto].
Case "lam". pick fresh x. eauto using wfenv_strip.
Case "gen". pick fresh a. eauto using wfenv_strip.
Case "exists". pick fresh a. eauto using wfenv_strip.
Case "open".
apply wfenv_weakening; auto. constructor; auto.
  eauto using wfenv_strip.
Case "nu". pick fresh a. eauto using wfenv_strip.
Case "sigma".
pick fresh a.
assert (wfenv (G2 ++ G1)) by eauto using wfenv_strip.
apply wfenv_weakening; auto.
constructor; auto. eauto using wfenv_strip.
Qed.
Hint Resolve wfterm_wfenv: fzip.

Lemma wfterm_wftyp : forall Γ e τ,
  wfterm Γ e τ → wftyp Γ τ.
Proof.
intros Γ e τ H.
induction H; try solve [eauto 2 with fzip
  | inversion IHwfterm; subst; auto].
Case "app". inversion IHwfterm1; subst; eauto 3 with fzip.
Case "abs". pick fresh x. assert ([(x, T t1)] ++ G ⊢ t2 ok) by auto.
assert (wfenv ([(x, T t1)] ++ G)) by eauto 2 with fzip.
inversion H3; subst.
rewrite_env (nil ++ x ~ T t1 ++ G) in H2.
apply wftyp_subst in H2; simpl_env in H2; auto.
Case "pair". constructor; eauto 3 with fzip.
Case "inst". inversion IHwfterm; subst.
pick fresh a. rewrite tsubst_typ_intro with (a1 := a); auto.
rewrite_env (env_map (tsubst_typ t a) nil ++ G).
apply wftyp_tsubst; simpl_env; auto.
Case "exists". apply wftyp_exists with (L := L); intros.
rewrite_env (nil ++ a ~ U ++ G). apply wftyp_EU. simpl_env. auto.
Case "open". inversion IHwfterm; subst.
pick fresh a.
replace G2 with (env_map (tsubst_typ (typ_var_f b) a) G2).
replace (open_typ_wrt_typ t (typ_var_f b)) with (tsubst_typ (typ_var_f b) a (open_typ_wrt_typ t (typ_var_f a))).
apply wftyp_renameE; auto.
rewrite_env (nil ++ G2 ++ [(a, E)] ++ G1).
apply wftyp_upperE. apply wftyp_UE. simpl_env. auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto.
simpl; unfold typvar; destruct (a == a); try congruence; auto.
autorewrite with lngen; auto.
rewrite tsubst_env_fresh_eq; auto.
Case "nu". pick fresh a.
replace t with (tsubst_typ (typ_forall (typ_var_b 0)) a t).
rewrite_env (env_map (tsubst_typ (typ_forall (typ_var_b 0)) a) nil ++ G).
apply wftyp_tsubst. apply wftyp_EU. simpl_env. auto.
apply wftyp_forall with (L := L ∪ dom G); intros; unfold open_typ_wrt_typ; simpl;
  simpl_env; constructor; auto.
  eauto 4 with fzip.
autorewrite with lngen; auto.
Case "sigma".
  rewrite_env (nil ++ G2 ++ b ~ E ++ G1).
  apply wftyp_upperE.
  pick fresh a.
  rewrite_env (env_map (tsubst_typ (typ_var_f b) a) nil ++ b ~ E ++ G2 ++ G1).
  replace t with
    (tsubst_typ (typ_var_f b) a (tsubst_typ (typ_var_f a) b t)).
  apply wftyp_renameE; auto.
  apply wftyp_UE. apply wftyp_EqU with (τ' := t'). simpl_env; auto.
  apply tsubst_typ_var_twice; auto.
  apply tsubst_typ_lc_typ_inv with (t1 := typ_var_f a) (a1 := b); auto.
  eapply wftyp_regular; eauto.
Qed.
Hint Resolve wfterm_wftyp: fzip.

Lemma wfterm_regular2 : forall Γ e τ,
  wfterm Γ e τ → lc_typ τ.
Proof.
intros Γ e τ H; eauto with lngen fzip.
Qed.
Hint Resolve wfterm_regular2: lngen.

Lemma wfterm_regular1 : forall Γ e τ,
  wfterm Γ e τ → lc_term e.
Proof.
intros Γ e τ H; induction H; eauto with lngen.
Case "abs". pick fresh x.
apply lc_term_abs_exists with (x1 := x); auto.
apply wfenv_regular_T with (Γ := [(x, T t1)] ++ G) (x := x); eauto with fzip.
Case "sigma". pick fresh a.
apply lc_term_sigma_exists with (a1 := a); auto.
apply wfenv_regular_Eq with (Γ := [(a, Eq t')] ++ G2 ++ G1) (x := a); eauto with fzip.
Qed.
Hint Resolve wfterm_regular1: lngen.

Lemma wfterm_env_uniq : forall Γ e τ,
  wfterm Γ e τ → uniq Γ.
Proof.
intros Γ e τ H. eauto with lngen fzip.
Qed.
Hint Resolve wfterm_env_uniq: lngen.


(* Lemmas about wfterm *)
Lemma wfterm_T_not_ftv : forall Γ M τ x τ',
  wfterm Γ M τ → binds x (T τ') Γ → x ∉ ftv_term M.
Proof.
intros Γ M τ x τ' H H0. induction H; simpl; auto.
Case "app". eauto 7 with fzip.
Case "lam". pick fresh y.
assert (x ∉ ftv_typ t1). eapply wftyp_T_not_ftv; eauto with fzip.
assert (x ∉ ftv_term (e ^ y)) by eauto with fzip.
assert (ftv_term e [<=] ftv_term (e ^ y)) by auto with lngen.
auto.
Case "pair". eauto 7 with fzip.
Case "inst". assert (x ∉ ftv_typ t) by eauto with fzip. auto.
Case "gen". pick fresh a.
assert (x ∉ ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto.
assert (ftv_term e [<=] ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
auto.
Case "exists". pick fresh a.
assert (x ∉ ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto.
assert (ftv_term e [<=] ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
auto.
Case "open".
assert (x ≠ b). analyze_binds_uniq H0. eauto with lngen.
assert (x ∉ ftv_term e). analyze_binds_uniq H0. eauto with lngen.
auto.
Case "nu". pick fresh a.
assert (x ∉ ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto.
assert (ftv_term e [<=] ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
auto.
Case "sigma". pick fresh a.
assert (x ≠ b). analyze_binds_uniq H0. eauto with lngen.
assert (x ∉ ftv_typ t').
  assert (wftyp (G2 ++ G1) t'). eapply wfenv_wftyp_Eq3.
    eapply wfterm_wfenv. eauto. 
  analyze_binds_uniq H0; eauto with lngen.
assert (x ∉ ftv_term (open_term_wrt_typ e (typ_var_f a))) by eauto.
assert (ftv_term e [<=] ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
auto.
Case "coerce". eauto with fzip.
Qed.

Lemma wfterm_UEEq_not_fv :
  forall Γ M τ a,
    wfterm Γ M τ →
    (binds a U Γ ∨ binds a E Γ ∨ (∃ τ', binds a (Eq τ') Γ) ∨ a ∉ dom Γ) →
    a ∉ fv_term M.
Proof.
intros Γ M τ a H H0. induction H; simpl; auto.
Case "var". destruct (a == x); subst; auto.
destruct H0. assert (U = T t). eapply binds_unique; eauto with lngen. congruence.
destruct H0. assert (E = T t). eapply binds_unique; eauto with lngen. congruence.
destruct H0. destruct H0. assert (Eq x0 = T t). eapply binds_unique; eauto with lngen. congruence.
eauto.
Case "app".
assert (a ∉ fv_term e1).
  destruct H0. eauto with fzip.
  destruct H0. apply zip_binds_E3_inv with (Γ₁:=G1) (Γ₂:=G2) in H0; auto; eauto with lngen.
  destruct H0. destruct H0. eauto 7 with fzip.
  assert (dom G1 [<=] dom G) by eauto with fzip. auto 8.
assert (a ∉ fv_term e2).
  destruct H0. eauto with fzip.
  destruct H0. apply zip_binds_E3_inv with (Γ₁:=G1) (Γ₂:=G2) in H0; auto; eauto with lngen.
  destruct H0.  destruct H0. eauto 7 with fzip.
  erewrite <- zip_dom2 in H0; eauto.
auto.
Case "lam". pick fresh x.
assert (a ∉ fv_term (e ^ x)). apply H2; auto.
  destruct H0. auto.
  destruct H0. auto.
  destruct H0. destruct H0; eauto 6.
  auto.
assert (fv_term e [<=] fv_term (e ^ x)) by auto with lngen.
auto.
Case "pair".
assert (a ∉ fv_term e1).
  destruct H0. eauto with fzip.
  destruct H0. apply zip_binds_E3_inv with (Γ₁:=G1) (Γ₂:=G2) in H0; auto; eauto with lngen.
  destruct H0. destruct H0. eauto 7 with fzip.
  assert (dom G1 [<=] dom G) by eauto with fzip. auto 8.
assert (a ∉ fv_term e2).
  destruct H0. eauto with fzip.
  destruct H0. apply zip_binds_E3_inv with (Γ₁:=G1) (Γ₂:=G2) in H0; auto; eauto with lngen.
  destruct H0.  destruct H0. eauto 7 with fzip.
  erewrite <- zip_dom2 in H0; eauto.
auto.
Case "gen". pick fresh b.
assert (a ∉ fv_term (open_term_wrt_typ e (typ_var_f b))).
  destruct H0. auto.
  destruct H0. auto.
  destruct H0. destruct H0; eauto 7.
  auto 6.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f b))) by auto with lngen.
auto.
Case "exists". pick fresh b.
assert (a ∉ fv_term (open_term_wrt_typ e (typ_var_f b))).
  destruct H0. auto.
  destruct H0. auto.
  destruct H0. destruct H0; eauto 7.
  auto 6.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f b))) by auto with lngen.
auto.
Case "open". apply IHwfterm.
  destruct H0. analyze_binds_uniq H0. eauto with lngen.
  destruct H0. analyze_binds_uniq H0. eauto with lngen.
  destruct H0. destruct H0. analyze_binds_uniq H0.
    eauto with lngen. eauto 6. eauto 6.
  auto.
Case "nu". pick fresh b.
assert (a ∉ fv_term (open_term_wrt_typ e (typ_var_f b))).
  destruct H0. auto.
  destruct H0. auto.
  destruct H0. destruct H0; eauto 7.
  auto 6.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f b))) by auto with lngen.
auto.
Case "sigma". pick fresh c.
assert (a ∉ fv_term (open_term_wrt_typ e (typ_var_f c))). apply H2; auto.
  destruct H0. analyze_binds_uniq H0. eauto with lngen.
  destruct H0. analyze_binds_uniq H0. eauto with lngen.
  destruct H0. destruct H0. analyze_binds_uniq H0.
    eauto with lngen. eauto 7. eauto 7.
  auto 6.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f c))) by auto with lngen.
auto.
Qed.

Lemma wfterm_fv : forall Γ e τ,
  wfterm Γ e τ → fv_term e [<=] dom Γ.
Proof.
intros Γ e τ H. induction H; simpl fv_term in *; repeat rewrite dom_app in *; simpl dom in *;
try solve [fsetdec].
Case "var". assert (x ∈ dom G) by eauto; fsetdec.
Case "app".
assert (dom G1 [<=] dom G) by eauto with fzip.
assert (dom G2 [=] dom G) by eauto with fzip.
fsetdec.
Case "lam". pick fresh x. 
assert (fv_term (e ^ x) [<=] add x (dom G)) by auto.
assert (fv_term e [<=] fv_term (e ^ x)) by auto with lngen.
fsetdec.
Case "pair".
assert (dom G1 [<=] dom G) by eauto with fzip.
assert (dom G2 [=] dom G) by eauto with fzip.
fsetdec.
Case "gen". pick fresh a. 
assert (fv_term (open_term_wrt_typ e (typ_var_f a)) [<=] add a (dom G)) by auto.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
fsetdec.
Case "exists". pick fresh a. 
assert (fv_term (open_term_wrt_typ e (typ_var_f a)) [<=] add a (dom G)) by auto.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
fsetdec.
Case "nu". pick fresh a. 
assert (fv_term (open_term_wrt_typ e (typ_var_f a)) [<=] add a (dom G)) by auto.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
fsetdec.
Case "sigma". pick fresh a.
assert (fv_term (open_term_wrt_typ e (typ_var_f a)) [<=] add a (dom (G2 ++ G1))) by auto.
repeat rewrite dom_app in H2.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
assert (fv_term e [<=] {{a}} ∪ dom G2 ∪ dom G1). clear Fr.
  simpl in H2. fsetdec.
clear H2 H3. 
assert (fv_term e [<=] dom G2 ∪ dom G1).
  assert (a ∉ fv_term e).
    replace (fv_term e) with
      (fv_term (term_sigma (typ_var_f b) t' e)) by reflexivity.
    apply wfterm_UEEq_not_fv with (Γ := G2 ++ b ~ E ++ G1) (τ := t); eauto.
clear Fr. fsetdec.
clear Fr. fsetdec.
Qed.

Lemma wfterm_ftv : forall Γ e τ,
  wfterm Γ e τ → ftv_term e [<=] dom Γ.
Proof.
intros Γ e τ H. induction H; simpl ftv_term in *; repeat rewrite dom_app in *; simpl dom in *;
try solve [fsetdec].
Case "app".
assert (dom G1 [<=] dom G) by eauto with fzip.
erewrite zip_dom2 in IHwfterm2; eauto.
fsetdec.
Case "abs". pick fresh x.
assert (ftv_typ t1 [<=] dom G). eapply wftyp_ftv; eauto with fzip.
assert (ftv_term e [<=] dom G). clear H2.
  assert (ftv_term (e ^ x)[<=] add x (dom G)) by auto.
  assert (ftv_term e [<=] ftv_term (e ^ x)) by auto with lngen.
  assert (x ∉ ftv_term (e ^ x)).
    apply wfterm_T_not_ftv with (Γ:= x~ T t1 ++ G) (τ:= t2) (τ':= t1); auto.
  clear Fr. simpl in H2. fsetdec.
clear Fr. fsetdec.
Case "pair".
assert (dom G1 [<=] dom G) by eauto with fzip.
erewrite zip_dom2 in IHwfterm2; eauto.
fsetdec.
Case "inst".
assert (ftv_typ t [<=] dom G) by auto with fzip.
fsetdec.
Case "gen". pick fresh a.
assert (ftv_term (open_term_wrt_typ e (typ_var_f a))[<=] add a (dom G)) by auto.
assert (ftv_term e [<=] ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
fsetdec.
Case "exists". pick fresh a.
assert (ftv_term (open_term_wrt_typ e (typ_var_f a))[<=] add a (dom G)) by auto.
assert (ftv_term e [<=] ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
fsetdec.
Case "nu". pick fresh a.
assert (ftv_term (open_term_wrt_typ e (typ_var_f a))[<=] add a (dom G)) by auto.
assert (ftv_term e [<=] ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
fsetdec.
Case "sigma". pick fresh a.
assert (ftv_typ t' [<=] dom (G2 ++ G1)).
  apply wftyp_ftv. eapply wfenv_wftyp_Eq3. eapply wfterm_wfenv. eauto.
assert (ftv_term e [<=] dom G2 ∪ dom G1).
  assert (ftv_term (open_term_wrt_typ e (typ_var_f a))[<=] add a (dom (G2 ++ G1))) by auto.
  assert (ftv_term e [<=] ftv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
  rewrite dom_app in H3.
  assert (a ∉ ftv_term e) by fsetdec.
  clear Fr. fsetdec.
rewrite dom_app in H2.
clear Fr. fsetdec.
Case "coerce".
assert (ftv_typ t [<=] dom G) by eauto with fzip.
fsetdec.
Qed.
Hint Resolve wfterm_fv wfterm_ftv: fzip.

Lemma wfterm_uniqueness_aux : forall Γ Γ' e τ τ',
  wfterm Γ e τ → wfterm Γ' e τ' →
  (forall x τ₀, binds x (T τ₀) Γ → binds x (T τ₀) Γ') →
  τ = τ'.
Proof.
intros Γ Γ' e τ τ' H H0 H1.
generalize dependent τ'. generalize dependent Γ'.
induction H; intros Γ' Hbinds τ' H2; inversion H2; subst; auto.
Case "var".
assert (T t = T τ'). eapply binds_unique with (E:=Γ'); eauto with lngen. congruence.
Case "app".
assert (typ_arrow t2 t1 = typ_arrow t3 τ') by eauto with fzip; congruence.
Case "abs". pick fresh x.
assert (t2 = t3).
  apply H1 with (Γ' := x ~ T t1 ++ Γ') (x := x); intros; auto.
  analyze_binds_uniq H3. eauto with lngen.
congruence.
Case "pair".
assert (t1 = t0) by eauto with fzip.
assert (t2 = t3) by eauto 6 with fzip.
congruence.
Case "projL".
assert (typ_prod t1 t2 = typ_prod τ' t3) by eauto with fzip; congruence.
Case "projR".
assert (typ_prod t1 t2 = typ_prod t3 τ') by eauto with fzip; congruence.
Case "inst".
assert (typ_forall t' = typ_forall t'0) by eauto with fzip; congruence.
Case "gen". pick fresh a.
assert (open_typ_wrt_typ t (typ_var_f a) = open_typ_wrt_typ t0 (typ_var_f a)).
  apply H1 with (Γ' := a ~ U ++ Γ') (a := a); intros; auto.
  analyze_binds_uniq H3. eauto with lngen.
f_equal; eapply open_typ_wrt_typ_inj; eauto.
Case "exists". pick fresh a.
assert (open_typ_wrt_typ t (typ_var_f a) = open_typ_wrt_typ t0 (typ_var_f a)).
  apply H0 with (Γ' := a ~ E ++ Γ') (a := a); intros; auto.
  analyze_binds_uniq H1. eauto with lngen.
f_equal; eapply open_typ_wrt_typ_inj; eauto.
Case "open".
assert (typ_exists t = typ_exists t0).
  apply IHwfterm with (Γ' := G3 ++ G0); intros; auto.
  assert (binds x (T τ₀) (G2 ++ b ~ E ++ G1)) by analyze_binds H1.
  apply Hbinds in H3. analyze_binds_uniq H3. eauto with lngen.
congruence.
Case "nu". pick fresh a.
apply H0 with (Γ' := a ~ E ++ Γ') (a := a); intros; auto.
analyze_binds H1.
Case "sigma". pick fresh a.
assert (tsubst_typ (typ_var_f a) b t = tsubst_typ (typ_var_f a) b τ').
  apply H1 with (Γ' := [(a, Eq t')] ++ G3 ++ G0) (a := a); intros; auto.
  assert (binds x (T τ₀) (G2 ++ b ~ E ++ G1)).
    analyze_binds_uniq H3. eauto with lngen.
  apply Hbinds in H4.
  analyze_binds_uniq H4. eauto with lngen.
assert (tsubst_typ (typ_var_f b) a (tsubst_typ (typ_var_f a) b t)
  = tsubst_typ (typ_var_f b) a (tsubst_typ (typ_var_f a) b τ'))
by congruence.
rewrite tsubst_typ_var_twice in H4; auto.
rewrite tsubst_typ_var_twice in H4; eauto with lngen fzip.
apply tsubst_typ_lc_typ_inv with (t1 := typ_var_f a) (a1 := b); auto.
eauto with lngen.
Qed.

Lemma wfterm_uniqueness : forall Γ e τ τ',
  wfterm Γ e τ → wfterm Γ e τ' → τ = τ'.
Proof.
intros; eauto using wfterm_uniqueness_aux.
Qed.

(*
Lemma wfterm_strengthening : forall Γ₁ Γ₂ x τ τ' e,
  x ∉ fv_term e →
  wfterm (Γ₁ ++ x ~ τ' ++ Γ₂) e τ →
  wfterm (Γ₁ ++ Γ₂) e τ.
Proof.
intros Γ₁ Γ₂ x τ τ' e Hx He.
dependent induction He; simpl in Hx.
Case "var".
constructor. solve_uniq. analyze_binds_uniq H0.
Case "app".
econstructor; eauto.
Case "abs".
apply wfterm_abs with (L := L `union` {{x}}); intros.
rewrite_env (([(x0, t1)] ++ Γ₁) ++ Γ₂).
eapply H0 with (x1 := x); auto.
assert (fv_term (e ^ x0) [<=] fv_term (term_var_f x0) ∪ fv_term e) as H2
 by auto with lngen.
simpl in H2; fsetdec.
simpl_env; eauto.
Qed.
*)


Lemma wfterm_T_not_E : forall Γ M τ x τ₁,
  wfterm Γ M τ →
  binds x (T τ₁) Γ →
  forall a, a ∈ ftv_typ τ₁ → not (binds a E Γ).
Proof.
intros Γ M τ x τ₁ H. induction H; intros; eauto.
Case "app". intro H4.
apply zip_binds_E3_inv with (Γ₁ := G1) (Γ₂ := G2) in H4; eauto with lngen.
destruct H4 as [[? ?] | [? ?]].
eapply IHwfterm1; eauto with fzip.
eapply IHwfterm2; eauto with fzip.
Case "pair". intro H4.
apply zip_binds_E3_inv with (Γ₁ := G1) (Γ₂ := G2) in H4; eauto with lngen.
destruct H4 as [[? ?] | [? ?]].
eapply IHwfterm1; eauto with fzip.
eapply IHwfterm2; eauto with fzip.
Case "exists". intro H4. pick fresh b.
eapply H0; eauto.
Case "open". intro H4. 
eapply IHwfterm; eauto. 
  analyze_binds H1.
  analyze_binds_uniq H4. eauto with lngen.
    assert (binds x (T τ₁) (G2 ++ G1)) by analyze_binds H1.
    assert (ftv_typ τ₁ [<=] dom (G2 ++ G1)). eapply wftyp_ftv.
    eapply wfenv_wftyp_T2; eauto. eapply wfterm_wfenv; eauto.
    assert (b ∈ dom (G2 ++ G1)) by auto.
    elimtype False. simpl_env in *. auto.
Case "nu". intro H3. pick fresh b.
eapply H0; eauto.
Case "sigma". intro H4. pick fresh c. 
eapply H1; eauto. 
  analyze_binds H2.
  analyze_binds_uniq H4. eauto with lngen.
    assert (binds x (T τ₁) (G2 ++ G1)) by analyze_binds H2.
    assert (ftv_typ τ₁ [<=] dom (c ~ Eq t' ++ G2 ++ G1)). eapply wftyp_ftv.
    eapply wfenv_wftyp_T2; eauto. eapply wfterm_wfenv; eauto.
    assert (b ∈ dom (c ~ Eq t' ++ G2 ++ G1)) by auto.
    assert (c ≠ b) by fsetdec. clear Fr.
    assert (b ∈ dom (G2 ++ G1)). simpl_env in *. fsetdec.
    contradiction.
Qed.

Lemma wfterm_Eq_not_E : forall Γ M τ a τ₁,
  wfterm Γ M τ →
  binds a (Eq τ₁) Γ →
  forall b, b ∈ ftv_typ τ₁ → not (binds b E Γ).
Proof.
intros Γ M τ a τ₁ H. induction H; intros; eauto.
Case "app". intro H4.
apply zip_binds_E3_inv with (Γ₁ := G1) (Γ₂ := G2) in H4; eauto with lngen.
destruct H4 as [[? ?] | [? ?]].
eapply IHwfterm1; eauto with fzip.
eapply IHwfterm2; eauto with fzip.
Case "pair". intro H4.
apply zip_binds_E3_inv with (Γ₁ := G1) (Γ₂ := G2) in H4; eauto with lngen.
destruct H4 as [[? ?] | [? ?]].
eapply IHwfterm1; eauto with fzip.
eapply IHwfterm2; eauto with fzip.
Case "exists". intro H4. pick fresh c.
eapply H0; eauto.
Case "open". intro H4. 
eapply IHwfterm; eauto. 
  analyze_binds H1.
  analyze_binds_uniq H4. eauto with lngen.
    assert (binds a (Eq τ₁) (G2 ++ G1)) by analyze_binds H1.
    assert (ftv_typ τ₁ [<=] dom (G2 ++ G1)). eapply wftyp_ftv.
    eapply wfenv_wftyp_Eq2; eauto. eapply wfterm_wfenv; eauto.
    assert (b ∈ dom (G2 ++ G1)) by auto.
    elimtype False. simpl_env in *. auto.
Case "nu". intro H3. pick fresh c.
eapply H0; eauto.
Case "sigma". intro H4. pick fresh c. 
eapply H1; eauto. 
  analyze_binds H2.
  analyze_binds_uniq H4. eauto with lngen.
    assert (binds a (Eq τ₁) (G2 ++ G1)) by analyze_binds H2.
    assert (ftv_typ τ₁ [<=] dom (c ~ Eq t' ++ G2 ++ G1)). eapply wftyp_ftv.
    eapply wfenv_wftyp_Eq2; eauto. eapply wfterm_wfenv; eauto.
    assert (b ∈ dom (c ~ Eq t' ++ G2 ++ G1)) by auto.
    assert (c ≠ b) by fsetdec. clear Fr.
    assert (b ∈ dom (G2 ++ G1)). simpl_env in *. fsetdec.
    contradiction.
Qed.

Lemma wfterm_upperU : forall Γ₁ a Γ₂ Γ₃ e τ,
  wfterm (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃) e τ →
  wfterm (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃) e τ.
Proof.
intros Γ₁ a Γ₂ Γ₃ e τ H. dependent induction H; eauto.
Case "var". constructor.
intros b Hb; eapply (H b); analyze_binds Hb.
auto using wfenv_upperU.
analyze_binds H1.
Case "app".
destruct (zip_app_U_inv G1 G2 Γ₁ a (Γ₂ ++ Γ₃)) as [? [? [? [? [? ?]]]]]; auto; subst.
assert (zip x0 x2 (Γ₂ ++ Γ₃)) as H2 by eauto using zip_remove_U2, zip_U.
apply zip_app_inv in H2. decompose record H2; clear H2; subst.
apply wfterm_app with
  (G1 := x ++ x3 ++ [(a, U)] ++ x4)
  (G2 := x1 ++ x5 ++ [(a, U)] ++ x6) (t2 := t2); auto using zip_upperU.
Case "abs". pick fresh x and apply wfterm_abs.
intros b Hb; eapply (H b); analyze_binds Hb.
rewrite_env (([(x, T t1)] ++ Γ₁) ++ Γ₂ ++ [(a, U)] ++ Γ₃).
apply H1; simpl_env; auto.
Case "pair".
destruct (zip_app_U_inv G1 G2 Γ₁ a (Γ₂ ++ Γ₃)) as [? [? [? [? [? ?]]]]]; auto; subst.
assert (zip x0 x2 (Γ₂ ++ Γ₃)) as H2 by eauto using zip_remove_U2, zip_U.
apply zip_app_inv in H2. decompose record H2; clear H2; subst.
apply wfterm_pair with
  (G1 := x ++ x3 ++ [(a, U)] ++ x4)
  (G2 := x1 ++ x5 ++ [(a, U)] ++ x6); auto using zip_upperU.
Case "inst". auto using wftyp_upperU.
Case "gen". pick fresh b and apply wfterm_gen.
intros b Hb; eapply (H b); analyze_binds Hb.
rewrite_env (([(b, U)] ++ Γ₁) ++ Γ₂ ++ [(a, U)] ++ Γ₃).
apply H1; simpl_env; auto.
Case "exists". pick fresh b and apply wfterm_exists.
rewrite_env (([(b, E)] ++ Γ₁) ++ Γ₂ ++ [(a, U)] ++ Γ₃).
apply H0; simpl_env; auto.
Case "open".
assert (uniq (G2 ++ G1)) by eauto with lngen.
assert (binds b E (Γ₁ ++ (a, U) :: Γ₂ ++ Γ₃)). rewrite <- H1; auto.
analyze_binds H3; apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
SCase "b binds in Γ₁".
apply uniq_app_inv in H1; auto. destruct H1; subst.
constructor. solve_uniq.
rewrite_env ((x ++ x0) ++ Γ₂ ++ [(a, U)] ++ Γ₃).
apply IHwfterm; simpl_env; auto.
SCase "b binds in Γ₂".
rewrite_env ((Γ₁ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0 ++ Γ₃) in H1.
apply uniq_app_inv in H1; auto. destruct H1; subst.
rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0 ++ [(a, U)] ++ Γ₃).
constructor. solve_uniq.
rewrite_env (Γ₁ ++ (x ++ x0) ++ [(a, U)] ++ Γ₃).
apply IHwfterm; simpl_env; auto.
SCase "b binds in Γ₃".
rewrite_env ((Γ₁ ++ [(a, U)] ++ Γ₂ ++ x) ++ [(b, E)] ++ x0) in H1.
apply uniq_app_inv in H1; auto. destruct H1; subst.
rewrite_env ((Γ₁ ++ Γ₂ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0).
constructor. solve_uniq.
simpl_env.
apply IHwfterm; simpl_env; auto.
Case "nu". pick fresh b and apply wfterm_nu.
rewrite_env (([(b, E)] ++ Γ₁) ++ Γ₂ ++ [(a, U)] ++ Γ₃).
apply H0; simpl_env; auto.
Case "sigma".
assert (uniq (G2 ++ G1)). pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
assert (binds b E (Γ₁ ++ (a, U) :: Γ₂ ++ Γ₃)). rewrite <- H2; auto.
analyze_binds H4; apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
SCase "b binds in Γ₁".
apply uniq_app_inv in H2; auto. destruct H2; subst.
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ x ++ x0) ++ Γ₂ ++ [(a, U)] ++ Γ₃).
apply H1; simpl_env; auto.
SCase "b binds in Γ₂".
rewrite_env ((Γ₁ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0 ++ Γ₃) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0 ++ [(a, U)] ++ Γ₃).
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ Γ₁) ++ (x ++ x0) ++ [(a, U)] ++ Γ₃).
apply H1; simpl_env; auto.
SCase "b binds in Γ₃".
rewrite_env ((Γ₁ ++ [(a, U)] ++ Γ₂ ++ x) ++ [(b, E)] ++ x0) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((Γ₁ ++ Γ₂ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0).
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ Γ₁) ++ Γ₂ ++ a ~ U ++ x ++ x0).
apply H1; simpl_env; auto.
Case "coerce".
apply wfterm_coerce with (t' := t'); auto using wftypeq_upperU.
Qed.

Lemma wfterm_upperE : forall Γ₁ a Γ₂ Γ₃ e τ,
  wfterm (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃) e τ →
  wfterm (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃) e τ.
Proof.
intros Γ₁ a Γ₂ Γ₃ e τ H. dependent induction H; eauto.
Case "var". elimtype False. eapply (H a); auto.
Case "app".
destruct (zip_app_inv G1 G2 Γ₁ (a ~ E ++ Γ₂ ++ Γ₃)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H5; subst.
SCase "EU".
apply zip_app_inv in H10. decompose record H10; clear H10; subst.
apply wfterm_app with
  (G1 := x ++ x0 ++ [(a, E)] ++ x2)
  (G2 := x1 ++ x3 ++ [(a, U)] ++ x4) (t2 := t2); auto using zip_upperEU, wfterm_upperU.
SCase "E".
apply zip_app_inv in H10. decompose record H10; clear H10; subst.
apply wfterm_app with
  (G1 := x ++ x2 ++ x3)
  (G2 := x1 ++ x4 ++ [(a, E)] ++ x5) (t2 := t2); auto using zip_upperE.
Case "abs". elimtype False. eapply (H a); auto.
Case "pair".
destruct (zip_app_inv G1 G2 Γ₁ (a ~ E ++ Γ₂ ++ Γ₃)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H5; subst.
SCase "EU".
apply zip_app_inv in H10. decompose record H10; clear H10; subst.
apply wfterm_pair with
  (G1 := x ++ x0 ++ [(a, E)] ++ x2)
  (G2 := x1 ++ x3 ++ [(a, U)] ++ x4); auto using zip_upperEU, wfterm_upperU.
SCase "E".
apply zip_app_inv in H10. decompose record H10; clear H10; subst.
apply wfterm_pair with
  (G1 := x ++ x2 ++ x3)
  (G2 := x1 ++ x4 ++ [(a, E)] ++ x5); auto using zip_upperE.
Case "inst". auto using wftyp_upperE.
Case "gen". elimtype False. eapply (H a); auto.
Case "exists". pick fresh b and apply wfterm_exists.
rewrite_env (([(b, E)] ++ Γ₁) ++ Γ₂ ++ [(a, E)] ++ Γ₃).
apply H0; simpl_env; auto.
Case "open".
assert (uniq (G2 ++ G1)) by eauto with lngen.
assert (binds b E (Γ₁ ++ (a, E) :: Γ₂ ++ Γ₃)). rewrite <- H1; auto.
analyze_binds H3.
SCase "b binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
apply uniq_app_inv in H1; auto. destruct H1; subst.
constructor. solve_uniq.
rewrite_env ((x ++ x0) ++ Γ₂ ++ [(a, E)] ++ Γ₃).
apply IHwfterm; simpl_env; auto.
SCase "b = a".
simpl_env in H1. apply uniq_app_inv in H1; auto. destruct H1; subst.
rewrite_env ((Γ₁ ++ Γ₂) ++ [(a, E)] ++ Γ₃).
constructor; simpl_env; auto.
SCase "b binds in Γ₂".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ [(a, E)] ++ x) ++ [(b, E)] ++ x0 ++ Γ₃) in H1.
apply uniq_app_inv in H1; auto. destruct H1; subst.
rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0 ++ [(a, E)] ++ Γ₃).
constructor. solve_uniq.
rewrite_env (Γ₁ ++ (x ++ x0) ++ [(a, E)] ++ Γ₃).
apply IHwfterm; simpl_env; auto.
SCase "b binds in Γ₃".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ [(a, E)] ++ Γ₂ ++ x) ++ [(b, E)] ++ x0) in H1.
apply uniq_app_inv in H1; auto. destruct H1; subst.
rewrite_env ((Γ₁ ++ Γ₂ ++ [(a, E)] ++ x) ++ [(b, E)] ++ x0).
constructor. solve_uniq.
simpl_env.
apply IHwfterm; simpl_env; auto.
Case "nu". pick fresh b and apply wfterm_nu.
rewrite_env (([(b, E)] ++ Γ₁) ++ Γ₂ ++ [(a, E)] ++ Γ₃).
apply H0; simpl_env; auto.
Case "sigma".
assert (uniq (G2 ++ G1)). pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
assert (binds b E (Γ₁ ++ (a, E) :: Γ₂ ++ Γ₃)). rewrite <- H2; auto.
analyze_binds H4.
SCase "b binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
apply uniq_app_inv in H2; auto. destruct H2; subst.
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ x ++ x0) ++ Γ₂ ++ [(a, E)] ++ Γ₃).
apply H1; simpl_env; auto.
SCase "a = b".
simpl_env in H2. apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((Γ₁ ++ Γ₂) ++ [(a, E)] ++ Γ₃).
pick fresh c and apply wfterm_sigma; simpl_env; auto.
SCase "b binds in Γ₂".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ [(a, E)] ++ x) ++ [(b, E)] ++ x0 ++ Γ₃) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0 ++ [(a, E)] ++ Γ₃).
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ Γ₁) ++ (x ++ x0) ++ [(a, E)] ++ Γ₃).
apply H1; simpl_env; auto.
SCase "b binds in Γ₃".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ [(a, E)] ++ Γ₂ ++ x) ++ [(b, E)] ++ x0) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((Γ₁ ++ Γ₂ ++ [(a, E)] ++ x) ++ [(b, E)] ++ x0).
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ Γ₁) ++ Γ₂ ++ a ~ E ++ x ++ x0).
apply H1; simpl_env; auto.
Case "coerce".
apply wfterm_coerce with (t' := t'); auto using wftypeq_upperE.
Qed.

Lemma wfterm_lowerU : forall Γ₁ a Γ₂ Γ₃ e τ,
  wfterm (Γ₁ ++ Γ₂ ++ a ~ U ++ Γ₃) e τ →
  a ∉ ftv_env Γ₂ →
  wfterm (Γ₁ ++ a ~ U ++ Γ₂ ++ Γ₃) e τ.
Proof.
intros Γ₁ a Γ₂ Γ₃ e τ H Ha. dependent induction H; eauto.
Case "var". constructor.
intros b Hb; eapply (H b); analyze_binds Hb.
auto using wfenv_lowerU.
analyze_binds H1.
Case "app".
destruct (zip_app_U_inv G1 G2 (Γ₁ ++ Γ₂) a Γ₃) as [? [? [? [? [? ?]]]]]; simpl_env; auto; subst.
rewrite_env ((Γ₁ ++ Γ₂) ++ [(a, U)] ++ Γ₃) in H.
assert (zip x x1 (Γ₁ ++ Γ₂)) as H2 by eauto using zip_remove_U1, zip_U.
assert (zip x0 x2 Γ₃) as H3 by eauto using zip_remove_U2, zip_U.
apply zip_app_inv in H2. decompose record H2; clear H2; subst.
apply wfterm_app with
  (G1 := x3 ++ [(a, U)] ++ x4 ++ x0)
  (G2 := x5 ++ [(a, U)] ++ x6 ++ x2) (t2 := t2).
apply zip_lowerU; simpl_env in *; auto.
apply IHwfterm1; simpl_env; auto.
erewrite zip_ftv_env1; eauto.
apply IHwfterm2; simpl_env; auto.
erewrite zip_ftv_env2; eauto.
Case "abs". pick fresh x and apply wfterm_abs.
intros b Hb; eapply (H b); analyze_binds Hb.
rewrite_env (([(x, T t1)] ++ Γ₁) ++ [(a, U)] ++ Γ₂ ++ Γ₃).
apply H1; simpl_env; auto.
Case "pair".
destruct (zip_app_U_inv G1 G2 (Γ₁ ++ Γ₂) a Γ₃) as [? [? [? [? [? ?]]]]]; simpl_env; auto; subst.
rewrite_env ((Γ₁ ++ Γ₂) ++ [(a, U)] ++ Γ₃) in H.
assert (zip x x1 (Γ₁ ++ Γ₂)) as H2 by eauto using zip_remove_U1, zip_U.
assert (zip x0 x2 Γ₃) as H3 by eauto using zip_remove_U2, zip_U.
apply zip_app_inv in H2. decompose record H2; clear H2; subst.
apply wfterm_pair with
  (G1 := x3 ++ [(a, U)] ++ x4 ++ x0)
  (G2 := x5 ++ [(a, U)] ++ x6 ++ x2).
apply zip_lowerU; simpl_env in *; auto.
apply IHwfterm1; simpl_env; auto.
erewrite zip_ftv_env1; eauto.
apply IHwfterm2; simpl_env; auto.
erewrite zip_ftv_env2; eauto.
Case "inst". auto using wftyp_lowerU.
Case "gen". pick fresh b and apply wfterm_gen.
intros b Hb; eapply (H b); analyze_binds Hb.
rewrite_env (([(b, U)] ++ Γ₁) ++ [(a, U)] ++ Γ₂ ++ Γ₃).
apply H1; simpl_env; auto.
Case "exists". pick fresh b and apply wfterm_exists.
rewrite_env (([(b, E)] ++ Γ₁) ++ [(a, U)] ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto.
Case "open".
assert (uniq (G2 ++ G1)) by eauto with lngen.
assert (binds b E (Γ₁ ++ Γ₂ ++ (a, U) :: Γ₃)). rewrite <- H1; auto.
analyze_binds H3.
SCase "b binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
apply uniq_app_inv in H1; auto. destruct H1; subst.
constructor. solve_uniq.
rewrite_env ((x ++ x0) ++ [(a, U)] ++ Γ₂ ++ Γ₃).
apply IHwfterm; simpl_env; auto.
SCase "b binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0 ++ [(a, U)] ++ Γ₃) in H1.
apply uniq_app_inv in H1; auto. destruct H1; subst.
rewrite_env ((Γ₁ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0 ++ Γ₃).
constructor. solve_uniq.
rewrite_env (Γ₁ ++ [(a, U)] ++ (x ++ x0) ++ Γ₃).
apply IHwfterm; simpl_env; auto. repeat rewrite ftv_env_app in *; auto.
SCase "b binds in Γ₃".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ Γ₂ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0) in H1.
apply uniq_app_inv in H1; auto. destruct H1; subst.
rewrite_env ((Γ₁ ++ [(a, U)] ++ Γ₂ ++ x) ++ [(b, E)] ++ x0).
constructor. solve_uniq.
simpl_env.
apply IHwfterm; simpl_env; auto.
Case "nu". pick fresh b and apply wfterm_nu.
rewrite_env (([(b, E)] ++ Γ₁) ++ [(a, U)] ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto.
Case "sigma".
assert (uniq (G2 ++ G1)). pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
assert (binds b E (Γ₁ ++ Γ₂ ++ (a, U) :: Γ₃)). rewrite <- H2; auto.
analyze_binds H4.
SCase "b binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
apply uniq_app_inv in H2; auto. destruct H2; subst.
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ x ++ x0) ++ [(a, U)] ++ Γ₂ ++ Γ₃).
apply H1; simpl_env; auto.
SCase "b binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0 ++ [(a, U)] ++ Γ₃) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((Γ₁ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0 ++ Γ₃).
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ Γ₁) ++ [(a, U)] ++ (x ++ x0) ++ Γ₃).
apply H1; simpl_env; auto.
rewrite ftv_env_app in *. auto.
SCase "b binds in Γ₃".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ Γ₂ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((Γ₁ ++ [(a, U)] ++ Γ₂ ++ x) ++ [(b, E)] ++ x0).
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ Γ₁) ++ a ~ U ++ Γ₂ ++ x ++ x0).
apply H1; simpl_env; auto.
Case "coerce".
apply wfterm_coerce with (t' := t'); auto using wftypeq_lowerU.
Qed.

Lemma wfterm_lowerE : forall Γ₁ a Γ₂ Γ₃ e τ,
  wfterm (Γ₁ ++ Γ₂ ++ a ~ E ++ Γ₃) e τ →
  a ∉ ftv_env Γ₂ →
  wfterm (Γ₁ ++ a ~ E ++ Γ₂ ++ Γ₃) e τ.
Proof.
intros Γ₁ a Γ₂ Γ₃ e τ H Ha. dependent induction H; eauto.
Case "var". elimtype False. eapply (H a); auto.
Case "app".
destruct (zip_app_inv G1 G2 (Γ₁ ++ Γ₂) (a ~ E ++ Γ₃)) as [? [? [? [? [? [? [? ?]]]]]]]; simpl_env; auto; subst.
inversion H5; subst.
SCase "EU".
apply zip_app_inv in H4. decompose record H4; clear H4; subst.
apply wfterm_app with
  (G1 := x0 ++ [(a, E)] ++ x2 ++ G1)
  (G2 := x3 ++ [(a, U)] ++ x4 ++ G2) (t2 := t2).
apply zip_lowerEU; simpl_env in H; auto.
apply IHwfterm1; simpl_env; auto. erewrite zip_ftv_env1; eauto.
apply wfterm_lowerU; simpl_env in *; auto. erewrite zip_ftv_env2; eauto.
SCase "E".
apply zip_app_inv in H4. decompose record H4; clear H4; subst.
apply wfterm_app with
  (G1 := x2 ++ x3 ++ x0)
  (G2 := x4 ++ [(a, E)] ++ x5 ++ G2) (t2 := t2).
apply zip_lowerE; simpl_env in H; auto.
simpl_env in *; auto.
apply IHwfterm2; simpl_env; auto. erewrite zip_ftv_env2; eauto.
Case "abs". elimtype False. eapply (H a); auto.
Case "pair".
destruct (zip_app_inv G1 G2 (Γ₁ ++ Γ₂) (a ~ E ++ Γ₃)) as [? [? [? [? [? [? [? ?]]]]]]]; simpl_env; auto; subst.
inversion H5; subst.
SCase "EU".
apply zip_app_inv in H4. decompose record H4; clear H4; subst.
apply wfterm_pair with
  (G1 := x0 ++ [(a, E)] ++ x2 ++ G1)
  (G2 := x3 ++ [(a, U)] ++ x4 ++ G2).
apply zip_lowerEU; simpl_env in H; auto.
apply IHwfterm1; simpl_env; auto. erewrite zip_ftv_env1; eauto.
apply wfterm_lowerU; simpl_env in *; auto. erewrite zip_ftv_env2; eauto.
SCase "E".
apply zip_app_inv in H4. decompose record H4; clear H4; subst.
apply wfterm_pair with
  (G1 := x2 ++ x3 ++ x0)
  (G2 := x4 ++ [(a, E)] ++ x5 ++ G2).
apply zip_lowerE; simpl_env in H; auto.
simpl_env in *; auto.
apply IHwfterm2; simpl_env; auto. erewrite zip_ftv_env2; eauto.
Case "inst". auto using wftyp_lowerE.
Case "gen". elimtype False. eapply (H a); auto.
Case "exists". pick fresh b and apply wfterm_exists.
rewrite_env (([(b, E)] ++ Γ₁) ++ [(a, E)] ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto.
Case "open".
assert (uniq (G2 ++ G1)) by eauto with lngen.
assert (binds b E (Γ₁ ++ Γ₂ ++ (a, E) :: Γ₃)). rewrite <- H1; auto.
analyze_binds H3.
SCase "b binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
apply uniq_app_inv in H1; auto. destruct H1; subst.
constructor. solve_uniq.
rewrite_env ((x ++ x0) ++ [(a, E)] ++ Γ₂ ++ Γ₃).
apply IHwfterm; simpl_env; auto.
SCase "b binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0 ++ [(a, E)] ++ Γ₃) in H1.
apply uniq_app_inv in H1; auto. destruct H1; subst.
rewrite_env ((Γ₁ ++ [(a, E)] ++ x) ++ [(b, E)] ++ x0 ++ Γ₃).
constructor. solve_uniq.
rewrite_env (Γ₁ ++ [(a, E)] ++ (x ++ x0) ++ Γ₃).
apply IHwfterm; simpl_env; auto.
rewrite ftv_env_app in *. auto.
SCase "b = a".
simpl_env in H1; rewrite_env ((Γ₁ ++ Γ₂) ++ a ~ E ++ Γ₃) in H1.
apply uniq_app_inv in H1; auto. destruct H1; subst.
constructor; simpl_env in *; auto.
SCase "b binds in Γ₃".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ Γ₂ ++ [(a, E)] ++ x) ++ [(b, E)] ++ x0) in H1.
apply uniq_app_inv in H1; auto. destruct H1; subst.
rewrite_env ((Γ₁ ++ [(a, E)] ++ Γ₂ ++ x) ++ [(b, E)] ++ x0).
constructor. solve_uniq.
simpl_env.
apply IHwfterm; simpl_env; auto.
Case "nu". pick fresh b and apply wfterm_nu.
rewrite_env (([(b, E)] ++ Γ₁) ++ [(a, E)] ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto.
Case "sigma".
assert (uniq (G2 ++ G1)). pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
assert (binds b E (Γ₁ ++ Γ₂ ++ (a, E) :: Γ₃)). rewrite <- H2; auto.
analyze_binds H4.
SCase "b binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
apply uniq_app_inv in H2; auto. destruct H2; subst.
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ x ++ x0) ++ [(a, E)] ++ Γ₂ ++ Γ₃).
apply H1; simpl_env; auto.
SCase "b binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0 ++ [(a, E)] ++ Γ₃) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((Γ₁ ++ [(a, E)] ++ x) ++ [(b, E)] ++ x0 ++ Γ₃).
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ Γ₁) ++ [(a, E)] ++ (x ++ x0) ++ Γ₃).
apply H1; simpl_env; auto.
rewrite ftv_env_app in *; auto.
SCase "a = b".
simpl_env in H2; rewrite_env ((Γ₁ ++ Γ₂) ++ [(a, E)] ++ Γ₃) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
pick fresh c and apply wfterm_sigma; simpl_env; auto.
rewrite_env ([(c, Eq t')] ++ (Γ₁ ++ Γ₂) ++ Γ₃). auto.
SCase "b binds in Γ₃".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ Γ₂ ++ [(a, E)] ++ x) ++ [(b, E)] ++ x0) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((Γ₁ ++ [(a, E)] ++ Γ₂ ++ x) ++ [(b, E)] ++ x0).
pick fresh c and apply wfterm_sigma. solve_uniq.
rewrite_env ((c ~ Eq t' ++ Γ₁) ++ a ~ E ++ Γ₂ ++ x ++ x0).
apply H1; simpl_env; auto.
Case "coerce".
apply wfterm_coerce with (t' := t'); auto using wftypeq_lowerE.
Qed.

Lemma wfterm_swap_Eq : forall Γ₁ Γ₂ a₁ a₂ τ₁ τ₂ e τ,
    wfterm (Γ₁ ++ a₁ ~ Eq τ₁ ++ a₂ ~ Eq τ₂ ++ Γ₂) e τ →
    wfterm (Γ₁ ++ a₂ ~ Eq τ₂ ++ a₁ ~ Eq (tsubst_typ τ₂ a₂ τ₁) ++ Γ₂) e τ.
Proof.
 intros Γ₁ Γ₂ a₁ a₂ τ₁ τ₂ e τ H. dependent induction H.
Case "var". analyze_binds H1; constructor; auto using wfenv_swap_Eq.
intros a Ha. eapply (H a). analyze_binds Ha.
intros a Ha. eapply (H a). analyze_binds Ha.
Case "app".
assert (zip G1 G2 (Γ₁ ++ [(a₁, Eq τ₁)] ++ [(a₂, Eq τ₂)] ++ Γ₂)) as Hinv by auto.
apply zip_app_inv in Hinv. decompose record Hinv; clear Hinv; subst.
inversion H6; subst. inversion H12; subst.
apply zip_swap_Eq in H. eauto.
Case "abs". pick fresh x and apply wfterm_abs.
intros a Ha; eapply (H a); analyze_binds Ha.
rewrite_env ((x ~ T t1 ++ Γ₁) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂). auto.
Case "pair".
assert (zip G1 G2 (Γ₁ ++ [(a₁, Eq τ₁)] ++ [(a₂, Eq τ₂)] ++ Γ₂)) as Hinv by auto.
apply zip_app_inv in Hinv. decompose record Hinv; clear Hinv; subst.
inversion H6; subst. inversion H12; subst.
apply zip_swap_Eq in H. eauto.
Case "fst". eauto.
Case "snd". eauto.
Case "inst". eauto using wftyp_swap_Eq.
Case "gen". pick fresh b and apply wfterm_gen.
intros a Ha; eapply (H a); analyze_binds Ha.
rewrite_env ((b ~ U ++ Γ₁) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂). auto.
Case "exists". pick fresh b and apply wfterm_exists.
rewrite_env ((b ~ E ++ Γ₁) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂). auto.
Case "open".
assert (binds b E (Γ₁ ++ (a₁, Eq τ₁) :: (a₂, Eq τ₂) :: Γ₂)).
  rewrite <- H1; auto.
analyze_binds H2;
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
SCase "b binds in Γ₁".
simpl_env in H1. apply uniq_app_inv in H1. destruct H1; subst.
simpl_env. constructor. auto.
rewrite_env ((x ++ x0) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂).
apply IHwfterm; simpl_env; auto.
assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
SCase "b binds in Γ₂".
simpl_env in H1.
rewrite_env ((Γ₁ ++ [(a₁, Eq τ₁)] ++ [(a₂, Eq τ₂)] ++ x)
  ++ [(b, E)] ++ x0) in H1.
apply uniq_app_inv in H1. destruct H1; subst.
rewrite_env ((Γ₁ ++ [(a₂, Eq τ₂)] ++ [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ x) ++
  [(b, E)] ++ x0).
constructor. auto.
simpl_env. apply IHwfterm; simpl_env; auto.
simpl_env in *. assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
Case "nu". pick fresh b and apply wfterm_nu.
rewrite_env ((b ~ E ++ Γ₁) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂). auto.
Case "sigma".
assert (binds b E (Γ₁ ++ (a₁, Eq τ₁) :: (a₂, Eq τ₂) :: Γ₂)).
  rewrite <- H2; auto.
analyze_binds H3;
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
SCase "b binds in Γ₁".
simpl_env in H2. apply uniq_app_inv in H2. destruct H2; subst.
simpl_env. pick fresh a and apply wfterm_sigma. auto.
rewrite_env ((a ~ Eq t' ++ x ++ x0) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ Γ₂).
apply H1; simpl_env; auto.
assert (uniq (G2 ++ G1)).
  pick fresh a. assert (uniq ( [(a, Eq t')] ++ G2 ++ G1)) by eauto with lngen.
  solve_uniq.
solve_uniq.
SCase "b binds in Γ₂".
simpl_env in H2.
rewrite_env ((Γ₁ ++ [(a₁, Eq τ₁)] ++ [(a₂, Eq τ₂)] ++ x)
  ++ [(b, E)] ++ x0) in H2.
apply uniq_app_inv in H2. destruct H2; subst.
rewrite_env ((Γ₁ ++ [(a₂, Eq τ₂)] ++ [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ x) ++
  [(b, E)] ++ x0).
pick fresh a and apply wfterm_sigma. auto.
rewrite_env (([(a, Eq t')] ++ Γ₁) ++ [(a₂, Eq τ₂)] ++
  [(a₁, Eq (tsubst_typ τ₂ a₂ τ₁))] ++ x ++ x0).
apply H1; simpl_env; auto.
assert (uniq (G2 ++ G1)).
  pick fresh a. assert (uniq ( [(a, Eq t')] ++ G2 ++ G1)) by eauto with lngen.
  solve_uniq.
solve_uniq.
Case "coerce". eauto using wftypeq_swap_Eq.
Qed.

(** Major lemmas about [wfterm] *)
Lemma wfterm_weakening : forall Γ₁ Γ₂ Γ₃ e τ,
  wfterm (Γ₁ ++ Γ₃) e τ →
  wfenv (Γ₂ ++ Γ₃) →
  disjoint Γ₁ Γ₂ →
  pure Γ₂ →
  (forall a, a ∈ ftv_env Γ₂ → ⌉(binds a E Γ₃)) →
  wfterm (Γ₁ ++ Γ₂ ++ Γ₃) e τ.
Proof.
intros Γ₁ Γ₂ Γ₃ e τ H H0 H1 H2 H3.
assert (forall a, a ∈ ftv_env (Γ₂ ++ Γ₃) → ⌉binds a E (Γ₂ ++ Γ₃)).
  intros. rewrite ftv_env_app in H4.
  assert (a ∈ ftv_env Γ₂ ∨ a ∈ ftv_env Γ₃) as [? | ?] by fsetdec; intro H6; analyze_binds H6.
    eapply (H2 a); auto.
    eapply (H3 a); auto.
    eapply (H2 a); auto.
    apply ftv_env_binds in H5. destruct H5 as [? [? [? [? | ?]]]].
      apply wfterm_T_not_E with (x := x) (a := a) (τ₁ := x0) in H; auto.
      apply wfterm_Eq_not_E with (b := a) (a := x) (τ₁ := x0) in H; auto.
assert (uniq (Γ₂ ++ Γ₃)) by eauto with lngen.
assert (lc_env (Γ₂ ++ Γ₃)) by eauto using wfenv_lc_env.
assert (uniq (Γ₁ ++ Γ₃)) by eauto with lngen.
assert (lc_env (Γ₁ ++ Γ₃)). apply wfenv_lc_env. eapply wfterm_wfenv; eauto.
generalize dependent Γ₂.
dependent induction H; intros; eauto.
Case "var".
constructor. eauto with fzip. auto with fzip. analyze_binds H1.
Case "app".
destruct (zip_app_inv G1 G2 Γ₁ Γ₃ H) as [G1' [G1'' [G2' [G2'' [? [? [? ?]]]]]]];
subst.
apply wfterm_app with (G1 := G1' ++ Γ₂ ++ G1'')
                      (G2 := G2' ++ Γ₂ ++ G2'')
                      (t2 := t2).
apply zip_app_weakening; my_auto; eauto with lngen.
apply IHwfterm1; eauto using zip_uniq1, zip_lc1.
  eapply wfenv_zip_inv1 with (Γ' := Γ₃); eauto.
  assert (uniq G1'). assert (uniq (G1' ++ G1'')) by eauto with lngen. solve_uniq.
  assert (uniq Γ₂) by solve_uniq. 
  assert (disjoint Γ₂ G1'). assert (dom G1' [<=] dom Γ₁) by eauto with fzip. solve_uniq. 
  solve_uniq.
  intros. intro. eapply (H6 a). rewrite ftv_env_app; auto. eauto with fzip.
  intros. intro. eapply (H6 a). rewrite ftv_env_app in *.
    rewrite (zip_ftv_env1 G1'') in H11; eauto.
    analyze_binds H12; eauto with fzip.
  assert (uniq G1''). assert (uniq (G1' ++ G1'')) by eauto with lngen. solve_uniq.
  assert (uniq Γ₂) by solve_uniq. 
  assert (disjoint Γ₂ G1''). assert (dom G1'' [<=] dom Γ₃) by eauto with fzip. assert (uniq (Γ₂ ++ Γ₃)) by eauto with lngen. solve_uniq.
  solve_uniq.
  eauto with lngen.
apply IHwfterm2; eauto using zip_uniq2, zip_lc2.
  eapply wfenv_zip_inv2 with (Γ' := Γ₃); eauto.
  assert (uniq G2'). assert (uniq (G2' ++ G2'')) by eauto with lngen. solve_uniq.
  assert (uniq Γ₂) by solve_uniq. 
  assert (disjoint Γ₂ G2'). assert (dom G2' [=] dom Γ₁) by eauto with fzip. solve_uniq. 
  solve_uniq.
  intros. intro. eapply (H6 a). rewrite ftv_env_app; auto. eauto with fzip.
  intros. intro. eapply (H6 a). rewrite ftv_env_app in *.
    rewrite (zip_ftv_env2 _ G2'') in H11 ; eauto.
    analyze_binds H12; eauto with fzip.
  assert (uniq G2''). assert (uniq (G2' ++ G2'')) by eauto with lngen. solve_uniq.
  assert (uniq Γ₂) by solve_uniq. 
  assert (disjoint Γ₂ G2''). assert (dom G2'' [=] dom Γ₃) by eauto with fzip. assert (uniq (Γ₂ ++ Γ₃)) by eauto with lngen. solve_uniq.
  solve_uniq.
  eauto with lngen.
Case "abs". pick fresh x and apply wfterm_abs.
eauto with fzip.
rewrite_env (([(x, T t1)] ++ Γ₁) ++ Γ₂ ++ Γ₃).
apply H1; simpl_env; auto. apply lc_env_app; auto. apply lc_env_T.
  apply wfenv_regular_T with (Γ := [(x, T t1)] ++ Γ₁ ++ Γ₃) (x := x); auto.
  eapply wfterm_wfenv; eauto.
Case "pair".
destruct (zip_app_inv G1 G2 Γ₁ Γ₃ H) as [G1' [G1'' [G2' [G2'' [? [? [? ?]]]]]]];
subst.
apply wfterm_pair with (G1 := G1' ++ Γ₂ ++ G1'')
                      (G2 := G2' ++ Γ₂ ++ G2'').
apply zip_app_weakening; my_auto; eauto with lngen.
apply IHwfterm1; eauto using zip_uniq1, zip_lc1.
  eapply wfenv_zip_inv1 with (Γ' := Γ₃); eauto.
  assert (uniq G1'). assert (uniq (G1' ++ G1'')) by eauto with lngen. solve_uniq.
  assert (uniq Γ₂) by solve_uniq. 
  assert (disjoint Γ₂ G1'). assert (dom G1' [<=] dom Γ₁) by eauto with fzip. solve_uniq. 
  solve_uniq.
  intros. intro. eapply (H6 a). rewrite ftv_env_app; auto. eauto with fzip.
  intros. intro. eapply (H6 a). rewrite ftv_env_app in *.
    rewrite (zip_ftv_env1 G1'') in H11; eauto.
    analyze_binds H12; eauto with fzip.
  assert (uniq G1''). assert (uniq (G1' ++ G1'')) by eauto with lngen. solve_uniq.
  assert (uniq Γ₂) by solve_uniq. 
  assert (disjoint Γ₂ G1''). assert (dom G1'' [<=] dom Γ₃) by eauto with fzip. assert (uniq (Γ₂ ++ Γ₃)) by eauto with lngen. solve_uniq.
  solve_uniq.
  eauto with lngen.
apply IHwfterm2; eauto using zip_uniq2, zip_lc2.
  eapply wfenv_zip_inv2 with (Γ' := Γ₃); eauto.
  assert (uniq G2'). assert (uniq (G2' ++ G2'')) by eauto with lngen. solve_uniq.
  assert (uniq Γ₂) by solve_uniq. 
  assert (disjoint Γ₂ G2'). assert (dom G2' [=] dom Γ₁) by eauto with fzip. solve_uniq. 
  solve_uniq.
  intros. intro. eapply (H6 a). rewrite ftv_env_app; auto. eauto with fzip.
  intros. intro. eapply (H6 a). rewrite ftv_env_app in *.
    rewrite (zip_ftv_env2 _ G2'') in H11 ; eauto.
    analyze_binds H12; eauto with fzip.
  assert (uniq G2''). assert (uniq (G2' ++ G2'')) by eauto with lngen. solve_uniq.
  assert (uniq Γ₂) by solve_uniq. 
  assert (disjoint Γ₂ G2''). assert (dom G2'' [=] dom Γ₃) by eauto with fzip. assert (uniq (Γ₂ ++ Γ₃)) by eauto with lngen. solve_uniq.
  solve_uniq.
  eauto with lngen.
Case "inst". constructor. auto using wftyp_weakening. eauto.
Case "gen". pick fresh a and apply wfterm_gen.
eauto with fzip.
rewrite_env (([(a, U)] ++ Γ₁) ++ Γ₂ ++ Γ₃).
apply H1; simpl_env; auto with lngen. 
Case "exists". pick fresh a and apply wfterm_exists.
rewrite_env (([(a, E)] ++ Γ₁) ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto with lngen.
Case "open".
assert (binds b E (Γ₁ ++ Γ₃)). rewrite <- H1; auto.
analyze_binds H11.
SCase "binds b E Γ₁". apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]].
subst. simpl_env in *. constructor.
simpl_env. solve_uniq.
rewrite_env ((x ++ x0) ++ Γ₂ ++ Γ₃). apply IHwfterm; simpl_env; my_auto.
eauto with lngen.
symmetry in H1. apply uniq_app_inv in H1.
  destruct H1; congruence. solve_uniq.
SCase "binds b E Γ₃". apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]].
subst. simpl_env in *.
symmetry in H1. rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0) in H1.
  apply uniq_app_inv in H1.
  destruct H1; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ Γ₂ ++ x) ++ [(b, E)] ++ G1). constructor; simpl_env.
solve_uniq.
apply IHwfterm; simpl_env; auto.
solve_uniq.
apply lc_env_app. eauto with lngen. eapply lc_env_app; eauto with lngen.
assert (b ∉ ftv_env (Γ₂ ++ x)).
rewrite ftv_env_app. intro. eapply (H6 b); auto. repeat rewrite ftv_env_app; fsetdec.
rewrite_env ((Γ₂ ++ x) ++ G1). replace (Γ₂ ++ x) with
  (env_map (tsubst_typ (typ_forall (typ_var_b 0)) b) (Γ₂ ++ x)).
apply wfenv_tsubst. apply wfenv_EU. simpl_env. auto.
eapply wftyp_forall with (L := dom G1). intros. unfold open_typ_wrt_typ; simpl.
simpl_env. constructor; auto. constructor; auto.
apply wfenv_strip with (Γ' := Γ₂ ++ x ++ [(b, E)]); simpl_env; auto.
apply tsubst_env_fresh_eq; auto.
intros. intro. eapply (H5 a); auto.
intros. intro. eapply (H6 a).
  repeat rewrite ftv_env_app in *. fsetdec.
  analyze_binds H11.
solve_uniq.
apply lc_env_app. eauto with lngen. apply lc_env_app; eauto with lngen.
simpl_env. solve_uniq.
Case "nu". pick fresh a and apply wfterm_nu.
rewrite_env (([(a, E)] ++ Γ₁) ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto with lngen.
Case "sigma".
assert (binds b E (Γ₁ ++ Γ₃)). rewrite <- H2; auto.
analyze_binds H12.
SCase "binds b E Γ₁". apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]].
subst. simpl_env in *. apply wfterm_sigma with (L := L ∪ dom x ∪ dom x0 ∪ dom Γ₂ ∪ dom Γ₃); intros.
simpl_env. solve_uniq.
rewrite_env ((a ~ Eq t' ++ x ++ x0) ++ Γ₂ ++ Γ₃). apply H1; simpl_env; auto.
solve_uniq.
apply lc_env_app. apply lc_env_Eq. apply wfenv_regular_Eq with (Γ := a ~ Eq t' ++ G2 ++ G1) (x := a); auto.
  eapply wfterm_wfenv; eauto.
  apply lc_env_app; eauto with lngen.
symmetry in H2. apply uniq_app_inv in H2.
  destruct H2; congruence. solve_uniq.
solve_uniq.
SCase "binds b E Γ₃". apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]].
subst. simpl_env in *.
symmetry in H2. rewrite_env ((Γ₁ ++ x) ++ [(b, E)] ++ x0) in H2.
  apply uniq_app_inv in H2.
  destruct H2; subst; simpl_env in *.
rewrite_env ((Γ₁ ++ Γ₂ ++ x) ++ [(b, E)] ++ G1).
apply wfterm_sigma with (L := L ∪ dom x ∪ dom G1 ∪ dom Γ₂ ∪ dom Γ₁); intros; simpl_env.
solve_uniq.
rewrite_env (([(a, Eq t')] ++ Γ₁) ++ Γ₂ ++ x ++ G1).
apply H1; simpl_env; auto.
solve_uniq.
apply lc_env_app.
assert (lc_typ t'). apply wfenv_regular_Eq with (Γ := [(a, Eq t')] ++ Γ₁ ++ x ++ G1) (x := a); auto. eapply wfterm_wfenv; eauto.
eauto with lngen. eapply lc_env_app. eauto with lngen. eapply lc_env_app; eauto with lngen.
assert (b ∉ ftv_env (Γ₂ ++ x)).
rewrite ftv_env_app. intro. eapply (H9 b); auto. repeat rewrite ftv_env_app; fsetdec.
rewrite_env ((Γ₂ ++ x) ++ G1). replace (Γ₂ ++ x) with
  (env_map (tsubst_typ (typ_forall (typ_var_b 0)) b) (Γ₂ ++ x)).
apply wfenv_tsubst. apply wfenv_EU. simpl_env. auto.
eapply wftyp_forall with (L := dom G1). intros. unfold open_typ_wrt_typ; simpl.
simpl_env. constructor; auto. constructor; auto.
apply wfenv_strip with (Γ' := Γ₂ ++ x ++ [(b, E)]); simpl_env; auto.
apply tsubst_env_fresh_eq; auto.
intros. intro. eapply (H6 a0); auto.
intros. intro. eapply (H9 a0).
  repeat rewrite ftv_env_app in *. fsetdec.
  analyze_binds H13.
solve_uniq.
apply lc_env_app. eauto with lngen. apply lc_env_app; eauto with lngen.
simpl_env. solve_uniq.
Case "coerce". apply wfterm_coerce with (t' := t').
auto using wftypeq_weakening. eauto.
Qed.

Lemma wfterm_weakenU : forall Γ Γ' e τ,
  wfterm Γ e τ → weakenU Γ' Γ → wfterm Γ' e τ.
Proof.
intros Γ Γ' e τ H H0. generalize dependent Γ'. induction H; intros; eauto using wftyp_weakenU, wftypeq_weakenU.
Case "var". constructor. eauto using pure_weakenU.
eauto using wfenv_weakenU. eauto with fzip.
Case "app". edestruct zip_weaken_inv as [? [? [? [? ?]]]]; eauto.
Case "abs". pick fresh x and apply wfterm_abs; auto.
eauto using pure_weakenU.
assert (lc_typ t1). eapply wftyp_regular. eapply wfenv_wftyp_T3.
eapply wfterm_wfenv. eauto.
auto.
Case "pair". edestruct zip_weaken_inv as [? [? [? [? ?]]]]; eauto.
Case "gen". pick fresh a and apply wfterm_gen; eauto using pure_weakenU.
Case "gen". pick fresh a and apply wfterm_exists; auto.
Case "open". (* needs weakenU_app_inv *)

ICI

Case "nu". pick fresh a and apply wfterm_nu; auto.


Lemma wfterm_subst : forall Γ₁ Γ₂ x τ₁ τ₂ e₁ e₂,
  wfterm (Γ₁ ++ x ~ T τ₂ ++ Γ₂) e₁ τ₁ →
  wfterm Γ₂ e₂ τ₂ → pure Γ₂ →
  wfterm (Γ₁ ++ Γ₂) (subst_term e₂ x e₁) τ₁.
Proof.
intros Γ₁ Γ₂ x τ₁ τ₂ e₁ e₂ H. dependent induction H; intros; simpl; eauto.
Case "var".
  destruct (x == x0); subst.
  SCase "x = x0".
    analyze_binds_uniq H1. eauto with lngen.
    apply wfterm_weakening with (Γ₁ := nil); auto.
    replace t with τ₂ by congruence; auto.
    eapply wfenv_subst; eauto.
    eauto with fzip.
  SCase "x <> x0".
  analyze_binds_uniq H1. eauto with lngen.
  constructor; eauto using pure_subst, wfenv_subst.
  constructor; eauto using pure_subst, wfenv_subst.
Case "app".
  destruct (zip_app_inv G1 G2 Γ₁ (x ~ T τ₂ ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; subst; auto.
  inversion H7; subst.
  apply wfterm_app with (G1 := x0 ++ G1) (G2 := x2 ++ G2) (t2 := t2).
  eapply zip_subst; eauto.
  eapply IHwfterm1. eauto.
    rewrite (zip_pure_inv1 G1 G2 Γ₂); auto. eapply pure_zip_inv1; eauto.
  eapply IHwfterm2. eauto.
    rewrite (zip_pure_inv2 G1 G2 Γ₂); auto. eapply pure_zip_inv2; eauto.
Case "abs".
  pick fresh z and apply wfterm_abs.
  eauto with fzip.
  rewrite_env ((z ~ T t1 ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_term_var; eauto with lngen.
  apply H1 with (τ₂0 := τ₂); simpl_env; auto.
Case "pair".
  destruct (zip_app_inv G1 G2 Γ₁ (x ~ T τ₂ ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; subst; auto.
  inversion H7; subst.
  apply wfterm_pair with (G1 := x0 ++ G1) (G2 := x2 ++ G2).
  eapply zip_subst; eauto.
  eapply IHwfterm1. eauto.
    rewrite (zip_pure_inv1 G1 G2 Γ₂); auto. eapply pure_zip_inv1; eauto.
  eapply IHwfterm2. eauto.
    rewrite (zip_pure_inv2 G1 G2 Γ₂); auto. eapply pure_zip_inv2; eauto.
Case "inst". constructor; eauto using wftyp_subst.
Case "gen".
  pick fresh a and apply wfterm_gen.
  eauto with fzip.
  rewrite_env ((a ~ U ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_typ_var; eauto with lngen.
  apply H1 with (τ₂0 := τ₂); simpl_env; auto.
Case "exists".
  pick fresh a and apply wfterm_exists.
  rewrite_env ((a ~ E ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_typ_var; eauto with lngen.
  apply H0 with (τ₂0 := τ₂); simpl_env; auto.
Case "open".
  assert (binds b E (Γ₁ ++ (x, T τ₂) :: Γ₂)). rewrite <- H1; auto.
  analyze_binds H4.
  SCase "b binds in Γ₁".
  apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
  simpl_env in *.
  symmetry in H1. apply uniq_app_inv in H1. destruct H1; subst.
  simpl_env in *.
  constructor. simpl_env; auto.
  rewrite_env ((G2 ++ x1) ++ Γ₂).
  eapply IHwfterm; simpl_env; eauto.
  rewrite H1. assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
  SCase "b binds in Γ₂".
  apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
  elimtype False. eapply (H3 b). auto.
Case "nu".
  pick fresh a and apply wfterm_nu.
  rewrite_env ((a ~ E ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_typ_var; eauto with lngen.
  apply H0 with (τ₂0 := τ₂); simpl_env; auto.
Case "sigma".
  assert (binds b E (Γ₁ ++ (x, T τ₂) :: Γ₂)). rewrite <- H2; auto.
  analyze_binds H5.
  SCase "b binds in Γ₁".
  apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
  simpl_env in *.
  symmetry in H2. apply uniq_app_inv in H2. destruct H2; subst.
  simpl_env in *.
  pick fresh a and apply wfterm_sigma. simpl_env; auto.
  rewrite subst_term_open_term_wrt_typ_var; eauto with lngen.
  rewrite_env ((a ~ Eq t' ++ G2 ++ x1) ++ Γ₂).
  eapply H1; simpl_env; eauto.
  rewrite H2. pick fresh a. assert (uniq (a ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
  SCase "b binds in Γ₂".
  apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
  elimtype False. eapply (H4 b). auto.
Qed.

Lemma wfterm_subst2 : forall Γ₁ Γ₂ Γ₃ Γ₄ x τ₁ τ₂ e₁ e₂,
  zip Γ₁ Γ₂ Γ₃ →
  wfterm Γ₁ e₁ τ₁ → pure Γ₁ →
  wfterm (Γ₄ ++ x ~ T τ₁ ++ Γ₂) e₂ τ₂ →
  wfterm (Γ₄ ++ Γ₃) (subst_term e₁ x e₂) τ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₄ x τ₁ τ₂ e₁ e₂ H H0 H1 H2.
dependent induction H2; simpl; eauto.
Case "var".
  assert (pure Γ₃). eapply pure_zip; eauto with fzip.
  assert (Γ₁ = Γ₃) by eauto using zip_pure_inv1.
  assert (Γ₂ = Γ₃) by eauto using zip_pure_inv2.
  subst.
  destruct (x == x0); subst.
  SCase "x = x0".
    analyze_binds_uniq H2. eauto with lngen.
    apply wfterm_weakening with (Γ₁ := nil); auto.
    replace t with τ₁ by congruence; auto.
    eapply wfenv_subst; eauto.
    eauto with fzip.
  SCase "x <> x0".
  analyze_binds_uniq H2. eauto with lngen.
  constructor; eauto using pure_subst, wfenv_subst.
  constructor; eauto using pure_subst, wfenv_subst.
Case "app".
  destruct (zip_app_inv G1 G2 Γ₄ (x ~ T τ₁ ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; subst; auto.
  inversion H6; subst.
  apply wfterm_app with (G1 := x0 ++ G1) (G2 := x2 ++ G2) (t2 := t2).
  eapply zip_subst; eauto. ICI
  eapply IHwfterm1. eauto.
    rewrite (zip_pure_inv1 G1 G2 Γ₂); auto. eapply pure_zip_inv1; eauto.
  eapply IHwfterm2. eauto.
    rewrite (zip_pure_inv2 G1 G2 Γ₂); auto. eapply pure_zip_inv2; eauto.
Case "abs".
  pick fresh z and apply wfterm_abs.
  eauto with fzip.
  rewrite_env ((z ~ T t1 ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_term_var; eauto with lngen.
  apply H1 with (τ₂0 := τ₂); simpl_env; auto.
Case "pair".
  destruct (zip_app_inv G1 G2 Γ₁ (x ~ T τ₂ ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; subst; auto.
  inversion H7; subst.
  apply wfterm_pair with (G1 := x0 ++ G1) (G2 := x2 ++ G2).
  eapply zip_subst; eauto.
  eapply IHwfterm1. eauto.
    rewrite (zip_pure_inv1 G1 G2 Γ₂); auto. eapply pure_zip_inv1; eauto.
  eapply IHwfterm2. eauto.
    rewrite (zip_pure_inv2 G1 G2 Γ₂); auto. eapply pure_zip_inv2; eauto.
Case "inst". constructor; eauto using wftyp_subst.
Case "gen".
  pick fresh a and apply wfterm_gen.
  eauto with fzip.
  rewrite_env ((a ~ U ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_typ_var; eauto with lngen.
  apply H1 with (τ₂0 := τ₂); simpl_env; auto.
Case "exists".
  pick fresh a and apply wfterm_exists.
  rewrite_env ((a ~ E ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_typ_var; eauto with lngen.
  apply H0 with (τ₂0 := τ₂); simpl_env; auto.
Case "open".
  assert (binds b E (Γ₁ ++ (x, T τ₂) :: Γ₂)). rewrite <- H1; auto.
  analyze_binds H4.
  SCase "b binds in Γ₁".
  apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
  simpl_env in *.
  symmetry in H1. apply uniq_app_inv in H1. destruct H1; subst.
  simpl_env in *.
  constructor. simpl_env; auto.
  rewrite_env ((G2 ++ x1) ++ Γ₂).
  eapply IHwfterm; simpl_env; eauto.
  rewrite H1. assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
  SCase "b binds in Γ₂".
  apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
  elimtype False. eapply (H3 b). auto.
Case "nu".
  pick fresh a and apply wfterm_nu.
  rewrite_env ((a ~ E ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_typ_var; eauto with lngen.
  apply H0 with (τ₂0 := τ₂); simpl_env; auto.
Case "sigma".
  assert (binds b E (Γ₁ ++ (x, T τ₂) :: Γ₂)). rewrite <- H2; auto.
  analyze_binds H5.
  SCase "b binds in Γ₁".
  apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
  simpl_env in *.
  symmetry in H2. apply uniq_app_inv in H2. destruct H2; subst.
  simpl_env in *.
  pick fresh a and apply wfterm_sigma. simpl_env; auto.
  rewrite subst_term_open_term_wrt_typ_var; eauto with lngen.
  rewrite_env ((a ~ Eq t' ++ G2 ++ x1) ++ Γ₂).
  eapply H1; simpl_env; eauto.
  rewrite H2. pick fresh a. assert (uniq (a ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
  SCase "b binds in Γ₂".
  apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
  elimtype False. eapply (H4 b). auto.
Qed.

Lemma wfterm_instantiate : forall Γ₁ Γ₂ a τ₁ e₁ τ₂,
  wfterm (Γ₁ ++ a ~ U ++ Γ₂) e₁ τ₁ →
  wftyp Γ₂ τ₂ →
  (forall a, a ∈ ftv_typ τ₂ → not (binds a E Γ₂)) →
  wfterm (Γ₁ ++ a ~ Eq τ₂ ++ Γ₂) e₁ τ₁.
Proof.
intros Γ₁ Γ₂ a τ₁ e₁ τ₂ H. dependent induction H; intros; eauto.
Case "var".
constructor.
apply pure_instantiate; eauto with lngen.
auto using wfenv_instantiate.
analyze_binds H1.
Case "app".
destruct (zip_app_inv G1 G2 Γ₁ (a ~ U ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H7; subst.
apply wfterm_app with (G1 := x ++ a ~ Eq τ₂ ++ G1) (G2 := x1 ++ a ~ Eq τ₂ ++ G2) (t2 := t2).
apply zip_instantiate; eauto with lngen.
apply IHwfterm1; auto.
  rewrite_env (nil ++ G1). eapply wftyp_zip_inv1; eauto.
  intros a0 H4 H5. simpl_env in *.
    assert (a0 ∈ ftv_env Γ₂ ∨ a0 ∈ ftv_typ τ₂) as [? | ?] by fsetdec.
      apply ftv_env_binds in H9. destruct H9 as [? [? [? [? | ?]]]].
      assert (wfterm (Γ₁ ++ [(a, U)] ++ Γ₂) (term_app e1 e2) t1) as HEx1 by eauto.
      assert (binds x0 (T x2) (Γ₁ ++ [(a, U)] ++ Γ₂)) as HEx2 by eauto.
      eapply (wfterm_T_not_E (Γ₁ ++ a ~ U ++ Γ₂) (term_app e1 e2) t1 x0 x2 _ _ a0); auto.
      Existential 1 := HEx1. Existential 1 := HEx2.
      assert (wfterm (Γ₁ ++ [(a, U)] ++ Γ₂) (term_app e1 e2) t1) as HEx1 by eauto.
      assert (binds x0 (Eq x2) (Γ₁ ++ [(a, U)] ++ Γ₂)) as HEx2 by auto.
      eapply (wfterm_Eq_not_E (Γ₁ ++ a ~ U ++ Γ₂) (term_app e1 e2) t1 x0 x2 _ _ a0); auto.
      Existential 1 := HEx1. Existential 1 := HEx2.
      eapply (H3 a0); auto.
  intros a0 H4 H5. eapply (H3 a0); eauto with fzip.
apply IHwfterm2; auto.
  rewrite_env (nil ++ G2). eapply wftyp_zip_inv2; eauto.
  intros a0 H4 H5. simpl_env in *.
    assert (a0 ∈ ftv_env Γ₂ ∨ a0 ∈ ftv_typ τ₂) as [? | ?] by fsetdec.
      apply ftv_env_binds in H9. destruct H9 as [? [? [? [? | ?]]]].
      assert (wfterm (Γ₁ ++ [(a, U)] ++ Γ₂) (term_app e1 e2) t1) as HEx1 by eauto.
      assert (binds x0 (T x2) (Γ₁ ++ [(a, U)] ++ Γ₂)) as HEx2 by eauto.
      eapply (wfterm_T_not_E (Γ₁ ++ a ~ U ++ Γ₂) (term_app e1 e2) t1 x0 x2 _ _ a0); auto.
      Existential 1 := HEx1. Existential 1 := HEx2.
      assert (wfterm (Γ₁ ++ [(a, U)] ++ Γ₂) (term_app e1 e2) t1) as HEx1 by eauto.
      assert (binds x0 (Eq x2) (Γ₁ ++ [(a, U)] ++ Γ₂)) as HEx2 by auto.
      eapply (wfterm_Eq_not_E (Γ₁ ++ a ~ U ++ Γ₂) (term_app e1 e2) t1 x0 x2 _ _ a0); auto.
      Existential 1 := HEx1. Existential 1 := HEx2.
      eapply (H3 a0); auto.
  intros a0 H4 H5. eapply (H3 a0); eauto with fzip.
Case "abs".
  pick fresh z and apply wfterm_abs.
  apply pure_instantiate; eauto with lngen.
  rewrite_env ((z ~ T t1 ++ Γ₁) ++ a ~ Eq τ₂ ++ Γ₂). auto.
Case "pair".
destruct (zip_app_inv G1 G2 Γ₁ (a ~ U ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H7; subst.
apply wfterm_pair with (G1 := x ++ a ~ Eq τ₂ ++ G1) (G2 := x1 ++ a ~ Eq τ₂ ++ G2).
apply zip_instantiate; eauto with lngen.
eapply IHwfterm1; auto.
  rewrite_env (nil ++ G1). eapply wftyp_zip_inv1; eauto.
  intros a0 H4 H5. simpl_env in *.
    assert (a0 ∈ ftv_env Γ₂ ∨ a0 ∈ ftv_typ τ₂) as [? | ?] by fsetdec.
      apply ftv_env_binds in H9. destruct H9 as [? [? [? [? | ?]]]].
      assert (wfterm (Γ₁ ++ [(a, U)] ++ Γ₂) (term_pair e1 e2) (typ_prod t1 t2)) as HEx1 by eauto.
      assert (binds x0 (T x2) (Γ₁ ++ [(a, U)] ++ Γ₂)) as HEx2 by auto.
      eapply (wfterm_T_not_E (Γ₁ ++ a ~ U ++ Γ₂) (term_pair e1 e2) (typ_prod t1 t2) x0 x2 _ _ a0); auto.
      Existential 1 := HEx1. Existential 1 := HEx2.
      assert (wfterm (Γ₁ ++ [(a, U)] ++ Γ₂) (term_pair e1 e2) (typ_prod t1 t2)) as HEx1 by eauto.
      assert (binds x0 (Eq x2) (Γ₁ ++ [(a, U)] ++ Γ₂)) as HEx2 by auto.
      eapply (wfterm_Eq_not_E (Γ₁ ++ a ~ U ++ Γ₂) (term_pair e1 e2) (typ_prod t1 t2) x0 x2 _ _ a0); auto.
      Existential 1 := HEx1. Existential 1 := HEx2.
      eapply (H3 a0); auto.
  intros a0 H4 H5. eapply (H3 a0); eauto with fzip.
eapply IHwfterm2; auto.
  rewrite_env (nil ++ G2). eapply wftyp_zip_inv2; eauto.
  intros a0 H4 H5. simpl_env in *.
    assert (a0 ∈ ftv_env Γ₂ ∨ a0 ∈ ftv_typ τ₂) as [? | ?] by fsetdec.
      apply ftv_env_binds in H9. destruct H9 as [? [? [? [? | ?]]]].
      assert (wfterm (Γ₁ ++ [(a, U)] ++ Γ₂) (term_pair e1 e2) (typ_prod t1 t2)) as HEx1 by eauto.
      assert (binds x0 (T x2) (Γ₁ ++ [(a, U)] ++ Γ₂)) as HEx2 by auto.
      eapply (wfterm_T_not_E (Γ₁ ++ a ~ U ++ Γ₂) (term_pair e1 e2) (typ_prod t1 t2) x0 x2 _ _ a0); auto.
      Existential 1 := HEx1. Existential 1 := HEx2.
      assert (wfterm (Γ₁ ++ [(a, U)] ++ Γ₂) (term_pair e1 e2) (typ_prod t1 t2)) as HEx1 by eauto.
      assert (binds x0 (Eq x2) (Γ₁ ++ [(a, U)] ++ Γ₂)) as HEx2 by auto.
      eapply (wfterm_Eq_not_E (Γ₁ ++ a ~ U ++ Γ₂) (term_pair e1 e2) (typ_prod t1 t2) x0 x2 _ _ a0); auto.
      Existential 1 := HEx1. Existential 1 := HEx2.
      eapply (H3 a0); auto.
  intros a0 H4 H5. eapply (H3 a0); eauto with fzip.
Case "inst".
  constructor; auto using wftyp_instantiate.
Case "gen".
  pick fresh b and apply wfterm_gen.
  apply pure_instantiate; eauto with lngen.
  rewrite_env ((b ~ U ++ Γ₁) ++ a ~ Eq τ₂ ++ Γ₂). auto.
Case "exists".
  pick fresh b and apply wfterm_exists.
  rewrite_env ((b ~ E ++ Γ₁) ++ a ~ Eq τ₂ ++ Γ₂). auto.
Case "open".
  assert (binds b E (Γ₁ ++ (a, U) :: Γ₂)). rewrite <- H1; auto.
  assert (uniq (G2 ++ G1)) by eauto with lngen.
  analyze_binds H4.
  SCase "b binds in Γ₁". apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
  simpl_env in *.
  apply uniq_app_inv in H1. destruct H1; subst.
  constructor.
    solve_uniq.
    rewrite_env ((x ++ x0) ++ [(a, Eq τ₂)] ++ Γ₂). apply IHwfterm; simpl_env; auto.
  solve_uniq.
  SCase "b binds in Γ₂". apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
  simpl_env in *.
  rewrite_env ((Γ₁ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0) in H1.
  apply uniq_app_inv in H1. destruct H1; subst.
  rewrite_env ((Γ₁ ++ [(a, Eq τ₂)] ++ x) ++ [(b, E)] ++ x0).
  constructor.
    solve_uniq.
    simpl_env. apply IHwfterm; simpl_env; auto.
    replace τ₂ with (tsubst_typ (typ_forall (typ_var_b 0)) b τ₂).
    replace x with (env_map (tsubst_typ (typ_forall (typ_var_b 0)) b) x).
    apply wftyp_tsubst. apply wftyp_EU; auto.
    apply wftyp_forall with (L := dom x0); intros. unfold open_typ_wrt_typ; simpl; simpl_env.
      constructor; auto. constructor; auto. apply wfenv_strip with (Γ' := x ++ [(b, E)]); simpl_env; eauto with fzip.
    apply tsubst_env_fresh_eq.
    assert (b ∉ ftv_env ((Γ₁ ++ [(a, U)] ++ x) ++ b ~ E ++ x0)). intro.
      apply ftv_env_binds in H1. destruct H1 as [? [? [? [? | ?]]]].
      eapply (wfterm_T_not_E ((Γ₁ ++ [(a, U)] ++ x) ++ b ~ E ++ x0)
             (term_open (typ_var_f b) e) (open_typ_wrt_typ t (typ_var_f b))
             x1 x2); auto. auto.
      eapply (wfterm_Eq_not_E ((Γ₁ ++ [(a, U)] ++ x) ++ b ~ E ++ x0)
             (term_open (typ_var_f b) e) (open_typ_wrt_typ t (typ_var_f b))
             x1 x2); auto. auto.
      repeat rewrite ftv_env_app in H1. auto.
      apply tsubst_typ_fresh_eq.
   intro. eapply (H3 b); auto.
   intros a0 H6 H7. eapply (H3 a0); auto.
  solve_uniq.
Case "nu".
  pick fresh b and apply wfterm_nu.
  rewrite_env ((b ~ E ++ Γ₁) ++ a ~ Eq τ₂ ++ Γ₂). auto.
Case "sigma".
  assert (binds b E (Γ₁ ++ (a, U) :: Γ₂)). rewrite <- H2; auto.
  pick fresh c.
  assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. clear Fr.
  analyze_binds H5.
  SCase "b binds in Γ₁". apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
  simpl_env in *.
  apply uniq_app_inv in H2. destruct H2; subst.
  apply wfterm_sigma with (L := L); intros.
    solve_uniq.
    rewrite_env ((a0 ~ Eq t' ++ x ++ x0) ++ [(a, Eq τ₂)] ++ Γ₂). apply H1; simpl_env; auto.
  solve_uniq.
  SCase "b binds in Γ₂". apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
  simpl_env in *.
  rewrite_env ((Γ₁ ++ [(a, U)] ++ x) ++ [(b, E)] ++ x0) in H2.
  apply uniq_app_inv in H2. destruct H2; subst.
  rewrite_env ((Γ₁ ++ [(a, Eq τ₂)] ++ x) ++ [(b, E)] ++ x0).
  apply wfterm_sigma with (L := L); intros.
    solve_uniq.
    rewrite_env (([(a0, Eq t')] ++ Γ₁) ++ [(a, Eq τ₂)] ++ x ++ x0).
    apply H1; simpl_env; auto.
    replace τ₂ with (tsubst_typ (typ_forall (typ_var_b 0)) b τ₂).
    replace x with (env_map (tsubst_typ (typ_forall (typ_var_b 0)) b) x).
    apply wftyp_tsubst. apply wftyp_EU; auto.
    apply wftyp_forall with (L := dom x0); intros. unfold open_typ_wrt_typ; simpl; simpl_env.
      constructor; auto. constructor; auto. apply wfenv_strip with (Γ' := x ++ [(b, E)]); simpl_env; eauto with fzip.
    apply tsubst_env_fresh_eq.
    assert (b ∉ ftv_env ((Γ₁ ++ [(a, U)] ++ x) ++ b ~ E ++ x0)). intro.
      apply ftv_env_binds in H5. destruct H5 as [? [? [? [? | ?]]]].
      eapply (wfterm_T_not_E ((Γ₁ ++ [(a, U)] ++ x) ++ b ~ E ++ x0)
             (term_sigma (typ_var_f b) t' e) t x1 x2); eauto.
      eapply (wfterm_Eq_not_E ((Γ₁ ++ [(a, U)] ++ x) ++ b ~ E ++ x0)
             (term_sigma (typ_var_f b) t' e) t x1 x2); eauto.
      repeat rewrite ftv_env_app in H5. auto.
      apply tsubst_typ_fresh_eq.
   intro. eapply (H4 b); auto.
   intros b0 H7 H8. eapply (H4 b0); auto.
  solve_uniq.
Case "coerce". eauto using wftypeq_instantiate.
Qed.

Lemma wfterm_subst_eq : forall Γ₁ Γ₂ a τ₁ e₁ τ₂,
  wfterm (Γ₁ ++ a ~ Eq τ₂ ++ Γ₂) e₁ τ₁ →
  wfterm (env_map (tsubst_typ τ₂ a) Γ₁ ++ Γ₂) (tsubst_term τ₂ a e₁) (tsubst_typ τ₂ a τ₁).
Proof.
intros Γ₁ Γ₂ a τ₁ e₁ τ₂ H.
assert (lc_typ τ₂) by eauto with lngen fzip.
dependent induction H; simpl; simpl_env; auto.
Case "var". constructor.
auto using pure_subst_eq.
auto using wfenv_subst_eq.
analyze_binds H1.
unfold env_map.
replace (T (tsubst_typ τ₂ a t)) with (tag_map (tsubst_typ τ₂ a) (T t)) by reflexivity.
auto.
rewrite tsubst_typ_fresh_eq; auto.
  assert (ftv_typ t [<=] dom Γ₂).
    apply wftyp_ftv. eapply wfenv_wftyp_T2; eauto. apply wfenv_strip with (Γ' := Γ₁ ++ [(a, Eq τ₂)]). simpl_env; auto.
  assert (uniq (Γ₁ ++ [(a, Eq τ₂)] ++ Γ₂)) by auto with lngen.
  destruct_uniq. fsetdec.
Case "app".
destruct (zip_app_Eq_inv G1 G2 Γ₁ a τ₂ Γ₂) as [? [? [? [? [? ?]]]]]; subst; auto.
apply wfterm_app with (G1 := env_map (tsubst_typ τ₂ a) x ++ x0) (G2 := env_map (tsubst_typ τ₂ a) x1 ++ x2) (t2 := tsubst_typ τ₂ a t2).
auto using zip_subst_eq.
apply IHwfterm1; auto.
apply IHwfterm2; auto.
Case "abs".
pick fresh x and apply wfterm_abs.
auto using pure_subst_eq.
rewrite tsubst_term_open_term_wrt_term_var.
rewrite_env (env_map (tsubst_typ τ₂ a) (x ~ T t1 ++ Γ₁) ++ Γ₂).
auto.
Case "pair".
destruct (zip_app_Eq_inv G1 G2 Γ₁ a τ₂ Γ₂) as [? [? [? [? [? ?]]]]]; subst; auto.
apply wfterm_pair with (G1 := env_map (tsubst_typ τ₂ a) x ++ x0) (G2 := env_map (tsubst_typ τ₂ a) x1 ++ x2).
auto using zip_subst_eq.
apply IHwfterm1; auto.
apply IHwfterm2; auto.
Case "fst". apply wfterm_fst with (t2 := tsubst_typ τ₂ a t2). apply IHwfterm; auto.
Case "snd". apply wfterm_snd with (t1 := tsubst_typ τ₂ a t1). apply IHwfterm; auto.
Case "inst".
rewrite tsubst_typ_open_typ_wrt_typ; auto.
apply wfterm_inst.
auto using wftyp_subst_eq.
apply IHwfterm; auto.
Case "gen".
pick fresh b and apply wfterm_gen.
auto using pure_subst_eq.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ τ₂ a) (b ~ U ++ Γ₁) ++ Γ₂).
auto.
Case "exists".
pick fresh b and apply wfterm_exists.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ τ₂ a) (b ~ E ++ Γ₁) ++ Γ₂).
auto.
Case "open".
assert (uniq (G2 ++ G1)) by eauto with lngen.
rewrite tsubst_typ_open_typ_wrt_typ; auto. simpl.
destruct (b == a); subst.
SCase "a = b (absurd)".
assert (E = Eq τ₂).
  eapply (binds_unique _ a  _ _ (Γ₁ ++ (a, Eq τ₂) :: Γ₂)); auto.
  rewrite <- H2; auto.
  rewrite <- H2. solve_uniq.
congruence.
SCase "a ≠ b".
assert (binds b E (Γ₁ ++ (a, Eq τ₂) :: Γ₂)). rewrite <- H2; auto.
analyze_binds H4.
SSCase "b binds in Γ₁".
apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
simpl_env in *.
apply uniq_app_inv in H2; auto. destruct H2; subst.
unfold env_map.
rewrite_env (env_map (tsubst_typ τ₂ a) x ++ b ~ E ++ env_map (tsubst_typ τ₂ a) x0 ++ Γ₂).
constructor.
unfold env_map. simpl_env in *. auto.
rewrite_env ((env_map (tsubst_typ τ₂ a) x ++ env_map (tsubst_typ τ₂ a) x0) ++ Γ₂).
replace (env_map (tsubst_typ τ₂ a) x ++ env_map (tsubst_typ τ₂ a) x0) with (env_map (tsubst_typ τ₂ a) (x ++ x0)).
apply IHwfterm; simpl_env; auto.
unfold env_map; simpl_env; auto.
SSCase "b binds in Γ₂".
apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in *.
rewrite_env ((Γ₁ ++ [(a, Eq τ₂)] ++ x) ++ [(b, E)] ++ x0) in H2.
apply uniq_app_inv in H2; auto. destruct H2; subst.
rewrite_env ((env_map (tsubst_typ τ₂ a) Γ₁ ++ x) ++ b ~ E ++ x0).
constructor.
unfold env_map. simpl_env in *. auto.
simpl_env.
apply IHwfterm; simpl_env; auto.
Case "nu".
pick fresh b and apply wfterm_nu.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ τ₂ a) (b ~ E ++ Γ₁) ++ Γ₂).
auto.
Case "sigma".
pick fresh c.
assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. clear Fr.
destruct (b == a); subst.
SCase "a = b (absurd)".
assert (E = Eq τ₂).
  eapply (binds_unique _ a  _ _ (Γ₁ ++ (a, Eq τ₂) :: Γ₂)); auto.
  rewrite <- H3; auto.
  rewrite <- H3. solve_uniq.
congruence.
SCase "a ≠ b".
assert (binds b E (Γ₁ ++ (a, Eq τ₂) :: Γ₂)). rewrite <- H3; auto.
analyze_binds H5.
SSCase "b binds in Γ₁".
apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
simpl_env in *.
apply uniq_app_inv in H3; auto. destruct H3; subst.
unfold env_map.
rewrite_env (env_map (tsubst_typ τ₂ a) x ++ b ~ E ++ env_map (tsubst_typ τ₂ a) x0 ++ Γ₂).
apply wfterm_sigma with (L := L ∪ {{a}}); intros.
unfold env_map. simpl_env in *. auto.
replace (typ_var_f a0) with (tsubst_typ τ₂ a (typ_var_f a0)).
rewrite <- tsubst_typ_tsubst_typ; auto.
rewrite <- tsubst_term_open_term_wrt_typ; auto.
rewrite_env ((env_map (tsubst_typ τ₂ a) (a0 ~ Eq t' ++ x) ++ env_map (tsubst_typ τ₂ a) x0) ++ Γ₂).
replace (env_map (tsubst_typ τ₂ a) (a0 ~ Eq t' ++ x) ++ env_map (tsubst_typ τ₂ a) x0) with (env_map (tsubst_typ τ₂ a) (a0 ~ Eq t' ++ x ++ x0)).
apply H1; simpl_env; auto.
unfold env_map; simpl_env; auto.
assert (ftv_typ τ₂ [<=] dom Γ₂). apply wftyp_ftv.
  apply wfenv_wftyp_Eq with (x := a) (Γ₁ := [(a0, Eq t')] ++ x ++ x0).
  simpl_env. eapply wfterm_wfenv. eauto.
  simpl_env in *. solve_notin.
simpl. unfold typvar. destruct (a0 == a); subst; auto. elimtype False; fsetdec.
solve_uniq.
SSCase "b binds in Γ₂".
apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in *.
rewrite_env ((Γ₁ ++ [(a, Eq τ₂)] ++ x) ++ [(b, E)] ++ x0) in H3.
apply uniq_app_inv in H3; auto. destruct H3; subst.
rewrite_env ((env_map (tsubst_typ τ₂ a) Γ₁ ++ x) ++ b ~ E ++ x0).
apply wfterm_sigma with (L := L ∪ {{a}}); intros.
unfold env_map. simpl_env in *. auto.
replace (typ_var_f a0) with (tsubst_typ τ₂ a (typ_var_f a0)).
rewrite <- tsubst_typ_tsubst_typ; auto.
rewrite <- tsubst_term_open_term_wrt_typ; auto.
rewrite_env (env_map (tsubst_typ τ₂ a) (a0 ~ Eq t' ++ Γ₁) ++ x ++ x0).
apply H1; simpl_env; auto.
assert (ftv_typ τ₂ [<=] dom (x ++ x0)). apply wftyp_ftv.
  apply wfenv_wftyp_Eq with (x := a) (Γ₁ := [(a0, Eq t')] ++ Γ₁).
  rewrite_env ([(a0, Eq t')] ++ (Γ₁ ++ [(a, Eq τ₂)] ++ x) ++ x0).
  eapply wfterm_wfenv. eauto.
  simpl_env in *. fsetdec.
simpl. unfold typvar. destruct (a0 == a); subst; auto. elimtype False; fsetdec.
solve_uniq.
Case "coerce".
apply wfterm_coerce with (t' := tsubst_typ τ₂ a t'); auto using wftypeq_subst_eq.
Qed.

Lemma wfterm_tsubst : forall Γ₁ Γ₂ a τ₁ e₁ τ₂,
  wfterm (Γ₁ ++ a ~ U ++ Γ₂) e₁ τ₁ →
  wftyp Γ₂ τ₂ →
  (forall a, a ∈ ftv_typ τ₂ → not (binds a E Γ₂)) →
  wfterm (env_map (tsubst_typ τ₂ a) Γ₁ ++ Γ₂) (tsubst_term τ₂ a e₁) (tsubst_typ τ₂ a τ₁).
Proof.
intros. auto using wfterm_subst_eq, wfterm_instantiate.
Qed.

Lemma wfterm_renameU : forall Γ₁ Γ₂ a b e τ,
  wfterm (Γ₁ ++ a ~ U ++ Γ₂) e τ →
  b ∉ dom (Γ₁ ++ Γ₂) →
  wfterm (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ U ++ Γ₂)
  (tsubst_term (typ_var_f b) a e) (tsubst_typ (typ_var_f b) a τ).
Proof.
intros Γ₁ Γ₂ a b e τ H H0. dependent induction H; simpl; simpl_env.
Case "var".
constructor.
apply pure_app. eauto with fzip.
  rewrite_env (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ nil).
  apply pure_tsubst; simpl_env; eauto with fzip.
auto using wfenv_renameU.
analyze_binds H1.
replace (T (tsubst_typ (typ_var_f b) a t)) with (tag_map (tsubst_typ (typ_var_f b) a) (T t)) by reflexivity.
  unfold env_map; auto.
rewrite tsubst_typ_fresh_eq; auto.
assert (ftv_typ t [<=] dom Γ₂). apply wftyp_ftv.
apply wfenv_wftyp_T2 with (x := x); auto.
apply wfenv_strip with (Γ' := Γ₁ ++ [(a, U)]). simpl_env; auto.
apply wfenv_uniq in H0. solve_uniq.
Case "app".
assert (uniq G1) by eauto with lngen.
assert (uniq G2) by eauto with lngen.
assert (uniq (Γ₁ ++ [(a, U)] ++ Γ₂)) by eauto with lngen.
destruct (zip_app_inv G1 G2 Γ₁ ([(a, U)] ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H9; subst.
simpl_env in *.
assert (dom x [<=] dom Γ₁) by eauto with fzip.
assert (dom x1 [=] dom Γ₁) by eauto with fzip.
assert (dom G1 [<=] dom Γ₂) by eauto with fzip.
assert (dom G2 [=] dom Γ₂) by eauto with fzip.
apply wfterm_app with
  (G1 := env_map (tsubst_typ (typ_var_f b) a) x ++ [(b, U)] ++ G1)
  (G2 := env_map (tsubst_typ (typ_var_f b) a) x1 ++ [(b, U)] ++ G2)
  (t2 := tsubst_typ (typ_var_f b) a t2).
apply zip_renameU; auto. simpl_env. fsetdec.
apply IHwfterm1; auto. simpl_env; fsetdec.
apply IHwfterm2; auto. simpl_env; fsetdec.
Case "abs".
pick fresh x and apply wfterm_abs. auto using pure_renameU.
rewrite tsubst_term_open_term_wrt_term_var.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (x ~ T t1 ++ Γ₁) ++ [(b, U)] ++ Γ₂).
auto.
Case "pair".
assert (uniq G1) by eauto with lngen.
assert (uniq G2) by eauto with lngen.
assert (uniq (Γ₁ ++ [(a, U)] ++ Γ₂)) by eauto with lngen.
destruct (zip_app_inv G1 G2 Γ₁ ([(a, U)] ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H9; subst.
simpl_env in *.
assert (dom x [<=] dom Γ₁) by eauto with fzip.
assert (dom x1 [=] dom Γ₁) by eauto with fzip.
assert (dom G1 [<=] dom Γ₂) by eauto with fzip.
assert (dom G2 [=] dom Γ₂) by eauto with fzip.
apply wfterm_pair with
  (G1 := env_map (tsubst_typ (typ_var_f b) a) x ++ [(b, U)] ++ G1)
  (G2 := env_map (tsubst_typ (typ_var_f b) a) x1 ++ [(b, U)] ++ G2).
apply zip_renameU; auto. simpl_env. fsetdec.
apply IHwfterm1; auto. simpl_env; fsetdec.
apply IHwfterm2; auto. simpl_env; fsetdec.
Case "fst".
apply wfterm_fst with (t2 := tsubst_typ (typ_var_f b) a t2).
apply IHwfterm; auto.
Case "snd".
apply wfterm_snd with (t1 := tsubst_typ (typ_var_f b) a t1).
apply IHwfterm; auto.
Case "inst".
rewrite tsubst_typ_open_typ_wrt_typ; auto.
apply wfterm_inst.
auto using wftyp_renameU.
apply IHwfterm; auto.
Case "gen".
pick fresh c and apply wfterm_gen. auto using pure_renameU.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, U)] ++ Γ₂).
auto.
Case "exists".
pick fresh c and apply wfterm_exists.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ E ++ Γ₁) ++ [(b, U)] ++ Γ₂).
auto.
Case "open".
destruct (b0 == a); subst.
SCase "b0 = a (absurd)".
assert (@E typ = U). apply binds_unique with (x := a) (E := Γ₁ ++ (a, U) :: Γ₂); auto.
  rewrite <- H2; auto.
  assert (uniq (G2 ++ G1)) by eauto with lngen.
  rewrite <- H2. solve_uniq.
congruence.
SCase "b0 ≠ a".
assert (binds b0 E (Γ₁ ++ (a, U) :: Γ₂)). rewrite <- H2; auto.
analyze_binds H3.
SSCase "b0 binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
simpl_env in H2.
apply uniq_app_inv in H2. destruct H2; subst.
repeat rewrite env_map_app.
unfold env_map at 2; simpl; simpl_env.
rewrite <- tsubst_typ_open_typ_wrt_typ_var; auto.
apply wfterm_open.
unfold env_map; auto.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) x ++
   env_map (tsubst_typ (typ_var_f b) a) x0) ++ [(b, U)] ++ Γ₂).
rewrite <- env_map_app.
apply IHwfterm; simpl_env; auto.
assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
SSCase "b0 binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in H2.
rewrite_env ((Γ₁ ++ [(a, U)] ++ x) ++ [(b0, E)] ++ x0) in H2.
apply uniq_app_inv in H2. destruct H2; subst.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++
   [(b, U)] ++ x) ++ [(b0, E)] ++ x0).
rewrite <- tsubst_typ_open_typ_wrt_typ_var; auto.
apply wfterm_open.
unfold env_map; auto.
simpl_env.
apply IHwfterm; simpl_env; auto.
assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
Case "nu".
pick fresh c and apply wfterm_nu.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ E ++ Γ₁) ++ [(b, U)] ++ Γ₂).
auto.
Case "sigma".
destruct (b0 == a); subst.
SCase "b0 = a (absurd)".
assert (@E typ = U). apply binds_unique with (x := a) (E := Γ₁ ++ (a, U) :: Γ₂); auto.
  rewrite <- H3; auto.
  pick fresh c.
  assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen.
  rewrite <- H3. solve_uniq.
congruence.
SCase "b0 ≠ a".
assert (binds b0 E (Γ₁ ++ (a, U) :: Γ₂)). rewrite <- H3; auto.
analyze_binds H4.
SSCase "b0 binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
simpl_env in H3.
apply uniq_app_inv in H3. destruct H3; subst.
repeat rewrite env_map_app.
unfold env_map at 2; simpl; simpl_env.
pick fresh c and apply wfterm_sigma.
unfold env_map; auto.
rewrite tsubst_typ_tsubst_typ; auto.
simpl. unfold typvar; destruct (b == b0); subst; simpl_env.
SSSCase "b = b0". elimtype False. simpl_env in *. auto.
SSSCase "b ≠ b0".
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) (c ~ Eq t' ++ x) ++
   env_map (tsubst_typ (typ_var_f b) a) x0) ++ [(b, U)] ++ Γ₂).
rewrite <- env_map_app.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
apply H1; simpl_env; auto.
pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
SSCase "b0 binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in H3.
rewrite_env ((Γ₁ ++ [(a, U)] ++ x) ++ [(b0, E)] ++ x0) in H3.
apply uniq_app_inv in H3. destruct H3; subst.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++
   [(b, U)] ++ x) ++ [(b0, E)] ++ x0).
pick fresh c and apply wfterm_sigma.
unfold env_map; auto.
rewrite tsubst_typ_tsubst_typ; auto.
simpl. unfold typvar; destruct (b == b0); subst; simpl_env.
SSSCase "b = b0". elimtype False. simpl_env in *. clear Fr. fsetdec.
SSSCase "b ≠ b0".
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ Eq t' ++ Γ₁) ++ [(b, U)] ++ x ++ x0).
apply H1; simpl_env; auto.
pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
Case "coerce".
apply wfterm_coerce with (t' := tsubst_typ (typ_var_f b) a t').
auto using wftypeq_renameU.
auto.
Qed.

Lemma wfterm_renameE : forall Γ₁ Γ₂ a b e τ,
  wfterm (Γ₁ ++ a ~ E ++ Γ₂) e τ →
  b ∉ dom (Γ₁ ++ Γ₂) →
  wfterm (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ E ++ Γ₂)
  (tsubst_term (typ_var_f b) a e) (tsubst_typ (typ_var_f b) a τ).
Proof.
intros Γ₁ Γ₂ a b e τ H H0. dependent induction H; simpl; simpl_env.
Case "var". elimtype False. eapply (H a); auto.
Case "app".
assert (uniq G1) by eauto with lngen.
assert (uniq G2) by eauto with lngen.
assert (uniq (Γ₁ ++ [(a, E)] ++ Γ₂)) by eauto with lngen.
destruct (zip_app_inv G1 G2 Γ₁ (a ~ E ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
assert (dom x [<=] dom Γ₁) by eauto with fzip.
assert (dom x1 [=] dom Γ₁) by eauto with fzip.
assert (dom x0 [<=] dom (a ~ E ++ Γ₂)) by eauto with fzip.
assert (dom x2 [=] dom (a ~ E ++ Γ₂)) by eauto with fzip.
inversion H9; subst.
SCase "EU".
apply wfterm_app with
  (G1 := env_map (tsubst_typ (typ_var_f b) a) x ++ b ~ E ++ G1)
  (G2 := env_map (tsubst_typ (typ_var_f b) a) x1 ++ b ~ U ++ G2)
  (t2 := tsubst_typ (typ_var_f b) a t2).
simpl_env in *.
apply zip_renameEU; auto. simpl_env; fsetdec.
apply IHwfterm1; auto. simpl_env in *; fsetdec.
apply wfterm_renameU; auto. simpl_env in *; fsetdec.
SCase "E".
apply wfterm_app with
  (G1 := env_map (tsubst_typ (typ_var_f b) a) x ++ x0)
  (G2 := env_map (tsubst_typ (typ_var_f b) a) x1 ++ b ~ E ++ G2)
  (t2 := tsubst_typ (typ_var_f b) a t2).
apply zip_renameE; auto. simpl_env in *; fsetdec.
replace (typ_arrow (tsubst_typ (typ_var_f b) a t2) (tsubst_typ (typ_var_f b) a t1))
with (tsubst_typ (typ_var_f b) a (typ_arrow t2 t1)) by reflexivity.
assert (a ∉ dom (x ++ x0)). simpl_env; destruct_uniq; fsetdec.
rewrite tsubst_term_fresh_eq.
rewrite tsubst_typ_fresh_eq.
rewrite tsubst_env_fresh_eq.
auto.
intro H13. destruct (ftv_env_binds x a H13) as [? [? [? ?]]].
  assert (ftv_typ x3 [<=] dom (x ++ x0)). apply wftyp_ftv.
  destruct H16.
    apply wfenv_wftyp_T2 with (x := x2). eapply wfterm_wfenv; eauto. auto.
    apply wfenv_wftyp_Eq2 with (x := x2). eapply wfterm_wfenv; eauto. auto.
  assert (a ∈ dom (x ++ x0)) by auto. contradiction.
intro H13. apply H12. assert (ftv_typ (typ_arrow t2 t1) [<=] dom (x ++ x0)).
  apply wftyp_ftv. eapply wfterm_wftyp; eauto.
  auto.
intro H13. apply H12. assert (ftv_term e1 [<=] dom (x ++ x0)).
  eapply wfterm_ftv; eauto.
  auto.
apply IHwfterm2; auto. simpl_env in *; fsetdec.
Case "abs". elimtype False. eapply (H a); auto.
Case "pair".
assert (uniq G1) by eauto with lngen.
assert (uniq G2) by eauto with lngen.
assert (uniq (Γ₁ ++ [(a, E)] ++ Γ₂)) by eauto with lngen.
destruct (zip_app_inv G1 G2 Γ₁ (a ~ E ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
assert (dom x [<=] dom Γ₁) by eauto with fzip.
assert (dom x1 [=] dom Γ₁) by eauto with fzip.
assert (dom x0 [<=] dom (a ~ E ++ Γ₂)) by eauto with fzip.
assert (dom x2 [=] dom (a ~ E ++ Γ₂)) by eauto with fzip.
inversion H9; subst.
SCase "EU".
apply wfterm_pair with
  (G1 := env_map (tsubst_typ (typ_var_f b) a) x ++ b ~ E ++ G1)
  (G2 := env_map (tsubst_typ (typ_var_f b) a) x1 ++ b ~ U ++ G2).
simpl_env in *.
apply zip_renameEU; auto. simpl_env; fsetdec.
apply IHwfterm1; auto. simpl_env in *; fsetdec.
apply wfterm_renameU; auto. simpl_env in *; fsetdec.
SCase "E".
apply wfterm_pair with
  (G1 := env_map (tsubst_typ (typ_var_f b) a) x ++ x0)
  (G2 := env_map (tsubst_typ (typ_var_f b) a) x1 ++ b ~ E ++ G2).
apply zip_renameE; auto. simpl_env in *; fsetdec.
assert (a ∉ dom (x ++ x0)). simpl_env; destruct_uniq; fsetdec.
rewrite tsubst_term_fresh_eq.
rewrite tsubst_typ_fresh_eq.
rewrite tsubst_env_fresh_eq.
auto.
intro H13. destruct (ftv_env_binds x a H13) as [? [? [? ?]]].
  assert (ftv_typ x3 [<=] dom (x ++ x0)). apply wftyp_ftv.
  destruct H16.
    apply wfenv_wftyp_T2 with (x := x2). eapply wfterm_wfenv; eauto. auto.
    apply wfenv_wftyp_Eq2 with (x := x2). eapply wfterm_wfenv; eauto. auto.
  assert (a ∈ dom (x ++ x0)) by auto. contradiction.
intro H13. apply H12. assert (ftv_typ t1 [<=] dom (x ++ x0)).
  apply wftyp_ftv. eapply wfterm_wftyp; eauto.
  auto.
intro H13. apply H12. assert (ftv_term e1 [<=] dom (x ++ x0)).
  eapply wfterm_ftv; eauto.
  auto.
apply IHwfterm2; auto. simpl_env in *; fsetdec.
Case "fst".
apply wfterm_fst with (t2 := tsubst_typ (typ_var_f b) a t2).
apply IHwfterm; auto.
Case "snd".
apply wfterm_snd with (t1 := tsubst_typ (typ_var_f b) a t1).
apply IHwfterm; auto.
Case "inst".
rewrite tsubst_typ_open_typ_wrt_typ; auto.
apply wfterm_inst.
auto using wftyp_renameE.
apply IHwfterm; auto.
Case "gen". elimtype False. eapply (H a); auto.
Case "exists".
pick fresh c and apply wfterm_exists.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ E ++ Γ₁) ++ [(b, E)] ++ Γ₂).
auto.
Case "open".
assert (uniq (G2 ++ G1)) by eauto with lngen.
destruct (b0 == a); subst.
SCase "b0 = a".
rewrite tsubst_typ_open_typ_wrt_typ; auto.
simpl. unfold typvar; destruct (a == a); subst; try congruence.
simpl_env. apply wfterm_open.
unfold env_map; auto.
simpl_env in H2. apply uniq_app_inv in H2. destruct H2; subst.
rewrite tsubst_term_fresh_eq.
rewrite tsubst_typ_fresh_eq.
rewrite tsubst_env_fresh_eq.
auto.
intro H13. destruct (ftv_env_binds Γ₁ a H13) as [? [? [? ?]]].
  assert (ftv_typ x0 [<=] dom (Γ₁ ++ Γ₂)). apply wftyp_ftv.
  destruct H4.
    apply wfenv_wftyp_T2 with (x := x). eapply wfterm_wfenv; eauto. auto.
    apply wfenv_wftyp_Eq2 with (x := x). eapply wfterm_wfenv; eauto. auto.
  assert (a ∈ dom (Γ₁ ++ Γ₂)) by auto. contradiction.
intro H13. apply H. assert (ftv_typ t [<=] dom (Γ₁ ++ Γ₂)).
  replace (ftv_typ t) with (ftv_typ (typ_exists t)) by reflexivity.
  apply wftyp_ftv. eapply wfterm_wftyp; eauto.
  auto.
intro H13. apply H. assert (ftv_term e [<=] dom (Γ₁ ++ Γ₂)).
  eapply wfterm_ftv; eauto.
  auto.
solve_uniq.
SCase "b0 ≠ a".
assert (binds b0 E (Γ₁ ++ (a, E) :: Γ₂)). rewrite <- H2; auto.
analyze_binds H4.
SSCase "b0 binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
simpl_env in H2.
apply uniq_app_inv in H2. destruct H2; subst.
repeat rewrite env_map_app.
unfold env_map at 2; simpl; simpl_env.
rewrite <- tsubst_typ_open_typ_wrt_typ_var; auto.
apply wfterm_open.
unfold env_map; auto.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) x ++
   env_map (tsubst_typ (typ_var_f b) a) x0) ++ [(b, E)] ++ Γ₂).
rewrite <- env_map_app.
apply IHwfterm; simpl_env; auto.
assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
SSCase "b0 binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in H2.
rewrite_env ((Γ₁ ++ [(a, E)] ++ x) ++ [(b0, E)] ++ x0) in H2.
apply uniq_app_inv in H2. destruct H2; subst.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++
   [(b, E)] ++ x) ++ [(b0, E)] ++ x0).
rewrite <- tsubst_typ_open_typ_wrt_typ_var; auto.
apply wfterm_open.
unfold env_map; auto.
simpl_env.
apply IHwfterm; simpl_env; auto.
assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
Case "nu".
pick fresh c and apply wfterm_nu.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ E ++ Γ₁) ++ [(b, E)] ++ Γ₂).
auto.
Case "sigma".
assert (uniq (G2 ++ G1)).
  pick fresh c. assert (uniq ([(c, Eq t')] ++ G2 ++ G1)) by eauto with lngen.
    solve_uniq.
destruct (a == b); subst.
SCase "a = b".
repeat rewrite tsubst_typ_var_self.
rewrite tsubst_term_var_self.
rewrite tsubst_env_var_self.
assert (binds b0 E (Γ₁ ++ (b, E) :: Γ₂)). rewrite <- H3; auto.
analyze_binds_uniq H5; simpl_env in *. rewrite <- H3; solve_uniq.
SSCase "b0 binds in Γ₁".
destruct (b0 == b); subst. elimtype False. fsetdec.
apply binds_decomp in BindsTac. destruct BindsTac as [? [? ?]]; subst.
simpl_env.
pick fresh c and apply wfterm_sigma.
simpl_env in *. assert (uniq (G2 ++ b0 ~ E ++ G1)). solve_uniq. rewrite H3 in H5. solve_uniq.
simpl_env in H3. apply uniq_app_inv in H3; auto. destruct H3; subst. auto.
SSCase "b0 = b".
simpl_env in H3. apply uniq_app_inv in H3; auto. destruct H3; subst.
unfold typvar; destruct (b == b); subst; try congruence.
pick fresh c and apply wfterm_sigma; auto.
SSCase "b0 binds in Γ₂".
destruct (b0 == b); subst. elimtype False. fsetdec.
apply binds_decomp in BindsTac0. destruct BindsTac0 as [? [? ?]]; subst.
rewrite_env ((Γ₁ ++ [(b, E)] ++ x) ++ [(b0, E)] ++ x0).
pick fresh c and apply wfterm_sigma.
simpl_env in *. assert (uniq (G2 ++ b0 ~ E ++ G1)). solve_uniq. rewrite H3 in H7. solve_uniq.
rewrite_env ((Γ₁ ++ [(b, E)] ++ x) ++ [(b0, E)] ++ x0) in H3. apply uniq_app_inv in H3; auto. destruct H3; subst. auto.
SCase "a ≠ b".
destruct (b0 == a); subst.
SSCase "b0 = a".
pick fresh c and apply wfterm_sigma.
unfold env_map; auto.
simpl_env in H3. apply uniq_app_inv in H3; auto. destruct H3; subst.
rewrite tsubst_term_fresh_eq.
rewrite tsubst_typ_fresh_eq.
rewrite tsubst_env_fresh_eq.
rewrite tsubst_typ_tsubst_typ; auto.
simpl; unfold typvar; destruct (b == b); subst; try congruence.
simpl_env.
rewrite tsubst_typ_fresh_eq with (a1 := b).
auto.
intro. apply H2. assert (ftv_typ t [<=] dom (Γ₁ ++ a ~ E ++ Γ₂)).
  apply wftyp_ftv. eapply wfterm_wftyp; eauto.
  clear Fr. simpl_env in *. fsetdec.
intro H13. destruct (ftv_env_binds Γ₁ a H13) as [? [? [? ?]]].
  assert (ftv_typ x0 [<=] dom (c ~ Eq t' ++ Γ₁ ++ Γ₂)). apply wftyp_ftv.
  destruct H5.
    apply wfenv_wftyp_T2 with (x := x). eapply wfterm_wfenv; eauto. auto.
    apply wfenv_wftyp_Eq2 with (x := x). eapply wfterm_wfenv; eauto. auto.
  assert (a ∈ dom (c ~ Eq t' ++ Γ₁ ++ Γ₂)) by auto.
  assert (a ∉ dom (c ~ Eq t' ++ Γ₁ ++ Γ₂)) by auto. contradiction.
intro. apply H. assert (ftv_typ t' [<=] dom (Γ₁ ++ Γ₂)).
  apply wftyp_ftv. eapply wfenv_wftyp_Eq3; eapply wfterm_wfenv; eauto.
  auto.
intro. apply H. assert (ftv_term e [<=] dom (c ~ Eq t' ++ Γ₁ ++ Γ₂)).
  transitivity (ftv_term (open_term_wrt_typ e (typ_var_f c))).
  auto with lngen.
  eapply wfterm_ftv; eauto.
  simpl_env in *. assert (c ≠ a) by fsetdec. clear Fr. fsetdec.
SSCase "b0 ≠ a".
assert (binds b0 E (Γ₁ ++ (a, E) :: Γ₂)). rewrite <- H3; auto.
analyze_binds H5.
SSSCase "b0 binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
simpl_env in H3.
apply uniq_app_inv in H3; auto. destruct H3; subst.
repeat rewrite env_map_app.
unfold env_map at 2; simpl; simpl_env.
pick fresh c and apply wfterm_sigma.
unfold env_map; auto.
rewrite tsubst_typ_tsubst_typ; auto.
simpl. unfold typvar; destruct (b == b0); subst; simpl_env.
SSSSCase "b = b0". elimtype False. simpl_env in *. auto.
SSSSCase "b ≠ b0".
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) (c ~ Eq t' ++ x) ++
   env_map (tsubst_typ (typ_var_f b) a) x0) ++ [(b, E)] ++ Γ₂).
rewrite <- env_map_app.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
apply H1; simpl_env; auto.
SSSCase "b0 binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in H3.
rewrite_env ((Γ₁ ++ [(a, E)] ++ x) ++ [(b0, E)] ++ x0) in H3.
apply uniq_app_inv in H3; auto. destruct H3; subst.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++
   [(b, E)] ++ x) ++ [(b0, E)] ++ x0).
pick fresh c and apply wfterm_sigma.
unfold env_map; auto.
rewrite tsubst_typ_tsubst_typ; auto.
simpl. unfold typvar; destruct (b == b0); subst; simpl_env.
SSSSCase "b = b0". elimtype False. simpl_env in *. clear Fr. fsetdec.
SSSSCase "b ≠ b0".
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ Eq t' ++ Γ₁) ++ [(b, E)] ++ x ++ x0).
apply H1; simpl_env; auto.
Case "coerce".
apply wfterm_coerce with (t' := tsubst_typ (typ_var_f b) a t').
auto using wftypeq_renameE.
auto.
Qed.

Lemma wfterm_renameEq : forall Γ₁ Γ₂ a b e τ τ₀,
  wfterm (Γ₁ ++ a ~ Eq τ₀ ++ Γ₂) e τ →
  b ∉ dom (Γ₁ ++ Γ₂) →
  wfterm (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ Eq τ₀ ++ Γ₂)
  (tsubst_term (typ_var_f b) a e) (tsubst_typ (typ_var_f b) a τ).
Proof.
intros Γ₁ Γ₂ a b e τ τ₀ H H0. dependent induction H; simpl; simpl_env.
Case "var".
constructor.
apply pure_app. eauto with fzip.
  rewrite_env (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ nil).
  apply pure_tsubst; simpl_env; eauto with fzip.
auto using wfenv_renameEq.
analyze_binds H1.
replace (T (tsubst_typ (typ_var_f b) a t)) with (tag_map (tsubst_typ (typ_var_f b) a) (T t)) by reflexivity.
  unfold env_map; auto.
rewrite tsubst_typ_fresh_eq; auto.
assert (ftv_typ t [<=] dom Γ₂). apply wftyp_ftv.
apply wfenv_wftyp_T2 with (x := x); auto.
apply wfenv_strip with (Γ' := Γ₁ ++ [(a, Eq τ₀)]). simpl_env; auto.
apply wfenv_uniq in H0. solve_uniq.
Case "app".
assert (uniq G1) by eauto with lngen.
assert (uniq G2) by eauto with lngen.
assert (uniq (Γ₁ ++ [(a, Eq τ₀)] ++ Γ₂)) by eauto with lngen.
destruct (zip_app_inv G1 G2 Γ₁ ([(a, Eq τ₀)] ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H9; subst.
simpl_env in *.
assert (dom x [<=] dom Γ₁) by eauto with fzip.
assert (dom x1 [=] dom Γ₁) by eauto with fzip.
assert (dom G1 [<=] dom Γ₂) by eauto with fzip.
assert (dom G2 [=] dom Γ₂) by eauto with fzip.
apply wfterm_app with
  (G1 := env_map (tsubst_typ (typ_var_f b) a) x ++ [(b, Eq τ₀)] ++ G1)
  (G2 := env_map (tsubst_typ (typ_var_f b) a) x1 ++ [(b, Eq τ₀)] ++ G2)
  (t2 := tsubst_typ (typ_var_f b) a t2).
apply zip_renameEq; auto. simpl_env. fsetdec.
apply IHwfterm1; auto. simpl_env; fsetdec.
apply IHwfterm2; auto. simpl_env; fsetdec.
Case "abs".
pick fresh x and apply wfterm_abs. auto using pure_renameEq.
rewrite tsubst_term_open_term_wrt_term_var.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (x ~ T t1 ++ Γ₁) ++ [(b, Eq τ₀)] ++ Γ₂).
auto.
Case "pair".
assert (uniq G1) by eauto with lngen.
assert (uniq G2) by eauto with lngen.
assert (uniq (Γ₁ ++ [(a, Eq τ₀)] ++ Γ₂)) by eauto with lngen.
destruct (zip_app_inv G1 G2 Γ₁ ([(a, Eq τ₀)] ++ Γ₂)) as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
inversion H9; subst.
simpl_env in *.
assert (dom x [<=] dom Γ₁) by eauto with fzip.
assert (dom x1 [=] dom Γ₁) by eauto with fzip.
assert (dom G1 [<=] dom Γ₂) by eauto with fzip.
assert (dom G2 [=] dom Γ₂) by eauto with fzip.
apply wfterm_pair with
  (G1 := env_map (tsubst_typ (typ_var_f b) a) x ++ [(b, Eq τ₀)] ++ G1)
  (G2 := env_map (tsubst_typ (typ_var_f b) a) x1 ++ [(b, Eq τ₀)] ++ G2).
apply zip_renameEq; auto. simpl_env. fsetdec.
apply IHwfterm1; auto. simpl_env; fsetdec.
apply IHwfterm2; auto. simpl_env; fsetdec.
Case "fst".
apply wfterm_fst with (t2 := tsubst_typ (typ_var_f b) a t2).
apply IHwfterm; auto.
Case "snd".
apply wfterm_snd with (t1 := tsubst_typ (typ_var_f b) a t1).
apply IHwfterm; auto.
Case "inst".
rewrite tsubst_typ_open_typ_wrt_typ; auto.
apply wfterm_inst.
auto using wftyp_renameEq.
apply IHwfterm; auto.
Case "gen".
pick fresh c and apply wfterm_gen. auto using pure_renameEq.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ U ++ Γ₁) ++ [(b, Eq τ₀)] ++ Γ₂).
auto.
Case "exists".
pick fresh c and apply wfterm_exists.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ E ++ Γ₁) ++ [(b, Eq τ₀)] ++ Γ₂).
auto.
Case "open".
destruct (b0 == a); subst.
SCase "b0 = a (absurd)".
assert (@E typ = Eq τ₀). apply binds_unique with (x := a) (E := Γ₁ ++ (a, Eq τ₀) :: Γ₂); auto.
  rewrite <- H2; auto.
  assert (uniq (G2 ++ G1)) by eauto with lngen.
  rewrite <- H2. solve_uniq.
congruence.
SCase "b0 ≠ a".
assert (binds b0 E (Γ₁ ++ (a, Eq τ₀) :: Γ₂)). rewrite <- H2; auto.
analyze_binds H3.
SSCase "b0 binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
simpl_env in H2.
apply uniq_app_inv in H2. destruct H2; subst.
repeat rewrite env_map_app.
unfold env_map at 2; simpl; simpl_env.
rewrite <- tsubst_typ_open_typ_wrt_typ_var; auto.
apply wfterm_open.
unfold env_map; auto.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) x ++
   env_map (tsubst_typ (typ_var_f b) a) x0) ++ [(b, Eq τ₀)] ++ Γ₂).
rewrite <- env_map_app.
apply IHwfterm; simpl_env; auto.
assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
SSCase "b0 binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in H2.
rewrite_env ((Γ₁ ++ [(a, Eq τ₀)] ++ x) ++ [(b0, E)] ++ x0) in H2.
apply uniq_app_inv in H2. destruct H2; subst.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++
   [(b, Eq τ₀)] ++ x) ++ [(b0, E)] ++ x0).
rewrite <- tsubst_typ_open_typ_wrt_typ_var; auto.
apply wfterm_open.
unfold env_map; auto.
simpl_env.
apply IHwfterm; simpl_env; auto.
assert (uniq (G2 ++ G1)) by eauto with lngen. solve_uniq.
Case "nu".
pick fresh c and apply wfterm_nu.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ E ++ Γ₁) ++ [(b, Eq τ₀)] ++ Γ₂).
auto.
Case "sigma".
destruct (b0 == a); subst.
SCase "b0 = a (absurd)".
assert (@E typ = Eq τ₀). apply binds_unique with (x := a) (E := Γ₁ ++ (a, Eq τ₀) :: Γ₂); auto.
  rewrite <- H3; auto.
  pick fresh c.
  assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen.
  rewrite <- H3. solve_uniq.
congruence.
SCase "b0 ≠ a".
assert (binds b0 E (Γ₁ ++ (a, Eq τ₀) :: Γ₂)). rewrite <- H3; auto.
analyze_binds H4.
SSCase "b0 binds in Γ₁".
apply binds_decomp in BindsTac; destruct BindsTac as [? [? ?]]; subst.
simpl_env in H3.
apply uniq_app_inv in H3. destruct H3; subst.
repeat rewrite env_map_app.
unfold env_map at 2; simpl; simpl_env.
pick fresh c and apply wfterm_sigma.
unfold env_map; auto.
rewrite tsubst_typ_tsubst_typ; auto.
simpl. unfold typvar; destruct (b == b0); subst; simpl_env.
SSSCase "b = b0". elimtype False. simpl_env in *. auto.
SSSCase "b ≠ b0".
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) (c ~ Eq t' ++ x) ++
   env_map (tsubst_typ (typ_var_f b) a) x0) ++ [(b, Eq τ₀)] ++ Γ₂).
rewrite <- env_map_app.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
apply H1; simpl_env; auto.
pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
SSCase "b0 binds in Γ₂".
apply binds_decomp in BindsTac0; destruct BindsTac0 as [? [? ?]]; subst.
simpl_env in H3.
rewrite_env ((Γ₁ ++ [(a, Eq τ₀)] ++ x) ++ [(b0, E)] ++ x0) in H3.
apply uniq_app_inv in H3. destruct H3; subst.
rewrite_env ((env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++
   [(b, Eq τ₀)] ++ x) ++ [(b0, E)] ++ x0).
pick fresh c and apply wfterm_sigma.
unfold env_map; auto.
rewrite tsubst_typ_tsubst_typ; auto.
simpl. unfold typvar; destruct (b == b0); subst; simpl_env.
SSSCase "b = b0". elimtype False. simpl_env in *. clear Fr. fsetdec.
SSSCase "b ≠ b0".
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (c ~ Eq t' ++ Γ₁) ++ [(b, Eq τ₀)] ++ x ++ x0).
apply H1; simpl_env; auto.
pick fresh c. assert (uniq (c ~ Eq t' ++ G2 ++ G1)) by eauto with lngen. solve_uniq.
Case "coerce".
apply wfterm_coerce with (t' := tsubst_typ (typ_var_f b) a t').
auto using wftypeq_renameEq.
auto.
Qed.

Lemma val_pure : forall Γ e τ,
  val e → wfterm Γ e τ → pure Γ.
Proof.
intros Γ e τ H H0. generalize dependent τ. generalize dependent Γ.
induction H; intros Γ τ Hwfterm; inversion Hwfterm; subst; try congruence; eauto using pure_zip.
Case "exists_sigma".
inversion H5; subst. clear H5.
pick fresh b.
assert (wfterm (b ~ E ++ Γ)
         (open_term_wrt_typ (term_sigma (typ_var_b 0) t' e') (typ_var_f b))
         (open_typ_wrt_typ t (typ_var_f b))) as H by auto.
unfold open_term_wrt_typ in H; simpl in H; simpl_env in H.
inversion H; subst.
simpl_env in H4; rewrite_env (nil ++ b ~ E ++ Γ) in H4; apply uniq_app_inv in H4; destruct H4; subst.
pick fresh a.
assert
(wfterm (a ~ Eq (open_typ_wrt_typ_rec 0 (typ_var_f b) t') ++ Γ)
        (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f b) e') (typ_var_f a))
        (tsubst_typ (typ_var_f a) b (open_typ_wrt_typ t (typ_var_f b)))) by auto.
assert (pure ([(a, Eq (open_typ_wrt_typ_rec 0 (typ_var_f b) t'))] ++ Γ)).
eapply H2 with (b := b) (a := a); auto.
unfold open_term_wrt_typ; simpl; reflexivity.
eauto with fzip.
simpl_env in *.
pick fresh a.
assert (uniq ( [(a, Eq (open_typ_wrt_typ_rec 0 (typ_var_f b) t'))] ++ G2 ++ G1)). eauto with lngen.
solve_uniq.
Qed.
