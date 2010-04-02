Add LoadPath "../metatheory".
Require Export FzipCore_init.
Require Import FzipCore_zip.
Require Import FzipCore_pure.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_term x) in
  let D2 := gather_atoms_with (fun x => ftv_typ x) in
  let D3 := gather_atoms_with (fun x => ftv_term x) in
  let D4 := gather_atoms_with (fun x => ftv_env x) in
  constr:(A \u B \u C \u D1 \u D2 \u D3 \u D4).

(** Mutual induction principles *)
Scheme val_mut_ind_aux  := Induction for val  Sort Prop
with   result_mut_ind_aux := Induction for result Sort Prop.
Combined Scheme val_result_mut_ind from val_mut_ind_aux, result_mut_ind_aux.

Scheme wfenv_mut_ind_aux := Induction for wfenv Sort Prop
with   wftyp_mut_ind_aux := Induction for wftyp Sort Prop.
Combined Scheme wfenv_wftyp_mut_ind from
  wfenv_mut_ind_aux, wftyp_mut_ind_aux.

(** Administrative lemmas *)
Lemma val_result_regular :
  (forall v, val v → lc_term v)
  ∧ (forall p, result p → lc_term p).
Proof.
apply val_result_mut_ind; eauto.
Case "val_exists".
  intros; subst.
  pick fresh b; pick fresh a.
  apply (lc_term_exists_exists b).
  unfold open_term_wrt_typ; simpl.
  apply (lc_term_sigma_exists a); auto.
    apply l; auto.
  eapply (H b a); auto; reflexivity.
Qed.

Lemma val_regular : forall v, val v → lc_term v.
Proof.
intros; destruct val_result_regular as [H1 _]; auto.
Qed.

Lemma result_regular : forall p, result p → lc_term p.
Proof.
intros; destruct val_result_regular as [_ H2]; auto.
Qed.
Hint Resolve val_regular result_regular: lngen.

Lemma red0_regular1 : forall e e', red0 e e' → lc_term e.
Proof.
intros e e' H. destruct H; auto with lngen.
Case "nu_sigma".
  pick fresh b; pick fresh a.
  apply (lc_term_nu_exists b).
  unfold open_term_wrt_typ; simpl.
  apply (lc_term_sigma_exists a); auto.
  apply H; auto.
  apply result_regular.
  eapply (H2 b a); auto; reflexivity.
Qed.

Lemma red0_regular2 : forall e e', red0 e e' → lc_term e'.
Proof.
intros e e' H; destruct H;
try solve [apply val_regular in H; inversion H; subst; auto];
auto with lngen.
Case "beta_v". eauto with lngen.
Case "beta_t".
  pick fresh a.
  assert (lc_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
  apply tsubst_term_lc_term
    with (t1 := typ_var_f b) (a1 := a) in H0; auto.
  rewrite tsubst_term_open_term_wrt_typ in H0; auto.
  autorewrite with lngen in H0; auto.
Case "nu_sigma".
  pick fresh b; pick fresh a.
  erewrite (H3 b a); auto.
  apply tsubst_term_lc_term; auto.
  apply result_regular.
  eapply (H2 b a); auto;
  unfold open_term_wrt_typ; simpl; reflexivity.
  reflexivity.
Case "coerce_coerce".
  inversion H0; subst; try congruence; auto with lngen.
Case "sigma_appL".
  pick fresh a.
  apply (lc_term_sigma_exists a); auto.
  apply result_regular in H; inversion H; subst; auto.
  replace (open_term_wrt_typ (term_app e1 e2') (typ_var_f a)) with
    (term_app (open_term_wrt_typ e1 (typ_var_f a)) (open_term_wrt_typ e2' (typ_var_f a)))
    by reflexivity.
  constructor.
    apply result_regular in H; inversion H; subst. apply H7.
    rewrite (H1 a); auto with lngen.
Case "sigma_appR".
  pick fresh a.
  apply (lc_term_sigma_exists a); auto.
  apply result_regular in H0; inversion H0; subst; auto.
  replace (open_term_wrt_typ (term_app e1' e2) (typ_var_f a)) with
    (term_app (open_term_wrt_typ e1' (typ_var_f a)) (open_term_wrt_typ e2 (typ_var_f a)))
    by reflexivity.
  constructor.
    rewrite (H1 a); auto with lngen.
    apply result_regular in H0; inversion H0; subst. apply H7.
Case "sigma_pairL".
  pick fresh a.
  apply (lc_term_sigma_exists a); auto.
  apply result_regular in H; inversion H; subst; auto.
  replace (open_term_wrt_typ (term_pair e1 e2') (typ_var_f a)) with
    (term_pair (open_term_wrt_typ e1 (typ_var_f a)) (open_term_wrt_typ e2' (typ_var_f a)))
    by reflexivity.
  constructor.
    apply result_regular in H; inversion H; subst. apply H7.
    rewrite (H1 a); auto with lngen.
Case "sigma_pairR".
  pick fresh a.
  apply (lc_term_sigma_exists a); auto.
  apply result_regular in H0; inversion H0; subst; auto.
  replace (open_term_wrt_typ (term_pair e1' e2) (typ_var_f a)) with
    (term_pair (open_term_wrt_typ e1' (typ_var_f a)) (open_term_wrt_typ e2 (typ_var_f a)))
    by reflexivity.
  constructor.
    rewrite (H1 a); auto with lngen.
    apply result_regular in H0; inversion H0; subst. apply H7.
Case "sigma_fst".
  pick fresh a.
  apply result_regular in H; inversion H; subst.
  apply (lc_term_sigma_exists a); auto.
  unfold open_term_wrt_typ; simpl.
  constructor; apply H5.
Case "sigma_snd".
  pick fresh a.
  apply result_regular in H; inversion H; subst.
  apply (lc_term_sigma_exists a); auto.
  unfold open_term_wrt_typ; simpl.
  constructor; apply H5.
Case "Sigma_inst".
  pick fresh a.
  apply result_regular in H0; inversion H0; subst.
  apply (lc_term_sigma_exists a); auto.
  replace (open_term_wrt_typ (term_inst e t'') (typ_var_f a)) with
    (term_inst (open_term_wrt_typ e (typ_var_f a)) (open_typ_wrt_typ t'' (typ_var_f a)))
    by reflexivity.
  constructor.
    apply H7.
    rewrite (H1 a); auto with lngen.
Case "sigma_open".
  pick fresh a.
  apply result_regular in H; inversion H; subst.
  apply (lc_term_sigma_exists a); auto.
  unfold open_term_wrt_typ; simpl.
  constructor; auto. apply H5.
Case "sigma_sigma".
  pick fresh a2; pick fresh a1.
  apply result_regular in H; inversion H; subst.
  apply (lc_term_sigma_exists a2); auto.
  rewrite (H3 a2); auto.
    assert
      (lc_term
        (open_term_wrt_typ
          (term_sigma (typ_var_f b2) t2 e)
          (typ_var_f a2))) as H11 by auto;
      inversion H11; subst; auto.
  unfold open_term_wrt_typ; simpl.
  apply (lc_term_sigma_exists a1); auto.
  rewrite (H2 a2) in H9; auto.
  assert (open_term_wrt_typ_rec 1 (typ_var_f a2) e'
  = open_term_wrt_typ_rec 1 (typ_var_f a1) e) as Heq.
    apply (H4 a1 a2); auto.
    unfold open_term_wrt_typ; simpl; rewrite (H3 a1); auto.
    unfold open_term_wrt_typ; simpl; rewrite (H2 a2); auto.
  rewrite Heq; clear Heq.
  assert
    (lc_term (open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e) (typ_var_f a1))) as H11 by auto.
  unfold open_term_wrt_typ in H11; simpl in H11; inversion H11; subst.
  auto.
Qed.
Hint Resolve red0_regular1 red0_regular2: lngen.

Lemma red1_regular1 : forall e e', e ⇝ e' → lc_term e.
Proof.
intros e e' H. induction H; eauto with lngen.
Qed.

Lemma red1_regular2 : forall e e', e ⇝ e' → lc_term e'.
Proof.
intros e e' H; induction H; eauto with lngen.
Qed.
Hint Resolve red1_regular1 red1_regular2: lngen.

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
destruct H. eapply zip_binds_U12 in H; eauto. tauto.
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

(*
(** Lemmas about values *)
Lemma value_is_normal_aux :
  (forall v, pval v → ~ exists e, v ⇝ e) ∧
  (forall v, val v → ~ exists e, v ⇝ e).
Proof.
apply pval_val_mut_ind; intros; intros [e0 Hred]; inversion Hred; subst; eauto.
inversion H.
inversion H1; subst. inversion p.
inversion H0; subst. inversion p.
inversion H0.
pick fresh x. eapply H; eauto.
inversion H0.
pick fresh a. eapply H; eauto.
Qed.

Lemma value_is_normal : forall v, val v → ~ exists e, v ⇝ e.
Proof.
destruct value_is_normal_aux as [_ Th]. intuition auto.
Qed.

(** Renaming lemmas *)
Lemma pval_val_renaming : forall x y,
  (forall v, pval v → pval (subst_term (term_var_f y) x v)) ∧
  (forall v, val v → val (subst_term (term_var_f y) x v)).
Proof.
intros x y.
apply pval_val_mut_ind; intros; simpl; auto.
Case "var". destruct (x0 == x); auto.
Case "abs". pick fresh z and apply val_abs; auto.
  rewrite subst_term_open_term_wrt_term_var; auto.
Case "gen". pick fresh a and apply val_gen; auto.
  rewrite subst_term_open_term_wrt_typ_var; auto.
Qed.

Lemma val_renaming : forall x y v,
  val v → val (subst_term (term_var_f y) x v).
Proof.
intros x y v H. destruct (pval_val_renaming x y); auto.
Qed.
Hint Resolve val_renaming.

Lemma pval_val_trenaming : forall a b,
  (forall v, pval v → pval (tsubst_term (typ_var_f b) a v)) ∧
  (forall v, val v → val (tsubst_term (typ_var_f b) a v)).
Proof.
intros a b.
apply pval_val_mut_ind; intros; simpl; auto with lngen.
Case "abs". pick fresh z and apply val_abs; auto with lngen.
  rewrite tsubst_term_open_term_wrt_term_var; auto.
Case "gen". pick fresh c and apply val_gen; auto.
  rewrite tsubst_term_open_term_wrt_typ_var; auto.
Qed.

Lemma val_trenaming : forall a b v,
  val v → val (tsubst_term (typ_var_f b) a v).
Proof.
intros a b v H. destruct (pval_val_trenaming a b); auto.
Qed.
Hint Resolve val_trenaming.
*)

(*
(** Lemmas about red0, red1 *)
Lemma red0_subst : forall x e'' e e', lc_term e'' → red0 e e' →
  red0 (subst_term e'' x e) (subst_term e'' x e').
Proof.
intros x e'' e e' Hlc H.
inversion H; subst; simpl.
rewrite subst_term_open_term_wrt_term; auto. apply red0_beta; auto with lngen.
assert (lc_term (subst_term e'' x (term_abs t e1))) by auto with lngen; auto.
rewrite subst_term_open_term_wrt_typ; auto. apply red0_beta_t; auto with lngen.
assert (lc_term (subst_term e'' x (term_gen e0))) by auto with lngen; auto.
Qed.
Hint Resolve red0_subst.

Lemma red1_subst : forall x e'' e e', lc_term e'' → e ⇝ e' →
  (subst_term e'' x e) ⇝ (subst_term e'' x e').
Proof.
intros x e'' e e' Hlc H.
induction H; subst; simpl; auto with lngen.
apply red1_abs with (L := L `union` {{x}}); auto; intros z Hz.
replace (term_var_f z) with (subst_term e'' x (term_var_f z)) by auto with lngen.
repeat rewrite <- subst_term_open_term_wrt_term; eauto.
apply red1_gen with (L := L `union` {{x}}); intros a Ha.
repeat rewrite <- subst_term_open_term_wrt_typ; eauto.
Qed.
Hint Resolve red1_subst.

Lemma red1_open : forall L e'' e e',
  lc_term e'' →
  (forall x, x ∉ L → e ^ x ⇝ e' ^ x) →
  e ^^ e'' ⇝ e' ^^ e''.
Proof.
intros L e'' e e' Hlc H.
pick fresh x.
rewrite subst_term_intro with (x1 := x) (e1 := e); auto.
rewrite subst_term_intro with (x1 := x) (e1 := e'); auto.
Qed.
Hint Resolve red1_open.

Lemma red0_tsubst : forall a τ e e', lc_typ τ → red0 e e' →
  red0 (tsubst_term τ a e) (tsubst_term τ a e').
Proof.
intros a τ e e' Hlc H.
inversion H; subst; simpl.
rewrite tsubst_term_open_term_wrt_term; auto. apply red0_beta; auto with lngen.
assert (lc_term (tsubst_term τ a (term_abs t e1))) by auto with lngen; auto.
rewrite tsubst_term_open_term_wrt_typ; auto. apply red0_beta_t; auto with lngen.
assert (lc_term (tsubst_term τ a (term_gen e0))) by auto with lngen; auto.
Qed.
Hint Resolve red0_tsubst.

Lemma red1_tsubst : forall a τ e e', lc_typ τ → e ⇝ e' →
  (tsubst_term τ a e) ⇝ (tsubst_term τ a e').
Proof.
intros a τ e e' Hlc H.
induction H; subst; simpl; auto with lngen.
apply red1_abs with (L := L `union` {{a}}); auto with lngen ; intros z Hz.
replace (term_var_f z) with (tsubst_term τ a (term_var_f z)) by reflexivity.
repeat rewrite <- tsubst_term_open_term_wrt_term; eauto.
apply red1_gen with (L := L `union` {{a}}); intros b Hb.
replace (typ_var_f b) with (tsubst_typ τ a (typ_var_f b)) by auto with lngen.
repeat rewrite <- tsubst_term_open_term_wrt_typ; eauto.
Qed.
Hint Resolve red1_tsubst.

Lemma red1_topen : forall L τ e e',
  lc_typ τ →
  (forall a, a ∉ L → open_term_wrt_typ e (typ_var_f a) ⇝ open_term_wrt_typ e' (typ_var_f a)) →
  open_term_wrt_typ e τ ⇝ open_term_wrt_typ e' τ.
Proof.
intros L τ e e' Hlc H.
pick fresh a.
rewrite tsubst_term_intro with (a1 := a) (e1 := e); auto.
rewrite tsubst_term_intro with (a1 := a) (e1 := e'); auto.
Qed.
Hint Resolve red1_topen.
*)

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
  assert (wftyp (G2 ++ G1) t'). eauto with fzip.
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
  apply wftyp_ftv; eauto with fzip.
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

(*
Lemma zip_assoc : forall Γ₁ Γ₂ Γ₃ Γ₁₂ Γ₂₃ Γ₁₂₃ Γ₁₂₃',
  zip Γ₁ Γ₂ Γ₁₂ → zip Γ₁₂ Γ₃ Γ₁₂₃ →
  zip Γ₁ Γ₂₃ Γ₁₂₃' → zip Γ₂ Γ₃ Γ₂₃ →
  Γ₁₂₃ = Γ₁₂₃'.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁₂ Γ₂₃ Γ₁₂₃ Γ₁₂₃' H H0 H1 H2.
generalize dependent Γ₃. generalize dependent Γ₂₃.
generalize dependent Γ₁₂₃. generalize dependent Γ₁₂₃'.
induction H; intros.
Case "nil".
inversion H0; subst; auto. inversion H1; subst.
auto.
inversion H2.
inversion H2; subst. inversion H1; subst.
  replace G3 with G in * by eauto using zip_unique.
  f_equal. auto using zip_nil.
Case "TT".
inversion H1; subst.
  inversion H2; subst.
    inversion H3; subst. f_equal. eauto.
    inversion H3; subst.
  clear H1. inversion H3; subst. clear H3. inversion H2; subst. clear H2. f_equal.
    eapply IHzip; eauto.
*)

(*
Lemma wfterm_ftv_env_not_E : forall Γ M τ,
  wfterm Γ M τ →
  forall a, a ∈ ftv_env Γ → not (binds a E Γ).
Proof.
intros Γ M τ H. induction H; intros.
Case "var".
intro; eapply (H a); auto.
Case "app".
intro H3. apply zip_binds_E3_inv with (Γ₁ := G1) (Γ₂ := G2) in H3; eauto with lngen.
assert (ftv_env G1 [=] ftv_env G) by eauto using zip_ftv_env1.
assert (ftv_env G2 [=] ftv_env G) by eauto using zip_ftv_env2.
destruct H3 as [[? ?] | [? ?]].
eapply (IHwfterm1 a); eauto with fzip. fsetdec.
eapply (IHwfterm2 a); eauto with fzip. fsetdec.
Case "lam". pick fresh x.
intro. eapply (H1 x _ a); auto.
rewrite ftv_env_app. auto.
Case "pair".
intro H3. apply zip_binds_E3_inv with (Γ₁ := G1) (Γ₂ := G2) in H3; eauto with lngen.
assert (ftv_env G1 [=] ftv_env G) by eauto using zip_ftv_env1.
assert (ftv_env G2 [=] ftv_env G) by eauto using zip_ftv_env2.
destruct H3 as [[? ?] | [? ?]].
eapply (IHwfterm1 a); eauto with fzip. fsetdec.
eapply (IHwfterm2 a); eauto with fzip. fsetdec.
Case "projL". intro. eapply (IHwfterm a); auto.
Case "projR". intro. eapply (IHwfterm a); auto.
Case "inst". intro. eapply (IHwfterm a); auto.
Case "gen". pick fresh a0. intro. eapply (H1 a0 _ a); auto.
Case "exists". pick fresh a0. intro. eapply (H0 a0 _ a); auto.
Case "open". intro. eapply (IHwfterm a); auto.
repeat rewrite ftv_env_app in *. unfold ftv_env at 2 in H1; simpl in H1. fsetdec.
analyze_binds_uniq H2.
  apply wfterm_wfenv in H0. apply wfenv_uniq in H0.
  simpl_env in *. solve_uniq.

ICI
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
