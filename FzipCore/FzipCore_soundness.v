Add LoadPath "../metatheory".
Require Export FzipCore_init.

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
Hint Resolve val_regular result_regular.

Lemma red0_regular1 : forall e e', red0 e e' → lc_term e.
Proof.
intros e e' H. destruct H; auto.
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
  assert (lc_term (open_term_wrt_typ e (typ_var_f a))) by auto.
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
  unfold open_term_wrt_typ; simpl.
  constructor.
    apply result_regular in H; inversion H; subst. apply H7.
    rewrite <- (H1 a) in H0; auto.
Case "sigma_appR".
  pick fresh a.
  apply (lc_term_sigma_exists a); auto.
  apply result_regular in H0; inversion H0; subst; auto.
  unfold open_term_wrt_typ; simpl.
  constructor.
    rewrite <- (H1 a) in H; auto.
    apply result_regular in H0; inversion H0; subst. apply H7.
Case "sigma_pairL".
  pick fresh a.
  apply (lc_term_sigma_exists a); auto.
  apply result_regular in H; inversion H; subst; auto.
  unfold open_term_wrt_typ; simpl.
  constructor.
    apply result_regular in H; inversion H; subst. apply H7.
    rewrite <- (H1 a) in H0; auto.
Case "sigma_pairR".
  pick fresh a.
  apply (lc_term_sigma_exists a); auto.
  apply result_regular in H0; inversion H0; subst; auto.
  unfold open_term_wrt_typ; simpl.
  constructor.
    rewrite <- (H1 a) in H; auto.
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
  unfold open_term_wrt_typ; simpl.
  constructor.
    apply H7.
    rewrite <- (H1 a) in H; auto.
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
Hint Resolve red0_regular1 red0_regular2.

Lemma red1_regular1 : forall e e', e ⇝ e' → lc_term e.
Proof.
intros e e' H. induction H; eauto.
Qed.

Lemma red1_regular2 : forall e e', e ⇝ e' → lc_term e'.
Proof.
intros e e' H; induction H; eauto.
Qed.
Hint Resolve red1_regular1 red1_regular2.

Lemma wftyp_regular : forall Γ τ, wftyp Γ τ → lc_typ τ.
Proof.
intros Γ τ H.
induction H; eauto.
Qed.
Hint Resolve wftyp_regular.

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
Hint Resolve wfenv_wftyp_T wfenv_wftyp_Eq.


Lemma wftyp_wfenv : forall Γ τ, wftyp Γ τ → wfenv Γ.
Proof.
destruct wfenv_wftyp_aux; auto.
Qed.
Hint Resolve wftyp_wfenv.

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
Hint Resolve wfenv_uniq.

Lemma wftyp_uniq :  forall Γ τ, wftyp Γ τ → uniq Γ.
Proof.
eauto.
Qed.
Hint Resolve wftyp_uniq.

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
inversion H; subst. eapply IHΓ; eauto.
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
inversion H; subst. eapply IHΓ; eauto.
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
inversion H; subst. eapply IHΓ; eauto.
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
inversion H; subst. eapply IHΓ; eauto.
Qed.
Hint Resolve wfenv_wftyp_T2 wfenv_wftyp_Eq2.

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
Hint Resolve wfenv_wftyp_T3 wfenv_wftyp_Eq3.

Lemma wfenv_regular_T :
forall Γ x τ, wfenv Γ → binds x (T τ) Γ → lc_typ τ.
Proof.
intros. induction H; analyze_binds H0.
replace t with τ in * by congruence; eauto.
eauto.
eauto.
Qed.

Lemma wfenv_regular_Eq :
forall Γ x τ, wfenv Γ → binds x (Eq τ) Γ → lc_typ τ.
Proof.
intros. induction H; analyze_binds H0.
eauto.
replace t with τ in * by congruence; eauto.
eauto.
Qed.
Hint Resolve wfenv_regular_T wfenv_regular_Eq.

Lemma wftyp_regular_T2 : forall Γ x τ τ',
  wftyp (x ~ T τ ++ Γ) τ' → lc_typ τ.
Proof.
intros Γ x τ τ' H. eauto.
Qed.

Lemma wftyp_regular_Eq2 : forall Γ x τ τ',
  wftyp (x ~ Eq τ ++ Γ) τ' → lc_typ τ.
Proof.
intros Γ x τ τ' H. eauto.
Qed.
Hint Resolve wftyp_regular_T2 wftyp_regular_Eq2.

Lemma wfenv_wftyp_subst :
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ x τ, Γ = Γ₁ ++ x ~ (T τ) ++ Γ₂ → wfenv (Γ₁ ++ Γ₂)) ∧
  (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ x τ', Γ = Γ₁ ++ x ~ (T τ') ++ Γ₂ → wftyp (Γ₁ ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros.
Case "wfenv_empty".
assert (binds x (T τ) nil). rewrite H; auto. analyze_binds H0.
Case "wfenv_T".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
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
Hint Resolve wfenv_subst.

Lemma wftyp_subst :
forall Γ₁ Γ₂ τ x τ', wftyp (Γ₁ ++ x ~ (T τ') ++ Γ₂) τ → wftyp (Γ₁ ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_subst as [H1 H2].
intros. eapply H2; eauto.
Qed.
Hint Resolve wftyp_subst.

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
Hint Resolve wfenv_instantiate.

Lemma wftyp_instantiate :
forall Γ₁ Γ₂ τ a τ', wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ →
wftyp Γ₂ τ' → wftyp (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_instantiate as [H1 H2].
intros. eapply H2; eauto.
Qed.
Hint Resolve wftyp_instantiate.

Lemma wfenv_strip :
forall Γ' Γ, wfenv (Γ' ++ Γ) -> wfenv Γ.
Proof.
intro Γ'; induction Γ'; intros; auto.
apply IHΓ'.
simpl_env in H.
inversion H; subst; auto.
eapply wftyp_wfenv; eauto.
eapply wftyp_wfenv; eauto.
Qed.
(* Hint Resolve wfenv_strip. *)

Lemma wfenv_wftyp_subst_eq :
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ a τ, Γ = Γ₁ ++ a ~ Eq τ ++ Γ₂ → wfenv ((env_map (tsubst_typ τ a) Γ₁) ++ Γ₂)) ∧
  (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ a τ', Γ = Γ₁ ++ a ~ Eq τ' ++ Γ₂ → wftyp ((env_map (tsubst_typ τ' a) Γ₁) ++ Γ₂) (tsubst_typ τ' a τ)).
Proof.
apply wfenv_wftyp_mut_ind; intros.
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
inversion H0; subst; eauto.
destruct p; destruct t0; inversion H0; subst; simpl_env in *;
simpl; simpl_env; constructor.
unfold env_map; auto. auto.
Case "wftyp_var".
subst G. simpl.
destruct (a == a0); subst.
SCase "a = a0".
rewrite_env (nil ++ env_map (tsubst_typ τ' a0) Γ₁ ++ Γ₂); apply wftyp_weakening; auto.
simpl_env. apply wfenv_wftyp_Eq3 with (x := a0).
eapply wfenv_strip; eauto.
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
subst G. simpl; constructor; auto.
Case "wftyp_prod".
subst G. simpl; constructor; auto.
Case "wftyp_forall".
subst G. simpl; apply wftyp_forall with (L := L ∪ {{a}}); intros.
rewrite_env (([(a0, U)] ++ env_map (tsubst_typ τ' a) Γ₁) ++ Γ₂).
replace ([(a0, U)] ++ env_map (tsubst_typ τ' a) Γ₁) with (env_map (tsubst_typ τ' a) ([(a0, U)] ++ Γ₁)) by reflexivity.
replace (typ_var_f a0) with (tsubst_typ τ' a (typ_var_f a0)).
rewrite <- tsubst_typ_open_typ_wrt_typ.
eapply H; simpl_env; eauto. eauto.
autorewrite with lngen; auto.
Case "wftyp_exists".
subst G. simpl; apply wftyp_exists with (L := L ∪ {{a}}); intros.
rewrite_env (([(a0, U)] ++ env_map (tsubst_typ τ' a) Γ₁) ++ Γ₂).
replace ([(a0, U)] ++ env_map (tsubst_typ τ' a) Γ₁) with (env_map (tsubst_typ τ' a) ([(a0, U)] ++ Γ₁)) by reflexivity.
replace (typ_var_f a0) with (tsubst_typ τ' a (typ_var_f a0)).
rewrite <- tsubst_typ_open_typ_wrt_typ.
eapply H; simpl_env; eauto. eauto.
autorewrite with lngen; auto.
Qed.

Lemma wfenv_subst_eq :
  forall Γ₁ Γ₂ a τ, wfenv (Γ₁ ++ a ~ Eq τ ++ Γ₂) →
    wfenv (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂).
Proof.
destruct wfenv_wftyp_subst_eq as [H1 H2].
intros Γ₁ Γ₂ x τ H. eapply H1; eauto.
Qed.
Hint Resolve wfenv_subst_eq.

Lemma wftyp_subst_eq :
forall Γ₁ Γ₂ τ a τ', wftyp (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ →
wftyp (env_map (tsubst_typ τ' a) Γ₁ ++ Γ₂) (tsubst_typ τ' a τ).
Proof.
destruct wfenv_wftyp_subst_eq as [H1 H2].
intros. eapply H2; eauto.
Qed.
Hint Resolve wftyp_subst_eq.

Lemma wfenv_tsubst :
  forall Γ₁ Γ₂ a τ, wfenv (Γ₁ ++ a ~ U ++ Γ₂) → wftyp Γ₂ τ →
    wfenv (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂).
Proof.
intros Γ₁ Γ₂ a τ H H0.
auto.
Qed.
Hint Resolve wfenv_tsubst.

Lemma wftyp_tsubst :
forall Γ₁ Γ₂ τ a τ', wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ →
wftyp Γ₂ τ' → wftyp (env_map (tsubst_typ τ' a) Γ₁ ++ Γ₂) (tsubst_typ τ' a τ).
Proof.
intros Γ₁ Γ₂ τ a τ' H H0.
auto.
Qed.
Hint Resolve wftyp_tsubst.

Lemma wftyp_fv : forall Γ τ, wftyp Γ τ → ftv_typ τ [<=] dom Γ.
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
Hint Resolve wftyp_fv.

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
apply wfenv_wftyp_mut_ind; intros; subst; auto.
assert (binds a (Eq τ') nil). rewrite H; auto.
  analyze_binds H0.
destruct Γ₁; inversion H0; simpl_env in *; subst.
  constructor; auto; eapply H; eauto.
destruct Γ₁; inversion H0; simpl_env in *; subst.
  constructor; auto; eapply H; eauto.
destruct Γ₁; inversion H0; simpl_env in *; subst.
  constructor; auto; eapply H; eauto.
destruct Γ₁; inversion H0; simpl_env in *; subst.
  constructor; auto. eapply wftyp_wfenv; eauto.
  constructor; auto; eapply H; eauto.
constructor; auto.
  destruct o. analyze_binds H0.
  destruct H0. analyze_binds H0.
  destruct H0. analyze_binds H0; eauto 6.
eapply H; eauto.
constructor. eapply H; eauto. eapply H0; eauto.
constructor. eapply H; eauto. eapply H0; eauto.
apply wftyp_forall with (L := L ∪ {{a}}); intros.
  rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ U ++ Γ₂). eapply H; simpl_env; eauto.
apply wftyp_exists with (L := L ∪ {{a}}); intros.
  rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ U ++ Γ₂). eapply H; simpl_env; eauto.
Qed.

Lemma wfenv_UE :
  forall Γ₁ a Γ₂, wfenv (Γ₁ ++ a ~ U ++ Γ₂) -> wfenv (Γ₁ ++ a ~ E ++ Γ₂).
Proof.
destruct wfenv_wftyp_UE_aux as [H _].
intros. eapply H. eauto. auto.
Qed.

Lemma wfenv_EU :
  forall Γ₁ a Γ₂, wfenv (Γ₁ ++ a ~ E ++ Γ₂) -> wfenv (Γ₁ ++ a ~ U ++ Γ₂).
Proof.
destruct wfenv_wftyp_EU_aux as [H _].
intros. eapply H. eauto. auto.
Qed.

Lemma wfenv_EqU :
  forall Γ₁ a Γ₂ τ, wfenv (Γ₁ ++ a ~ Eq τ ++ Γ₂) -> wfenv (Γ₁ ++ a ~ U ++ Γ₂).
Proof.
destruct wfenv_wftyp_EqU_aux as [H _].
intros. eapply H. eauto. auto.
Qed.

Lemma wftyp_UE :
  forall Γ₁ a Γ₂ τ, wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ -> wftyp (Γ₁ ++ a ~ E ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_UE_aux as [_ H].
intros. eapply H. eauto. auto.
Qed.

Lemma wftyp_EU :
  forall Γ₁ a Γ₂ τ, wftyp (Γ₁ ++ a ~ E ++ Γ₂) τ -> wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_EU_aux as [_ H].
intros. eapply H. eauto. auto.
Qed.

Lemma wftyp_EqU :
  forall Γ₁ a Γ₂ τ τ', wftyp (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ -> wftyp (Γ₁ ++ a ~ U ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_EqU_aux as [_ H].
intros. eapply H. eauto. auto.
Qed.

(** Lemmas about [wfeq] *)
Lemma wftypeq_wfenv : forall Γ τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → wfenv Γ.
Proof.
intros Γ τ₁ τ₂ H; induction H; auto.
Case "forall".
pick fresh a.
assert (wfenv (a ~ U ++ G)) as H1 by auto.
inversion H1; auto.
Case "exists".
pick fresh a.
assert (wfenv (a ~ U ++ G)) as H1 by auto.
inversion H1; auto.
Qed.

Lemma wftypeq_wftyp : forall Γ τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → wftyp Γ τ₁ ∧ wftyp Γ τ₂.
Proof.
intros Γ τ₁ τ₂ H; induction H; split; intuition; auto.
constructor; eauto.
eapply wfenv_wftyp_Eq2; eauto.
apply wftyp_forall with (L := L); firstorder.
apply wftyp_forall with (L := L); firstorder.
apply wftyp_exists with (L := L); firstorder.
apply wftyp_exists with (L := L); firstorder.
Qed.

Lemma wftypeq_wftyp_1 : forall Γ τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → wftyp Γ τ₁.
Proof.
intros Γ τ₁ τ₂ H. edestruct wftypeq_wftyp; eauto.
Qed.

Lemma wftypeq_wftyp_2 : forall Γ τ₁ τ₂,
  wftypeq Γ τ₁ τ₂ → wftyp Γ τ₂.
Proof.
intros Γ τ₁ τ₂ H. edestruct wftypeq_wftyp; eauto.
Qed.

Lemma wftypeq_refl : forall Γ τ, wftyp Γ τ →
  wftypeq Γ τ τ.
Proof.
intros Γ τ H; induction H; eauto.
Qed.

Lemma wftypeq_UE : forall Γ₁ a Γ₂ τ₁ τ₂,
  wftypeq (Γ₂ ++ a ~ U ++ Γ₁) τ₁ τ₂ →
  wftypeq (Γ₂ ++ a ~ E ++ Γ₁) τ₁ τ₂.
Proof.
intros Γ₁ a Γ₂ τ₁ τ₂ H. dependent induction H; auto.
Case "var". destruct (a == a0); subst.
SCase "a = a0". constructor; auto 6 using wfenv_UE.
SCase "a ≠ a0". constructor; auto 6 using wfenv_UE.
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto 6.
Case "eq".
constructor; auto using wfenv_UE.
analyze_binds H.
Case "forall".
apply wftypeq_forall with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₂) ++ a ~ E ++ Γ₁). auto.
Case "exists".
apply wftypeq_exists with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₂) ++ a ~ E ++ Γ₁). auto.
Case "trans". eauto.
Qed.

Lemma wftypeq_EU : forall Γ₁ a Γ₂ τ₁ τ₂,
  wftypeq (Γ₂ ++ a ~ E ++ Γ₁) τ₁ τ₂ →
  wftypeq (Γ₂ ++ a ~ U ++ Γ₁) τ₁ τ₂.
Proof.
intros Γ₁ a Γ₂ τ₁ τ₂ H. dependent induction H; auto.
Case "var". destruct (a == a0); subst.
SCase "a = a0". constructor; auto 6 using wfenv_EU.
SCase "a ≠ a0". constructor; auto 6 using wfenv_EU.
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto 6.
Case "eq".
constructor; auto using wfenv_EU.
analyze_binds H.
Case "forall".
apply wftypeq_forall with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₂) ++ a ~ U ++ Γ₁). auto.
Case "exists".
apply wftypeq_exists with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₂) ++ a ~ U ++ Γ₁). auto.
Case "trans". eauto.
Qed.

Lemma wftypeq_instantiate :
  forall Γ₁ Γ₂ τ₁ τ₂ a τ, wftypeq (Γ₁ ++ a ~ U ++ Γ₂) τ₁ τ₂ →
    wftyp Γ₂ τ → wftypeq (Γ₁ ++ a ~ Eq τ ++ Γ₂) τ₁ τ₂.
Proof.
intros Γ₁ Γ₂ τ₁ τ₂ a τ H. dependent induction H; intros; auto.
Case "var". constructor; auto.
destruct H. analyze_binds H; eauto 7.
destruct H. analyze_binds H.
destruct H. analyze_binds H; eauto 7.
Case "eq". analyze_binds H.
Case "forall". apply wftypeq_forall with (L := L); intros; auto.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ ++ Γ₂). auto.
Case "exists". apply wftypeq_exists with (L := L); intros; auto.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ ++ Γ₂). auto.
Case "trans". eauto.
Qed.

Lemma wftypeq_subst_eq :
  forall Γ₁ Γ₂ τ₁ τ₂ a τ, wftypeq (Γ₁ ++ a ~ Eq τ ++ Γ₂) τ₁ τ₂ →
    wftypeq (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂)
    ((tsubst_typ τ a) τ₁) ((tsubst_typ τ a) τ₂).
Proof.
intros Γ₁ Γ₂ τ₁ τ₂ a τ H.
dependent induction H; intros; try solve [simpl; auto].
Case "var". destruct (a == a0); subst.
SCase "a = a0". auto using wftypeq_refl, wftyp_subst_eq.
SCase "a ≠ a0". simpl; destruct (a == a0). contradiction.
destruct H. analyze_binds H. constructor; auto using wfenv_subst_eq.
replace (@U typ) with (tag_map (tsubst_typ τ a0) U) by reflexivity.
  unfold env_map. auto.
destruct H. analyze_binds H. constructor; auto using wfenv_subst_eq.
replace (@E typ) with (tag_map (tsubst_typ τ a0) E) by reflexivity.
  unfold env_map. auto.
destruct H. analyze_binds H.
  constructor; auto using wfenv_subst_eq.
  right; right; exists (tsubst_typ τ a0 x).
replace (Eq (tsubst_typ τ a0 x)) with (tag_map (tsubst_typ τ a0) (Eq x))
  by reflexivity.
  unfold env_map. auto.
  constructor; auto using wfenv_subst_eq.
  right; right; exists x. auto.
Case "eq". assert (uniq (Γ₁ ++ [(a0, Eq τ)] ++ Γ₂)) by auto.
analyze_binds_uniq H.
SCase "binds a Γ₁". assert (a ≠ a0) by auto. simpl; destruct (a == a0); try contradiction.
constructor; auto using wfenv_subst_eq.
replace (Eq (tsubst_typ τ a0 t)) with (tag_map (tsubst_typ τ a0) (Eq t)) by reflexivity.
unfold env_map. auto.
SCase "a = a0". assert (t = τ) by congruence; subst.
assert (a0 ∉ ftv_typ τ).
  apply wfenv_strip in H0. inversion H0; subst. apply wftyp_fv in H7. auto.
  assert (wftypeq (env_map (tsubst_typ τ a0) Γ₁ ++ Γ₂) (tsubst_typ τ a0 τ) (tsubst_typ τ a0 τ)).
  apply wftypeq_refl; apply wftyp_subst_eq; apply wfenv_wftyp_Eq2 with (x := a0); auto.
  autorewrite with lngen in *; auto.
SCase "binds a Γ₂". assert (a ≠ a0) by auto. simpl; destruct (a == a0); try contradiction.
constructor; auto using wfenv_subst_eq.
assert (a0 ∉ ftv_typ t).
assert (ftv_typ t [<=] dom Γ₂). apply wftyp_fv. apply wfenv_wftyp_Eq2 with (x := a); auto. apply wfenv_strip in H0. apply wfenv_strip in H0. auto.
solve_uniq.
autorewrite with lngen. auto.
Case "forall". simpl. apply wftypeq_forall with (L := L ∪ {{a}}); intros; auto.
replace (typ_var_f a0) with (tsubst_typ τ a (typ_var_f a0)).
 assert (lc_typ τ).
   apply wfenv_regular_Eq with
         (Γ := [(a0, U)] ++ Γ₁ ++ [(a, Eq τ)] ++ Γ₂) (x := a); auto.
   apply wftypeq_wfenv with (τ₁ := open_typ_wrt_typ t1 (typ_var_f a0))
                            (τ₂ := open_typ_wrt_typ t2 (typ_var_f a0)); auto.
 repeat rewrite <- tsubst_typ_open_typ_wrt_typ; auto.
 rewrite_env (env_map (tsubst_typ τ a) (a0 ~ U ++ Γ₁) ++ Γ₂). auto.
 assert (a0 ≠ a) by auto.
 simpl; unfold typvar. destruct (a0 == a); congruence.
Case "exists". simpl. apply wftypeq_exists with (L := L ∪ {{a}}); intros; auto.
replace (typ_var_f a0) with (tsubst_typ τ a (typ_var_f a0)).
 assert (lc_typ τ).
   apply wfenv_regular_Eq with
         (Γ := [(a0, U)] ++ Γ₁ ++ [(a, Eq τ)] ++ Γ₂) (x := a); auto.
   apply wftypeq_wfenv with (τ₁ := open_typ_wrt_typ t1 (typ_var_f a0))
                            (τ₂ := open_typ_wrt_typ t2 (typ_var_f a0)); auto.
 repeat rewrite <- tsubst_typ_open_typ_wrt_typ; auto.
 rewrite_env (env_map (tsubst_typ τ a) (a0 ~ U ++ Γ₁) ++ Γ₂). auto.
 assert (a0 ≠ a) by auto.
 simpl; unfold typvar. destruct (a0 == a); congruence.
Case "trans". eauto.
Qed.

Lemma wftypeq_tsubst :
  forall Γ₁ Γ₂ τ₁ τ₂ a τ, wftypeq (Γ₁ ++ a ~ U ++ Γ₂) τ₁ τ₂ →
    wftyp Γ₂ τ →
    wftypeq (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂)
    ((tsubst_typ τ a) τ₁) ((tsubst_typ τ a) τ₂).
Proof.
auto using wftypeq_instantiate, wftypeq_subst_eq.
Qed.

Lemma wftypeq_subst :
  forall Γ₁ Γ₂ τ₁ τ₂ x τ, wftypeq (Γ₁ ++ x ~ T τ ++ Γ₂) τ₁ τ₂ →
    wftypeq (Γ₁ ++ Γ₂) τ₁ τ₂.
Proof.
intros Γ₁ Γ₂ τ₁ τ₂ x τ H.
dependent induction H.
Case "var". constructor. 
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. right; right; exists x0. analyze_binds H.
eapply wfenv_subst; eauto.
Case "eq". constructor.
analyze_binds H. eapply wfenv_subst; eauto.
Case "arrow". constructor; eauto.
Case "prod". constructor; eauto.
Case "forall". apply wftypeq_forall with (L := L); intros.
rewrite_env ((a ~ U ++ Γ₁) ++ Γ₂).
 eapply H0; simpl_env; auto.
Case "exists". apply wftypeq_exists with (L := L); intros.
rewrite_env ((a ~ U ++ Γ₁) ++ Γ₂).
 eapply H0; simpl_env; auto.
Case "sym". eauto.
Case "trans". eauto.
Qed.

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
apply wfenv_wftyp_mut_ind; intros; subst.
Case "nil".
assert (binds x (T τ₁) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor; auto. eapply wftypeq_wftyp_2; eauto.
constructor; auto. eapply H; eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor; auto. eapply H; eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor; auto. eapply H; eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor; auto. eapply H; eauto.
Case "var". constructor.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0.
destruct H0. right; right; exists x0. analyze_binds H0.
eapply H; eauto.
Case "arrow". constructor. eapply H; eauto. eapply H0; eauto.
Case "prod". constructor. eapply H; eauto. eapply H0; eauto.
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
apply wfenv_wftyp_mut_ind; intros; subst.
Case "nil".
assert (binds a (Eq τ₁) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor; auto. eapply H; eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor; auto. eapply H; eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor; auto. eapply H; eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor; auto. eapply wftypeq_wftyp_2; eauto.
constructor; auto. eapply H; eauto.
Case "var". constructor.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0.
destruct H0. right; right. analyze_binds H0; eauto.
eapply H; eauto.
Case "arrow". constructor. eapply H; eauto. eapply H0; eauto.
Case "prod". constructor. eapply H; eauto. eapply H0; eauto.
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
destruct H. right; right. analyze_binds H; eauto.
Case "forall".
apply wftypeq_forall with (L := L ∪ dom Γ₂); intros.
rewrite_env ((a~U ++ Γ₁) ++ Γ₂ ++ Γ₃); apply H0; eauto.
Case "exists".
apply wftypeq_exists with (L := L ∪ dom Γ₂); intros.
rewrite_env ((a~U ++ Γ₁) ++ Γ₂ ++ Γ₃); apply H0; eauto.
Case "trans". eauto.
Qed.

Lemma wftypeq_wftypeq :
  forall Γ₁ Γ₂ τ₁ τ₂ a τ τ', wftypeq (Γ₁ ++ a ~ Eq τ ++ Γ₂) τ₁ τ₂ →
    wftypeq Γ₂ τ τ' →
    wftypeq (Γ₁ ++ a ~ Eq τ' ++ Γ₂) τ₁ τ₂.
Proof.
intros Γ₁ Γ₂ τ₁ τ₂ a τ τ' H H0. dependent induction H.
Case "var". constructor.
destruct H. analyze_binds H.
destruct H. analyze_binds H.
destruct H. right; right. analyze_binds H; eauto.
eapply wfenv_wftypeq_Eq; eauto.
Case "eq". analyze_binds H.
constructor; auto. eapply wfenv_wftypeq_Eq; eauto.
replace t with τ by congruence. apply wftypeq_trans with (t2 := τ').
constructor; auto. eapply wfenv_wftypeq_Eq; eauto. apply wftypeq_sym.
rewrite_env (nil ++ (Γ₁ ++ a0 ~ Eq τ') ++ Γ₂). apply wftypeq_weakening; simpl_env in *; auto.
eapply wfenv_wftypeq_Eq; eauto.
constructor; auto. eapply wfenv_wftypeq_Eq; eauto.
Case "arrow". constructor; eauto.
Case "prod". constructor; eauto.
Case "forall". apply wftypeq_forall with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ' ++ Γ₂). eapply H0; eauto.
Case "exists". apply wftypeq_exists with (L := L); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ a ~ Eq τ' ++ Γ₂). eapply H0; eauto.
Case "sym". eauto.
Case "trans". eauto.
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
apply wfenv_wftyp_mut_ind; intros; subst; simpl; simpl_env.
Case "nil".
assert (binds a (@E typ) nil) as H1. rewrite H; auto.
analyze_binds H1.
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *.
simpl; simpl_env.
constructor. unfold env_map; auto. eapply H; eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *.
simpl; simpl_env.
constructor. unfold env_map; auto. eapply H; eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor; auto.
simpl; simpl_env.
constructor. unfold env_map; auto. eapply H; eauto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *.
simpl; simpl_env.
constructor. unfold env_map; auto. eapply H; eauto.
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
Case "arrow". constructor. eapply H; eauto. eapply H0; eauto.
Case "prod". constructor. eapply H; eauto. eapply H0; eauto.
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
Case "T". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor. auto. eapply H; eauto.
Case "U". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor. auto. eapply H; eauto.
Case "E". destruct Γ₁; inversion H0; subst; simpl_env in *.
eapply wfenv_weakening; auto. apply wfenv_strip in w; auto.
constructor; auto.
Case "Eq". destruct Γ₁; inversion H0; subst; simpl_env in *.
constructor. auto. eapply H; eauto.
Case "var". constructor; simpl_env in *; auto 6.
destruct o. analyze_binds H0.
destruct H0. analyze_binds H0; auto 7.
destruct H0. right; right.
  analyze_binds H0; eauto.
Case "forall". apply wftyp_forall with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ Γ₂ ++ a ~ E ++ Γ₃).
eapply H; auto.
Case "exists". apply wftyp_exists with (L := L ∪ {{a}}); intros.
rewrite_env ((a0 ~ U ++ Γ₁) ++ Γ₂ ++ a ~ E ++ Γ₃).
eapply H; auto.
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

(** Lemmas about [zip] *)
Lemma zip_dom1 :
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
  dom Γ₁ [<=] dom Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; simpl in *; fsetdec.
Qed.

Lemma zip_dom2 :
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
  dom Γ₂ = dom Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; simpl in *; congruence.
Qed.

Lemma zip_dom3 :
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
  dom Γ₁ [<=] dom Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ H. rewrite (zip_dom2 Γ₁ Γ₂ Γ₃); auto. eapply zip_dom1; eauto.
Qed.

Lemma zip_binds_T12 :
  forall Γ₁ Γ₂ Γ₃ x τ, zip Γ₁ Γ₂ Γ₃ →
    binds x (T τ) Γ₁ → binds x (T τ) Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ x τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_T13 :
  forall Γ₁ Γ₂ Γ₃ x τ, zip Γ₁ Γ₂ Γ₃ →
    binds x (T τ) Γ₁ → binds x (T τ) Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ x τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_T23 :
  forall Γ₁ Γ₂ Γ₃ x τ, zip Γ₁ Γ₂ Γ₃ →
    binds x (T τ) Γ₂ → binds x (T τ) Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ x τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_Eq12 :
  forall Γ₁ Γ₂ Γ₃ a τ, zip Γ₁ Γ₂ Γ₃ →
    binds a (Eq τ) Γ₁ → binds a (Eq τ) Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_Eq13 :
  forall Γ₁ Γ₂ Γ₃ a τ, zip Γ₁ Γ₂ Γ₃ →
    binds a (Eq τ) Γ₁ → binds a (Eq τ) Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_Eq23 :
  forall Γ₁ Γ₂ Γ₃ a τ, zip Γ₁ Γ₂ Γ₃ →
    binds a (Eq τ) Γ₂ → binds a (Eq τ) Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_E12 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a E Γ₁ → binds a U Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_E13 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a E Γ₁ → binds a E Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_E23 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a E Γ₂ → binds a E Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_U12 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a U Γ₁ → binds a U Γ₂ ∨ binds a E Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0; intuition].
Qed.

Lemma zip_binds_U13 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a U Γ₁ → binds a U Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_U23 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a U Γ₂ → binds a U Γ₃ ∨ binds a E Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0; intuition].
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
inversion H1; inversion H2; subst; auto.
constructor; auto.
  erewrite <- zip_dom2; eauto.
  rewrite_env (nil ++ G); auto.
Case "wftype_T".
rewrite_env ((Γ ++ [(x, T t)]) ++ G); apply IHzip2; simpl_env; auto.
Case "wfenv_U".
inversion H0; inversion H1; subst; auto.
constructor; auto.
  erewrite <- zip_dom2; eauto.
Case "wftype_U".
rewrite_env ((Γ ++ [(a, U)]) ++ G); apply IHzip2; simpl_env; auto.
Case "wfenv_E".
inversion H0; inversion H1; subst; auto.
constructor; auto.
  erewrite <- zip_dom2; eauto.
Case "wftype_E".
rewrite_env ((Γ ++ [(a, E)]) ++ G); apply IHzip2; simpl_env; auto using wftyp_UE.
Case "wfenv_E".
inversion H2; subst. constructor; auto. erewrite <- zip_dom2; eauto.
Case "wftyp_E".
rewrite_env ((Γ ++ [(a, E)]) ++ G); apply IHzip2; simpl_env; auto.
apply wftyp_weakening; auto.
  constructor; auto. apply wfenv_strip with (Γ' := Γ); auto.
  eauto.
  apply uniq_app_3; apply uniq_app_1 with (F := G2); simpl_env; eauto. 
Case "wfenv_Eq".
inversion H1; inversion H2; subst; auto.
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
intros Γ₁ Γ₂ Γ₃ H H0 H1.
destruct (wfenv_wftyp_zip_aux Γ₁ Γ₂ Γ₃ H) as [? _].
auto.
Qed.

Lemma wftyp_zip:
  forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₁ τ -> wftyp Γ₂ τ -> wftyp Γ₃ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ τ H H0 H1.
destruct (wfenv_wftyp_zip_aux Γ₁ Γ₂ Γ₃ H) as [_ ?].
rewrite_env (nil ++ Γ₃). auto.
Qed.

Lemma wftyp_zip12:
  forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₁ τ -> wfenv Γ₂ → wftyp Γ₂ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ τ H H0. generalize dependent Γ₃. generalize dependent Γ₂.
induction H0; intros; auto.
Case "var". constructor; auto.
destruct H. eapply zip_binds_U12 in H; eauto. tauto.
destruct H. eapply zip_binds_E12 in H; eauto.
destruct H. eapply zip_binds_Eq12 in H; eauto.
Case "arrow". constructor; [eapply IHwftyp1 | eapply IHwftyp2]; eauto.
Case "prod". constructor; [eapply IHwftyp1 | eapply IHwftyp2]; eauto.
Case "forall". apply wftyp_forall with (L := L ∪ dom Γ₂); intros; auto.
eapply H0; auto. constructor; eauto.
Case "exists". apply wftyp_exists with (L := L ∪ dom Γ₂); intros; auto.
eapply H0; auto. constructor; eauto.
Qed.

Lemma wftyp_zip13:
  forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₁ τ -> wfenv Γ₂ → wftyp Γ₃ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ τ H H0. generalize dependent Γ₃. generalize dependent Γ₂.
induction H0; intros; auto.
Case "var". constructor; auto.
destruct H. eapply zip_binds_U13 in H; eauto.
destruct H. eapply zip_binds_E13 in H; eauto.
destruct H. eapply zip_binds_Eq13 in H; eauto.
eapply wfenv_zip; eauto.
Case "arrow". constructor; [eapply IHwftyp1 | eapply IHwftyp2]; eauto.
Case "prod". constructor; [eapply IHwftyp1 | eapply IHwftyp2]; eauto.
Case "forall". apply wftyp_forall with (L := L ∪ dom Γ₂); intros; auto.
eapply H0; auto. constructor; eauto. constructor; auto.
Case "exists". apply wftyp_exists with (L := L ∪ dom Γ₂); intros; auto.
eapply H0; auto. constructor; eauto. constructor; auto.
Qed.

Lemma wftyp_zip23:
  forall Γ₁ Γ₂ Γ₃ τ, zip Γ₁ Γ₂ Γ₃ ->
    wftyp Γ₂ τ -> wfenv Γ₁ → wftyp Γ₃ τ.
Proof.
intros Γ₁ Γ₂ Γ₃ τ H H0. generalize dependent Γ₃. generalize dependent Γ₁.
induction H0; intros; auto.
Case "var". constructor; auto.
destruct H. eapply zip_binds_U23 in H; eauto. tauto.
destruct H. eapply zip_binds_E23 in H; eauto.
destruct H. eapply zip_binds_Eq23 in H; eauto.
eapply wfenv_zip; eauto.
Case "arrow". constructor; [eapply IHwftyp1 | eapply IHwftyp2]; eauto.
Case "prod". constructor; [eapply IHwftyp1 | eapply IHwftyp2]; eauto.
Case "forall". apply wftyp_forall with (L := L ∪ dom Γ₁); intros; auto.
eapply H0; auto. constructor; eauto. constructor; auto.
Case "exists". apply wftyp_exists with (L := L ∪ dom Γ₁); intros; auto.
eapply H0; auto. constructor; eauto. constructor; auto.
Qed.

(** Lemmas about [wfterm] *)
Lemma wfterm_wfenv : forall Γ e τ,
  wfterm Γ e τ → wfenv Γ.
Proof.
intros Γ e τ H.
induction H; auto; try solve [eapply wfenv_zip; eauto].
Case "lam".
pick fresh x. apply wfenv_strip with (Γ' := x ~ T t1). auto.
Case "gen".
pick fresh a. apply wfenv_strip with (Γ' := a ~ U). auto.
Case "exists".
pick fresh a. apply wfenv_strip with (Γ' := a ~ E). auto.
Case "open".
apply wfenv_weakening; auto. constructor; auto.
  eapply wfenv_strip; eauto.
Case "nu".
pick fresh a. apply wfenv_strip with (Γ' := a ~ E). auto.
Case "sigma".
pick fresh a.
assert (wfenv (G2 ++ G1)).
  apply wfenv_strip with (Γ' := [(a, Eq t')]). auto.
apply wfenv_weakening; auto.
constructor; auto. apply wfenv_strip with (Γ' := G2). auto.
Qed.
Hint Resolve wfterm_wfenv.

Lemma wfterm_wftyp : forall Γ e τ,
  wfterm Γ e τ → wftyp Γ τ.
Proof.
intros Γ e τ H.
induction H.
Case "var". eapply wfenv_wftyp_T2; eauto.
Case "app". inversion IHwfterm1; subst; auto.
  eapply wftyp_zip13. eauto. auto. eapply wfterm_wfenv; eauto.
Case "abs". pick fresh x. assert ([(x, T t1)] ++ G ⊢ t2 ok) by auto.
assert (wfenv ([(x, T t1)] ++ G)) by eauto.
inversion H3; subst.
rewrite_env (nil ++ x ~ T t1 ++ G) in H2.
apply wftyp_subst in H2; simpl_env in H2.
auto.
Case "pair". constructor.
eapply wftyp_zip13. eauto. auto. eapply wftyp_wfenv; eauto.
eapply wftyp_zip23. eauto. auto. eapply wftyp_wfenv; eauto.
Case "projL". inversion IHwfterm; subst; auto.
Case "projR". inversion IHwfterm; subst; auto.
Case "inst". inversion IHwfterm; subst.
pick fresh a. rewrite tsubst_typ_intro with (a1 := a); auto.
rewrite_env (env_map (tsubst_typ t a) nil ++ G).
apply wftyp_tsubst; simpl_env; auto.
Case "gen". apply wftyp_forall with (L := L); auto.
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
  constructor; auto. apply wfenv_strip with (Γ' := a ~ E). eapply wftyp_wfenv; eauto.
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
Case "coerce". eapply wftypeq_wftyp_2; eauto.
Qed.
Hint Resolve wfterm_wftyp.

Lemma wfterm_regular2 : forall Γ e τ,
  wfterm Γ e τ → lc_typ τ.
Proof.
intros Γ e τ H; eauto.
Qed.
Hint Resolve wfterm_regular2.

Lemma wfterm_regular1 : forall Γ e τ,
  wfterm Γ e τ → lc_term e.
Proof.
intros Γ e τ H; induction H; auto.
Case "abs". pick fresh x.
apply lc_term_abs_exists with (x1 := x); auto.
apply wfenv_regular_T with (Γ := [(x, T t1)] ++ G) (x := x); eauto.
Case "inst". apply wftyp_regular in H; auto.
Case "sigma". pick fresh a.
apply lc_term_sigma_exists with (a1 := a); auto.
apply wfenv_regular_Eq with (Γ := [(a, Eq t')] ++ G2 ++ G1) (x := a); eauto.
Case "coerce". apply wftypeq_wftyp_2 in H. apply wftyp_regular in H. auto.
Qed.
Hint Resolve wfterm_regular1.

Lemma wfterm_env_uniq : forall Γ e τ,
  wfterm Γ e τ → uniq Γ.
Proof.
intros Γ e τ H. eauto.
Qed.
Hint Resolve wfterm_env_uniq.

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
Lemma wfterm_fv : forall Γ e τ,
  wfterm Γ e τ → fv_term e [<=] dom Γ.
Proof.
intros Γ e τ H. induction H; simpl fv_term in *; repeat rewrite dom_app in *;
try solve [fsetdec].
Case "var". assert (x ∈ dom G) by eauto; fsetdec.
Case "app".
assert (dom G1 [<=] dom G). eapply zip_dom1; eauto.
assert (dom G2 [=] dom G). rewrite zip_dom2 with (Γ₁ := G1) (Γ₃ := G); auto; fsetdec.
fsetdec.
Case "lam". pick fresh x. 
assert (fv_term (e ^ x) [<=] dom (x ~ T t1 ++ G)) by auto.
assert (fv_term e [<=] fv_term (e ^ x)) by auto with lngen.
assert (fv_term e [<=] {{x}} ∪ dom G). simpl in *; fsetdec.
fsetdec.
Case "pair".
assert (dom G1 [<=] dom G). eapply zip_dom1; eauto.
assert (dom G2 [=] dom G). rewrite zip_dom2 with (Γ₁ := G1) (Γ₃ := G); auto; fsetdec.
fsetdec.
Case "gen". pick fresh a. 
assert (fv_term (open_term_wrt_typ e (typ_var_f a)) [<=] dom (a ~ U ++ G)) by auto.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
assert (fv_term e [<=] {{a}} ∪ dom G). simpl in *; fsetdec.
fsetdec.
Case "exists". pick fresh a. 
assert (fv_term (open_term_wrt_typ e (typ_var_f a)) [<=] dom (a ~ E ++ G)) by auto.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
assert (fv_term e [<=] {{a}} ∪ dom G). simpl in *; fsetdec.
fsetdec.
Case "nu". pick fresh a. 
assert (fv_term (open_term_wrt_typ e (typ_var_f a)) [<=] dom (a ~ E ++ G)) by auto.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
assert (fv_term e [<=] {{a}} ∪ dom G). simpl in *; fsetdec.
fsetdec.
Case "sigma". pick fresh a.
assert (fv_term (open_term_wrt_typ e (typ_var_f a)) [<=] dom (a ~ Eq t' ++ G2 ++ G1)) by auto.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
assert (fv_term e [<=] {{a}} ∪ dom G2 ∪ dom G1). repeat rewrite dom_app in *.
simpl in *. transitivity (add a empty∪dom G2∪dom G1). fsetdec. ICI fsetdec.
fsetdec.

Qed.

Lemma wfterm_uniqueness : forall Γ e τ τ',
  wfterm Γ e τ → wfterm Γ e τ' → τ = τ'.
Proof.
intros Γ e τ τ' H1 H2. generalize dependent τ'.
induction H1; intros τ' H2; inversion H2; subst.
Case "var".
assert (T t = T τ'). eapply binds_unique; eauto. congruence.
Case "app".
assert (typ_arrow t2 t1 = typ_arrow t3 τ') by auto; congruence.
Case "abs".
pick fresh x; assert (t2 = t3) by eauto; congruence.
Case "inst".
assert (typ_forall t' = typ_forall t'0) by auto; congruence.
Case "gen".
pick fresh a. assert (open_typ_wrt_typ t (typ_var_f a) = open_typ_wrt_typ t0 (typ_var_f a)) by auto.
f_equal; eapply open_typ_wrt_typ_inj; eauto.
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

(** Major lemmas about [wfterm] *)
Lemma wfterm_weakening : forall Γ₁ Γ₂ Γ₃ e τ,
  wfterm (Γ₁ ++ Γ₃) e τ →
  wfenv (Γ₂ ++ Γ₃) →
  disjoint Γ₁ Γ₂ →
  wfterm (Γ₁ ++ Γ₂ ++ Γ₃) e τ.
Proof.
intros Γ₁ Γ₂ Γ₃ e τ H. dependent induction H; intros; eauto.
Case "var".
constructor. auto using wfenv_weakening. analyze_binds H0.
Case "abs". pick fresh x and apply wfterm_abs.
rewrite_env (([(x, T t1)] ++ Γ₁) ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto.
Case "inst". constructor. auto using wftyp_weakening. eauto.
Case "gen". pick fresh a and apply wfterm_gen.
rewrite_env (([(a, None)] ++ Γ₁) ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto.
Qed.

Lemma wfterm_subst : forall Γ₁ Γ₂ x τ₁ τ₂ e₁ e₂,
  wfterm (Γ₁ ++ x ~ T τ₂ ++ Γ₂) e₁ τ₁ →
  wfterm Γ₂ e₂ τ₂ →
  wfterm (Γ₁ ++ Γ₂) (subst_term e₂ x e₁) τ₁.
Proof with eauto.
intros Γ₁ Γ₂ x τ₁ τ₂ e₁ e₂ H. dependent induction H; intro; simpl...
Case "var".
  destruct (x == x0); subst.
  SCase "x = x0".
    analyze_binds_uniq H0; apply wfterm_weakening with (Γ₁ := nil); auto.
    replace t with τ₂ by congruence; auto.
    eapply wfenv_subst; eauto.
  SCase "x <> x0".
    analyze_binds_uniq H0...
Case "abs".
  pick fresh z and apply wfterm_abs.
  rewrite_env ((z ~ T t1 ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_term_var...
  apply H0 with (τ₂0 := τ₂)...
Case "gen".
  pick fresh a and apply wfterm_gen.
  rewrite_env ((a ~ None ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_typ_var...
  apply H0 with (τ₂0 := τ₂)...
Qed.

Lemma wfterm_tsubst : forall Γ₁ Γ₂ a τ₁ e₁ τ₂,
  wfterm (Γ₁ ++ a ~ None ++ Γ₂) e₁ τ₁ →
  wftyp Γ₂ τ₂ →
  wfterm (env_map (tsubst_typ τ₂ a) Γ₁ ++ Γ₂) (tsubst_term τ₂ a e₁) (tsubst_typ τ₂ a τ₁).
Proof with eauto.
intros Γ₁ Γ₂ a τ₁ e₁ τ₂ H. dependent induction H; intro; simpl...
Case "var".
constructor. auto using wfenv_tsubst.
replace (T (tsubst_typ τ₂ a t)) with (tag_map (tsubst_typ τ₂ a) (T t)) by reflexivity.
unfold env_map. analyze_binds H0.
simpl.
assert (a ∉ ftv_typ t).
  assert (ftv_typ t [<=] dom Γ₂) by eauto.
  assert (uniq (Γ₁ ++ [(a, None)] ++ Γ₂)) by auto.
  destruct_uniq. fsetdec.
autorewrite with lngen; auto.
Case "app".
econstructor.
eapply IHwfterm1; auto.
eapply IHwfterm2; auto.
Case "abs".
  pick fresh z and apply wfterm_abs.
  rewrite_env (env_map (tsubst_typ τ₂ a) ([(z, T t1)] ++ Γ₁) ++ Γ₂).
  rewrite tsubst_term_open_term_wrt_term_var...
Case "inst".
  rewrite tsubst_typ_open_typ_wrt_typ...
  constructor; auto. apply IHwfterm; auto.
Case "gen".
  pick fresh b and apply wfterm_gen.
  rewrite_env (env_map (tsubst_typ τ₂ a) ([(b, None)] ++ Γ₁) ++ Γ₂).
  rewrite tsubst_term_open_term_wrt_typ_var...
  rewrite tsubst_typ_open_typ_wrt_typ_var...
Qed.

(** Soundness *)
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
