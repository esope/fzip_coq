Add LoadPath "metatheory".
Require Export F_init.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_term x) in
  let D2 := gather_atoms_with (fun x => ftv_typ x) in
  let D3 := gather_atoms_with (fun x => ftv_term x) in
  constr:(A \u B \u C \u D1 \u D2 \u D3).

(** Mutual induction principles *)
Scheme pval_mut_ind_aux := Induction for pval Sort Prop
with   val_mut_ind_aux  := Induction for val  Sort Prop.
Combined Scheme pval_val_mut_ind from pval_mut_ind_aux, val_mut_ind_aux.

Scheme wfenv_mut_ind_aux := Induction for wfenv Sort Prop
with   wftyp_mut_ind_aux := Induction for wftyp Sort Prop.
Combined Scheme wfenv_wftyp_mut_ind from
  wfenv_mut_ind_aux, wftyp_mut_ind_aux.

(** Administrative lemmas *)
Lemma pval_val_regular :
  (forall p, pval p → lc_term p) ∧ (forall v, val v → lc_term v).
Proof.
apply pval_val_mut_ind; eauto.
Qed.

Lemma pval_regular : forall p, pval p → lc_term p.
Proof.
intros; destruct pval_val_regular as [H1 _]; auto.
Qed.

Lemma val_regular : forall v, val v → lc_term v.
Proof.
intros; destruct pval_val_regular as [_ H2]; auto.
Qed.
Hint Resolve pval_regular val_regular.

Lemma red0_regular1 : forall e e', red0 e e' → lc_term e.
Proof.
intros e e' H. destruct H; auto.
Qed.

Lemma red0_regular2 : forall e e', red0 e e' → lc_term e'.
Proof.
intros e e' H; destruct H; eauto with lngen.
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
  (forall Γ, wfenv Γ → forall Γ₁ x τ, Γ = x ~ (Some τ) ++ Γ₁ → wftyp Γ₁ τ) ∧
  (forall Γ τ, wftyp Γ τ → wfenv Γ).
Proof.
apply wfenv_wftyp_mut_ind; intros; eauto.
inversion H.
inversion H0; subst; auto.
inversion H0.
pick fresh a; assert (a ~ None ++ G ⊢ ok) by auto; inversion H0; subst; auto.
Qed.

Lemma wfenv_wftyp :
forall Γ₁ Γ₂ x τ, wfenv (Γ₁ ++ x ~ Some τ ++ Γ₂) → wftyp Γ₂ τ.
Proof.
destruct wfenv_wftyp_aux as [H1 H2].
intros Γ₁ Γ₂ x τ H0.
generalize dependent Γ₂.
induction Γ₁; intros; simpl_env in H0; eauto.
inversion H0; subst; simpl_env in H5; eauto.
Qed.
Hint Resolve wfenv_wftyp.

Lemma wftyp_wfenv : forall Γ τ, wftyp Γ τ → wfenv Γ.
Proof.
destruct wfenv_wftyp_aux; auto.
Qed.
Hint Resolve wftyp_wfenv.

Lemma wfenv_wftyp_uniq_aux :
  (forall Γ, wfenv Γ → uniq Γ) ∧ (forall Γ τ, wftyp Γ τ → uniq Γ).
Proof.
apply wfenv_wftyp_mut_ind; intros; auto.
pick fresh a. assert (uniq (a ~ None ++ G)) by auto. destruct_uniq; auto.
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
Case "wfenv_cons_x".
destruct Γ₁; simpl_env in *.
destruct Γ₃; simpl_env in *; auto.
inversion H0; subst.
apply wfenv_cons_x.
simpl in H2; apply disjoint_cons_1 in H2; auto.
apply H; auto.
simpl in H2; apply disjoint_cons_2 in H2; auto.
Case "wfenv_cons_a".
destruct Γ₁; simpl_env in *.
destruct Γ₃; simpl_env in *; auto.
inversion H0; subst.
apply wfenv_cons_a.
simpl in H2; apply disjoint_cons_1 in H2; auto.
apply H; auto.
simpl in H2; apply disjoint_cons_2 in H2; auto.
Case "wftyp_var".
subst G; analyze_binds b.
Case "wftyp_forall".
subst G; apply wftyp_forall with (L := L ∪ dom Γ₂); intros.
rewrite_env ((a~None ++ Γ₁) ++ Γ₂ ++ Γ₃); apply H; eauto.
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

Lemma wfenv_wftyp2 :
forall Γ x τ, wfenv Γ → binds x (Some τ) Γ → wftyp Γ τ.
Proof.
intro Γ; induction Γ; intros.
analyze_binds H0.
destruct a; destruct o; simpl_env in *; analyze_binds H0.
replace t with τ in * by congruence.
rewrite_env (nil ++ a ~ Some τ ++ Γ).
inversion H; subst.
apply wftyp_weakening; auto.
rewrite_env (nil ++ a ~ Some t ++ Γ).
apply wftyp_weakening; auto. simpl.
inversion H; subst. eapply IHΓ; eauto.
rewrite_env (nil ++ a ~ None ++ Γ).
apply wftyp_weakening; auto.
inversion H; subst. eapply IHΓ; eauto.
Qed.
Hint Resolve wfenv_wftyp2.

Lemma wfenv_wftyp3 :
forall Γ x τ, wfenv (x ~ Some τ ++ Γ) → wftyp Γ τ.
Proof.
intros Γ x τ H; inversion H; subst; auto.
Qed.
Hint Resolve wfenv_wftyp3.

Lemma wfenv_regular :
forall Γ x τ, wfenv Γ → binds x (Some τ) Γ → lc_typ τ.
Proof.
intros. induction H; analyze_binds H0.
replace t with τ in * by congruence; eauto.
eauto.
Qed.
Hint Resolve wfenv_regular.

Lemma wftyp_regular2 : forall Γ x τ τ',
  wftyp (x ~ Some τ ++ Γ) τ' → lc_typ τ.
Proof.
intros Γ x τ τ' H. eauto.
Qed.
Hint Resolve wftyp_regular2.

Lemma wfenv_wftyp_subst :
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ x τ, Γ = Γ₁ ++ x ~ (Some τ) ++ Γ₂ → wfenv (Γ₁ ++ Γ₂)) ∧
  (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ x τ', Γ = Γ₁ ++ x ~ (Some τ') ++ Γ₂ → wftyp (Γ₁ ++ Γ₂) τ).
Proof.
apply wfenv_wftyp_mut_ind; intros.
Case "wfenv_empty".
assert (binds x (Some τ) nil). rewrite H; auto. analyze_binds H0.
Case "wfenv_cons_x".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
destruct p; destruct o; inversion H0; subst; simpl_env in *.
constructor; eauto.
Case "wfenv_cons_a".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
destruct p; destruct o; inversion H0; subst; simpl_env in *.
constructor; eauto.
Case "wftyp_var".
subst G. constructor. analyze_binds b. eauto.
Case "wftyp_arrow".
subst G. constructor; eauto.
Case "wftyp_forall".
subst G. econstructor; intros.
rewrite_env (([(a, None)] ++ Γ₁) ++ Γ₂). eapply H; simpl_env; eauto.
Qed.

Lemma wfenv_subst :
forall Γ₁ Γ₂ x τ, wfenv (Γ₁ ++ x ~ (Some τ) ++ Γ₂) → wfenv (Γ₁ ++ Γ₂).
Proof.
destruct wfenv_wftyp_subst as [H1 H2].
intros Γ₁ Γ₂ x τ H. eapply H1; eauto.
Qed.
Hint Resolve wfenv_subst.

Lemma wftyp_subst :
forall Γ₁ Γ₂ τ x τ', wftyp (Γ₁ ++ x ~ (Some τ') ++ Γ₂) τ → wftyp (Γ₁ ++ Γ₂) τ.
Proof.
destruct wfenv_wftyp_subst as [H1 H2].
intros. eapply H2; eauto.
Qed.
Hint Resolve wftyp_subst.

Lemma wfenv_wftyp_tsubst :
  (forall Γ, wfenv Γ → forall Γ₁ Γ₂ a τ, Γ = Γ₁ ++ a ~ None ++ Γ₂ → wftyp Γ₂ τ → wfenv ((env_map (tsubst_typ τ a) Γ₁) ++ Γ₂)) ∧
  (forall Γ τ, wftyp Γ τ → forall Γ₁ Γ₂ a τ', Γ = Γ₁ ++ a ~ None ++ Γ₂ → wftyp Γ₂ τ' → wftyp ((env_map (tsubst_typ τ' a) Γ₁) ++ Γ₂) (tsubst_typ τ' a τ)).
Proof.
apply wfenv_wftyp_mut_ind; intros.
Case "wfenv_empty".
assert (binds a (@None typ) nil). rewrite H; auto. analyze_binds H1.
Case "wfenv_cons_x".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
destruct p; destruct o; inversion H0; subst; simpl_env in *.
simpl; simpl_env.
constructor. unfold env_map; auto. eapply H; auto.
Case "wfenv_cons_a".
destruct Γ₁; simpl_env in *.
inversion H0; subst; eauto.
destruct p; destruct o; inversion H0; subst; simpl_env in *.
simpl; simpl_env.
constructor. unfold env_map; auto. eapply H; auto.
Case "wftyp_var".
subst G. simpl.
destruct (a == a0); subst.
rewrite_env (nil ++ env_map (tsubst_typ τ' a0) Γ₁ ++ Γ₂); apply wftyp_weakening; auto.
constructor; auto.
analyze_binds b;
replace (@None typ) with (option_map (tsubst_typ τ' a0) None) by reflexivity;
unfold env_map; auto.
Case "wftyp_arrow".
subst G. simpl; constructor; auto.
Case "wftyp_forall".
subst G. simpl; apply wftyp_forall with (L := L ∪ {{a}}); intros.
rewrite_env (([(a0, None)] ++ env_map (tsubst_typ τ' a) Γ₁) ++ Γ₂).
replace ([(a0, None)] ++ env_map (tsubst_typ τ' a) Γ₁) with (env_map (tsubst_typ τ' a) ([(a0, None)] ++ Γ₁)) by reflexivity.
replace (typ_var_f a0) with (tsubst_typ τ' a (typ_var_f a0)).
rewrite <- tsubst_typ_open_typ_wrt_typ.
eapply H; simpl_env; eauto. eauto.
autorewrite with lngen; auto.
Qed.

Lemma wfenv_tsubst :
  forall Γ₁ Γ₂ a τ, wfenv (Γ₁ ++ a ~ None ++ Γ₂) → wftyp Γ₂ τ →
    wfenv (env_map (tsubst_typ τ a) Γ₁ ++ Γ₂).
Proof.
destruct wfenv_wftyp_tsubst as [H1 H2].
intros Γ₁ Γ₂ x τ H. eapply H1; eauto.
Qed.
Hint Resolve wfenv_tsubst.

Lemma wftyp_tsubst :
forall Γ₁ Γ₂ τ a τ', wftyp (Γ₁ ++ a ~ None ++ Γ₂) τ →
wftyp Γ₂ τ' → wftyp (env_map (tsubst_typ τ' a) Γ₁ ++ Γ₂) (tsubst_typ τ' a τ).
Proof.
destruct wfenv_wftyp_tsubst as [H1 H2].
intros. eapply H2; eauto.
Qed.
Hint Resolve wftyp_tsubst.

Lemma wftyp_fv : forall Γ τ, wftyp Γ τ → ftv_typ τ [<=] dom Γ.
Proof.
intros Γ τ H. induction H; simpl in *; try fsetdec.
assert (a ∈ dom G) by eauto; fsetdec.
pick fresh a.
assert (ftv_typ (open_typ_wrt_typ t (typ_var_f a))[<=]add a (dom G)) by auto.
assert (ftv_typ t [<=] ftv_typ (open_typ_wrt_typ t (typ_var_f a))); auto with lngen.
fsetdec.
Qed.
Hint Resolve wftyp_fv.

(** Lemmas about [wfterm] *)
Lemma wfterm_wfenv : forall Γ e τ,
  wfterm Γ e τ → wfenv Γ.
Proof.
intros Γ e τ H.
induction H; auto.
pick fresh x; assert (wfenv ([(x, Some t1)] ++ G)) by auto; inversion H1; subst; eauto.
pick fresh a; assert (wfenv ([(a, None)] ++ G)) by auto; inversion H1; subst; eauto.
Qed.
Hint Resolve wfterm_wfenv.

Lemma wfterm_wftyp : forall Γ e τ,
  wfterm Γ e τ → wftyp Γ τ.
Proof.
intros Γ e τ H.
induction H.
Case "var". eapply wfenv_wftyp2; eauto.
Case "app". inversion IHwfterm1; subst; auto.
Case "abs". pick fresh x. assert ([(x, Some t1)] ++ G ⊢ t2 ok) by auto.
assert (wfenv ([(x, Some t1)] ++ G)) by eauto.
inversion H2; subst.
constructor; auto. rewrite_env (nil ++ G). eauto.
Case "inst". inversion IHwfterm; subst.
inversion IHwfterm; subst.
pick fresh a. rewrite tsubst_typ_intro with (a1 := a); auto.
rewrite_env (env_map (tsubst_typ t a) nil ++ G).
apply wftyp_tsubst; simpl_env; auto.
Case "gen".
apply wftyp_forall with (L := L); auto.
Qed.
Hint Resolve wfterm_wftyp.

Lemma wfterm_regular2 : forall Γ e τ,
  wfterm Γ e τ → lc_typ τ.
Proof.
intros Γ e τ H; induction H; eauto.
Qed.
Hint Resolve wfterm_regular2.

Lemma wfterm_regular1 : forall Γ e τ,
  wfterm Γ e τ → lc_term e.
Proof.
intros Γ e τ H; induction H; auto.
pick fresh x.
apply lc_term_abs_exists with (x1 := x).
apply wfenv_regular with (Γ := [(x, Some t1)] ++ G) (x := x); eauto.
auto.
eauto.
Qed.
Hint Resolve wfterm_regular1.

Lemma wfterm_env_uniq : forall Γ e τ,
  wfterm Γ e τ → uniq Γ.
Proof.
intros Γ e τ H. eauto.
Qed.
Hint Resolve wfterm_env_uniq.

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

(** Lemmas about [red0], [red1] *)
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

(*
(* Lemmas about wfterm *)
Lemma wfterm_fv : forall Γ e τ,
  wfterm Γ e τ → fv_term e [<=] dom Γ.
Proof.
intros Γ e τ H. induction H; simpl fv_term in *.
assert (x ∈ dom G) by eauto; fsetdec.
fsetdec.
pick fresh x. assert (fv_term (e ^ x) [<=] dom (x ~ t1 ++ G)) by auto.
assert (fv_term e [<=] fv_term (e ^ x)) by auto with lngen.
assert (fv_term e [<=] {{x}} ∪ dom G). simpl in *; fsetdec.
fsetdec.
Qed.
*)

Lemma wfterm_uniqueness : forall Γ e τ τ',
  wfterm Γ e τ → wfterm Γ e τ' → τ = τ'.
Proof.
intros Γ e τ τ' H1 H2. generalize dependent τ'.
induction H1; intros τ' H2; inversion H2; subst.
Case "var".
assert (Some t = Some τ'). eapply binds_unique; eauto. congruence.
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
rewrite_env (([(x, Some t1)] ++ Γ₁) ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto.
Case "inst". constructor. auto using wftyp_weakening. eauto.
Case "gen". pick fresh a and apply wfterm_gen.
rewrite_env (([(a, None)] ++ Γ₁) ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto.
Qed.

Lemma wfterm_subst : forall Γ₁ Γ₂ x τ₁ τ₂ e₁ e₂,
  wfterm (Γ₁ ++ x ~ Some τ₂ ++ Γ₂) e₁ τ₁ →
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
  rewrite_env ((z ~ Some t1 ++ Γ₁) ++ Γ₂).
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
replace (Some (tsubst_typ τ₂ a t)) with (option_map (tsubst_typ τ₂ a) (Some t)) by reflexivity.
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
  rewrite_env (env_map (tsubst_typ τ₂ a) ([(z, Some t1)] ++ Γ₁) ++ Γ₂).
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
