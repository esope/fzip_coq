Add LoadPath "metatheory".
Require Export STLC_init.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_term x) in
  constr:(A \u B \u C \u D1).

(* Mutual induction principles *)
Scheme pval_mut_ind_aux := Induction for pval Sort Prop
with   val_mut_ind_aux  := Induction for val  Sort Prop.
Combined Scheme pval_val_mut_ind from pval_mut_ind_aux, val_mut_ind_aux.

(* Administrative lemmas *)
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

Lemma wfterm_regular : forall Γ e τ,
  wfterm Γ e τ → lc_term e.
Proof.
intros Γ e τ H; induction H; auto.
Qed.
Hint Resolve wfterm_regular.

(* Lemmas about values *)
Lemma value_is_normal_aux :
  (forall v, pval v → ~ exists e, v ⇝ e) ∧
  (forall v, val v → ~ exists e, v ⇝ e).
Proof.
apply pval_val_mut_ind; intros; intros [e0 Hred]; inversion Hred; subst; eauto.
inversion H.
inversion H1; subst. inversion p.
inversion H0.
pick fresh x. eapply H; eauto.
Qed.

Lemma value_is_normal : forall v, val v → ~ exists e, v ⇝ e.
Proof.
destruct value_is_normal_aux as [_ Th]. intuition auto.
Qed.

(* Renaming lemmas *)
Lemma pval_val_renaming : forall x y,
  (forall v, pval v → pval (subst_term (term_var_f y) x v)) ∧
  (forall v, val v → val (subst_term (term_var_f y) x v)).
Proof.
intros x y.
apply pval_val_mut_ind; intros; simpl; auto.
Case "var". destruct (x0 == x); auto.
Case "abs". pick fresh z and apply val_abs.
  rewrite subst_term_open_term_wrt_term_var; auto.
Qed.

Lemma val_renaming : forall x y v,
  val v → val (subst_term (term_var_f y) x v).
Proof.
intros x y v H. destruct (pval_val_renaming x y); auto.
Qed.
Hint Resolve val_renaming.

Lemma red0_renaming : forall x y e e', red0 e e' →
  red0 (subst_term (term_var_f y) x e) (subst_term (term_var_f y) x e').
Proof.
intros x y e e' H.
inversion H; subst.
simpl. rewrite subst_term_open_term_wrt_term; auto. apply red0_beta; auto with lngen.
assert (lc_term (subst_term (term_var_f y) x (term_abs t e1))) by auto with lngen; auto.
Qed.
Hint Resolve red0_renaming.

Lemma red1_renaming : forall x y e e', e ⇝ e' →
  (subst_term (term_var_f y) x e) ⇝ (subst_term (term_var_f y) x e').
Proof.
intros x y e e' H.
induction H; subst; simpl; auto.
apply red1_appL; auto with lngen.
apply red1_appR; auto with lngen.
apply red1_abs with (L := L `union` {{x}}); intros z Hz.
replace (term_var_f z) with (subst_term (term_var_f y) x (term_var_f z)) by auto with lngen.
repeat rewrite <- subst_term_open_term_wrt_term; eauto.
Qed.
Hint Resolve red1_renaming.

(* Lemmas about wfterm *)
Lemma wfterm_weakening : forall Γ₁ Γ₂ Γ₃ e τ,
  wfterm (Γ₁ ++ Γ₃) e τ →
  uniq (Γ₁ ++ Γ₂ ++ Γ₃) →
  wfterm (Γ₁ ++ Γ₂ ++ Γ₃) e τ.
Proof.
intros Γ₁ Γ₂ Γ₃ e τ H. dependent induction H; intro; eauto.
Case "lam". pick fresh x and apply wfterm_abs.
rewrite_env (([(x, t1)] ++ Γ₁) ++ Γ₂ ++ Γ₃).
apply H0; simpl_env; auto.
Qed.

Lemma wfterm_subst : forall Γ₁ Γ₂ x τ₁ τ₂ e₁ e₂,
  wfterm (Γ₁ ++ x ~ τ₂ ++ Γ₂) e₁ τ₁ →
  wfterm Γ₂ e₂ τ₂ →
  wfterm (Γ₁ ++ Γ₂) (subst_term e₂ x e₁) τ₁.
Proof with eauto.
intros Γ₁ Γ₂ x τ₁ τ₂ e₁ e₂ H. dependent induction H; intro; simpl...
Case "var".
  destruct (x == x0); subst.
  SCase "x = x0".
    analyze_binds_uniq H0; apply wfterm_weakening with (Γ₁ := nil)...
  SCase "x <> x0".
    analyze_binds_uniq H0...
Case "abs".
  pick fresh z and apply wfterm_abs.
  rewrite_env ((z ~ t1 ++ Γ₁) ++ Γ₂).
  rewrite subst_term_open_term_wrt_term_var...
  apply H0 with (τ₂0 := τ₂)...
Qed.

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
  Case "lam".
    intros e' J; inversion J; subst.
    inversion H1.
    pick fresh z and apply wfterm_abs...
Qed.

Theorem progress : forall Γ e τ,
  wfterm Γ e τ →
  (exists e', e ⇝ e') ∨ val e.
Proof with eauto 10.
  intros Γ e τ H.
  dependent induction H; simpl...
  Case "typing_app".
    destruct IHwfterm1 as [[e1' ?] | ?]...
    destruct IHwfterm2 as [[e2' ?] | ?]...
    destruct e1; simpl in H1; inversion H1...
  Case "abs".
    pick fresh z. edestruct (H0 z) as [[e1 ?] | ?]...
    left.
      exists (term_abs t1 (close_term_wrt_term z e1)).
      apply red1_abs with (L := L `union` {{z}}); intros.
      rewrite <- subst_term_spec.
      rewrite (subst_term_intro z)...
    right.
      apply val_abs with (L := L `union` {{z}}); intros...
      rewrite (subst_term_intro z)...
Qed.
