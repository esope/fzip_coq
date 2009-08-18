Add LoadPath "../metatheory".
Require Export STLC_other.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_term x) in
  constr:(A \u B \u C \u D1).

(** Lemmas about [wfterm] *)
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

Lemma wfterm_uniqueness : forall Γ e τ τ',
  wfterm Γ e τ → wfterm Γ e τ' → τ = τ'.
Proof.
intros Γ e τ τ' H1 H2. generalize dependent τ'.
induction H1; intros τ' H2; inversion H2; subst.
eauto using binds_unique.
assert (typ_arrow t2 t1 = typ_arrow t3 τ') by auto; congruence.
pick fresh x; assert (t2 = t3) by eauto; congruence.
Qed.

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
Proof with eauto 7.
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
