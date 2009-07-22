Add LoadPath "metatheory".
Require Export STLC_soundness.

Inductive sn (e : term) : Prop :=
| sn_intro : lc_term e → (forall e', e ⇝ e' → sn e') → sn e.

Axiom c : termvar.
Axiom wfterm_c : forall Γ τ, wfterm Γ (term_var_f c) τ.

Inductive neutral : term → Prop :=
| neutral_var : forall x, neutral (term_var_f x)
| neutral_app : forall e e', neutral (term_app e e').
Hint Constructors neutral.

Fixpoint reduce Γ e τ : Prop := match τ with
| typ_base => wfterm Γ e typ_base ∧ sn e
| typ_arrow τ₁ τ₂ =>
  wfterm Γ e (typ_arrow τ₁ τ₂) ∧
  forall e', reduce Γ e' τ₁ → reduce Γ (term_app e e') τ₂
end.

Lemma reduce_wfterm : forall τ Γ e,
  reduce Γ e τ → wfterm Γ e τ.
Proof.
intro τ; induction τ; intros; simpl reduce in *; intuition auto.
Qed.
Hint Resolve reduce_wfterm.

(*
Lemma reduce_fv : forall τ Γ e,
  reduce Γ e τ → fv_term e [<=] dom Γ.
Proof.
intros τ; induction τ; intros; simpl in *; destruct H.
eauto using wfterm_fv.
Admitted.
*)
(*
Lemma reduce_weakening_aux : forall τ Γ₁ Γ₂ e,
  reduce Γ₂ e τ →
  uniq (Γ₁ ++ Γ₂) →
  reduce (Γ₁ ++ Γ₂) e τ.
Proof.
intro τ; induction τ; intros; simpl reduce in *; destruct H; split; auto.
apply wfterm_weakening with (Γ₁ := nil); simpl_env; auto.
intros.
apply IHτ2; eauto.
*)

(*
Lemma reduce_weakening_aux : forall τ Γ e x τ',
  ((reduce Γ e τ ∧ x ∉ dom Γ) ↔
    (reduce (x ~ τ' ++ Γ) e τ ∧ x ∉ fv_term e)).
Proof.
intro τ; induction τ; intros; split; intro H; simpl reduce in *; decompose record H; clear H; split; try split; intros; simpl_env in *; eauto.
Case "typ_base".
apply wfterm_weakening with (Γ₁ := nil); simpl_env; eauto.
assert (fv_term e [<=] dom Γ) by eauto using wfterm_fv; auto.
eapply wfterm_strengthening with (Γ₁ := nil); simpl_env; eauto.
assert (uniq (x ~ τ' ++ Γ)) by eauto; solve_uniq.
Case "typ_arrow".



simpl in H; rewrite <- IHτ1 in H; auto.
Focus 2.
apply H1 in H2. rewrite IHτ2 in H2; simpl; auto. eauto.
assert (fv_term (term_app e e') [<=] dom Γ) by eauto using reduce_fv.
simpl in H3. auto.

solve_uniq.
*)

Lemma sn_regular : forall e, sn e → lc_term e.
Proof.
intros e H; destruct H; assumption.
Qed.
Hint Resolve sn_regular.

Lemma sn_red : forall e e', sn e → e ⇝ e' → sn e'.
Proof.
intros e e' He Hred.
induction He.
auto.
Qed.

Lemma cr2 : forall Γ τ e e',
  reduce Γ e τ → e ⇝ e' → reduce Γ e' τ.
Proof.
intros Γ τ e e' H1 H2.
assert (wfterm Γ e τ) as H3 by auto using reduce_wfterm.
assert (wfterm Γ e' τ) as H4 by eauto using subject_reduction.
generalize dependent Γ. generalize dependent e. generalize dependent e'.
induction τ; intros; simpl reduce in *; split; try split; intros; try tauto; eauto.
destruct H1; eauto using sn_red.
destruct H1. apply IHτ2 with (e := term_app e e'0); auto.
apply red1_appL; eauto using reduce_wfterm.
econstructor; eauto using reduce_wfterm.
Qed.

Lemma sn_appR : forall e e',
  sn (term_app e e') → sn e.
Proof.
intros e e' H.
remember (term_app e e') as f.
generalize dependent e. generalize dependent e'.
induction H; intros; subst.
inversion H; subst.
apply sn_intro; intros; eauto.
Qed.

Lemma cr1_cr3 : forall τ Γ,
(forall e, reduce Γ e τ → sn e) ∧
(forall e, neutral e →
  wfterm Γ e τ →
  (forall e', e ⇝ e' → reduce Γ e' τ) ->
  reduce Γ e τ).
Proof.
intro τ; induction τ; intros; split; intros; simpl reduce in *; split; auto; intros; intuition eauto.
Case "typ_base1".
eauto using sn_red.
Case "typ_base2".
apply sn_intro; intros; [eauto | edestruct H1; eauto].
Case "typ_arrow1".
destruct (IHτ2 Γ) as [H21 H22]; clear IHτ2.
assert (reduce Γ (term_var_f c) τ1).
  destruct (IHτ1 Γ); apply H3; eauto using wfterm_c; intros;
  inversion H4; subst; inversion H5.
apply sn_red with (e := e); auto.
apply (sn_appR _ (term_var_f c)); eauto.
Case "typ_arrow2".
destruct (IHτ1 Γ) as [H11 H12]; clear IHτ1.
destruct (IHτ2 Γ) as [H21 H22]; clear IHτ2.
assert (sn e') as H3 by auto.
induction H3.
eapply H22; eauto using reduce_wfterm; intros.
inversion H6; subst.
inversion H7; subst; inversion H.
edestruct H1 as [_ H8]; eauto.
eauto using cr2.
Qed.

Lemma cr1 :  forall τ Γ e, reduce Γ e τ → sn e.
Proof.
intros τ Γ; destruct (cr1_cr3 τ Γ); auto.
Qed.

Lemma cr3 : forall τ Γ e,
  neutral e →
  wfterm Γ e τ →
  (forall e', e ⇝ e' → reduce Γ e' τ) ->
  reduce Γ e τ.
Proof.
intros τ Γ; destruct (cr1_cr3 τ Γ); auto.
Qed.

Lemma reduce_const : forall τ Γ, reduce Γ (term_var_f c) τ.
Proof.
intros τ Γ.
apply cr3; auto using wfterm_c; intros.
inversion H; subst; inversion H0.
Qed.

Theorem abs_step_reduce_lemma : forall Γ e₁ e₂ τ₁ τ₂,
  sn e₁ -> sn (e₂ ^ c) -> reduce Γ e₁ τ₁ ->
     (forall e, reduce Γ e τ₁ -> reduce Γ (e₂ ^^ e) τ₂) ->
     wfterm Γ (term_abs τ₁ e₂) (typ_arrow τ₁ τ₂) ->
       reduce Γ (term_app (term_abs τ₁ e₂) e₁) τ₂.
Proof.
intros Γ e₁ e₂ τ₁ τ₂ H H0 H1 H2 H3.
generalize dependent e₂.
assert (lc_term e₁) as Hlc1 by eauto.
induction Hlc1; intros; eapply cr3; eauto; intros.
Case "e₁ = term_var_f x".
pick fresh y. assert (lc_term (e₂ ^ y)) by eauto.
remember (e₂ ^ y) as e. assert (close_term_wrt_term y e = e₂). subst. eauto with lngen.
clear Heqe. generalize dependent y.
generalize dependent e₂. induction H5; intros; subst.
unfold close_term_wrt_term in *; simpl in *;
unfold termvar in *; destruct (y == x0); unfold open_term_wrt_term in *; simpl in *.
SCase "bound var".
inversion H4; subst. inversion H5; subst; auto.
inversion H9; subst. inversion H5.
pick fresh y. assert (term_var_b 0 ^ y ⇝ e' ^ y) as H5 by auto.
unfold open_term_wrt_term in H5; simpl in H5. inversion H5; subst. inversion H6.
inversion H9; subst. inversion H5.
SCase "free var".
inversion H4; subst. inversion H5; subst; autorewrite with lngen; eauto.
inversion H9; subst. inversion H5.
pick fresh z. assert (term_var_f x0 ^ z ⇝ e' ^ z) as H5 by auto.
autorewrite with lngen in H5. inversion H5; subst. inversion H6.
inversion H9; subst. inversion H5.
SCase "abs".

Focus 2.
SCase "app".
autorewrite with lngen in *.

Theorem strong_normalization : well_founded red1.
