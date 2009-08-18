Add LoadPath "PLC".
Add LoadPath "../metatheory".
Add LoadPath "../lib".
Require PLC_confluence.
Require Export STLC_soundness.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_term x) in
  let D2 := gather_atoms_with (fun x => PLC_ott.fv_term x) in
  constr:(A \u B \u C \u D1 \u D2).

Inductive erase : term -> PLC_ott.term -> Prop :=
| erase_var : forall (x: termvar),
  erase (term_var_f x) (PLC_ott.term_var_f x)
| erase_abs : forall L τ e e',
  (forall (x: termvar), x ∉ L ->
  erase (open_term_wrt_term e (term_var_f x)) (PLC_ott.open_term_wrt_term e' (PLC_ott.term_var_f x))) ->
  erase (term_abs τ e) (PLC_ott.term_abs e')
| erase_app : forall e₁ e₁' e₂ e₂',
  erase e₁ e₁' ->
  erase e₂ e₂' ->
  erase (term_app e₁ e₂) (PLC_ott.term_app e₁' e₂')
.
Hint Constructors erase.

Lemma erase_regular1 : forall e e',
  erase e e' → lc_term e.
Proof.
intros e e' H.
induction H; auto.
Qed.

Lemma erase_regular2 : forall e e',
  erase e e' → PLC_ott.lc_term e'.
Proof.
intros e e' H.
induction H; auto.
Qed.
Hint Resolve erase_regular1 erase_regular2.

Lemma erase_subst : forall e₁ e₂ e₁' e₂' x,
  erase e₁ e₁' → erase e₂ e₂' →
  erase (subst_term e₂ x e₁) (PLC_ott.subst_term e₂' x e₁').
Proof.
intros e₁ e₂ e₁' e₂' x H1 H2.
induction H1; simpl in *; auto.
Case "var".
unfold termvar in *; unfold PLC_ott.termvar in *.
destruct (x0 == x); auto.
Case "abs".
pick fresh y. apply erase_abs with (L := L ∪ {{x}}); intros; auto.
replace (term_var_f x0) with (subst_term e₂ x (term_var_f x0)).
rewrite <- subst_term_open_term_wrt_term; eauto.
replace (PLC_ott.term_var_f x0) with (PLC_ott.subst_term e₂' x (PLC_ott.term_var_f x0)).
rewrite <- PLC_inf.subst_term_open_term_wrt_term; eauto.
autorewrite with lngen; reflexivity.
autorewrite with lngen; reflexivity.
Qed.
Hint Resolve erase_subst.

Lemma erase_uniqueness : forall e e₁ e₂,
  erase e e₁ → erase e e₂ → e₁ = e₂.
Proof.
intros e e1 e2 H1 H2.
generalize dependent e2.
induction H1; intros e2 H2; inversion H2; subst; f_equal; auto.
Case "abs". pick fresh x.
apply PLC_inf.open_term_wrt_term_inj with (x1 := x); auto.
Qed.

Lemma erase_exists : forall e, lc_term e → exists e', erase e e'.
Proof.
intros e H.
induction H; eauto.
Case "abs". pick fresh x.
destruct (H0 x) as [e' H2].
exists (PLC_ott.term_abs (PLC_inf.close_term_wrt_term x e')).
apply erase_abs with (L := PLC_ott.fv_term e' ∪ {{x}}); intros; auto.
rewrite <- PLC_inf.subst_term_spec.
rewrite (subst_term_intro x); auto.
Case "app".
destruct IHlc_term1 as [e1' H1].
destruct IHlc_term2 as [e2' H2].
eauto.
Qed.

Lemma erase_red0 : forall e₁ e₂ e₁' e₂',
  red0 e₁ e₂ → erase e₁ e₁' →
  erase e₂ e₂' → PLC_ott.red0 e₁' e₂'.
Proof.
intros e₁ e₂ e₁' e₂' Hred H1 H2.
inversion Hred; subst; inversion H1; subst.
Case "beta".
inversion H5; subst. assert (e₂' = PLC_ott.open_term_wrt_term e' e₂'0).
eapply erase_uniqueness; eauto.
pick fresh x. rewrite (subst_term_intro x); auto.
rewrite (PLC_inf.subst_term_intro x); auto.
subst; eauto.
Qed.

Lemma erase_red1 : forall e₁ e₂ e₁' e₂',
  e₁ ⇝ e₂ → erase e₁ e₁' →
  erase e₂ e₂' → PLC_ott.red1 e₁' e₂'.
Proof.
intros e₁ e₂ e₁' e₂' Hred Herase1 Herase2.
generalize dependent e₁'. generalize dependent e₂'.
induction Hred; intros.
Case "empty". eauto using erase_red0.
Case "appL". inversion Herase1; subst; inversion Herase2; subst.
replace e₂'1 with e₂'0 by eauto using erase_uniqueness; eauto.
Case "appR". inversion Herase1; subst; inversion Herase2; subst.
replace e₁' with e₁'0 by eauto using erase_uniqueness; eauto.
Case "abs". inversion Herase1; subst; inversion Herase2; subst.
pick fresh x.
apply PLC_ott.red1_abs with (L := L ∪ L0 ∪ L1 ∪ {{x}}); intros; eauto.
Qed.

Lemma erase_red0_inv : forall Γ τ e₁' e₂' e₁,
  PLC_ott.red0 e₁' e₂' →
  erase e₁ e₁' →
  wfterm Γ e₁ τ →
  exists e₂, red0 e₁ e₂.
Proof.
intros Γ τ e₁' e₂' e₁ Hred Herase Hwfterm.
inversion Hred; subst.
inversion Herase; subst.
Case "app". inversion H4; subst.
SCase "abs". eauto.
Qed.

Lemma erase_red1_inv : forall Γ τ e₁' e₂' e₁,
  PLC_ott.red1 e₁' e₂' →
  erase e₁ e₁' →
  wfterm Γ e₁ τ →
  exists e₂, e₁ ⇝ e₂.
Proof.
intros Γ τ e₁' e₂' e₁ Hred Herase Hwfterm.
generalize dependent e₁. generalize dependent τ. generalize dependent Γ.
induction Hred; intros.
Case "empty". edestruct erase_red0_inv; eauto.
Case "appL". inversion Herase; subst; inversion Hwfterm; subst; edestruct IHHred; eauto.
Case "appR". inversion Herase; subst; inversion Hwfterm; subst.
SCase "app". edestruct IHHred; eauto.
Case "abs". inversion Herase; subst; inversion Hwfterm; subst.
SCase "abs". pick fresh x. edestruct (H0 x); eauto.
exists (term_abs τ0 (close_term_wrt_term x x0)).
apply red1_abs with (L := {{x}}); intros; auto.
rewrite <- subst_term_spec.
rewrite (subst_term_intro x); auto.
Qed.

Lemma simulation : forall Γ τ e₁ e₁',
  wfterm Γ e₁ τ →
  erase e₁ e₁' →
  ((exists e₂, e₁ ⇝ e₂) ↔ (exists e₂', PLC_ott.red1 e₁' e₂')).
Proof.
intros Γ τ e₁ e₁' Hwfterm Herase; split; intros [e H].
destruct (erase_exists e); eauto using erase_red1.
edestruct erase_red1_inv; eauto.
Qed.
