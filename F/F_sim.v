Add LoadPath "PLC".
Add LoadPath "metatheory".
Require PLC_init.
Require Export F_init.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_term x) in
  let D2 := gather_atoms_with (fun x => ftv_typ x) in
  let D3 := gather_atoms_with (fun x => ftv_term x) in
  let D4 := gather_atoms_with (fun x => PLC_ott.fv_term x) in
  constr:(A \u B \u C \u D1 \u D2 \u D3 \u D4).


Inductive erase : term -> PLC_ott.term -> Prop :=
| erase_var : forall (x: termvar),
  erase (term_var_f x) (PLC_ott.term_var_f x)
| erase_abs : forall L τ e e',
  lc_typ τ ->
  (forall (x: termvar), x ∉ L ->
  erase (open_term_wrt_term e (term_var_f x)) (PLC_ott.open_term_wrt_term e' (PLC_ott.term_var_f x))) ->
  erase (term_abs τ e) (PLC_ott.term_abs e')
| erase_app : forall e₁ e₁' e₂ e₂',
  erase e₁ e₁' ->
  erase e₂ e₂' ->
  erase (term_app e₁ e₂) (PLC_ott.term_app e₁' e₂')
| erase_gen : forall L e e',
  (forall (x: termvar), x `notin` L ->
  erase (open_term_wrt_typ e (typ_var_f x)) (PLC_ott.open_term_wrt_term e' (PLC_ott.term_var_f x))) ->
  erase (term_gen e) (PLC_ott.term_abs e')
| erase_TApp : forall τ e e',
  lc_typ τ ->
  erase e e' ->
  erase (term_inst e τ) (PLC_ott.term_app e' (PLC_ott.term_abs (PLC_ott.term_var_b 0)))
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
constructor; auto.
constructor; intros;
unfold PLC_ott.open_term_wrt_term; simpl; auto.
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
Case "gen".
pick fresh y. apply erase_gen with (L := L ∪ {{x}}); intros; auto.
rewrite <- subst_term_open_term_wrt_typ; eauto.
replace (PLC_ott.term_var_f x0) with (PLC_ott.subst_term e₂' x (PLC_ott.term_var_f x0)).
rewrite <- PLC_inf.subst_term_open_term_wrt_term; eauto.
autorewrite with lngen; reflexivity.
Qed.
Hint Resolve erase_subst.

Lemma erase_tsubst : forall e e' τ a,
  lc_typ τ → erase e e' → erase (tsubst_term τ a e) e'.
Proof.
intros e e' τ a Hlc H.
induction H; simpl in *; auto with lngen.
Case "abs".
pick fresh x. apply erase_abs with (L := L ∪ {{a}}); intros; auto with lngen.
replace (term_var_f x0) with (tsubst_term τ a (term_var_f x0)) by reflexivity.
rewrite <- tsubst_term_open_term_wrt_term; eauto.
Case "gen".
pick fresh x. apply erase_gen with (L := L ∪ {{a}}); intros; auto.
replace (typ_var_f x0) with (tsubst_typ τ a (typ_var_f x0)).
rewrite <- tsubst_term_open_term_wrt_typ; eauto.
autorewrite with lngen; auto.
Qed.
Hint Resolve erase_tsubst.

Lemma erase_fv : forall e e',
  erase e e' → fv_term e [=] PLC_ott.fv_term e'.
Proof.
intros e e' H. induction H; simpl in *; try fsetdec.
pick fresh x.
intro a; split; intro.

ICI

destruct (a == x).

Lemma erase_uniqueness : forall e e₁ e₂,
  erase e e₁ → erase e e₂ → e₁ = e₂.
Proof.
intros e e1 e2 H1 H2.
generalize dependent e2.
induction H1; intros e2 H2; inversion H2; subst; f_equal; auto.
Case "abs". pick fresh x.
apply PLC_inf.open_term_wrt_term_inj with (x1 := x); auto.
Case "gen". pick fresh x.
apply PLC_inf.open_term_wrt_term_inj with (x1 := x); auto.
Qed.

Lemma erase_exists : forall e, lc_term e → exists e', erase e e'.
Proof.
intros e H.
induction H; eauto.
Case "abs". pick fresh x.
destruct (H1 x) as [e' H2].
exists (PLC_ott.term_abs (PLC_inf.close_term_wrt_term x e')).
apply erase_abs with (L := PLC_ott.fv_term e' ∪ {{x}}); intros; auto.
rewrite <- PLC_inf.subst_term_spec.
rewrite (subst_term_intro x); auto.
Case "app".
destruct IHlc_term1 as [e1' H1].
destruct IHlc_term2 as [e2' H2].
eauto.
Case "gen". pick fresh x.
destruct (H0 x) as [e' H1].
exists (PLC_ott.term_abs (PLC_inf.close_term_wrt_term x e')).
apply erase_gen with (L := PLC_ott.fv_term e' ∪ {{x}}); intros; auto.
rewrite <- PLC_inf.subst_term_spec.
rewrite (tsubst_term_intro x); auto.


Lemma erase_red0 : forall e₁ e₂ e₁',
  red0 e₁ e₂ → erase e₁ e₁' → exists e₂', PLC_ott.red0 e₁' e₂'.
Proof.
intros e₁ e₂ e₁' H H0.
inversion H; subst; inversion H0; subst.
inversion H6; subst.