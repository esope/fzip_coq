Add LoadPath "PLC".
Add LoadPath "metatheory".
Require PLC_confluence.
Require Export F_soundness.

Definition c_arrow : atom.
Proof.
pick fresh x. exact x.
Defined.

Definition c_forall : atom.
Proof.
pick fresh x for {{c_arrow}}. exact x.
Defined.

Lemma c_arrow_neq_c_forall : c_arrow ≠ c_forall.
Proof.
unfold c_forall.
destruct (atom_fresh (singleton c_arrow)).
unfold c_arrow in *.
destruct (atom_fresh empty).
auto.
Qed.
Hint Immediate c_arrow_neq_c_forall.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_term x) in
  let D2 := gather_atoms_with (fun x => ftv_typ x) in
  let D3 := gather_atoms_with (fun x => ftv_term x) in
  let D4 := gather_atoms_with (fun x => PLC_ott.fv_term x) in
  constr:(A \u B \u C \u D1 \u D2 \u D3 \u D4 \u {{c_arrow}} \u {{c_forall}}).

Inductive erase_typ : typ -> PLC_ott.term -> Prop :=
| erase_typ_var : forall x,
  erase_typ (typ_var_f x) (PLC_ott.term_var_f x)
| erase_typ_arrow : forall τ₁ τ₂ t₁ t₂,
  erase_typ τ₁ t₁ → erase_typ τ₂ t₂ →
  erase_typ (typ_arrow τ₁ τ₂) (PLC_ott.term_app (PLC_ott.term_app (PLC_ott.term_var_f c_arrow) t₁) t₂)
| erase_typ_forall : forall L τ t,
  (forall x, x ∉ L → erase_typ (open_typ_wrt_typ τ (typ_var_f x)) (PLC_ott.open_term_wrt_term t (PLC_ott.term_var_f x))) →
  erase_typ (typ_forall τ) (PLC_ott.term_app (PLC_ott.term_var_f c_forall) (PLC_ott.term_abs t))
.
Hint Constructors erase_typ.

Lemma erase_typ_regular1 : forall τ t, erase_typ τ t → lc_typ τ.
Proof.
intros τ t H; induction H; auto.
Qed.

Lemma erase_typ_regular2 : forall τ t, erase_typ τ t → PLC_ott.lc_term t.
Proof.
intros τ t H; induction H; auto.
Qed.
Hint Resolve erase_typ_regular1 erase_typ_regular2.

Lemma erase_typ_tsubst : forall τ τ' t t' x,
  x ∉ {{ c_arrow }} ∪ {{ c_forall }} ->
  erase_typ τ t -> erase_typ τ' t' ->
  erase_typ (tsubst_typ τ' x τ) (PLC_ott.subst_term t' x t).
Proof.
intros τ τ' t t' x Hx He1 He2.
induction He1; simpl in *; unfold PLC_ott.termvar in *; unfold typvar in *.
destruct (x0 == x); subst; auto.
destruct (c_arrow == x); auto. absurdity with auto.
destruct (c_forall == x); auto. absurdity with auto.
apply erase_typ_forall with (L := L ∪ {{x}}); intros.
replace (typ_var_f x0) with (tsubst_typ τ' x (typ_var_f x0)).
rewrite <- tsubst_typ_open_typ_wrt_typ; eauto.
replace (PLC_ott.term_var_f x0) with (PLC_ott.subst_term t' x (PLC_ott.term_var_f x0)).
rewrite <- PLC_inf.subst_term_open_term_wrt_term; eauto.
autorewrite with lngen; auto.
autorewrite with lngen; auto.
Qed.
Hint Resolve erase_typ_tsubst.

Lemma erase_typ_fv_upper : forall τ t,
  erase_typ τ t -> PLC_ott.fv_term t [<=] {{c_arrow}} ∪ {{c_forall}} ∪ ftv_typ τ.
Proof.
intros τ t H.
induction H; simpl in *; try fsetdec.
pick fresh x.
assert (ftv_typ (open_typ_wrt_typ τ (typ_var_f x)) [<=] ftv_typ (typ_var_f x) ∪ ftv_typ τ) by auto with lngen.
assert (PLC_ott.fv_term t [<=] PLC_ott.fv_term (PLC_ott.open_term_wrt_term t (PLC_ott.term_var_f x))) by auto with lngen.
simpl in *.
assert (PLC_ott.fv_term (PLC_ott.open_term_wrt_term t (PLC_ott.term_var_f x)) [<=]
  singleton c_arrow∪singleton c_forall∪
         ftv_typ (open_typ_wrt_typ τ (typ_var_f x))) by auto.
fsetdec.
Qed.

Lemma erase_typ_fv_lower : forall τ t,
  erase_typ τ t -> ftv_typ τ [<=] PLC_ott.fv_term t.
Proof.
intros τ t H.
induction H; simpl in *; try fsetdec.
pick fresh x.
assert (ftv_typ τ [<=] ftv_typ (open_typ_wrt_typ τ (typ_var_f x))) by auto with lngen.
assert (PLC_ott.fv_term (PLC_ott.open_term_wrt_term t (PLC_ott.term_var_f x)) [<=] PLC_ott.fv_term (PLC_ott.term_var_f x) ∪ PLC_ott.fv_term t) by auto with lngen.
assert (ftv_typ (open_typ_wrt_typ τ (typ_var_f x))[<=]PLC_ott.fv_term (PLC_ott.open_term_wrt_term t (PLC_ott.term_var_f x))) by auto.
simpl in *.
fsetdec.
Qed.

Lemma erase_typ_uniqueness : forall τ t₁ t₂,
  erase_typ τ t₁ -> erase_typ τ t₂ -> t₁ = t₂.
Proof.
intros τ t₁ t₂ He1 He2.
generalize dependent t₂.
induction He1; intros t2 He2; inversion He2; subst; auto.
f_equal; auto. f_equal; auto.
pick fresh x; f_equal; eauto. f_equal; eapply PLC_inf.open_term_wrt_term_inj; eauto.
Qed.

Lemma erase_typ_exists : forall τ, lc_typ τ -> exists t, erase_typ τ t.
Proof.
intros τ H. induction H.
eauto.
destruct IHlc_typ1; destruct IHlc_typ2; eauto.
pick fresh a; destruct (H0 a) as [t' H4].
exists (PLC_ott.term_app (PLC_ott.term_var_f c_forall) (PLC_ott.term_abs (PLC_inf.close_term_wrt_term a t'))).
apply erase_typ_forall with (L := {{a}} ∪ {{c_arrow}} ∪ {{c_forall}} ∪ PLC_ott.fv_term t' ∪ ftv_typ t).
intros; auto.
rewrite (tsubst_typ_intro a); auto.
rewrite <- PLC_inf.subst_term_spec.
auto.
Qed.

Lemma erase_typ_inj : forall τ₁ τ₂ t,
  erase_typ τ₁ t -> erase_typ τ₂ t -> τ₁ = τ₂.
Proof.
intros τ₁ τ₂ t He1 He2.
generalize dependent τ₂.
induction He1; intros τ2 He2; inversion He2; subst; f_equal; auto.
pick fresh x. eapply open_typ_wrt_typ_inj; eauto.
Qed.

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
| erase_TApp : forall τ t e e',
  erase_typ τ t ->
  erase e e' ->
  erase (term_inst e τ) (PLC_ott.term_app e' t)
.
Hint Constructors erase.

Lemma erase_regular1 : forall e e',
  erase e e' → lc_term e.
Proof.
intros e e' H.
induction H; eauto.
Qed.

Lemma erase_regular2 : forall e e',
  erase e e' → PLC_ott.lc_term e'.
Proof.
intros e e' H.
induction H; eauto.
Qed.
Hint Resolve erase_regular1 erase_regular2.

Lemma erase_subst : forall e₁ e₂ e₁' e₂' x,
  x ∉ {{c_arrow}} ∪ {{c_forall}} ∪ ftv_term e₁ ->
  erase e₁ e₁' → erase e₂ e₂' →
  erase (subst_term e₂ x e₁) (PLC_ott.subst_term e₂' x e₁').
Proof.
intros e₁ e₂ e₁' e₂' x Hx H1 H2.
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
eapply H1; eauto.
assert (ftv_term (e ^ x0) [<=] ftv_term (term_var_f x0) ∪ ftv_term e) by auto with lngen.
simpl in *. clear Fr. fsetdec.
autorewrite with lngen; reflexivity.
autorewrite with lngen; reflexivity.
Case "gen".
pick fresh y. apply erase_gen with (L := L ∪ {{x}}); intros; auto.
rewrite <- subst_term_open_term_wrt_typ; eauto.
replace (PLC_ott.term_var_f x0) with (PLC_ott.subst_term e₂' x (PLC_ott.term_var_f x0)).
rewrite <- PLC_inf.subst_term_open_term_wrt_term; eauto.
eapply H0; eauto.
assert (ftv_term (open_term_wrt_typ e (typ_var_f x0)) [<=] ftv_typ (typ_var_f x0) ∪ ftv_term e) by auto with lngen.
simpl in *. clear Fr. fsetdec.
autorewrite with lngen; reflexivity.
Case "inst".
constructor; auto.
assert (x ∉ PLC_ott.fv_term t).
assert (PLC_ott.fv_term t [<=] {{c_arrow}} ∪ {{c_forall}} ∪ ftv_typ τ) by auto using erase_typ_fv_upper.
fsetdec.
autorewrite with lngen; auto.
Qed.
Hint Resolve erase_subst.

Lemma erase_tsubst : forall e e' τ t a,
  a ∉ {{c_arrow}} ∪ {{c_forall}} ∪ fv_term e ->
  erase_typ τ t → erase e e' → erase (tsubst_term τ a e) (PLC_ott.subst_term t a e').
Proof.
intros e e' τ t a Ha He H.
induction H; simpl in *; auto with lngen.
Case "var".
unfold PLC_ott.termvar in *. unfold termvar in *.
destruct (x == a); auto. absurdity with auto.
Case "abs".
assert (lc_typ τ) by eauto.
pick fresh x. apply erase_abs with (L := L ∪ {{a}}); intros; auto with lngen.
replace (term_var_f x0) with (tsubst_term τ a (term_var_f x0)) by reflexivity.
rewrite <- tsubst_term_open_term_wrt_term; eauto.
replace (PLC_ott.term_var_f x0) with (PLC_ott.subst_term t a (PLC_ott.term_var_f x0)).
rewrite <- PLC_inf.subst_term_open_term_wrt_term; eauto.
apply H1; auto.
assert (fv_term (e ^ x0) [<=] fv_term (term_var_f x0) ∪ fv_term e) by auto with lngen.
clear Fr. simpl in *. fsetdec.
autorewrite with lngen; auto.
Case "gen".
pick fresh x. apply erase_gen with (L := L ∪ {{a}}); intros; auto.
replace (typ_var_f x0) with (tsubst_typ τ a (typ_var_f x0)).
rewrite <- tsubst_term_open_term_wrt_typ; eauto.
replace (PLC_ott.term_var_f x0) with (PLC_ott.subst_term t a (PLC_ott.term_var_f x0)).
rewrite <- PLC_inf.subst_term_open_term_wrt_term; eauto.
apply H0; auto.
assert (fv_term (open_term_wrt_typ e (typ_var_f x0)) [<=] fv_term e) by auto with lngen.
clear Fr. fsetdec.
autorewrite with lngen; auto.
autorewrite with lngen; auto.
Qed.
Hint Resolve erase_tsubst.

Lemma erase_fv_lower : forall e e',
  erase e e' → fv_term e [<=] PLC_ott.fv_term e'.

Lemma erase_fv_upper : forall e e',
  erase e e' → PLC_ott.fv_term e' [<=] {{c_arrow}} ∪ {{c_forall}} ∪ fv_term e.

Lemma erase_fv : forall e e',
  erase e e' → fv_term e [=] PLC_ott.fv_term e'.
Proof.
intros e e' H. induction H; simpl in *; try fsetdec.
Case "abs".
pick fresh x.
assert (PLC_ott.fv_term (PLC_ott.open_term_wrt_term e' (PLC_ott.term_var_f x)) [<=] PLC_ott.fv_term (PLC_ott.term_var_f x) ∪ PLC_ott.fv_term e') by auto with lngen.
assert (PLC_ott.fv_term e' [<=] PLC_ott.fv_term (PLC_ott.open_term_wrt_term e' (PLC_ott.term_var_f x))) by auto with lngen.
assert (fv_term (open_term_wrt_term e (term_var_f x)) [<=] fv_term (term_var_f x) ∪ fv_term e) by auto with lngen.
assert (fv_term e [<=] fv_term (open_term_wrt_term e (term_var_f x))) by auto with lngen.
assert (fv_term (open_term_wrt_term e (term_var_f x)) [=] PLC_ott.fv_term (PLC_ott.open_term_wrt_term e' (PLC_ott.term_var_f x))) by auto.
simpl in *. fsetdec.
Case "gen".
pick fresh x.
assert (PLC_ott.fv_term (PLC_ott.open_term_wrt_term e' (PLC_ott.term_var_f x)) [<=] PLC_ott.fv_term (PLC_ott.term_var_f x) ∪ PLC_ott.fv_term e') by auto with lngen.
assert (PLC_ott.fv_term e' [<=] PLC_ott.fv_term (PLC_ott.open_term_wrt_term e' (PLC_ott.term_var_f x))) by auto with lngen.
assert (fv_term (open_term_wrt_typ e (typ_var_f x)) [<=] fv_term e) by auto with lngen.
assert (fv_term e [<=] fv_term (open_term_wrt_typ e (typ_var_f x))) by auto with lngen.
assert (fv_term (open_term_wrt_typ e (typ_var_f x)) [=] PLC_ott.fv_term (PLC_ott.open_term_wrt_term e' (PLC_ott.term_var_f x))) by auto.
simpl in *.
fsetdec.
Qed.

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
assert (x ∉ PLC_ott.fv_term e').
assert (fv_term (open_term_wrt_typ e (typ_var_f x)) [=] PLC_ott.fv_term e') by auto using erase_fv.
assert (fv_term (open_term_wrt_typ e (typ_var_f x)) [<=] fv_term e). auto with lngen.
fsetdec.
autorewrite with lngen. auto.
Case "inst". destruct IHlc_term as [e' H1]. eauto.
Qed.

Lemma erase_red0 : forall e₁ e₂ e₁' e₂',
  red0 e₁ e₂ → erase e₁ e₁' →
  erase e₂ e₂' → PLC_ott.red0 e₁' e₂'.
Proof.
intros e₁ e₂ e₁' e₂' Hred H1 H2.
inversion Hred; subst; inversion H1; subst.
Case "beta".
inversion H6; subst. assert (e₂' = PLC_ott.open_term_wrt_term e' e₂'0).
eapply erase_uniqueness; eauto.
pick fresh x. rewrite (subst_term_intro x); auto.
rewrite (PLC_inf.subst_term_intro x); auto.
subst; eauto.
Case "beta_t".
inversion H7; subst. assert (e₂' = PLC_ott.open_term_wrt_term e'0 (PLC_ott.term_abs (PLC_ott.term_var_b 0))).
eapply erase_uniqueness; eauto.
pick fresh x. rewrite (tsubst_term_intro x); auto.
rewrite (PLC_inf.subst_term_intro x); auto.
assert (x ∉ PLC_ott.fv_term (PLC_ott.open_term_wrt_term e'0 (PLC_ott.term_var_f x))).
assert (fv_term (open_term_wrt_typ e (typ_var_f x)) [=] PLC_ott.fv_term (PLC_ott.open_term_wrt_term e'0 (PLC_ott.term_var_f x))) by eauto using erase_fv.
assert (fv_term (open_term_wrt_typ e (typ_var_f x)) [<=] fv_term e) by auto with lngen.
fsetdec.
autorewrite with lngen. auto.
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
Case "inst". inversion Herase1; subst; inversion Herase2; subst; eauto.
Case "gen". inversion Herase1; subst; inversion Herase2; subst.
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
SCase "gen". inversion Hwfterm; subst. inversion H7.
Case "inst". inversion H5; subst.
SCase "abs". inversion Hwfterm; subst. inversion H10.
SCase "gen". eauto.
Qed.

Lemma erase_id :
erase (term_abs (typ_forall (typ_var_b 0)) (term_var_b 0))
     (PLC_ott.term_abs (PLC_ott.term_var_b 0)).
Proof.
pick fresh x. apply erase_abs with (L := {{x}}); intros.
constructor; intros; unfold open_typ_wrt_typ; simpl; auto.
unfold open_term_wrt_term; unfold PLC_ott.open_term_wrt_term; simpl.
auto.
Qed.
Hint Immediate erase_id.

Lemma wftyp_id : forall Γ, wfenv Γ → wftyp Γ (typ_forall (typ_var_b 0)).
Proof.
intros Γ H. apply wftyp_forall with (L := dom Γ); intros.
unfold open_typ_wrt_typ; simpl; simpl_env; auto.
Qed.
Hint Immediate wftyp_id.

Lemma wfterm_id : forall Γ, wfenv Γ →
wfterm Γ (term_abs (typ_forall (typ_var_b 0)) (term_var_b 0)) (typ_arrow (typ_forall (typ_var_b 0)) (typ_forall (typ_var_b 0))).
Proof.
intros Γ H.
apply wfterm_abs with (L := dom Γ); intros.
unfold open_term_wrt_term; simpl; simpl_env; auto.
Qed.
Hint Resolve wfterm_id.

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
SCase "inst". edestruct IHHred with (e₁ := term_abs (typ_forall (typ_var_b 0)) (term_var_b 0)); eauto.
inversion H0; subst. inversion H1. pick fresh x. assert (term_var_b 0 ^ x ⇝ e' ^ x) as H1 by auto.
unfold open_term_wrt_term in H1; simpl in H1; inversion H1; subst. inversion H2.
Case "abs". inversion Herase; subst; inversion Hwfterm; subst.
SCase "abs". pick fresh x. edestruct (H0 x); eauto.
exists (term_abs τ0 (close_term_wrt_term x x0)).
apply red1_abs with (L := {{x}}); intros; auto.
rewrite <- subst_term_spec.
rewrite (subst_term_intro x); auto.
SCase "gen". pick fresh x. edestruct (H0 x); eauto.
exists (term_gen (close_term_wrt_typ x x0)).
apply red1_gen with (L := {{x}}); intros; auto.
rewrite <- tsubst_term_spec.
rewrite (tsubst_term_intro x); auto.
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
