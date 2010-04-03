Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_val.

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
