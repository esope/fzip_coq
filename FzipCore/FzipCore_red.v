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
Case "sigma_nu".
  apply (lc_term_nu_exists c).
  unfold open_term_wrt_typ; simpl.
  pick fresh a. apply (lc_term_sigma_exists a); auto.
  apply H; auto.
  apply result_regular. apply H1; auto.
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
Case "sigma_nu".
  pick fresh a. apply (lc_term_sigma_exists a); auto.
  unfold open_term_wrt_typ; simpl.
  apply (lc_term_nu_exists c); auto.
  unfold open_term_wrt_typ. rewrite <- H2; auto.
  apply result_regular; auto.
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
*)

Lemma red0_trenaming : forall a b e e',
  b ∉ ftv_term e →
  red0 e e' →
  red0 (tsubst_term (typ_var_f b) a e) (tsubst_term (typ_var_f b) a e').
Proof with auto using val_trenaming, result_trenaming with lngen.
intros a b e e' Hb H. inversion H; subst; simpl in *.
Case "beta_v". rewrite tsubst_term_open_term_wrt_term; auto.
constructor... unsimpl (tsubst_term (typ_var_f b) a (term_abs t e1))...
Case "projL". inversion H0; subst; try congruence...
Case "projR". inversion H0; subst; try congruence...
Case "beta_t". rewrite tsubst_term_open_term_wrt_typ; auto.
constructor... unsimpl (tsubst_term (typ_var_f b) a (term_gen e0))...
Case "open exists". destruct (b0 == a); subst.
SCase "b0 = a". rewrite tsubst_term_open_term_wrt_typ; auto.
simpl. destruct (a == a); try congruence.
pick fresh c and apply red0_open_exists.
rewrite tsubst_term_open_term_wrt_typ_var...
SCase "b0 ≠ a". rewrite tsubst_term_open_term_wrt_typ; auto.
simpl. destruct (b0 == a); try congruence.
pick fresh c and apply red0_open_exists.
rewrite tsubst_term_open_term_wrt_typ_var...
Case "nu sigma".  pick fresh c and apply red0_nu_sigma; intros; subst.
rewrite tsubst_typ_open_typ_wrt_typ_var...
rewrite tsubst_typ_open_typ_wrt_typ_var...
rewrite tsubst_term_open_term_wrt_typ_var...
inversion H7; subst; clear H7.
replace (typ_var_f b0) with (tsubst_typ (typ_var_f b) a (typ_var_f b0)).
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
apply result_trenaming. eapply (H3 b0 a0); auto. reflexivity.
autorewrite with lngen; auto.
inversion H7; subst; clear H7.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
replace (open_term_wrt_typ_rec 1 (typ_var_f b0) (tsubst_term (typ_var_f b) a e0))
with (open_term_wrt_typ_rec 1 (tsubst_typ (typ_var_f b) a (typ_var_f b0)) (tsubst_term (typ_var_f b) a e0)).
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite <- tsubst_term_tsubst_term; auto.
f_equal. eapply H4; auto. reflexivity.
f_equal. apply tsubst_typ_fresh_eq; auto.
Case "coerce app". constructor...
unsimpl (tsubst_term (typ_var_f b) a (term_abs t2' e1))...
Case "coerce fst". inversion H2; subst; try congruence...
Case "coerce snd". inversion H2; subst; try congruence...
Case "coerce inst". rewrite tsubst_typ_open_typ_wrt_typ; auto.
constructor...
unsimpl (tsubst_typ (typ_var_f b) a (typ_forall t1))...
unsimpl (tsubst_term (typ_var_f b) a (term_gen e0))...
Case "coerce open". destruct (b0 == a); subst.
SCase "b0 = a". rewrite tsubst_typ_open_typ_wrt_typ; auto.
simpl. destruct (a == a); try congruence. constructor...
unsimpl (tsubst_typ (typ_var_f b) a (typ_exists t))...
unsimpl (tsubst_term (typ_var_f b) a (term_exists e0))...
SCase "b0 ≠ a". rewrite tsubst_typ_open_typ_wrt_typ; auto.
simpl. destruct (b0 == a); try congruence. constructor...
unsimpl (tsubst_typ (typ_var_f b) a (typ_exists t))...
unsimpl (tsubst_term (typ_var_f b) a (term_exists e0))...
Case "coerce coerce". constructor...
unsimpl (tsubst_term (typ_var_f b) a (term_coerce e0 t1))...
Case "sigma appL". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_appL...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e1))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e1))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H2...
rewrite tsubst_term_fresh_eq with (t1 := typ_var_f b)...
rewrite tsubst_term_fresh_eq with (a1 := b)...
SCase "b0 ≠ a". pick fresh c and apply red0_sigma_appL...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e1))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e1))...
simpl. destruct (b0 == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b0); subst.
elimtype False. auto.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H2...

Case "sigma appR". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_appR...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e2))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e2))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H2...
rewrite tsubst_term_fresh_eq with (t1 := typ_var_f b)...
rewrite tsubst_term_fresh_eq with (a1 := b)...
SCase "b0 ≠ a". pick fresh c and apply red0_sigma_appR...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e2))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e2))...
simpl. destruct (b0 == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b0); subst.
elimtype False. auto.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H2...

Case "sigma pairL". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_pairL...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e1))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e1))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H2...
rewrite tsubst_term_fresh_eq with (t1 := typ_var_f b)...
rewrite tsubst_term_fresh_eq with (a1 := b)...
SCase "b0 ≠ a". pick fresh c and apply red0_sigma_pairL...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e1))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e1))...
simpl. destruct (b0 == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b0); subst.
elimtype False. auto.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H2...

Case "sigma pairR". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_pairR...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e2))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e2))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H2...
rewrite tsubst_term_fresh_eq with (t1 := typ_var_f b)...
rewrite tsubst_term_fresh_eq with (a1 := b)...
SCase "b0 ≠ a". pick fresh c and apply red0_sigma_pairR...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e2))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e2))...
simpl. destruct (b0 == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b0); subst.
elimtype False. auto.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H2...

Case "sigma fst". destruct (b0 == a); subst.
SCase "b0 = a". apply red0_sigma_fst...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e0))...
simpl. destruct (a == a); try congruence.
SCase "b0 ≠ a". apply red0_sigma_fst...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e0))...
simpl. f_equal. destruct (b0 == a); try congruence.


Case "sigma snd". destruct (b0 == a); subst.
SCase "b0 = a". apply red0_sigma_snd...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e0))...
simpl. destruct (a == a); try congruence.
SCase "b0 ≠ a". apply red0_sigma_snd...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e0))...
simpl. f_equal. destruct (b0 == a); try congruence.

Case "sigma inst". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_inst...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e0))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_typ_tsubst_typ...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ_var...
rewrite H2...
rewrite tsubst_typ_fresh_eq with (t1 := typ_var_f b)...
rewrite tsubst_typ_fresh_eq with (a1 := b)...
SCase "b0 ≠ a". pick fresh c and apply red0_sigma_inst...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e0))...
simpl. destruct (b0 == a); try congruence.
rewrite tsubst_typ_tsubst_typ...
simpl. unfold typvar; destruct (b == b0); subst.
elimtype False. auto.
rewrite tsubst_typ_open_typ_wrt_typ_var...
rewrite H2...

Case "sigma open". destruct (b0 == a); subst.
SCase "b0 = a". destruct (c == a); subst.
SSCase "c = a". apply red0_sigma_open...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e0))...
simpl. destruct (a == a); try congruence.
SSCase "c ≠ a". apply red0_sigma_open...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e0))...
simpl. destruct (a == a); try congruence.
SCase "b0 ≠ a". destruct (c == a); subst.
SSCase "c = a". apply red0_sigma_open...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e0))...
simpl. destruct (b0 == a); try congruence.
SSCase "c ≠ a". apply red0_sigma_open...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e0))...
simpl. destruct (b0 == a); try congruence.

Case "sigma nu". rewrite tsubst_typ_open_typ_wrt_typ...
simpl. destruct (b0 == a); subst.
SCase "b0 = a". unfold typvar; destruct (c == a); subst.
SSCase "c = a".

ICI

 pick fresh c and apply red0_sigma_nu; intros.
rewrite tsubst_typ_open_typ_wrt_typ_var...
rewrite tsubst_typ_open_typ_wrt_typ_var...
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
replace (typ_var_f a0) with (tsubst_typ (typ_var_f b) a (typ_var_f a0)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec...
simpl. unfold typvar; destruct (a0 == a); subst; auto.
  assert (a ≠ a) by auto. congruence.
simpl. unfold typvar; destruct (c == a); subst; auto.
  assert (a ≠ a) by auto. congruence.
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
replace (typ_var_f a0) with (tsubst_typ (typ_var_f b) a (typ_var_f a0)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec...
rewrite H3...
simpl. unfold typvar; destruct (a0 == a); subst; auto.
  assert (a ≠ a) by auto. congruence.
simpl. unfold typvar; destruct (c == a); subst; auto.
  assert (a ≠ a) by auto. congruence.


SSCase "c ≠ a".




SCase "b0 ≠ a".

Qed.

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

(*
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
