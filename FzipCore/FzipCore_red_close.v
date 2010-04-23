Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_val.

(** Versions of red0 rules using [close], i.e. closer to the pencil
    and paper definitions *)
Lemma red0_beta_v_red_close : forall (t:typ) x (e1 e2:term),
  lc_typ t → lc_term e1 →
  val e2 →
  red0 (term_app (term_abs t (close_term_wrt_term x e1)) e2) NoEps
  (term_let e2 (close_term_wrt_term x e1)).
Proof.
intros t x e1 e2 H H0 H1. constructor; auto with lngen.
Qed.

Lemma red0_beta_v_let_close : forall (e1 e2:term) x,
  lc_term e1 → lc_term e2 →
  val e1 →
  red0 (term_let e1 (close_term_wrt_term x e2)) NoEps
  (subst_term e1 x e2).
Proof.
intros e1 e2 x H H0 H1. rewrite subst_term_spec.
constructor; auto with lngen.
Qed.

Lemma red0_beta_t_close : forall (e:term) (t:typ) a,
     lc_term e →
     lc_typ t →
     red0 (term_inst (term_gen (close_term_wrt_typ a e)) t) NoEps
     (tsubst_term t a e).
Proof.
intros e t a H H0. rewrite tsubst_term_spec.
constructor; auto with lngen.
Qed.

Lemma red0_open_exists_close : forall (b a:typvar) (e:term),
  result e →
  red0 (term_open (typ_var_f b) (term_exists (close_term_wrt_typ a e))) NoEps
  (tsubst_term (typ_var_f b) a e).
Proof.
intros b a e H. rewrite tsubst_term_spec.
pick fresh c and apply red0_open_exists.
rewrite <- tsubst_term_spec. auto using result_trenaming.
Qed.

Lemma red0_nu_sigma_close : forall (t:typ) (e:term) b a,
  lc_typ t → b ∉ ftv_typ t → a ∉ ftv_typ t → result e →
  red0
  (term_nu (close_term_wrt_typ b
    (term_sigma (typ_var_f b) t (close_term_wrt_typ a e))))
  NoEps
  (tsubst_term t a (tsubst_term (typ_var_f a) b e)).
Proof.
intros t e b a H H0 H1 H2.
unfold close_term_wrt_typ; simpl.
unfold typvar; destruct (b == b); try congruence.
pick fresh c and apply red0_nu_sigma; intros; subst; auto with lngen.
unfold open_typ_wrt_typ. rewrite <- tsubst_typ_spec_rec.
autorewrite with lngen. auto.
unfold open_term_wrt_typ in H5; inversion H5; subst; clear H5.
unfold open_term_wrt_typ; unfold close_term_wrt_typ.
rewrite <- tsubst_term_spec_rec.
replace (typ_var_f a0) with (tsubst_typ (typ_var_f b0) b (typ_var_f a0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite <- tsubst_term_spec_rec.
auto using result_trenaming.
unfold open_term_wrt_typ in H5; inversion H5; subst; clear H5.
unfold open_term_wrt_typ; unfold close_term_wrt_typ.
rewrite <- tsubst_term_spec_rec.
replace (typ_var_f a0) with (tsubst_typ (typ_var_f b0) b (typ_var_f a0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
unfold open_typ_wrt_typ. rewrite <- tsubst_typ_spec_rec.
repeat rewrite tsubst_typ_fresh_eq; auto.
rewrite <- tsubst_term_spec_rec.
destruct (a == b); subst.
rewrite tsubst_term_var_self.
  rewrite tsubst_term_fresh_eq with (t1 := typ_var_f b0) (a1 := b);
    auto with lngen.
  rewrite tsubst_term_tsubst_term with (a1 := b0); auto.
  rewrite tsubst_typ_fresh_eq; auto.
  rewrite tsubst_term_fresh_eq with (a1 := b0); auto.
  rewrite tsubst_term_tsubst_term; auto.
  rewrite tvar_tsubst.
  rewrite tsubst_term_fresh_eq with (a1 := a0); auto.
rewrite tsubst_term_tsubst_term with (a1 := b); auto.  
  rewrite tsubst_typ_fresh_eq; auto.
  rewrite tsubst_term_tsubst_term with (a1 := b0); auto.
  rewrite tsubst_typ_fresh_eq; auto.
  rewrite tsubst_term_tsubst_term with (a1 := b0); auto.
  rewrite tvar_tsubst.
  rewrite tsubst_term_fresh_eq with (a1 := b0); auto.
  rewrite tsubst_term_tsubst_term with (a1 := a0); auto.
  rewrite tvar_tsubst.
  rewrite tsubst_term_tsubst_term with (a1 := a0); auto.
  rewrite tvar_tsubst.
  rewrite tsubst_term_fresh_eq with (a1 := a0); auto.
  rewrite tsubst_term_tsubst_term; auto.
  rewrite tvar_tsubst.
  rewrite tsubst_term_tsubst_term; auto.
  rewrite tsubst_typ_fresh_eq; auto.
Qed.

Lemma red0_sigma_appL_close : forall (b a:typvar) (t:typ) (e1 e2:term),
  lc_typ t → a ∉ ftv_term e2 → result e1 →
  result e2 →
  red0
  (term_app (term_sigma (typ_var_f b) t (close_term_wrt_typ a e1)) e2)
  NoEps
  (term_sigma (typ_var_f b) t
    (close_term_wrt_typ a
      (term_app e1 (tsubst_term (typ_var_f a) b e2)))).
Proof.
intros b a t e1 e2 H H0 H1 H2.
unfold close_term_wrt_typ; simpl.
pick fresh c and apply red0_sigma_appL; intros; auto with lngen.
apply result_sigma_exists with (a := a); auto.
unfold open_term_wrt_typ. autorewrite with lngen. auto.
unfold open_term_wrt_typ. rewrite <- tsubst_term_spec_rec.
destruct (a == b); subst.
rewrite tsubst_term_var_self; auto.
rewrite tsubst_term_tsubst_term; auto. autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (a1 := a); auto.
Qed.

Lemma red0_sigma_appR_close : forall (b a:typvar) (t:typ) (e1 e2:term),
  lc_typ t → a ∉ ftv_term e1 → val e1 →
  result e2 →
  red0
  (term_app e1 (term_sigma (typ_var_f b) t (close_term_wrt_typ a e2)))
  NoEps
  (term_sigma (typ_var_f b) t
    (close_term_wrt_typ a
      (term_app (tsubst_term (typ_var_f a) b e1) e2))).
Proof.
intros b a t e1 e2 H H0 H1 H2.
unfold close_term_wrt_typ; simpl.
pick fresh c and apply red0_sigma_appR; intros; auto with lngen.
apply result_sigma_exists with (a := a); auto.
unfold open_term_wrt_typ. autorewrite with lngen. auto.
unfold open_term_wrt_typ. rewrite <- tsubst_term_spec_rec.
destruct (a == b); subst.
rewrite tsubst_term_var_self; auto.
rewrite tsubst_term_tsubst_term; auto. autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (a1 := a); auto.
Qed.

Lemma red0_sigma_letL_close : forall (b a x:typvar) (t:typ) (e1 e2:term),
  lc_typ t → a ∉ ftv_term e2 → result e1 →
  lc_term e2 →
  red0
  (term_let (term_sigma (typ_var_f b) t (close_term_wrt_typ a e1))
    (close_term_wrt_term x e2))
  NoEps
  (term_sigma (typ_var_f b) t
    (close_term_wrt_typ a
      (term_let e1
      (close_term_wrt_term x (tsubst_term (typ_var_f a) b e2))))).
Proof.
intros b a x t e1 e2 H H0 H1 H2.
unfold close_term_wrt_typ; simpl.
pick fresh c and apply red0_sigma_letL; intros; auto with lngen.
apply lc_term_let_exists with (x1 := x); autorewrite with lngen; auto.
apply lc_term_sigma_exists with (a1 := a); unfold open_term_wrt_typ;
  autorewrite with lngen; auto with lngen.
apply result_sigma_exists with (a := a); unfold open_term_wrt_typ;
  autorewrite with lngen; auto.
unfold open_term_wrt_typ; rewrite <- tsubst_term_spec_rec.
repeat rewrite tsubst_term_close_term_wrt_term; auto. f_equal.
destruct (a == b); subst.
rewrite tsubst_term_var_self; auto.
rewrite tsubst_term_tsubst_term; auto. autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (a1 := a); auto.
Qed.

Lemma red0_sigma_pairL_close : forall (b a:typvar) (t:typ) (e1 e2:term),
  lc_typ t → a ∉ ftv_term e2 → result e1 →
  result e2 →
  red0
  (term_pair (term_sigma (typ_var_f b) t (close_term_wrt_typ a e1)) e2)
  NoEps
  (term_sigma (typ_var_f b) t
    (close_term_wrt_typ a (term_pair e1 (tsubst_term (typ_var_f a) b e2)))).
Proof.
intros b a t e1 e2 H H0 H1 H2.
unfold close_term_wrt_typ; simpl.
pick fresh c and apply red0_sigma_pairL; intros; auto with lngen.
apply result_sigma_exists with (a := a); auto.
unfold open_term_wrt_typ. autorewrite with lngen. auto.
unfold open_term_wrt_typ. rewrite <- tsubst_term_spec_rec.
destruct (a == b); subst.
rewrite tsubst_term_var_self; auto.
rewrite tsubst_term_tsubst_term; auto. autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (a1 := a); auto.
Qed.

Lemma red0_sigma_pairR_close : forall (b a:typvar) (t:typ) (e1 e2:term),
  lc_typ t → a ∉ ftv_term e1 → val e1 →
  result e2 →
  red0
  (term_pair e1 (term_sigma (typ_var_f b) t (close_term_wrt_typ a e2)))
  NoEps
  (term_sigma (typ_var_f b) t
    (close_term_wrt_typ a (term_pair (tsubst_term (typ_var_f a) b e1) e2))).
Proof.
intros b a t e1 e2 H H0 H1 H2.
unfold close_term_wrt_typ; simpl.
pick fresh c and apply red0_sigma_pairR; intros; auto with lngen.
apply result_sigma_exists with (a := a); auto.
unfold open_term_wrt_typ. autorewrite with lngen. auto.
unfold open_term_wrt_typ. rewrite <- tsubst_term_spec_rec.
destruct (a == b); subst.
rewrite tsubst_term_var_self; auto.
rewrite tsubst_term_tsubst_term; auto. autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (a1 := a); auto.
Qed.

Lemma red0_sigma_inst_close : forall (b a:typvar) (t:typ) (e:term) (t':typ),
  lc_typ t' → lc_typ t → result e →
  a ∉ ftv_typ t' →
  red0 (term_inst (term_sigma (typ_var_f b) t (close_term_wrt_typ a e)) t')
  NoEps
  (term_sigma (typ_var_f b) t
    (close_term_wrt_typ a (term_inst e (tsubst_typ (typ_var_f a) b t')))).
Proof.
intros b a t e t' H H0 H1 H2.
unfold close_term_wrt_typ; simpl.
pick fresh c and apply red0_sigma_inst; intros; auto with lngen.
apply result_sigma_exists with (a := a); unfold open_term_wrt_typ;
  autorewrite with lngen; auto.
unfold open_typ_wrt_typ; rewrite <- tsubst_typ_spec_rec.
destruct (a == b); subst.
rewrite tsubst_typ_var_self; auto.
rewrite tsubst_typ_tsubst_typ; auto. autorewrite with lngen.
rewrite tsubst_typ_fresh_eq with (a1 := a); auto.
Qed.

Lemma red0_sigma_exists : forall (c b a:typvar) (t:typ) (e:term),
  lc_typ t → c ∉ ftv_typ t → c ≠ b → c ≠ a → result e →
  red0
  (term_exists
    (close_term_wrt_typ c
      (term_sigma (typ_var_f b) t (close_term_wrt_typ a e))))
  NoEps
  (term_sigma (typ_var_f b) t
    (close_term_wrt_typ a (term_exists (close_term_wrt_typ c e)))).
Proof.
intros c b a t e H H0 H1 H2 H3.
unfold close_term_wrt_typ; simpl.
unfold typvar in *; destruct (c == b); try congruence.
pick fresh d and apply red0_sigma_exists; intros;
  unfold open_typ_wrt_typ; unfold open_term_wrt_typ;
    autorewrite with lngen; auto with lngen.
rewrite <- tsubst_typ_spec_rec. autorewrite with lngen. auto.
rewrite <- tsubst_term_spec_rec.
replace (typ_var_f a0) with (tsubst_typ (typ_var_f c0) c (typ_var_f a0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite <- tsubst_term_spec_rec.
auto using result_trenaming.
rewrite <- tsubst_typ_spec_rec. autorewrite with lngen. auto.
repeat rewrite <- tsubst_term_spec_rec.
replace (typ_var_f a0) with (tsubst_typ (typ_var_f c0) c (typ_var_f a0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite <- tsubst_term_spec_rec.
autorewrite with lngen.
replace (typ_var_f c0) with (tsubst_typ (typ_var_f a0) a (typ_var_f c0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite <- tsubst_term_spec_rec.
autorewrite with lngen.
rewrite tsubst_term_tsubst_term; auto.
autorewrite with lngen. auto.
Qed.

Lemma red0_sigma_coerce_close : forall (b a:typvar) (t:typ) (e:term) (t':typ),
  lc_typ t' → lc_typ t → result e →
  a ∉ ftv_typ t' →
  red0 (term_coerce (term_sigma (typ_var_f b) t (close_term_wrt_typ a e)) t')
  NoEps
  (term_sigma (typ_var_f b) t
    (close_term_wrt_typ a (term_coerce e (tsubst_typ (typ_var_f a) b t')))).
Proof.
intros b a t e t' H H0 H1 H2.
unfold close_term_wrt_typ; simpl.
pick fresh c and apply red0_sigma_coerce; intros; auto with lngen.
apply result_sigma_exists with (a := a); unfold open_term_wrt_typ;
  autorewrite with lngen; auto.
unfold open_typ_wrt_typ; rewrite <- tsubst_typ_spec_rec.
destruct (a == b); subst.
rewrite tsubst_typ_var_self; auto.
rewrite tsubst_typ_tsubst_typ; auto. autorewrite with lngen.
rewrite tsubst_typ_fresh_eq with (a1 := a); auto.
Qed.

Lemma red0_sigma_sigma_close : forall (b1 b2 a1 a2:typvar) (t1 t2:typ)
  (e:term),
  lc_typ t1 → lc_typ t2 → result e → a1 ≠ b2 → a2 ≠ b1 → a1 ≠ a2 →
  a2 ∉ ftv_typ t1 →
  red0
  (term_sigma (typ_var_f b1) t1
    (close_term_wrt_typ a1
      (term_sigma (typ_var_f b2) t2 (close_term_wrt_typ a2 e))))
  Eps
  (term_sigma (typ_var_f b2) (tsubst_typ t1 a1 t2)
    (close_term_wrt_typ a2
      (term_sigma (typ_var_f b1) t1 (close_term_wrt_typ a1 e)))).
Proof.
intros b1 b2 a1 a2 t1 t2 e H H0 H1 H2 H3 H4 H5.
unfold close_term_wrt_typ; simpl.
unfold typvar in *; destruct (a1 == b2); try congruence.
unfold typvar in *; destruct (a2 == b1); try congruence.
rewrite tsubst_typ_spec.
pick fresh c and apply red0_sigma_sigma; intros; auto with lngen.
apply lc_term_sigma_exists with (a1 := a1); auto.
unfold open_term_wrt_typ; simpl.
apply lc_term_sigma_exists with (a1 := a2); auto.
unfold close_typ_wrt_typ. autorewrite with lngen. auto.
unfold open_term_wrt_typ. autorewrite with lngen. auto with lngen.
rewrite <- tsubst_term_spec_rec.
replace (typ_var_f c) with (tsubst_typ (typ_var_f a0) a1 (typ_var_f c))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite <- tsubst_term_spec_rec. auto using result_trenaming.
unfold open_typ_wrt_typ. rewrite <- tsubst_typ_spec_rec.
  autorewrite with lngen. auto.
repeat rewrite <- tsubst_term_spec_rec.
replace (typ_var_f a3) with (tsubst_typ (typ_var_f a0) a1 (typ_var_f a3))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
autorewrite with lngen.
replace (typ_var_f a0) with (tsubst_typ (typ_var_f a3) a2 (typ_var_f a0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
autorewrite with lngen.
repeat rewrite <- tsubst_term_spec_rec.
rewrite tsubst_term_tsubst_term; auto. autorewrite with lngen. auto.
Qed.
