Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_pure.
Require Import FzipCore_zip.
Require Import FzipCore_env_typ.
Require Import FzipCore_typeq.
Require Import FzipCore_term.
Require Import FzipCore_renameT.

Ltac simpl_eq a b :=
  unfold typvar in *; unfold termvar in *;
  destruct (a == b); try congruence.

Ltac simpl_close :=
  unfold close_typ_wrt_typ; simpl close_typ_wrt_typ_rec;
  unfold close_term_wrt_typ; simpl close_term_wrt_typ_rec;
  unfold close_term_wrt_term; simpl close_term_wrt_term_rec.

Tactic Notation "simpl_close*" := repeat progress simpl_close.

Ltac simpl_open :=
  unfold open_typ_wrt_typ; simpl open_typ_wrt_typ_rec;
  unfold open_term_wrt_typ; simpl open_term_wrt_typ_rec;
  unfold open_term_wrt_term; simpl open_term_wrt_term_rec.

Tactic Notation "simpl_open*" := repeat progress simpl_open.

Definition Abs x t e := term_abs t (close_term_wrt_term x e).
Definition App := term_app.
Definition Let x e e' := term_let e (close_term_wrt_term x e').
Definition Gen a e := term_gen (close_term_wrt_typ a e).
Definition Inst := term_inst.
Definition Pair := term_pair.
Definition Fst := term_fst.
Definition Snd := term_snd.
Definition Ex a e := term_exists (close_term_wrt_typ a e).
Definition Open a e := term_open (typ_var_f a) e.
Definition Nu a e := term_nu (close_term_wrt_typ a e).
Definition Sig b a t e := term_sigma (typ_var_f b) t (close_term_wrt_typ a e).
Definition Coerce := term_coerce.

Definition Arrow := typ_arrow.
Definition Prod := typ_prod.
Definition Forall a t := typ_forall (close_typ_wrt_typ a t).
Definition Exists a t := typ_exists (close_typ_wrt_typ a t).

Ltac unfold_smart_cons :=
  unfold Abs; unfold App; unfold Let;
  unfold Gen; unfold Inst;
  unfold Pair; unfold Fst; unfold Snd;
  unfold Ex; unfold Open;
  unfold Nu; unfold Sig; unfold Coerce;
  unfold Arrow; unfold Prod; unfold Forall; unfold Exists.

Ltac unfold_fzip := repeat progress unfold_smart_cons.

Definition term_id a x :=
  Gen a (Abs x (typ_var_f a) (term_var_f x)).

Definition typ_id t := Arrow t t.

Lemma wfterm_identity : forall x a, x ≠ a →
  nil ⊢ term_id a x ~: Forall a (typ_id (typ_var_f a)).
Proof.
intros x a H. unfold term_id. unfold typ_id.
unfold_fzip. simpl_close. simpl_eq a a.
simpl_eq x x. simpl_close.
pick fresh b1 and apply wfterm_gen; auto; simpl_open.
pick fresh y1 and apply wfterm_abs; auto with fzip; simpl_open.
auto 7 with fzip.
Qed.

Lemma wftyp_poly_typ_id : forall a, nil ⊢ Forall a (typ_id (typ_var_f a)) ok.
Proof.
intros a. pick fresh x.
eapply wfterm_wftyp. eauto using wfterm_identity.
Qed.

Lemma wfterm_projL : forall a b x, a ≠ b →
  nil ⊢
  Gen a (Gen b (Abs x (Prod (typ_var_f a) (typ_var_f b))
    (Fst (term_var_f x)))) ~:
  Forall a (Forall b (Arrow (Prod (typ_var_f a) (typ_var_f b))
    (typ_var_f a))).
Proof.
intros.
unfold_fzip. simpl_close. simpl_eq b b. simpl_eq x x. simpl_eq b a.
simpl_close. simpl_eq a a. clear.
pick fresh a and apply wfterm_gen; auto; simpl_open.
pick fresh b and apply wfterm_gen; auto with fzip; simpl_open.
pick fresh x and apply wfterm_abs; auto with fzip; simpl_open.
apply wfterm_fst with (t2 := typ_var_f b).
auto 9 with fzip.
Qed.

Lemma wfterm_projR : forall a b x, a ≠ b →
  nil ⊢
  Gen a (Gen b (Abs x (Prod (typ_var_f a) (typ_var_f b))
    (Snd (term_var_f x)))) ~:
  Forall a (Forall b (Arrow (Prod (typ_var_f a) (typ_var_f b))
    (typ_var_f b))).
Proof.
intros.
unfold_fzip. simpl_close. simpl_eq b b. simpl_eq x x. simpl_eq b a.
simpl_close. simpl_eq a a. clear.
pick fresh a and apply wfterm_gen; auto; simpl_open.
pick fresh b and apply wfterm_gen; auto with fzip; simpl_open.
pick fresh x and apply wfterm_abs; auto with fzip; simpl_open.
apply wfterm_snd with (t1 := typ_var_f a).
auto 9 with fzip.
Qed.

Definition typ_nat a :=
  Forall a (Arrow (typ_var_f a)
    (Arrow (typ_id (typ_var_f a)) (typ_var_f a))).

Definition term_zero a x f :=
  Gen a (Abs x (typ_var_f a) (Abs f (typ_id (typ_var_f a))
    (term_var_f x))).

Lemma wfterm_zero : forall a b x f, x ≠ f →
  nil ⊢ term_zero a x f ~: typ_nat b.
Proof.
intros a b x f H. unfold term_zero. unfold typ_nat.
unfold_fzip. simpl_close. simpl_eq a a. simpl_eq f x. simpl_eq b b.
simpl_close. simpl_eq x x. simpl_close. clear.
pick fresh a and apply wfterm_gen; simpl_open; auto.
pick fresh x and apply wfterm_abs; simpl_open; auto with fzip.
pick fresh f and apply wfterm_abs; simpl_open; auto with fzip.
auto 10 with fzip.
Qed.

Lemma wftyp_nat : forall a, nil ⊢ typ_nat a ok.
Proof.
intros a. pick fresh b. pick fresh x. pick fresh f.
eapply wfterm_wftyp. apply (wfterm_zero b a x f). auto.
Qed.

Definition term_plus a n x f :=
  Abs n (typ_nat a)
  (Gen a
    (Abs x (typ_var_f a)
      (Abs f (typ_id (typ_var_f a))
        (App (term_var_f f)
          (App
            (App (Inst (term_var_f n) (typ_var_f a))
              (term_var_f x))
            (term_var_f f)))))).

Lemma wfterm_plus : forall a n x f,
  n ≠ x → n ≠ f → x ≠ f →
  nil ⊢ term_plus a n x f ~: typ_id (typ_nat a).
Proof.
intros a n x f H H0 H1. unfold term_plus. unfold typ_id.
unfold typ_nat.
unfold_fzip. simpl_close. simpl_eq f f. simpl_eq a a.
simpl_eq f n. simpl_eq f x. simpl_close. simpl_eq x n.
simpl_eq x x. simpl_close. simpl_eq n n. clear.
pick fresh n and apply wfterm_abs; simpl_open; auto.
pick fresh a and apply wfterm_gen; simpl_open; auto with fzip.
pick fresh x and apply wfterm_abs; simpl_open; auto with fzip.
pick fresh f and apply wfterm_abs; simpl_open; auto 6 with fzip.
remember ([(f, T (typ_arrow (typ_var_f a) (typ_var_f a)))] ++
   [(x, T (typ_var_f a))] ++
   [(a, U)] ++
   [(n,
    T
      (typ_forall
         (typ_arrow (typ_var_b 0)
            (typ_arrow (typ_arrow (typ_var_b 0) (typ_var_b 0)) (typ_var_b 0)))))] ++
   nil) as Γ.
assert (Γ ⊢ ok). subst.
  constructor; auto. constructor; auto.
  constructor; auto. constructor; auto. constructor; auto.
  constructor; auto. constructor; auto.
  pick fresh b and apply wftyp_forall; simpl_open. auto 8.
  constructor; auto. constructor; auto.
  constructor; auto. constructor; auto. constructor; auto.
  pick fresh b and apply wftyp_forall; simpl_open. auto 8.
assert (lc_env Γ) by auto using wfenv_lc_env.
assert (pure Γ). subst. auto 7 with fzip.
assert (zip Γ Γ Γ) by auto using zip_self with lngen.
apply wfterm_app with (G1 := Γ) (G2 := Γ) (t2 := typ_var_f a).
auto.
subst; auto.
apply wfterm_app with (G1 := Γ) (G2 := Γ)
  (t2 := typ_id (typ_var_f a)).
auto.
apply wfterm_app with (G1 := Γ) (G2 := Γ) (t2 := typ_var_f a).
auto.
rewrite <- tsubst_typ_var_self with (a := a).
rewrite tsubst_typ_spec.
apply wfterm_inst. constructor; subst; auto 6.
simpl_close. simpl_eq a a.
constructor; auto; subst; auto 6.
constructor; auto; subst; auto.
constructor; auto; subst; auto.
Qed.

Lemma wfterm_sigma_pair : forall a b x f,
  x ≠ f → x ≠ a →
  b ~ E ⊢
  Pair
    (Sig b a (typ_nat a) (Coerce (term_zero a x f) (typ_var_f a)))
    (Inst (term_id a x) (typ_var_f b)) ~:
  Prod (typ_var_f b) (typ_id (typ_var_f b)).
Proof.
intros. unfold_fzip. simpl_close. simpl_eq a a. simpl_eq f x.
simpl_close. simpl_eq x x. simpl_close.
apply wfterm_pair with (G1 := b ~ E ++ nil) (G2 := b ~ U ++ nil).
simpl_env; auto with fzip.
rewrite_env (nil ++ b ~ @E typ ++ nil).
pick fresh c and apply wfterm_sigma; simpl_open; auto.
autorewrite with lngen.
apply wfterm_coerce with (t' := typ_nat a).
apply wftypeq_sym. apply wftypeq_eq; auto. constructor; auto using wftyp_nat.
pick fresh d and apply wfterm_gen; simpl_open; auto with fzip.
simpl_eq a a. simpl_open.
pick fresh y and apply wfterm_abs; simpl_open; auto with fzip.
pick fresh z and apply wfterm_abs; simpl_open; auto 6 with fzip.
constructor. auto 7 with fzip.
auto 9 using wftyp_nat.
auto.
rewrite <- tsubst_typ_var_self with (a := b). rewrite tsubst_typ_spec.
constructor; auto.
simpl_close. simpl_eq b b.
replace (typ_forall (typ_arrow (typ_var_b 0) (typ_var_b 0))) with
  (Forall a (typ_id (typ_var_f a))).
rewrite_env (nil ++ b ~ @U typ ++ nil).
apply wfterm_weakening; auto using wfterm_identity with fzip.
unfold_fzip. simpl_close. simpl_eq a a.
Qed.

Lemma wfterm_open_exists_sigma_zero : forall a b c d e x f,
  a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ x → a ≠ f →
  b ≠ c → b ≠ d → b ≠ e → b ≠ x → b ≠ f →
  c ≠ d → c ≠ e → c ≠ x → c ≠ f →
  d ≠ e → d ≠ x → d ≠ f →
  e ≠ x → e ≠ f →
  x ≠ f →
  b ~ E ⊢
  Open b (Ex c (Sig c a (typ_nat d)
    (Coerce (term_zero e x f) (typ_var_f a)))) ~:
  typ_var_f b.
Proof.
intros a b c d e x f H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
  H11 H12 H13 H14 H15 H16 H17. intros H18 H19.
rewrite_env (nil ++ b ~ @E typ ++ nil).
Opaque typ_nat. Opaque term_zero.
unfold_fzip. simpl_close. simpl_eq c c. simpl_eq a a. simpl_close.
replace (typ_var_f b) with (open_typ_wrt_typ (typ_var_b 0) (typ_var_f b))
  by reflexivity.
apply wfterm_open; auto. pick fresh a' and apply wfterm_exists.
simpl_open. rewrite <- tsubst_typ_spec_rec. rewrite tsubst_typ_fresh_eq.
rewrite <- tsubst_term_spec_rec. rewrite tsubst_term_fresh_eq.
rewrite_env (nil ++ a' ~ @E typ ++ nil).
pick fresh b' and apply wfterm_sigma; simpl_open; auto.
rewrite <- tsubst_term_spec_rec. rewrite tsubst_term_fresh_eq.
simpl tsubst_typ. simpl_eq a' a'.
apply wfterm_coerce with (t' := typ_nat d). auto using wftyp_nat.
rewrite_env (nil ++ b' ~ Eq (typ_nat d) ++ nil).
apply wfterm_weakening; auto using wfterm_zero, wftyp_nat with fzip.
Transparent term_zero. simpl. simpl_eq e e. simpl_close. simpl_eq f x.
simpl_close. simpl_eq x x. simpl_close. auto.
Transparent term_zero. simpl. simpl_eq e e. simpl_close. simpl_eq f x.
simpl_close. simpl_eq x x. simpl_close. auto.
Transparent typ_nat. simpl. simpl_eq d d. auto.
Qed.

Definition F_exists a τ b :=
  Forall b (Arrow (Forall a (Arrow τ (typ_var_f b))) (typ_var_f b)).

Definition F_pack τ M a τ' b f :=
  Gen b (Abs f (Forall a (Arrow τ' (typ_var_f b)))
    (App (Inst (term_var_f f) τ) M)).

Definition F_unpack M a x τ M' τ' :=
  App (Inst M τ') (Gen a (Abs x τ M')).

Definition Fzip_pack τ M a τ' :=
  Ex a (Sig a a τ (Coerce M τ')).

Definition Fzip_unpack M a x M' :=
  Nu a (Let x (Open a M) M').

Lemma wfterm_F_pack : forall Γ M a τ₀ τ b f,
  a ≠ b → a ≠ f → b ≠ f → b ∉ dom Γ → f ∉ dom Γ → pure Γ →
  Γ ⊢ τ₀ ok → a ~ U ++ Γ ⊢ τ ok →
  Γ ⊢ M ~: tsubst_typ τ₀ a τ →
  Γ ⊢ F_pack τ₀ M a τ b f ~: F_exists a τ b.
Proof.
intros Γ M a τ₀ τ b f H H0 H1 H2 H3 H4 H5 H6 H7.
assert (b ∉ ftv_typ τ). apply wftyp_ftv in H6. simpl_env in H6. fsetdec.
assert (b ∉ ftv_typ τ₀). apply wftyp_ftv in H5. fsetdec.
unfold F_pack; unfold F_exists.
unfold_fzip. simpl_close. simpl_eq a b. simpl_eq f f. simpl_eq b b. simpl_close.
simpl_eq b b. clear e e0 e1 n.
pick fresh c and apply wfterm_gen; auto. simpl_open.
repeat rewrite <- tsubst_typ_spec_rec.
repeat rewrite <- tsubst_term_spec_rec.
rewrite tsubst_typ_close_typ_wrt_typ_rec; auto.
rewrite tsubst_term_close_term_wrt_term_rec; auto.
pick fresh x and apply wfterm_abs; auto with fzip. simpl_open.
repeat rewrite <- subst_term_spec_rec.
remember ([(x,
    T
      (typ_forall
         (typ_arrow
            (close_typ_wrt_typ_rec 0 a (tsubst_typ (typ_var_f c) b τ))
            (typ_var_f c))))] ++ [(c, U)] ++ Γ) as G.
assert (G ⊢ ok). subst.
  constructor; auto. pick fresh d and apply wftyp_forall. simpl_open.
  rewrite <- tsubst_typ_spec_rec.
  rewrite tsubst_typ_tsubst_typ; auto.
  rewrite tsubst_typ_fresh_eq with (a1 := a); simpl; simpl_env; auto.
  constructor; auto.
  replace (d ~ @U typ) with (env_map (tsubst_typ (typ_var_f c) b) (d ~ U))
    by reflexivity.
  apply wftyp_renameU; auto. apply wftyp_weakening; auto.
  rewrite_env (env_map (tsubst_typ (typ_var_f d) a) nil ++ [(d, U)] ++ Γ).
  apply wftyp_renameU; auto. constructor; auto; eauto with fzip.
  constructor; auto. constructor; auto. constructor; auto. eauto with fzip.
eapply wfterm_app with (G1 := G) (G2 := G)
  (t2 := tsubst_typ (tsubst_typ (typ_var_f c) b τ₀) a
    (tsubst_typ (typ_var_f c) b τ)).
apply zip_self; subst; auto with fzip lngen. apply lc_env_app.
  apply lc_env_T.
  apply lc_typ_forall_exists with (a1 := a). simpl_open.
  autorewrite with lngen. eauto with lngen.
  apply lc_env_app; auto with lngen. eapply wftyp_lc_env; eauto.
repeat rewrite tsubst_typ_fresh_eq with (a1 := b); auto.
replace (typ_arrow
     (tsubst_typ τ₀ a τ) (typ_var_f c)) with
(tsubst_typ τ₀ a (typ_arrow τ (typ_var_f c))).
rewrite tsubst_typ_spec with (a1 := a). apply wfterm_inst.
subst. rewrite_env (nil ++
([(x, T
      (typ_forall
         (typ_arrow
            (close_typ_wrt_typ_rec 0 a (tsubst_typ (typ_var_f c) b τ))
            (typ_var_f c))))] ++ [(c, U)]) ++ Γ).
apply wftyp_weakening; auto.
constructor; subst; auto with fzip.
  rewrite tsubst_typ_fresh_eq with (a1 := b); auto.
  simpl_close. simpl_eq a c. assert (c ≠ a) by auto. congruence. auto.
simpl. simpl_eq c a. assert (c ≠ a) by auto. congruence.
rewrite_env (nil ++ G). apply wfterm_subst with (Γ₁ := G) (Γ₂ := G)
(τ₁ := typ_forall
  (typ_arrow
    (close_typ_wrt_typ_rec 0 a (tsubst_typ (typ_var_f c) b τ))
    (typ_var_f c))).
apply zip_self; subst; auto with fzip lngen. apply lc_env_app.
  apply lc_env_T.
  apply lc_typ_forall_exists with (a1 := a). simpl_open.
  autorewrite with lngen. eauto with lngen.
  apply lc_env_app; auto with lngen. eapply wftyp_lc_env; eauto.
constructor; subst; auto with fzip.
subst; auto with fzip.
apply wfterm_weakening; intros; auto with fzip.
assert (b ∉ ftv_term M). apply wfterm_ftv in H7. clear Fr Fr0. fsetdec.
rewrite tsubst_term_fresh_eq; auto.
repeat rewrite tsubst_typ_fresh_eq with (a1 := b); auto.
subst. apply wfterm_weakening; intros; auto with fzip.
apply wfterm_weakening; intros; auto with fzip.
constructor; auto. eauto with fzip.
intro. analyze_binds H13. apply (H4 a0); auto.
constructor; try solve [subst; auto].
rewrite_env (nil ++ G). subst. apply wftyp_weakening; auto. simpl_env.
eapply wfenv_wftyp_T3; eauto.
intro. subst. analyze_binds H12. apply (H4 a0); auto.
Qed.

Lemma wfterm_F_unpack : forall Γ M M' τ τ' a b x,
  a ≠ b → x ≠ b → b ∉ dom Γ ∪ ftv_typ τ → x ∉ dom Γ →
  pure Γ →
  Γ ⊢ M ~: F_exists a τ b →
  x ~ T τ ++ a ~ U ++ Γ ⊢ M' ~: τ' →
  a ∉ ftv_typ τ' →
  Γ ⊢ F_unpack M a x τ M' τ' ~: τ'.
Proof.
unfold F_exists. unfold F_unpack. unfold_fzip. simpl_close.
intros Γ M M' τ τ' a b x H H0 H1 H2 H3 H4 H5 H6.
simpl_eq a b. simpl_eq b b. simpl in H4. simpl_eq b b.
assert (a ≠ x). assert (uniq (x ~ T τ ++ a ~ U ++ Γ)) by eauto with lngen.
  solve_uniq.
assert (b ∉ ftv_typ τ'). apply wfterm_wftyp in H5. apply wftyp_ftv in H5.
  simpl_env in H5. fsetdec.
assert (b ∉ ftv_term M). apply wfterm_ftv in H4. fsetdec.
assert (a ∉ ftv_term M). apply wfterm_ftv in H4.
  assert (uniq (x ~ T τ ++ a ~ U ++ Γ)) by eauto with lngen. solve_uniq.
assert (b ∉ ftv_term M'). apply wfterm_ftv in H5. simpl_env in H5. fsetdec.
apply wfterm_app with (G1 := Γ) (G2 := Γ)
  (t2 := tsubst_typ τ' b
      (typ_forall
        (typ_arrow
          (close_typ_wrt_typ_rec 0 a τ)
          (typ_var_f b)))).
apply zip_self; auto with fzip.
  apply wfterm_wfenv in H4. apply wfenv_lc_env in H4. auto.
  eauto with lngen.
replace (typ_arrow
  (tsubst_typ τ' b
    (typ_forall (typ_arrow (close_typ_wrt_typ_rec 0 a τ) (typ_var_f b))))
  τ') with
(tsubst_typ τ' b
  (typ_arrow
    (typ_forall (typ_arrow (close_typ_wrt_typ_rec 0 a τ) (typ_var_f b)))
     (typ_var_f b))).
rewrite tsubst_typ_spec. apply wfterm_inst; auto.
apply wfterm_wftyp in H5.
apply wftyp_tsubst with (τ' := (typ_forall (typ_var_b 0))) in H5.
rewrite tsubst_typ_fresh_eq in H5; auto.
rewrite_env (nil ++
  env_map (tsubst_typ (typ_forall (typ_var_b 0)) a) [(x, T τ)] ++ Γ) in H5.
unfold env_map in H5. simpl map in H5.
apply wftyp_subst in H5. auto.
pick fresh c and apply wftyp_forall. simpl_open. constructor; auto.
  constructor; auto. eapply wfterm_wfenv; eauto.
simpl_close. simpl_eq b b.
simpl. simpl_eq b b.
simpl. simpl_eq b b. pick fresh c and apply wfterm_gen; auto. simpl_open.
rewrite tsubst_typ_close_typ_wrt_typ_rec; eauto with lngen.
rewrite <- tsubst_term_spec_rec. repeat rewrite <- tsubst_typ_spec_rec.
replace (open_typ_wrt_typ_rec 0 (typ_var_f c) τ') with
  (open_typ_wrt_typ τ' (typ_var_f c)) by reflexivity.
rewrite open_typ_wrt_typ_lc_typ; eauto with lngen.
unsimpl
(tsubst_term (typ_var_f c) a (term_abs τ (close_term_wrt_term_rec 0 x M'))).
rewrite tsubst_typ_fresh_eq with (a1 := b); auto.
rewrite <- tsubst_typ_fresh_eq with (a1 := a)
  (t1 := (typ_var_f c)) (t2 := τ'); auto.
unsimpl (tsubst_typ (typ_var_f c) a (typ_arrow τ τ')).
rewrite_env (env_map (tsubst_typ (typ_var_f c) a) nil ++ c ~ U ++ Γ).
apply wfterm_renameU; auto.
simpl_env. pick fresh y and apply wfterm_abs; auto with fzip.
simpl_open; rewrite <- subst_term_spec_rec.
rewrite_env (nil ++ y ~ T τ ++ a ~ U ++ Γ).
apply wfterm_renameT; auto.
Qed.

Lemma wfterm_Fzip_pack : forall Γ M a τ₀ τ,
  pure Γ →
  Γ ⊢ τ₀ ok → a ~ U ++ Γ ⊢ τ ok →
  Γ ⊢ M ~: tsubst_typ τ₀ a τ →
  Γ ⊢ Fzip_pack τ₀ M a τ ~: Exists a τ.
Proof.
intros Γ M a τ₀ τ H H0 H1 H2.
assert (a ∉ dom Γ). assert (uniq (a ~ U ++ Γ)) by eauto with lngen. solve_uniq.
assert (a ∉ ftv_term M). apply wfterm_ftv in H2. fsetdec.
assert (a ∉ ftv_typ τ₀). apply wftyp_ftv in H0; fsetdec.
assert (a ∉ ftv_typ (tsubst_typ τ₀ a τ)).
  apply wfterm_wftyp in H2. apply wftyp_ftv in H2. fsetdec.
unfold Fzip_pack; unfold_fzip; simpl_close.
simpl_eq a a. pick fresh b and apply wfterm_exists. simpl_open.
repeat rewrite <- tsubst_typ_spec_rec.
rewrite <- tsubst_term_spec_rec.
rewrite tsubst_typ_fresh_eq with (t2 := τ₀); auto.
rewrite tsubst_typ_fresh_eq with (t2 := (close_typ_wrt_typ_rec 0 a τ)); auto.
rewrite tsubst_term_fresh_eq; auto.
rewrite_env (nil ++ b ~ E ++ Γ). pick fresh c and apply wfterm_sigma; auto.
simpl_open. rewrite <- tsubst_term_spec_rec. rewrite <- tsubst_typ_spec_rec.
unsimpl (tsubst_term (typ_var_f c) a (term_coerce M τ)).
rewrite tsubst_typ_tsubst_typ; auto.
rewrite tvar_tsubst. rewrite tsubst_typ_fresh_eq with (a1 := b); auto.
rewrite_env (env_map (tsubst_typ (typ_var_f c) a) nil ++ c ~ Eq τ₀ ++ Γ).
apply wfterm_renameEq; auto.
apply wfterm_coerce with (t' := tsubst_typ τ₀ a τ).
apply wftypeq_sym. apply wftypeq_unfold_eq; auto using wftyp_instantiate.
apply wfterm_weakening; auto with fzip.
rewrite ftv_term_close_term_wrt_typ_rec; auto.
rewrite ftv_typ_close_typ_wrt_typ_rec; auto.
Qed.

Lemma wfterm_Fzip_unpack : forall Γ M M' τ τ' a x,
  a ≠ x → pure Γ →
  Γ ⊢ M ~: Exists a τ →
  x ~ T τ ++ a ~ U ++ Γ ⊢ M' ~: τ' →
  a ∉ ftv_typ τ' →
  Γ ⊢ Fzip_unpack M a x M' ~: τ'.
Proof.
intros Γ M M' τ τ' a x H H0 H1 H2 H3.
assert (x ∉ dom Γ). assert (uniq (x ~ T τ ++ a ~ U ++ Γ)) by eauto with lngen.
  solve_uniq.
assert (a ∉ dom Γ). assert (uniq (x ~ T τ ++ a ~ U ++ Γ)) by eauto with lngen.
  solve_uniq.
assert (x ∉ fv_term M). apply wfterm_fv in H1. fsetdec.
assert (a ∉ ftv_term M). apply wfterm_ftv in H1. fsetdec.
unfold Fzip_unpack; unfold_fzip; simpl_close. simpl_eq a a.
pick fresh b and apply wfterm_nu. simpl_open.
repeat rewrite <- tsubst_term_spec_rec.
rewrite tsubst_term_fresh_eq; auto.
rewrite tsubst_term_close_term_wrt_term_rec; auto.
apply wfterm_let with
  (L := {{ b }} ∪ {{ a }} ∪ {{ x }} ∪ dom Γ)
  (G1 := b ~ E ++ Γ) (G2 := b ~ U ++ Γ)
  (t1 := tsubst_typ (typ_var_f b) a τ); intros.
apply zip_app; auto with fzip.
  apply wfterm_wfenv in H1.
  apply zip_self; eauto using wfenv_lc_env with lngen.
rewrite_env (nil ++ b ~ E ++ Γ). rewrite tsubst_typ_spec. auto.
simpl_open; rewrite <- subst_term_spec_rec.
rewrite_env (nil ++ [(x0, T (tsubst_typ (typ_var_f b) a τ))] ++ [(b, U)] ++ Γ).
apply wfterm_renameT; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) (x ~ T τ) ++ [(b, U)] ++ Γ).
rewrite <- tsubst_typ_fresh_eq with (t2 := τ') (a1 := a) (t1 := typ_var_f b);
auto.
apply wfterm_renameU; auto.
Qed.

Lemma exists_iso1 : forall Γ a b τ x y f,
  a ≠ b → a ≠ x → a ≠ y → a ≠ f →
  b ≠ x → b ≠ y → b ≠ f →
  x ≠ y → x ≠ f →
  y ≠ f →
  y ∉ dom Γ →
  a ∉ dom Γ →
  b ∉ dom Γ →
  x ∉ dom Γ →
  y ∉ dom Γ →
  f ∉ dom Γ →
  pure Γ → Γ ⊢ Exists a τ ok →
  Γ ⊢
  Abs x (Exists a τ)
  (Fzip_unpack (term_var_f x) a y
    (F_pack (typ_var_f a) (term_var_f y) a τ b f))
  ~: Arrow (Exists a τ) (F_exists a τ b).
Proof.
intros Γ a b τ x y f H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
pick fresh z and apply wfterm_abs; auto.
rewrite <- subst_term_spec.
rewrite_env (nil ++ z ~ T (Exists a τ) ++ Γ).
apply wfterm_renameT; auto.
apply wfterm_Fzip_unpack with (τ := τ); simpl_env; auto with fzip.
unfold Exists in H16. inversion H16; subst.
pick fresh c. replace (F_pack (typ_var_f a) (term_var_f y) a τ b f)
with (F_pack (typ_var_f a) (term_var_f y) c
  (tsubst_typ (typ_var_f c) a τ) b f).
replace (F_exists a τ b) with
(F_exists c (tsubst_typ (typ_var_f c) a τ) b).
assert (lc_typ τ).
  apply wftyp_regular in H16.
  rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (a1 := a). auto with lngen.
assert (a ~ U ++ Γ ⊢ τ ok).
  rewrite_env (env_map (tsubst_typ (typ_var_f a) c) nil ++ a ~ U ++ Γ).
  rewrite <- tsubst_typ_var_twice with (a := c) (b := a); auto.
  apply wftyp_renameU; auto.
  rewrite tsubst_typ_spec; simpl_env; auto.
apply wfterm_F_pack; auto with fzip.
constructor; auto.
constructor; auto. apply wftyp_weakening; auto.
apply wftyp_weakening; auto. apply wftyp_weakening; auto.
apply wftyp_weakening; auto. rewrite tsubst_typ_spec; auto.
constructor; auto. apply wftyp_weakening; auto.
rewrite tsubst_typ_var_twice; auto.
constructor; auto with fzip.
unfold F_exists. f_equal. f_equal. unfold_fzip; simpl_close. f_equal. f_equal.
rewrite tsubst_typ_spec. simpl_open.
rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec. auto.
rewrite ftv_typ_close_typ_wrt_typ; auto.
assert (c ≠ b) by auto. simpl_eq c b. simpl_eq a b.
unfold F_pack. f_equal. f_equal. unfold_fzip. simpl_close. f_equal. f_equal.
rewrite tsubst_typ_spec. simpl_open.
rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec. auto.
rewrite ftv_typ_close_typ_wrt_typ; auto.
assert (c ≠ b) by auto. simpl_eq c b. simpl_eq a b.
unfold F_exists. unfold_fzip. simpl.
repeat rewrite ftv_typ_close_typ_wrt_typ_rec. simpl_eq a b. simpl_eq b b. simpl.
clear Fr. auto.
Qed.

Lemma exists_iso2 : forall Γ a b τ x y f,
  a ≠ b → a ≠ x → a ≠ y → a ≠ f →
  b ≠ x → b ≠ y → b ≠ f →
  x ≠ y → x ≠ f →
  y ≠ f →
  y ∉ dom Γ →
  a ∉ dom Γ →
  b ∉ dom Γ →
  x ∉ dom Γ →
  y ∉ dom Γ →
  f ∉ dom Γ →
  b ∉ ftv_typ τ →
  pure Γ → Γ ⊢ F_exists a τ b ok →
  Γ ⊢
  Abs x (F_exists a τ b)
  (F_unpack (term_var_f x) a y τ
    (Fzip_pack (typ_var_f a) (term_var_f y) a τ) (* <– *)
    (Exists a τ))
  ~: Arrow (F_exists a τ b) (Exists a τ).
Proof.
intros Γ a b τ x y f H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17.
assert (lc_typ τ).
  apply wftyp_regular in H17. inversion H17; subst.
  pose (H19 b). rewrite open_typ_wrt_typ_close_typ_wrt_typ in l.
  inversion l; subst. inversion H21; subst.
  pose (H20 a). rewrite open_typ_wrt_typ_close_typ_wrt_typ in l0.
  inversion l0; subst. auto.
assert (a ~ U ++ Γ ⊢ τ ok).
  inversion H17; subst. pick fresh c.
  assert ([(c, U)] ++ Γ
          ⊢ open_typ_wrt_typ
              (close_typ_wrt_typ b
                 (Arrow (Forall a (Arrow τ (typ_var_f b))) (typ_var_f b)))
              (typ_var_f c) ok) by auto. clear H21.

  rewrite <- tsubst_typ_spec in H19. simpl in H19.
  simpl_eq a b. simpl_eq b b. inversion H19; subst. clear H19.
  inversion H23; subst. clear H23. pick fresh c0.
  assert ([(c0, U)] ++ (c, U) :: Γ
          ⊢ open_typ_wrt_typ
              (typ_arrow
                 (tsubst_typ (typ_var_f c) b (close_typ_wrt_typ_rec 0 a τ))
                 (if b == b then typ_var_f c else typ_var_f b))
              (typ_var_f c0) ok) by auto. clear H21 H24.
  unfold open_typ_wrt_typ in H19; simpl in H19. inversion H19; subst. clear H19.
  clear H24.
  rewrite tsubst_typ_close_typ_wrt_typ_rec in H23; auto.
  rewrite <- tsubst_typ_spec_rec in H23; auto.
  rewrite tsubst_typ_fresh_eq with (a1 := b) in H23; auto.
  simpl_env in H23.
  rewrite <- tsubst_typ_var_twice with (a := c0) (b := a); auto.
  rewrite_env (env_map (tsubst_typ (typ_var_f a) c0) nil ++ a ~ U ++ Γ).
  apply wftyp_renameU; auto.
  rewrite <- tsubst_typ_fresh_eq with (a1 := c)
    (t1 := typ_forall (typ_var_b 0)).
  rewrite_env (env_map (tsubst_typ (typ_forall (typ_var_b 0)) c) (c0 ~ U)
    ++ Γ).
  apply wftyp_tsubst; auto.
  pick fresh d and apply wftyp_forall; simpl_open; auto.
  constructor; auto. constructor; eauto with fzip.
  assert (ftv_typ (tsubst_typ (typ_var_f c0) a τ)
    [<=] ftv_typ (typ_var_f c0) ∪ remove a (ftv_typ τ)) by auto with lngen.
  assert (c0 ≠ c) by auto. clear Fr0. simpl in H19. fsetdec.
pick fresh z and apply wfterm_abs; auto.
rewrite <- subst_term_spec. rewrite_env (nil ++ z ~ T (F_exists a τ b) ++ Γ).
apply wfterm_renameT; auto. apply wfterm_F_unpack with (b := b); auto with fzip.
constructor; auto with fzip. constructor; auto.
pick fresh c.
replace (Fzip_pack (typ_var_f a) (term_var_f y) a τ) with
  (Fzip_pack (typ_var_f a) (term_var_f y) c (tsubst_typ (typ_var_f c) a τ)).
replace (Exists a τ) with (Exists c (tsubst_typ (typ_var_f c) a τ)).
apply wfterm_Fzip_pack.
auto 7 with fzip.
simpl_env. constructor; auto. constructor; auto.  apply wftyp_weakening; auto.
simpl_env. apply wftyp_weakening; auto. apply wftyp_weakening; auto. 
apply wftyp_weakening; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f c) a) nil ++ c ~ U ++ Γ).
apply wftyp_renameU; auto. constructor; auto. apply wftyp_weakening; auto.
rewrite tsubst_typ_var_twice; auto. constructor; auto.
auto 7 with fzip.
simpl_env. constructor; auto.  apply wftyp_weakening; auto.
unfold Exists; simpl_close. f_equal.
rewrite tsubst_typ_spec. simpl_open.
rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec; auto.
rewrite ftv_typ_close_typ_wrt_typ; auto.
unfold Fzip_pack; unfold_fzip; simpl_close. simpl_eq c c. simpl_eq a a.
assert (c ≠ a) by auto. simpl_eq c a.



