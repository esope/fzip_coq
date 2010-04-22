Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_pure.
Require Import FzipCore_zip.
Require Import FzipCore_env_typ.

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
Definition Exists a t := typ_forall (close_typ_wrt_typ a t).

Ltac unfold_smart_cons :=
  unfold Abs; unfold App;
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
  wfterm nil
  (term_id a x)
  (Forall a (typ_id (typ_var_f a))).
Proof.
intros x a H. unfold term_id. unfold typ_id.
unfold_fzip. simpl_close. simpl_eq a a.
simpl_eq x x. simpl_close.
pick fresh b1 and apply wfterm_gen; auto; simpl_open.
pick fresh y1 and apply wfterm_abs; auto with fzip; simpl_open.
auto 7 with fzip.
Qed.

Lemma wfterm_projL : forall a b x, a ≠ b →
  wfterm nil
  (Gen a (Gen b (Abs x (Prod (typ_var_f a) (typ_var_f b))
    (Fst (term_var_f x)))))
  (Forall a (Forall b (Arrow (Prod (typ_var_f a) (typ_var_f b))
    (typ_var_f a)))).
Proof.
intros.
unfold_fzip. simpl_close. simpl_eq b b. simpl_eq x x. simpl_eq b a.
simpl_close. simpl_eq a a.
clear a b x H e e0 n e1.
pick fresh a and apply wfterm_gen; auto; simpl_open.
pick fresh b and apply wfterm_gen; auto with fzip; simpl_open.
pick fresh x and apply wfterm_abs; auto with fzip; simpl_open.
apply wfterm_fst with (t2 := typ_var_f b).
auto 9 with fzip.
Qed.

Lemma wfterm_projR : forall a b x, a ≠ b →
  wfterm nil
  (Gen a (Gen b (Abs x (Prod (typ_var_f a) (typ_var_f b))
    (Snd (term_var_f x)))))
  (Forall a (Forall b (Arrow (Prod (typ_var_f a) (typ_var_f b))
    (typ_var_f b)))).
Proof.
intros.
unfold_fzip. simpl_close. simpl_eq b b. simpl_eq x x. simpl_eq b a.
simpl_close. simpl_eq a a.
clear a b x H e e0 n e1.
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

Lemma wfterm_zero : forall a x f, x ≠ f →
  wfterm nil (term_zero a x f) (typ_nat a).
Proof.
intros a x f H. unfold term_zero. unfold typ_nat.
unfold_fzip. simpl_close. simpl_eq a a. simpl_eq f x.
simpl_close. simpl_eq x x. simpl_close.
clear a x f H e n e0.
pick fresh a and apply wfterm_gen; simpl_open; auto.
pick fresh x and apply wfterm_abs; simpl_open; auto with fzip.
pick fresh f and apply wfterm_abs; simpl_open; auto with fzip.
auto 10 with fzip.
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
  wfterm nil (term_plus a n x f) (typ_id (typ_nat a)).
Proof.
intros a n x f H H0 H1. unfold term_plus. unfold typ_id.
unfold typ_nat.
unfold_fzip. simpl_close. simpl_eq f f. simpl_eq a a.
simpl_eq f n. simpl_eq f x. simpl_close. simpl_eq x n.
simpl_eq x x. simpl_close. simpl_eq n n.
clear a n x f H H0 H1 e e0 n0 n1 n2 e1 e2.
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
assert (wfenv Γ). subst.
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
  x ≠ f →
  wfterm (b ~ E)
  (Pair
    (Sig b a (typ_nat a) (Coerce (term_zero a x f) (typ_var_f a)))
    (Inst (term_id a x) (typ_var_f b)))
  (Prod (typ_var_f b) (typ_id (typ_var_f b))).
Proof.
intros. unfold_fzip. simpl_close. simpl_eq a a. simpl_eq f x.
simpl_close. simpl_eq x x. simpl_close.
apply wfterm_pair with (G1 := b ~ E ++ nil) (G2 := b ~ U ++ nil).
simpl_env; auto with fzip.
rewrite_env (nil ++ b ~ @E typ ++ nil).
pick fresh c and apply wfterm_sigma; simpl_open; auto.
autorewrite with lngen.
apply wfterm_coerce with (t' := typ_nat a).
apply wftypeq_sym. apply wftypeq_eq; auto. constructor; auto. 
unfold typ_nat. unfold_fzip. simpl_close. simpl_eq a a.
pick fresh d and apply wftyp_forall; simpl_open.
auto 8 with lngen.
unfold typ_nat. unfold_fzip. simpl_close. simpl_eq a a.
pick fresh d and apply wfterm_gen; simpl_open; auto with fzip.
pick fresh y and apply wfterm_abs; simpl_open; auto with fzip.
pick fresh z and apply wfterm_abs; simpl_open; auto 6 with fzip.
constructor. auto 7 with fzip.
constructor; auto. constructor; auto. constructor; auto.
constructor; auto. constructor; auto. constructor; auto.
constructor; auto. pick fresh a' and apply wftyp_forall; simpl_open.
constructor; auto. constructor; auto. constructor; auto.
constructor; auto. constructor; auto. constructor; auto.
constructor; auto. constructor; auto.
pick fresh a' and apply wftyp_forall; simpl_open. auto 8. auto.
rewrite <- tsubst_typ_var_self with (a := b).
rewrite tsubst_typ_spec.
constructor; auto.
unfold term_id. unfold_fzip. simpl_close. simpl_eq a a.
simpl_eq b b. simpl_eq x x. simpl_close.
clear a x f H e n e0 e1 e2 e3.
pick fresh a and apply wfterm_gen; simpl_open; auto with fzip.
pick fresh x and apply wfterm_abs; simpl_open; auto with fzip.
auto 7 with fzip.
Qed.
