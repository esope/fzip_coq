Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_val.

(** Lemmas about [lc] *)
Lemma red0_regular1 : forall e A e', red0 e A e' → lc_term e.
Proof.
intros e A e' H. destruct H; auto with lngen.
Case "nu_sigma".
  pick fresh b; pick fresh a.
  apply (lc_term_nu_exists b).
  unfold open_term_wrt_typ; simpl.
  apply (lc_term_sigma_exists a); auto.
  apply H; auto.
  apply result_regular.
  eapply (H1 b a); auto; reflexivity.
Case "sigma_exists".
  pick fresh c. pick fresh a.
  apply (lc_term_exists_exists c).
  unfold open_term_wrt_typ; simpl.
  apply (lc_term_sigma_exists a); auto.
  apply H; auto.
  apply result_regular.
  eapply (H1 c a); auto; reflexivity.
Qed.

Lemma red0_regular2 : forall e A e', red0 e A e' → lc_term e'.
Proof.
intros e A e' H; destruct H;
try solve [apply val_regular in H; inversion H; subst; auto];
auto with lngen.
Case "beta_v_red". inversion H0; subst.
  pick fresh x. apply (lc_term_let_exists x); auto.
  apply val_regular; auto.
Case "beta_v_let". eauto with lngen.
Case "beta_t".
  pick fresh a.
  assert (lc_term (open_term_wrt_typ e (typ_var_f a))) by auto with lngen.
  apply tsubst_term_lc_term
    with (t1 := typ_var_f b) (a1 := a) in H0; auto.
  rewrite tsubst_term_open_term_wrt_typ in H0; auto.
  autorewrite with lngen in H0; auto.
Case "nu_sigma".
  pick fresh b; pick fresh a.
  erewrite (H2 b a); auto.
  apply tsubst_term_lc_term; auto.
  apply tsubst_term_lc_term; auto.
  apply result_regular.
  eapply (H1 b a); auto;
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
Case "sigma_letL".
  pick fresh a.
  apply (lc_term_sigma_exists a); auto.
  apply result_regular in H0; inversion H0; subst; auto.
  replace (open_term_wrt_typ (term_let e1 e2') (typ_var_f a)) with
    (term_let (open_term_wrt_typ e1 (typ_var_f a)) (open_term_wrt_typ e2' (typ_var_f a)))
    by reflexivity.
  constructor.
    apply result_regular in H0; inversion H0; subst; auto.
    intros. rewrite (H1 a); auto with lngen.
    rewrite tsubst_term_open_term_wrt_term_var.
    inversion H; subst; auto with lngen.
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
Case "sigma_exists".
  pick fresh c. pick fresh a.
  rewrite (H2 c); auto.
  apply (lc_term_sigma_exists a); auto.
  unfold open_term_wrt_typ; simpl.
  apply (lc_term_exists_exists c); auto.
  rewrite <- (H3 c a); auto.
  apply result_regular; auto.
Case "sigma coerce".
  pick fresh a.
  apply result_regular in H0; inversion H0; subst.
  apply (lc_term_sigma_exists a); auto.
  replace (open_term_wrt_typ (term_coerce e t'') (typ_var_f a)) with
    (term_coerce (open_term_wrt_typ e (typ_var_f a)) (open_typ_wrt_typ t'' (typ_var_f a)))
    by reflexivity.
  constructor.
    apply H7.
    rewrite (H1 a); auto with lngen.
Case "sigma_sigma".
  inversion H; subst.
  pick fresh a1.
  assert (lc_term
         (open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e) (typ_var_f a1)))
  by auto.
  unfold open_term_wrt_typ in H3; simpl in H3. inversion H3; subst.
  pick fresh a2.
  apply (lc_term_sigma_exists a2); auto.
  rewrite tsubst_typ_intro with (a1 := a1); auto with lngen.
  replace (open_term_wrt_typ (term_sigma (typ_var_f b1) t1' e') (typ_var_f a2))
    with (term_sigma (typ_var_f b1) (open_typ_wrt_typ t1' (typ_var_f a2)) (open_term_wrt_typ_rec 1 (typ_var_f a2) e'))
      by reflexivity.
  rewrite <- H1; auto.
  apply (lc_term_sigma_exists a1); auto.
  unfold open_term_wrt_typ. rewrite <- H2; auto.
  apply H12.
Qed.
Hint Resolve red0_regular1 red0_regular2: lngen.

Lemma red1_regular1 : forall e A e', e ⇝[A] e' → lc_term e.
Proof.
intros e A e' H. induction H; eauto with lngen.
Qed.

Lemma red1_regular2 : forall e A e', e ⇝[A] e' → lc_term e'.
Proof.
intros e A e' H; induction H; eauto with lngen.
Qed.
Hint Resolve red1_regular1 red1_regular2: lngen.

(** Lemmas about free variables *)
Lemma red0_ftv : forall A e e', red0 e A e' →
  ftv_term e' [<=] ftv_term e.
Proof.
intros A e e' H. destruct H; simpl in *; try solve [fsetdec].
Case "let". auto with lngen.
Case "gen". assert (ftv_term (open_term_wrt_typ e t) [<=]
ftv_typ t∪ftv_term e) by auto with lngen. fsetdec.
Case "open". assert (ftv_term (open_term_wrt_typ e (typ_var_f b))
 [<=] ftv_typ (typ_var_f b)∪ftv_term e) by auto with lngen.
simpl in *. fsetdec.
Case "nu_sigma". pick fresh b. pick fresh a.
erewrite (H2 b a)
with (e1 := open_term_wrt_typ_rec 1 (typ_var_f b) e); auto.
clear H2.
transitivity (ftv_typ (open_typ_wrt_typ t (typ_var_f b)) ∪ remove a
(ftv_term (tsubst_term (typ_var_f a) b (open_term_wrt_typ
(open_term_wrt_typ_rec 1 (typ_var_f b) e) (typ_var_f a)))));
  auto with lngen.
transitivity (ftv_typ (open_typ_wrt_typ t (typ_var_f b))∪ remove a
   (ftv_typ (typ_var_f a) ∪ remove b (ftv_term (open_term_wrt_typ
   (open_term_wrt_typ_rec 1 (typ_var_f b) e) (typ_var_f a))))).
assert (ftv_term (tsubst_term (typ_var_f a) b (open_term_wrt_typ
        (open_term_wrt_typ_rec 1 (typ_var_f b) e) (typ_var_f a))) [<=]
        ftv_typ (typ_var_f a)∪ remove b (ftv_term (open_term_wrt_typ
        (open_term_wrt_typ_rec 1 (typ_var_f b) e) (typ_var_f a)))) by
        auto with lngen.
  clear Fr Fr0. fsetdec.
transitivity (ftv_typ (open_typ_wrt_typ t (typ_var_f b))∪ remove a
   (ftv_typ (typ_var_f a)∪ remove b (ftv_typ (typ_var_f a) ∪ ftv_term
   (open_term_wrt_typ_rec 1 (typ_var_f b) e) ))).
assert (ftv_term (open_term_wrt_typ (open_term_wrt_typ_rec 1
           (typ_var_f b) e) (typ_var_f a)) [<=] ftv_typ (typ_var_f a)∪
           ftv_term (open_term_wrt_typ_rec 1 (typ_var_f b) e)) by auto
           with lngen.
  clear Fr Fr0. fsetdec.
transitivity (ftv_typ (open_typ_wrt_typ t (typ_var_f b))∪ remove a
   (ftv_typ (typ_var_f a)∪ remove b (ftv_typ (typ_var_f a)∪ ftv_typ
   (typ_var_f b) ∪ ftv_term e))).
assert (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f b) e) [<=]
  ftv_typ (typ_var_f b) ∪ ftv_term e) by auto with lngen.
  clear Fr Fr0. fsetdec.
assert (ftv_typ (open_typ_wrt_typ t (typ_var_f b)) [<=] ftv_typ t).
  assert (ftv_typ (open_typ_wrt_typ t (typ_var_f b)) [<=]
    ftv_typ (typ_var_f b) ∪ ftv_typ t) by auto with lngen.
  assert (b ∉ ftv_typ (open_typ_wrt_typ t (typ_var_f b))) by auto.
  simpl in H2. clear Fr0. fsetdec.
simpl. clear Fr Fr0. fsetdec.
Case "coerce_inst".
assert (ftv_typ (open_typ_wrt_typ t1 t2) [<=] ftv_typ t2 ∪ ftv_typ t1)
  by auto with lngen. fsetdec.
Case "coerce_open".
assert (ftv_typ (open_typ_wrt_typ t (typ_var_f b)) [<=]
  ftv_typ (typ_var_f b) ∪ ftv_typ t) by auto with lngen. simpl in *. fsetdec.
Case "sigma_appL". assert (ftv_term e2' [<=] ftv_term e2).
pick fresh a.
assert (ftv_term e2'[<=] ftv_typ (typ_var_f a) ∪ ftv_term e2).
  transitivity (ftv_term (open_term_wrt_typ e2' (typ_var_f a)));
    auto with lngen.
  rewrite H1; auto.
  transitivity (ftv_typ (typ_var_f a) ∪ remove b (ftv_term e2));
    auto with lngen. clear Fr. fsetdec.
simpl in *. assert (a ∉ ftv_term e2') by auto. clear Fr. fsetdec.
fsetdec.
Case "sigma_appR". assert (ftv_term e1' [<=] ftv_term e1).
pick fresh a.
assert (ftv_term e1'[<=] ftv_typ (typ_var_f a) ∪ ftv_term e1).
  transitivity (ftv_term (open_term_wrt_typ e1' (typ_var_f a)));
    auto with lngen.
  rewrite H1; auto.
  transitivity (ftv_typ (typ_var_f a) ∪ remove b (ftv_term e1));
    auto with lngen. clear Fr. fsetdec.
simpl in *. assert (a ∉ ftv_term e1') by auto. clear Fr. fsetdec.
fsetdec.
Case "sigma_letL". assert (ftv_term e2' [<=] ftv_term e2).
pick fresh a.
assert (ftv_term e2'[<=] ftv_typ (typ_var_f a) ∪ ftv_term e2).
  transitivity (ftv_term (open_term_wrt_typ e2' (typ_var_f a)));
    auto with lngen.
  rewrite H1; auto.
  transitivity (ftv_typ (typ_var_f a) ∪ remove b (ftv_term e2));
    auto with lngen. clear Fr. fsetdec.
simpl in *. assert (a ∉ ftv_term e2') by auto. clear Fr. fsetdec.
fsetdec.
Case "sigma_pairL". assert (ftv_term e2' [<=] ftv_term e2).
pick fresh a.
assert (ftv_term e2'[<=] ftv_typ (typ_var_f a) ∪ ftv_term e2).
  transitivity (ftv_term (open_term_wrt_typ e2' (typ_var_f a)));
    auto with lngen.
  rewrite H1; auto.
  transitivity (ftv_typ (typ_var_f a) ∪ remove b (ftv_term e2));
    auto with lngen. clear Fr. fsetdec.
simpl in *. assert (a ∉ ftv_term e2') by auto. clear Fr. fsetdec.
fsetdec.
Case "sigma_pairR". assert (ftv_term e1' [<=] ftv_term e1).
pick fresh a.
assert (ftv_term e1'[<=] ftv_typ (typ_var_f a) ∪ ftv_term e1).
  transitivity (ftv_term (open_term_wrt_typ e1' (typ_var_f a)));
    auto with lngen.
  rewrite H1; auto.
  transitivity (ftv_typ (typ_var_f a) ∪ remove b (ftv_term e1));
    auto with lngen. clear Fr. fsetdec.
simpl in *. assert (a ∉ ftv_term e1') by auto. clear Fr. fsetdec.
fsetdec.
Case "sigma_inst". assert (ftv_typ t'' [<=] ftv_typ t').
pick fresh a.
assert (ftv_typ t''[<=] ftv_typ (typ_var_f a) ∪ ftv_typ t').
  transitivity (ftv_typ (open_typ_wrt_typ t'' (typ_var_f a)));
    auto with lngen.
  rewrite H1; auto.
  transitivity (ftv_typ (typ_var_f a) ∪ remove b (ftv_typ t'));
    auto with lngen. clear Fr. fsetdec.
simpl in *. assert (a ∉ ftv_typ t'') by auto. clear Fr. fsetdec.
fsetdec.
Case "sigma_exists".
assert (ftv_typ t' [<=] ftv_typ t).
  pick fresh c. assert (ftv_typ t' [<=] ftv_typ (typ_var_f c) ∪ ftv_typ t).
  transitivity (ftv_typ (open_typ_wrt_typ t (typ_var_f c))).
  rewrite (H2 c); auto with lngen. auto with lngen.
  assert (c ∉ ftv_typ t') by auto. clear Fr. simpl in H4. fsetdec.
assert (ftv_term e' [<=] ftv_term e).
  pick fresh c. pick fresh a.
  assert (ftv_term e' [<=] ftv_typ (typ_var_f a) ∪ ftv_typ (typ_var_f c) ∪
    ftv_term e).
  transitivity (ftv_typ (typ_var_f a) ∪ ftv_term
  (open_term_wrt_typ_rec 1 (typ_var_f c) e)); auto with lngen.
  transitivity (ftv_term (open_term_wrt_typ (open_term_wrt_typ_rec 1
  (typ_var_f c) e) (typ_var_f a))); auto with lngen.
  rewrite H3; auto.
  transitivity (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f a) e'));
    auto with lngen.
  assert (a ∉ ftv_term e') by auto. assert (c ∉ ftv_term e') by auto.
  clear Fr Fr0. simpl in H5. fsetdec.
fsetdec.
Case "sigma_coerce". assert (ftv_typ t'' [<=] ftv_typ t').
pick fresh a.
assert (ftv_typ t''[<=] ftv_typ (typ_var_f a) ∪ ftv_typ t').
  transitivity (ftv_typ (open_typ_wrt_typ t'' (typ_var_f a)));
    auto with lngen.
  rewrite H1; auto.
  transitivity (ftv_typ (typ_var_f a) ∪ remove b (ftv_typ t'));
    auto with lngen. clear Fr. fsetdec.
simpl in *. assert (a ∉ ftv_typ t'') by auto. clear Fr. fsetdec.
fsetdec.
Case "sigma_sigma".
assert (ftv_typ (open_typ_wrt_typ t2 t1) [<=] ftv_typ t1 ∪ ftv_typ t2)
  by auto with lngen.
assert (ftv_typ t1' [<=] ftv_typ t1).
  pick fresh a2. rewrite (H1 a2); auto with lngen.
assert (ftv_term e' [<=] ftv_term e).
  pick fresh a2. pick fresh a1.
  assert (ftv_term e' [<=]
    ftv_typ (typ_var_f a2) ∪ ftv_typ (typ_var_f a1) ∪ ftv_term e).
    transitivity (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f a2) e'));
      auto with lngen.
    transitivity (ftv_term (open_term_wrt_typ_rec 0 (typ_var_f a1)
      (open_term_wrt_typ_rec 1 (typ_var_f a2) e'))); auto with lngen.
    rewrite <- H2; auto.
    transitivity (ftv_typ (typ_var_f a2) ∪
      ftv_term (open_term_wrt_typ_rec 1 (typ_var_f a1) e)); auto with lngen.
  assert (a1 ∉ ftv_term e') by auto. assert (a2 ∉ ftv_term e') by auto.
  clear Fr Fr0. simpl in *. fsetdec.
fsetdec.
Qed.

Lemma red1_ftv : forall A e e', e ⇝[A] e' →
  ftv_term e' [<=] ftv_term e.
Proof.
intros A e e' H. induction H; simpl; try solve [fsetdec].
Case "empty". eauto using red0_ftv.
Case "exists". pick fresh a.
assert (ftv_term e' [<=] ftv_typ (typ_var_f a) ∪ ftv_term e).
  transitivity (ftv_term (open_term_wrt_typ e' (typ_var_f a))); auto with lngen.
  transitivity (ftv_term (open_term_wrt_typ e (typ_var_f a))); auto with lngen.
simpl in *. fsetdec.
Case "nu". pick fresh a.
assert (ftv_term e' [<=] ftv_typ (typ_var_f a) ∪ ftv_term e).
  transitivity (ftv_term (open_term_wrt_typ e' (typ_var_f a))); auto with lngen.
  transitivity (ftv_term (open_term_wrt_typ e (typ_var_f a))); auto with lngen.
simpl in *. fsetdec.
Case "sigma". assert (ftv_term e' [<=] ftv_term e).
pick fresh a.
assert (ftv_term e' [<=] ftv_typ (typ_var_f a) ∪ ftv_term e).
  transitivity (ftv_term (open_term_wrt_typ e' (typ_var_f a))); auto with lngen.
  transitivity (ftv_term (open_term_wrt_typ e (typ_var_f a))); auto with lngen.
simpl in *. fsetdec.
fsetdec.
Qed.

Lemma redn_ftv : forall A e e', e ⇝⋆[A] e' →
  ftv_term e' [<=] ftv_term e.
Proof.
intros A e e' H. induction H; try fsetdec. eauto using red1_ftv.
Qed.

(* Renaming lemmas *)
Lemma red0_trenaming : forall A a b e e',
  b ∉ ftv_term e →
  red0 e A e' →
  red0 (tsubst_term (typ_var_f b) a e) A (tsubst_term (typ_var_f b) a e').
Proof with auto using val_trenaming, result_trenaming with lngen.
intros A a b e e' Hb H. inversion H; subst; simpl in *.
Case "beta_v_red". 
constructor... unsimpl (tsubst_term (typ_var_f b) a (term_abs t e1))...
Case "beta_v_let". rewrite tsubst_term_open_term_wrt_term; auto.
constructor... unsimpl (tsubst_term (typ_var_f b) a (term_let e1 e2))...
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
unfold open_term_wrt_typ in H6; inversion H6; subst. clear H6.
replace (typ_var_f b0) with (tsubst_typ (typ_var_f b) a (typ_var_f b0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec...
replace (typ_var_f a0) with (tsubst_typ (typ_var_f b) a (typ_var_f a0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ...
apply result_trenaming. eapply (H2 b0 a0); auto. reflexivity.
unfold open_term_wrt_typ in H6; inversion H6; subst; clear H6.
replace (typ_var_f b0) with (tsubst_typ (typ_var_f b) a (typ_var_f b0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
replace (typ_var_f a0) with (tsubst_typ (typ_var_f b) a (typ_var_f a0))
  by auto with lngen.
rewrite <- tsubst_typ_open_typ_wrt_typ; auto.
rewrite <- tsubst_term_tsubst_term; auto.
rewrite <- tsubst_term_tsubst_term; auto.
rewrite tsubst_typ_fresh_eq with (t2 := typ_var_f a0); auto.
erewrite (H3 b0 a0); auto. reflexivity.
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
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
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
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
Case "sigma appR". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_appR...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e2))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e2))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
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
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
Case "sigma letL". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_letL...
replace (term_let (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e1))
        (tsubst_term (typ_var_f b) a e2))
 with (tsubst_term (typ_var_f b) a (term_let (term_sigma (typ_var_f a) t e1) e2))...
simpl. destruct (a == a); try congruence.
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e1))
with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e1))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
rewrite tsubst_term_fresh_eq with (t1 := typ_var_f b)...
rewrite tsubst_term_fresh_eq with (a1 := b)...
SCase "b0 ≠ a". pick fresh c and apply red0_sigma_letL...
replace (term_let (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e1))
        (tsubst_term (typ_var_f b) a e2))
 with (tsubst_term (typ_var_f b) a (term_let (term_sigma (typ_var_f b0) t e1) e2))...
simpl. destruct (b0 == a); try congruence.
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e1))
with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e1))...
simpl. destruct (b0 == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b0); subst.
elimtype False. auto.
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
Case "sigma pairL". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_pairL...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e1))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e1))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
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
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
Case "sigma pairR". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_pairR...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e2))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e2))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_term_tsubst_term...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
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
rewrite tsubst_term_open_term_wrt_typ_var... rewrite H2...
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
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite H2...
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
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite H2...
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
Case "sigma exists". unfold typvar in *; destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_exists; intros.
rewrite tsubst_typ_open_typ_wrt_typ_var...
rewrite tsubst_typ_open_typ_wrt_typ_var...
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
rewrite <- tsubst_term_open_term_wrt_typ_rec...
rewrite tsubst_term_open_term_wrt_typ_var...
autorewrite with lngen...
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite <- H3...
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
rewrite <- tsubst_term_open_term_wrt_typ_rec...
rewrite tsubst_term_open_term_wrt_typ_var...
replace (open_term_wrt_typ_rec 1 (typ_var_f a0)
        (tsubst_term (typ_var_f b) a e'0)) with
(tsubst_term (typ_var_f b) a (open_term_wrt_typ_rec 1 (typ_var_f a0) e'0)).
autorewrite with lngen.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H4...
rewrite tsubst_term_open_term_wrt_typ_rec... autorewrite with lngen...
autorewrite with lngen...
SCase "b0 ≠ a". pick fresh c and apply red0_sigma_exists; intros.
rewrite tsubst_typ_open_typ_wrt_typ_var...
rewrite tsubst_typ_open_typ_wrt_typ_var...
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
rewrite <- tsubst_term_open_term_wrt_typ_rec...
rewrite tsubst_term_open_term_wrt_typ_var...
autorewrite with lngen...
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite <- H3...
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
rewrite <- tsubst_term_open_term_wrt_typ_rec...
rewrite tsubst_term_open_term_wrt_typ_var...
replace (open_term_wrt_typ_rec 1 (typ_var_f a0)
        (tsubst_term (typ_var_f b) a e'0)) with
(tsubst_term (typ_var_f b) a (open_term_wrt_typ_rec 1 (typ_var_f a0) e'0)).
autorewrite with lngen.
rewrite tsubst_term_open_term_wrt_typ_var...
rewrite H4...
rewrite tsubst_term_open_term_wrt_typ_rec... autorewrite with lngen...
autorewrite with lngen...
Case "sigma coerce". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh c and apply red0_sigma_coerce...
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f a) t e0))...
simpl. destruct (a == a); try congruence.
rewrite tsubst_typ_tsubst_typ...
simpl. unfold typvar; destruct (b == b); try congruence.
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite H2...
rewrite tsubst_typ_fresh_eq with (t1 := typ_var_f b)...
rewrite tsubst_typ_fresh_eq with (a1 := b)...
SCase "b0 ≠ a". pick fresh c and apply red0_sigma_coerce...
replace (term_sigma (typ_var_f b0) (tsubst_typ (typ_var_f b) a t)
        (tsubst_term (typ_var_f b) a e0))
 with (tsubst_term (typ_var_f b) a (term_sigma (typ_var_f b0) t e0))...
simpl. destruct (b0 == a); try congruence.
rewrite tsubst_typ_tsubst_typ...
simpl. unfold typvar; destruct (b == b0); subst.
elimtype False. auto.
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite H2...
Case "sigma sigma". unfold typvar in *; destruct (a == b); subst.
SCase "a = b".
destruct (b1 == b); destruct (b2 == b); subst; auto;
repeat rewrite tsubst_typ_var_self; repeat rewrite tsubst_term_var_self; auto.
SCase "a ≠ b". destruct (b1 == a); destruct (b2 == a); subst;
rewrite tsubst_typ_open_typ_wrt_typ...
SSCase "b1 = a and b2 = a". pick fresh c and apply red0_sigma_sigma; intros.
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t1)
        (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t2)
           (tsubst_term (typ_var_f b) a e0)))
with (tsubst_term (typ_var_f b) a
  (term_sigma (typ_var_f a) t1 (term_sigma (typ_var_f a) t2 e0)))...
simpl. unfold typvar; destruct (a == a); try congruence.
replace (typ_var_f a2) with (tsubst_typ (typ_var_f b) a (typ_var_f a2)).
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec...
autorewrite with lngen...
autorewrite with lngen...
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite <- H2...
replace (typ_var_f a2) with (tsubst_typ (typ_var_f b) a (typ_var_f a2)).
replace (typ_var_f a1) with (tsubst_typ (typ_var_f b) a (typ_var_f a1)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec... rewrite <- H3...
autorewrite with lngen...
autorewrite with lngen...
SSCase "b1 = a and b2 ≠ a". pick fresh c and apply red0_sigma_sigma; intros.
replace (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t1)
        (term_sigma (typ_var_f b2) (tsubst_typ (typ_var_f b) a t2)
           (tsubst_term (typ_var_f b) a e0)))
with (tsubst_term (typ_var_f b) a
  (term_sigma (typ_var_f a) t1 (term_sigma (typ_var_f b2) t2 e0)))...
simpl. unfold typvar; destruct (a == a); destruct (b2 == a); try congruence.
replace (typ_var_f a2) with (tsubst_typ (typ_var_f b) a (typ_var_f a2)).
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec...
autorewrite with lngen...
autorewrite with lngen...
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite <- H2...
replace (typ_var_f a2) with (tsubst_typ (typ_var_f b) a (typ_var_f a2)).
replace (typ_var_f a1) with (tsubst_typ (typ_var_f b) a (typ_var_f a1)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec... rewrite <- H3...
autorewrite with lngen...
autorewrite with lngen...
SSCase "b1 ≠ a and b2 = a". pick fresh c and apply red0_sigma_sigma; intros.
replace (term_sigma (typ_var_f b1) (tsubst_typ (typ_var_f b) a t1)
        (term_sigma (typ_var_f b) (tsubst_typ (typ_var_f b) a t2)
           (tsubst_term (typ_var_f b) a e0)))
with (tsubst_term (typ_var_f b) a
  (term_sigma (typ_var_f b1) t1 (term_sigma (typ_var_f a) t2 e0)))...
simpl. unfold typvar; destruct (a == a); destruct (b1 == a); try congruence.
replace (typ_var_f a2) with (tsubst_typ (typ_var_f b) a (typ_var_f a2)).
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec...
autorewrite with lngen...
autorewrite with lngen...
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite <- H2...
replace (typ_var_f a2) with (tsubst_typ (typ_var_f b) a (typ_var_f a2)).
replace (typ_var_f a1) with (tsubst_typ (typ_var_f b) a (typ_var_f a1)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec... rewrite <- H3...
autorewrite with lngen...
autorewrite with lngen...
SSCase "b1 ≠ a and b2 ≠ a". pick fresh c and apply red0_sigma_sigma; intros.
replace (term_sigma (typ_var_f b1) (tsubst_typ (typ_var_f b) a t1)
        (term_sigma (typ_var_f b2) (tsubst_typ (typ_var_f b) a t2)
           (tsubst_term (typ_var_f b) a e0)))
with (tsubst_term (typ_var_f b) a
  (term_sigma (typ_var_f b1) t1 (term_sigma (typ_var_f b2) t2 e0)))...
simpl. unfold typvar; destruct (b1 == a); destruct (b2 == a); try congruence.
replace (typ_var_f a2) with (tsubst_typ (typ_var_f b) a (typ_var_f a2)).
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec...
autorewrite with lngen...
autorewrite with lngen...
rewrite tsubst_typ_open_typ_wrt_typ_var... rewrite <- H2...
replace (typ_var_f a2) with (tsubst_typ (typ_var_f b) a (typ_var_f a2)).
replace (typ_var_f a1) with (tsubst_typ (typ_var_f b) a (typ_var_f a1)).
repeat rewrite <- tsubst_term_open_term_wrt_typ_rec... rewrite <- H3...
autorewrite with lngen...
autorewrite with lngen...
Qed.

Lemma red1_trenaming : forall A a b e e',
  b ∉ ftv_term e →
  e ⇝[A] e' →
  (tsubst_term (typ_var_f b) a e) ⇝[A] (tsubst_term (typ_var_f b) a e').
Proof.
intros A a b e e' Hb H.
induction H; subst; simpl in *; auto with lngen.
Case "empty". auto using red0_trenaming.
Case "let". apply red1_let; auto.
unsimpl (tsubst_term (typ_var_f b) a (term_let e1 e2)). auto with lngen.
Case "exists".
apply red1_exists with (L := L ∪ {{a}} ∪ {{b}} ∪ ftv_term e); intros c Hc.
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)) by auto with lngen.
repeat rewrite <- tsubst_term_open_term_wrt_typ; eauto.
apply H0; auto.
assert (ftv_term (open_term_wrt_typ e (typ_var_f c))
  [<=] ftv_typ (typ_var_f c) ∪ ftv_term e) by auto with lngen.
simpl in *; fsetdec.
Case "open". destruct (b0 == a); subst; auto.
Case "nu".
apply red1_nu with (L := L ∪ {{a}} ∪ {{b}} ∪ ftv_term e); intros c Hc.
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)) by auto with lngen.
repeat rewrite <- tsubst_term_open_term_wrt_typ; eauto.
apply H0; auto.
assert (ftv_term (open_term_wrt_typ e (typ_var_f c))
  [<=] ftv_typ (typ_var_f c) ∪ ftv_term e) by auto with lngen.
simpl in *; fsetdec.
Case "sigma". destruct (b0 == a); subst.
SCase "b0 = a".
apply red1_sigma with (L := L ∪ {{a}} ∪ {{b}} ∪ ftv_term e); auto with lngen.
intros c Hc.
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)) by auto with lngen.
repeat rewrite <- tsubst_term_open_term_wrt_typ; eauto.
apply H1; auto.
assert (ftv_term (open_term_wrt_typ e (typ_var_f c))
  [<=] ftv_typ (typ_var_f c) ∪ ftv_term e) by auto with lngen.
simpl in *; fsetdec.
SCase "b0 ≠ a".
apply red1_sigma with (L := L ∪ {{a}} ∪ {{b}} ∪ {{b0}} ∪ ftv_term e);
 auto with lngen. intros c Hc.
replace (typ_var_f c) with (tsubst_typ (typ_var_f b) a (typ_var_f c)) by auto with lngen.
repeat rewrite <- tsubst_term_open_term_wrt_typ; eauto.
apply H1; auto.
assert (ftv_term (open_term_wrt_typ e (typ_var_f c))
  [<=] ftv_typ (typ_var_f c) ∪ ftv_term e) by auto with lngen.
simpl in *; fsetdec.
Qed.

Lemma redn_trenaming : forall A a b e e',
  b ∉ ftv_term e →
  e ⇝⋆[A] e' →
  (tsubst_term (typ_var_f b) a e) ⇝⋆[A] (tsubst_term (typ_var_f b) a e').
Proof.
intros A a b e e' H H0.
induction H0; auto using rt_step, red1_trenaming, rt_refl.
Case "trans".
assert (ftv_term y [<=] ftv_term x) by eauto using redn_ftv.
eauto 7 using rt_trans.
Qed.

(** [red0] is well defined *)
Lemma red0_nu_sigma_defined: forall t e b,
   b ∉ ftv_typ (open_typ_wrt_typ t (typ_var_f b)) →
   result (open_term_wrt_typ (term_sigma (typ_var_b 0) t e) (typ_var_f b)) →
   exists e', red0 (term_nu (term_sigma (typ_var_b 0) t e)) NoEps e'.
Proof.
intros t e b H H0.
unfold open_term_wrt_typ in H0; inversion H0; subst.
simpl in H1; inversion H1; try congruence.
pick fresh a.
exists (open_term_wrt_typ
     (open_term_wrt_typ_rec 1 (open_typ_wrt_typ t (typ_var_f b)) e)
     (open_typ_wrt_typ t (typ_var_f b))).
pick fresh c and apply red0_nu_sigma; intros; auto.
apply result_regular in H0. unfold open_term_wrt_typ in H0; inversion H0; subst.
apply tsubst_typ_lc_typ_inv with (a1 := c) (t1 := typ_var_f b); auto.
  rewrite tsubst_typ_open_typ_wrt_typ; auto. autorewrite with lngen; auto.
replace (open_typ_wrt_typ t (typ_var_f c)) with
  (tsubst_typ (typ_var_f c) b (open_typ_wrt_typ t (typ_var_f b))).
rewrite ftv_typ_tsubst_typ_fresh; auto.
assert (ftv_typ (open_typ_wrt_typ t (typ_var_f b)) [<=]
  ftv_typ (typ_var_f b) ∪ ftv_typ t) by auto with lngen. simpl in H1; fsetdec.
assert (b ∉ ftv_typ t).
  assert (ftv_typ t [<=] ftv_typ (open_typ_wrt_typ t (typ_var_f b)))
    by auto with lngen. simpl in H1; auto.
rewrite <- tsubst_typ_intro; auto.
unfold open_term_wrt_typ in H4; inversion H4; subst.
apply result_trenaming_inv with (a := b0) (b := b).
rewrite tsubst_term_open_term_wrt_typ; auto.
rewrite tsubst_term_open_term_wrt_typ_rec; auto. autorewrite with lngen. auto.
unfold open_term_wrt_typ in H4; inversion H4; subst.
repeat rewrite tsubst_term_open_term_wrt_typ; auto.
rewrite <- tsubst_term_intro_rec with (a1 := b0); auto.
rewrite <- tsubst_term_intro_rec with (a1 := a0); auto.
rewrite tsubst_typ_fresh_eq with (a1 := b0); auto. rewrite tvar_tsubst.
replace (open_typ_wrt_typ t (typ_var_f b0)) with
  (open_typ_wrt_typ t (typ_var_f b)). auto.
transitivity (tsubst_typ (typ_var_f b0) b (open_typ_wrt_typ t (typ_var_f b))).
rewrite tsubst_typ_fresh_eq; auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto.
assert (b ∉ ftv_typ t).
  assert (ftv_typ t [<=] ftv_typ (open_typ_wrt_typ t (typ_var_f b)))
    by auto with lngen. fsetdec.
autorewrite with lngen. auto.
apply tsubst_typ_lc_typ_inv with (a1 := b0) (t1 := typ_var_f b); auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto. autorewrite with lngen. auto.
Qed.

Lemma red0_sigma_appL_defined: forall e1 e2 t b,
  result (term_sigma (typ_var_f b) t e1) →
  result e2 →
  exists e',
    red0 (term_app (term_sigma (typ_var_f b) t e1) e2) NoEps e'.
Proof.
intros e1 e2 t b H1 H2. inversion H1; subst.
inversion H; try congruence.
pick fresh a.
exists (term_sigma (typ_var_f b) t
  (term_app e1
    (close_term_wrt_typ a (tsubst_term (typ_var_f a) b e2)))).
pick fresh a0 and apply red0_sigma_appL; intros; auto.
rewrite <- tsubst_term_spec.
rewrite tsubst_term_tsubst_term; auto.
autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (e1 := e2); auto.
Qed.

Lemma red0_sigma_appR_defined: forall e1 e2 t b,
  result (term_sigma (typ_var_f b) t e2) →
  val e1 →
  exists e',
    red0 (term_app e1 (term_sigma (typ_var_f b) t e2)) NoEps e'.
Proof.
intros e1 e2 t b H1 H2. inversion H1; subst.
inversion H; try congruence.
pick fresh a.
exists (term_sigma (typ_var_f b) t
  (term_app
    (close_term_wrt_typ a (tsubst_term (typ_var_f a) b e1)) e2)).
pick fresh a0 and apply red0_sigma_appR; intros; auto.
rewrite <- tsubst_term_spec.
rewrite tsubst_term_tsubst_term; auto.
autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (e1 := e1); auto.
Qed.

Lemma red0_sigma_letL_defined: forall e1 e2 t b,
  result (term_sigma (typ_var_f b) t e1) →
  lc_term (term_let (term_sigma (typ_var_f b) t e1) e2) →
  exists e',
    red0 (term_let (term_sigma (typ_var_f b) t e1) e2) NoEps e'.
Proof.
intros e1 e2 t b H1 H2. inversion H1; subst.
inversion H; try congruence.
pick fresh a.
exists (term_sigma (typ_var_f b) t
  (term_let e1
    (close_term_wrt_typ a (tsubst_term (typ_var_f a) b e2)))).
pick fresh a0 and apply red0_sigma_letL; intros; auto.
rewrite <- tsubst_term_spec.
rewrite tsubst_term_tsubst_term; auto.
autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (e1 := e2); auto.
Qed.

Lemma red0_sigma_inst_defined: forall e t' t b,
  lc_typ t' →
  result (term_sigma (typ_var_f b) t e) →
  exists e',
    red0 (term_inst (term_sigma (typ_var_f b) t e) t') NoEps e'.
Proof.
intros e t' t b Ht' He. inversion He; subst.
inversion H; try congruence.
pick fresh a.
exists (term_sigma (typ_var_f b) t
  (term_inst e
    (close_typ_wrt_typ a (tsubst_typ (typ_var_f a) b t')))).
pick fresh a0 and apply red0_sigma_inst; intros; auto.
rewrite <- tsubst_typ_spec.
rewrite tsubst_typ_tsubst_typ; auto.
autorewrite with lngen.
rewrite tsubst_typ_fresh_eq with (t2 := t'); auto.
Qed.

Lemma red0_sigma_pairL_defined: forall e1 e2 t b,
  result (term_sigma (typ_var_f b) t e1) →
  result e2 →
  exists e',
    red0 (term_pair (term_sigma (typ_var_f b) t e1) e2) NoEps e'.
Proof.
intros e1 e2 t b H1 H2. inversion H1; subst.
inversion H; try congruence.
pick fresh a.
exists (term_sigma (typ_var_f b) t
  (term_pair e1
    (close_term_wrt_typ a (tsubst_term (typ_var_f a) b e2)))).
pick fresh a0 and apply red0_sigma_pairL; intros; auto.
rewrite <- tsubst_term_spec.
rewrite tsubst_term_tsubst_term; auto.
autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (e1 := e2); auto.
Qed.

Lemma red0_sigma_pairR_defined: forall e1 e2 t b,
  result (term_sigma (typ_var_f b) t e2) →
  val e1 →
  exists e',
    red0 (term_pair e1 (term_sigma (typ_var_f b) t e2)) NoEps e'.
Proof.
intros e1 e2 t b H1 H2. inversion H1; subst.
inversion H; try congruence.
pick fresh a.
exists (term_sigma (typ_var_f b) t
  (term_pair
    (close_term_wrt_typ a (tsubst_term (typ_var_f a) b e1)) e2)).
pick fresh a0 and apply red0_sigma_pairR; intros; auto.
rewrite <- tsubst_term_spec.
rewrite tsubst_term_tsubst_term; auto.
autorewrite with lngen.
rewrite tsubst_term_fresh_eq with (e1 := e1); auto.
Qed.

Lemma red0_sigma_exists_defined: forall b c a t e,
  a ≠ c → a ∉ ftv_term e → c ∉ ftv_term e →
  c  `notin` ftv_typ (open_typ_wrt_typ t (typ_var_f c)) →
  result (open_term_wrt_typ (term_sigma (typ_var_b 0) t e) (typ_var_f c)) →
  exists e', red0 (term_exists (term_sigma (typ_var_f b) t e)) NoEps e'.
Proof.
intros b c a t e H H0 H1 H2 H3.
unfold open_term_wrt_typ in H3; inversion H3; subst.
simpl in H4; inversion H4; try congruence.
exists (term_sigma (typ_var_f b) (open_typ_wrt_typ t (typ_var_f c))
  (term_exists
    (close_term_wrt_typ_rec 1 c
      (close_term_wrt_typ a
        (open_term_wrt_typ
          (open_term_wrt_typ e (typ_var_f c)) (typ_var_f a)))))).
pick fresh d and apply red0_sigma_exists; intros.
apply tsubst_typ_lc_typ_inv with (a1 := d) (t1 := typ_var_f c); auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto. autorewrite with lngen. auto.
replace (open_typ_wrt_typ t (typ_var_f d)) with
  (tsubst_typ (typ_var_f d) c (open_typ_wrt_typ t (typ_var_f c))).
rewrite ftv_typ_tsubst_typ_fresh; auto.
assert (ftv_typ (open_typ_wrt_typ t (typ_var_f c)) [<=]
  ftv_typ (typ_var_f c) ∪ ftv_typ t) by auto with lngen. simpl in H4; fsetdec.
assert (c ∉ ftv_typ t).
  assert (ftv_typ t [<=] ftv_typ (open_typ_wrt_typ t (typ_var_f c)))
    by auto with lngen. simpl in H4; auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto. autorewrite with lngen; auto.
apply result_trenaming_inv with (a := c0) (b := c).
rewrite tsubst_term_open_term_wrt_typ; auto.
rewrite tsubst_term_open_term_wrt_typ_rec; auto.
autorewrite with lngen. auto.
transitivity (tsubst_typ (typ_var_f d) c (open_typ_wrt_typ t (typ_var_f c))).
autorewrite with lngen. auto.
assert (c ∉ ftv_typ t).
  assert (ftv_typ t [<=] ftv_typ (open_typ_wrt_typ t (typ_var_f c)))
    by auto with lngen. solve_notin.
rewrite tsubst_typ_open_typ_wrt_typ; auto. autorewrite with lngen. auto.
unfold open_term_wrt_typ.
rewrite open_term_wrt_typ_close_term_wrt_typ_twice.
f_equal. f_equal. unfold close_term_wrt_typ.
rewrite close_term_wrt_typ_rec_open_term_wrt_typ_rec.
rewrite close_term_wrt_typ_rec_open_term_wrt_typ_rec; auto.
assert (ftv_term (open_term_wrt_typ_rec 0 (typ_var_f c) e) [<=]
  ftv_typ (typ_var_f c) ∪ ftv_term e) by auto with lngen.
assert (a ∉ ftv_term e) by auto. clear H5 H6. simpl in H7. fsetdec.
Qed.

Lemma red0_sigma_coerce_defined: forall e t' t b,
  lc_typ t' →
  result (term_sigma (typ_var_f b) t e) →
  exists e',
    red0 (term_coerce (term_sigma (typ_var_f b) t e) t') NoEps e'.
Proof.
intros e t' t b Ht' He. inversion He; subst.
inversion H; try congruence.
pick fresh a.
exists (term_sigma (typ_var_f b) t
  (term_coerce e
    (close_typ_wrt_typ a (tsubst_typ (typ_var_f a) b t')))).
pick fresh a0 and apply red0_sigma_coerce; intros; auto.
rewrite <- tsubst_typ_spec.
rewrite tsubst_typ_tsubst_typ; auto.
autorewrite with lngen.
rewrite tsubst_typ_fresh_eq with (t2 := t'); auto.
Qed.

Lemma red0_sigma_sigma_defined: forall e b1 b2 t1 t2,
  result
  (term_sigma (typ_var_f b1) t1 (term_sigma (typ_var_f b2) t2 e)) →
  exists e',
    red0
    (term_sigma (typ_var_f b1) t1 (term_sigma (typ_var_f b2) t2 e))
    Eps e'.
Proof.
intros e b1 b2 t1 t2 H. inversion H; subst.
inversion H0; try congruence.
pick fresh a1.
assert (result (open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e)
           (typ_var_f a1))) by auto.
unfold open_term_wrt_typ in H0; inversion H0; subst.
inversion H1; subst. inversion H3.
pick fresh a2.
exists (term_sigma (typ_var_f b2) (open_typ_wrt_typ t2 t1)
  (term_sigma (typ_var_f b1)
    (close_typ_wrt_typ a2 t1)
    (close_term_wrt_typ_rec 1 a2
      (close_term_wrt_typ_rec 0 a1
        (open_term_wrt_typ_rec 0 (typ_var_f a1)
          (open_term_wrt_typ_rec 0 (typ_var_f a2) e)))))).
apply red0_sigma_sigma with (L := L ∪ L0 ∪ {{a1}}); intros.
auto with lngen.
replace (open_term_wrt_typ_rec 0 (typ_var_f a0) (open_term_wrt_typ_rec
        1 (typ_var_f a3) e)) with (tsubst_term (typ_var_f a3) a1
        (open_term_wrt_typ_rec 0 (typ_var_f a0) (open_term_wrt_typ_rec
        1 (typ_var_f a1) e))).
apply result_trenaming; apply H7; auto.
rewrite tsubst_term_open_term_wrt_typ_rec; auto.
rewrite tsubst_term_open_term_wrt_typ_rec; auto.
f_equal.
autorewrite with lngen; auto.
autorewrite with lngen; auto.
rewrite <- tsubst_typ_spec. autorewrite with lngen. auto.
rewrite open_term_wrt_typ_close_term_wrt_typ_twice.
f_equal. f_equal.
rewrite close_term_wrt_typ_rec_open_term_wrt_typ_rec.
rewrite close_term_wrt_typ_rec_open_term_wrt_typ_rec; auto.
assert (ftv_term (open_term_wrt_typ_rec 0 (typ_var_f a2) e)
[<=] ftv_typ (typ_var_f a2) ∪ ftv_term e) by auto with lngen.
simpl in H6. clear H3. assert (a1 ≠ a2) by auto. clear Fr0.
fsetdec.
Qed.

(** [redn] reduction is contextually closed *)
Lemma redn_context_letL : forall A e1 e1' e2 x,
  lc_term (open_term_wrt_term e2 (term_var_f x)) →
  e1 ⇝⋆[A] e1' →
  term_let e1 e2 ⇝⋆[A] term_let e1' e2.
Proof.
intros A e1 e1' e2 x Hlc H.
induction H; eauto with clos_refl_trans.
Case "step". apply rt_step. apply red1_let; auto.
eauto using red1_regular1, lc_term_let_exists.
Qed.

Lemma redn_context_appL : forall A e1 e1' e2,
  lc_term e2 → e1 ⇝⋆[A] e1' →
  term_app e1 e2 ⇝⋆[A] term_app e1' e2.
Proof.
intros A e1 e1' e2 Hlc H.
induction H; eauto with clos_refl_trans.
Qed.

Lemma redn_context_appR : forall A e1 e2 e2',
  lc_term e1 → e2 ⇝⋆[A] e2' →
  term_app e1 e2 ⇝⋆[A] term_app e1 e2'.
Proof.
intros A e1 e2 e2' Hlc H.
induction H; eauto with clos_refl_trans.
Qed.

Lemma redn_context_pairL : forall A e1 e1' e2,
  lc_term e2 → e1 ⇝⋆[A] e1' →
  term_pair e1 e2 ⇝⋆[A] term_pair e1' e2.
Proof.
intros A e1 e1' e2 Hlc H.
induction H; eauto with clos_refl_trans.
Qed.

Lemma redn_context_pairR : forall A e1 e2 e2',
  lc_term e1 → e2 ⇝⋆[A] e2' →
  term_pair e1 e2 ⇝⋆[A] term_pair e1 e2'.
Proof.
intros A e1 e2 e2' Hlc H.
induction H; eauto with clos_refl_trans.
Qed.

Lemma redn_context_fst : forall A e e',
  e ⇝⋆[A] e' → term_fst e ⇝⋆[A] term_fst e'.
Proof.
intros A e e' H.
induction H; eauto with clos_refl_trans.
Qed.

Lemma redn_context_snd : forall A e e',
  e ⇝⋆[A] e' → term_snd e ⇝⋆[A] term_snd e'.
Proof.
intros A e e' H.
induction H; eauto with clos_refl_trans.
Qed.

Lemma redn_context_inst : forall A e e' τ,
  lc_typ τ → e ⇝⋆[A] e' →
  term_inst e τ ⇝⋆[A] term_inst e' τ.
Proof.
intros A e e' τ Hlc H.
induction H; eauto with clos_refl_trans.
Qed.

Lemma redn_context_exists : forall A e e' a,
  e ⇝⋆[A] e' →
  term_exists (close_term_wrt_typ a e)
  ⇝⋆[A] term_exists (close_term_wrt_typ a e').
Proof.
intros A e e' a H. induction H; eauto with clos_refl_trans.
Case "step". apply rt_step. pick fresh c and apply red1_exists; auto.
repeat rewrite <- tsubst_term_spec. auto using red1_trenaming.
Qed.

Lemma redn_context_open : forall A e e' b,
  e ⇝⋆[A] e' →
  term_open (typ_var_f b) e ⇝⋆[A] term_open (typ_var_f b) e'.
Proof.
intros A e e' b H.
induction H; eauto with clos_refl_trans.
Qed.

Lemma redn_context_nu : forall A e e' a,
  e ⇝⋆[A] e' →
  term_nu (close_term_wrt_typ a e)
  ⇝⋆[A] term_nu (close_term_wrt_typ a e').
Proof.
intros A e e' a H. induction H; eauto with clos_refl_trans.
Case "step". apply rt_step. pick fresh c and apply red1_nu; auto.
repeat rewrite <- tsubst_term_spec. auto using red1_trenaming.
Qed.

Lemma redn_context_sigma : forall A e e' b a τ,
  lc_typ τ → e ⇝⋆[A] e' →
  (term_sigma (typ_var_f b) τ (close_term_wrt_typ a e))
  ⇝⋆[A] (term_sigma (typ_var_f b) τ (close_term_wrt_typ a e')).
Proof.
intros A e e' b a τ H H0. induction H0; eauto with clos_refl_trans.
Case "step". apply rt_step. pick fresh c and apply red1_sigma; auto.
repeat rewrite <- tsubst_term_spec. auto using red1_trenaming.
Qed.

Lemma redn_context_coerce : forall A e e' τ,
  lc_typ τ → e ⇝⋆[A] e' →
  term_coerce e τ ⇝⋆[A] term_coerce e' τ.
Proof.
intros A e e' τ Hlc H.
induction H; eauto with clos_refl_trans.
Qed.

Hint Resolve redn_context_appL redn_context_appR redn_context_letL
redn_context_pairL redn_context_pairR redn_context_fst
redn_context_snd redn_context_inst redn_context_exists
redn_context_open redn_context_nu redn_context_sigma
redn_context_coerce : redn_context.

(** Eps-reduction preserves results *)
Lemma result_red0_Eps_result : forall e e',
  result e → red0 e Eps e' → result e'.
Proof.
intros e e' H H0. generalize dependent e'.
induction H; intros e' He'; inversion He'; subst.
Case "val". inversion H; congruence.
Case "sigma". inversion H5; subst.
apply result_sigma with (L := L ∪ L0); intros.
SCase "lc proof". pick fresh a.
assert (lc_term (open_term_wrt_typ (term_sigma (typ_var_f b2) t2 e0)
          (typ_var_f a))) by auto.
unfold open_term_wrt_typ in H2; simpl in H2. inversion H2; subst.
rewrite tsubst_typ_intro with (a1 := a); auto with lngen.
SCase "result proof". unfold open_term_wrt_typ; simpl.
apply result_sigma with (L := L ∪ L0 ∪ {{a}}); intros.
SSCase "lc_proof". rewrite (H7 a) in H10; auto.
SSCase "result proof". unfold open_term_wrt_typ; rewrite <- H9; auto.
Qed.

Lemma result_red1_Eps_result : forall e e',
  result e → e ⇝[Eps] e' → result e'.
Proof.
intros e e' H H0. dependent induction H0;
try solve [inversion H; subst; inversion H2; congruence
| inversion H; subst; inversion H1; congruence ].
Case "empty". eauto using result_red0_Eps_result.
Case "pairL". inversion H; subst. inversion H2; subst; try congruence.
elimtype False. eapply val_is_normal with (v := e1); eauto.
Case "pairR". inversion H; subst. inversion H2; subst; try congruence.
elimtype False. eapply val_is_normal with (v := e2); eauto.
Case "exists". inversion H; subst. inversion H2; subst. elimtype False.
pick fresh a. pick fresh b.
assert (open_term_wrt_typ e (typ_var_f a) ⇝[ Eps]
         open_term_wrt_typ e' (typ_var_f a)) by auto; clear H0.
inversion H3; subst. clear H3. unfold open_term_wrt_typ in H6; simpl in H6.
inversion H6; subst.
SCase "empty context".
assert (val (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a)
e'0) (typ_var_f b))). eapply (H5 a b); eauto. reflexivity. clear H5.
inversion H0; subst. destruct e'0; inversion H8; subst.
rewrite <- H8 in H3.
unfold open_term_wrt_typ in H3; simpl in H3; inversion H3; subst. congruence.
SCase "sigma context".
pick fresh c.
assert (val (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f a)
e'0) (typ_var_f c))). eapply (H5 a c); eauto. reflexivity. clear H5.
apply val_is_normal with (A := Eps) in H0. eapply H0. clear H0.
eauto.
Case "sigma". inversion H; subst. inversion H3; congruence.
apply result_sigma with (L := L ∪ L0); intros; auto.
Case "coerce". inversion H; subst. inversion H2; subst; try congruence.
elimtype False. eapply val_is_normal with (v := e); eauto.
Qed.

Lemma result_redn_Eps_result : forall e e',
  result e → e ⇝⋆[Eps] e' → result e'.
Proof.
intros e e' H H0. induction H0; eauto using result_red1_Eps_result.
Qed.
