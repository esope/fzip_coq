Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_val.

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
  eapply (H2 b a); auto; reflexivity.
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
erewrite (H3 b a)
with (e1 := open_term_wrt_typ_rec 1 (typ_var_f b) e); auto.
clear H3.
assert (ftv_term (tsubst_term (open_typ_wrt_typ t (typ_var_f b)) a
     (open_term_wrt_typ (open_term_wrt_typ_rec 1 (typ_var_f b) e)
     (typ_var_f a)))[<=] ftv_typ (open_typ_wrt_typ t (typ_var_f b)) ∪
     remove a (ftv_term (open_term_wrt_typ (open_term_wrt_typ_rec 1
     (typ_var_f b) e) (typ_var_f a)))) by auto with lngen.
assert (ftv_typ (open_typ_wrt_typ t (typ_var_f b)) [<=] ftv_typ t).
  assert (ftv_typ (open_typ_wrt_typ t (typ_var_f b)) [<=] ftv_typ
  (typ_var_f b) ∪ ftv_typ t) by auto with lngen.
  assert (b ∉ ftv_typ (open_typ_wrt_typ t (typ_var_f b))) by auto.
  simpl in *. clear Fr Fr0. fsetdec.
assert (ftv_term (open_term_wrt_typ (open_term_wrt_typ_rec 1
               (typ_var_f b) e) (typ_var_f a)) [<=] ftv_typ (typ_var_f
               a) ∪ ftv_term e).
assert (b ∉ ftv_term (open_term_wrt_typ_rec 1 (typ_var_f b) e)).
  assert (b ∉ ftv_term (open_term_wrt_typ_rec 0 (typ_var_f a)
                 (open_term_wrt_typ_rec 1 (typ_var_f b) e))) by auto.
    assert (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f b) e) [<=]
    ftv_term (open_term_wrt_typ_rec 0 (typ_var_f a) (open_term_wrt_typ_rec
    1 (typ_var_f b) e))) by auto with lngen.
    clear Fr Fr0. fsetdec.
  assert (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f b) e) [<=] ftv_term e).
    assert (ftv_term (open_term_wrt_typ_rec 1 (typ_var_f b) e) [<=]
    ftv_typ (typ_var_f b) ∪ ftv_term e) by auto with lngen.
    clear Fr Fr0. simpl in *. fsetdec.
  assert (ftv_term (open_term_wrt_typ (open_term_wrt_typ_rec 1
     (typ_var_f b) e) (typ_var_f a)) [<=] ftv_typ (typ_var_f a) ∪
     ftv_term (open_term_wrt_typ_rec 1 (typ_var_f
     b) e)) by auto with lngen.
  simpl in *. clear Fr Fr0. fsetdec.
clear Fr Fr0. simpl in *. fsetdec.
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
replace (typ_var_f b0) with (tsubst_typ (typ_var_f b) a (typ_var_f b0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec...
replace (typ_var_f a0) with (tsubst_typ (typ_var_f b) a (typ_var_f a0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec...
inversion H7; subst; clear H7.
replace (typ_var_f b0) with (tsubst_typ (typ_var_f b) a (typ_var_f b0))
  by auto with lngen.
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
apply result_trenaming. eapply (H3 b0 a0); auto. reflexivity.
inversion H7; subst; clear H7.
rewrite tsubst_typ_open_typ_wrt_typ_var; auto.
replace (open_term_wrt_typ_rec 1 (typ_var_f b0) (tsubst_term (typ_var_f b) a e0))
with (open_term_wrt_typ_rec 1 (tsubst_typ (typ_var_f b) a (typ_var_f b0)) (tsubst_term (typ_var_f b) a e0)).
rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
rewrite tsubst_term_open_term_wrt_typ_var; auto.
rewrite <- tsubst_term_tsubst_term; auto.
f_equal. eapply H4; auto. reflexivity.
f_equal. auto with lngen.
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

Lemma redn_context_sigma : forall A e e' b a τ,
  lc_typ τ → e ⇝⋆[A] e' →
  (term_sigma (typ_var_f b) τ (close_term_wrt_typ a e))
  ⇝⋆[A] (term_sigma (typ_var_f b) τ (close_term_wrt_typ a e')).
Proof.
intros A e e' b a τ H H0. induction H0; eauto using rt_refl, rt_trans.
Case "step". apply rt_step. pick fresh c and apply red1_sigma; auto.
repeat rewrite <- tsubst_term_spec. auto using red1_trenaming.
Qed.

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
