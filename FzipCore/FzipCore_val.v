Add LoadPath "../metatheory".
Require Import FzipCore_init.

Scheme val_mut_ind_aux  := Induction for val  Sort Prop
with   result_mut_ind_aux := Induction for result Sort Prop.
Combined Scheme val_result_mut_ind from val_mut_ind_aux, result_mut_ind_aux.

Lemma val_result_regular :
  (forall v, val v → lc_term v)
  ∧ (forall p, result p → lc_term p).
Proof.
apply val_result_mut_ind; eauto.
Case "val_exists".
  intros; subst.
  pick fresh b; pick fresh a.
  apply (lc_term_exists_exists b).
  unfold open_term_wrt_typ; simpl.
  apply (lc_term_sigma_exists a); auto.
    apply l; auto.
  eapply (H b a); auto; reflexivity.
Qed.

Lemma val_regular : forall v, val v → lc_term v.
Proof.
intros; destruct val_result_regular as [H1 _]; auto.
Qed.

Lemma result_regular : forall p, result p → lc_term p.
Proof.
intros; destruct val_result_regular as [_ H2]; auto.
Qed.
Hint Resolve val_regular result_regular: lngen.

(** Lemmas about values *)
Lemma val_result_is_normal_aux :
  (forall v, val v → forall A, ~ exists e, v ⇝[A] e) ∧
  (forall r, result r → ~ exists e, r ⇝[NoEps] e).
Proof.
apply val_result_mut_ind; intros; intros [e3 He3]; subst.
Case "abs". inversion He3; subst. inversion H.
Case "gen". inversion He3; subst. inversion H.
Case "pair". inversion He3; subst; try solve [intuition eauto].
SCase "empty context". inversion H1; subst.
SSCase "sigma pairL". inversion v; subst; congruence.
SSCase "sigma pairR". inversion v0; subst; congruence.
Case "coerce". inversion He3; subst; try solve [intuition eauto].
SCase "empty context". inversion H0; subst. intuition eauto.
Case "exists". inversion He3; subst.
SCase "empty context". inversion H0.
SCase "exists sigma context".
  pick fresh b.
  assert (open_term_wrt_typ (term_sigma (typ_var_b 0) t' e') (typ_var_f b)
         ⇝[ A]open_term_wrt_typ e'0 (typ_var_f b)) by auto. clear H1.
  unfold open_term_wrt_typ in H0; simpl in H0.
  inversion H0; subst.
  SSCase "sigma sigma in exists context". inversion H1; subst.
  pick fresh a.
  assert (val (open_term_wrt_typ_rec 0 (typ_var_f a)
    (open_term_wrt_typ_rec 1 (typ_var_f b) e'))) as H2.
    eapply (v b a); auto.
    unfold open_term_wrt_typ; simpl; reflexivity. reflexivity.
  rewrite <- H4 in H2. simpl in H2. inversion H2; congruence.
  SSCase "reduction in exists sigma context".
  pick fresh a. eapply (H b a); auto.
  unfold open_term_wrt_typ; simpl; reflexivity. eauto.
Case "result val". intuition eauto.
Case "result sigma". inversion He3; subst.
SCase "sigma sigma in empty context". inversion H0; subst.
SCase "reduction in sigma context". pick fresh a. eapply (H a); eauto.
Qed.

Lemma val_is_normal : forall v, val v → forall A, ~ exists e, v ⇝[A] e.
Proof.
destruct val_result_is_normal_aux. intuition auto.
Qed.

Lemma result_is_normal : forall r, result r → ~ exists e, r ⇝[NoEps] e.
Proof.
destruct val_result_is_normal_aux. intuition auto.
Qed.

(** Renaming lemmas *)
Lemma val_result_trenaming : forall a b,
  (forall v, val v → val (tsubst_term (typ_var_f b) a v)) ∧
  (forall r, result r → result (tsubst_term (typ_var_f b) a r)).
Proof.
intros a b.
apply val_result_mut_ind; intros; subst; simpl; auto.
Case "val abs". inversion l0; subst.
  constructor. auto with lngen.
  constructor; intros. auto with lngen.
  rewrite tsubst_term_open_term_wrt_term_var. auto with lngen.
Case "val gen". inversion l; subst.
  constructor. apply lc_term_gen_exists with (a1 := b).
  replace (open_term_wrt_typ (tsubst_term (typ_var_f b) a e) (typ_var_f b))
  with (open_term_wrt_typ (tsubst_term (typ_var_f b) a e)
    (tsubst_typ (typ_var_f b) a (typ_var_f a))).
  rewrite <- tsubst_term_open_term_wrt_typ; auto with lngen.
  simpl. destruct (a == a); congruence.
Case "val coerce". constructor; intros; auto with lngen.
  destruct e; simpl; congruence.
Case "val exists". pick fresh b1 and apply val_exists; intros; subst.
  reflexivity.
  replace (typ_var_f b1) with (tsubst_typ (typ_var_f b) a (typ_var_f b1)).
  rewrite <- tsubst_typ_open_typ_wrt_typ; auto with lngen.
    autorewrite with lngen; auto.
  inversion H2; subst.
  replace (typ_var_f b0) with (tsubst_typ (typ_var_f b) a (typ_var_f b0)).
  rewrite <- tsubst_term_open_term_wrt_typ_rec; auto.
  replace (typ_var_f a0) with (tsubst_typ (typ_var_f b) a (typ_var_f a0)).
  rewrite <- tsubst_term_open_term_wrt_typ; auto.
  eapply (H b0 a0); auto. reflexivity.
  autorewrite with lngen; auto.
  autorewrite with lngen; auto.
Case "result". destruct (b0 == a); subst.
SCase "b0 = a". pick fresh a0 and apply result_sigma. auto with lngen.
replace (typ_var_f a0) with (tsubst_typ (typ_var_f b) a (typ_var_f a0)).
rewrite <- tsubst_term_open_term_wrt_typ; auto.
autorewrite with lngen; auto.
SCase "b0 ≠ a". pick fresh a0 and apply result_sigma. auto with lngen.
replace (typ_var_f a0) with (tsubst_typ (typ_var_f b) a (typ_var_f a0)).
rewrite <- tsubst_term_open_term_wrt_typ; auto.
autorewrite with lngen; auto.
Qed.

Lemma val_trenaming : forall a b v,
  val v → val (tsubst_term (typ_var_f b) a v).
Proof.
intros. edestruct val_result_trenaming; eauto.
Qed.

Lemma result_trenaming : forall a b r,
  result r → result (tsubst_term (typ_var_f b) a r).
Proof.
intros. edestruct val_result_trenaming; eauto.
Qed.

Lemma val_result_trenaming_inv : forall a b,
  (forall v, val v →
    forall v', v = tsubst_term (typ_var_f b) a v' → val v') ∧
  (forall r, result r →
    forall r', r = tsubst_term (typ_var_f b) a r' → result r').
Proof.
intros a b.
apply val_result_mut_ind; intros; subst; simpl; auto.
Case "val abs". inversion l0; subst.
  destruct v'; inversion H; subst. clear H.
  constructor.
  apply tsubst_typ_lc_typ_inv with (a1 := a) (t1 := typ_var_f b); auto.
  constructor; intros.
  apply tsubst_typ_lc_typ_inv with (a1 := a) (t1 := typ_var_f b); auto.
  apply tsubst_term_lc_term_inv with (a1 := a) (t1 := typ_var_f b); auto.
  rewrite <- tsubst_term_open_term_wrt_term_var. auto.
Case "val gen". inversion l; subst.
  destruct v'; inversion H; subst. clear H.
  constructor.
  apply tsubst_term_lc_term_inv with (a1 := a) (t1 := typ_var_f b); auto.
Case "val pair". destruct v'; inversion H1; subst. auto.
Case "val coerce". destruct v'; inversion H0; subst.
  constructor; intros; auto.
  apply tsubst_typ_lc_typ_inv with (a1 := a) (t1 := typ_var_f b); auto.
  destruct v'; simpl in *; congruence.
Case "val exists".
  destruct v'; simpl in H0; inversion H0; subst. clear H0.
  destruct v'; simpl in H2; inversion H2; subst. 
  destruct t; simpl in H2; inversion H2; subst.
  pick fresh b1 and apply val_exists; intros; subst.
  reflexivity.
  apply tsubst_typ_lc_typ_inv with (a1 := a) (t1 := typ_var_f b); auto.
  rewrite tsubst_typ_open_typ_wrt_typ; auto.
  rewrite tsubst_typ_fresh_eq with (t2 := typ_var_f b1); auto.
  eapply (H b0); auto.
  unfold open_term_wrt_typ; simpl. reflexivity.
  unfold open_term_wrt_typ in H4; inversion H4; subst.
  rewrite tsubst_term_open_term_wrt_typ; auto.
  rewrite tsubst_term_open_term_wrt_typ_rec; auto.
  rewrite tsubst_typ_fresh_eq with (t2 := typ_var_f a0); auto.
  rewrite tsubst_typ_fresh_eq with (t2 := typ_var_f b0); auto.
  unfold typvar in *; destruct (t == a); congruence.
Case "result".
destruct r'; simpl in H0; inversion H0; subst.
destruct t0; simpl in H2; inversion H2; subst.
pick fresh c and apply result_sigma.
  apply tsubst_typ_lc_typ_inv with (a1 := a) (t1 := typ_var_f b); auto.
  apply (H c); auto.
  rewrite tsubst_term_open_term_wrt_typ; auto.
  autorewrite with lngen. auto.
Qed.

Lemma val_trenaming_inv : forall a b v,
  val (tsubst_term (typ_var_f b) a v) → val v.
Proof.
intros. edestruct val_result_trenaming_inv; eauto.
Qed.

Lemma result_trenaming_inv : forall a b r,
  result (tsubst_term (typ_var_f b) a r) → result r.
Proof.
intros. edestruct val_result_trenaming_inv; eauto.
Qed.

Lemma result_sigma_exists : forall a b t e,
  lc_typ t →
  result (open_term_wrt_typ e (typ_var_f a)) →
  result (term_sigma (typ_var_f b) t e).
Proof.
intros a b t e H H0. pick fresh c and apply result_sigma; auto.
apply result_trenaming_inv with (a := c) (b := a).
rewrite tsubst_term_open_term_wrt_typ; auto.
autorewrite with lngen. auto.
Qed.

Lemma val_exists_exists : forall a b t e,
  lc_typ (open_typ_wrt_typ t (typ_var_f b)) →
  val (open_term_wrt_typ 
    (open_term_wrt_typ_rec 1 (typ_var_f b) e) (typ_var_f a)) →
  val (term_exists (term_sigma (typ_var_b 0) t e)).
Proof.
intros a b t e H H0.
pick fresh c and apply val_exists; intros; subst.
reflexivity.
apply tsubst_typ_lc_typ_inv with (a1 := c) (t1 := typ_var_f b).
auto. rewrite tsubst_typ_open_typ_wrt_typ; auto.
autorewrite with lngen. auto.
unfold open_term_wrt_typ in H3; inversion H3; subst.
apply val_trenaming_inv with (a := b0) (b := b).
rewrite tsubst_term_open_term_wrt_typ; auto.
rewrite tsubst_term_open_term_wrt_typ_rec; auto.
autorewrite with lngen.
apply val_trenaming_inv with (a := a0) (b := a).
rewrite tsubst_term_open_term_wrt_typ; auto.
rewrite tsubst_term_open_term_wrt_typ_rec; auto.
autorewrite with lngen. auto.
Qed.
