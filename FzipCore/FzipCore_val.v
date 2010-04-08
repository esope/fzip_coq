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

(*
(** Lemmas about values *)
Lemma value_is_normal_aux :
  (forall v, pval v → ~ exists e, v ⇝ e) ∧
  (forall v, val v → ~ exists e, v ⇝ e).
Proof.
apply pval_val_mut_ind; intros; intros [e0 Hred]; inversion Hred; subst; eauto.
inversion H.
inversion H1; subst. inversion p.
inversion H0; subst. inversion p.
inversion H0.
pick fresh x. eapply H; eauto.
inversion H0.
pick fresh a. eapply H; eauto.
Qed.

Lemma value_is_normal : forall v, val v → ~ exists e, v ⇝ e.
Proof.
destruct value_is_normal_aux as [_ Th]. intuition auto.
Qed.
*)

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
