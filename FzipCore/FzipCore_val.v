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

(** Renaming lemmas *)
Lemma pval_val_renaming : forall x y,
  (forall v, pval v → pval (subst_term (term_var_f y) x v)) ∧
  (forall v, val v → val (subst_term (term_var_f y) x v)).
Proof.
intros x y.
apply pval_val_mut_ind; intros; simpl; auto.
Case "var". destruct (x0 == x); auto.
Case "abs". pick fresh z and apply val_abs; auto.
  rewrite subst_term_open_term_wrt_term_var; auto.
Case "gen". pick fresh a and apply val_gen; auto.
  rewrite subst_term_open_term_wrt_typ_var; auto.
Qed.

Lemma val_renaming : forall x y v,
  val v → val (subst_term (term_var_f y) x v).
Proof.
intros x y v H. destruct (pval_val_renaming x y); auto.
Qed.
Hint Resolve val_renaming.

Lemma pval_val_trenaming : forall a b,
  (forall v, pval v → pval (tsubst_term (typ_var_f b) a v)) ∧
  (forall v, val v → val (tsubst_term (typ_var_f b) a v)).
Proof.
intros a b.
apply pval_val_mut_ind; intros; simpl; auto with lngen.
Case "abs". pick fresh z and apply val_abs; auto with lngen.
  rewrite tsubst_term_open_term_wrt_term_var; auto.
Case "gen". pick fresh c and apply val_gen; auto.
  rewrite tsubst_term_open_term_wrt_typ_var; auto.
Qed.

Lemma val_trenaming : forall a b v,
  val v → val (tsubst_term (typ_var_f b) a v).
Proof.
intros a b v H. destruct (pval_val_trenaming a b); auto.
Qed.
Hint Resolve val_trenaming.
*)
