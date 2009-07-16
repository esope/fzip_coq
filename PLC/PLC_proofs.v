Add LoadPath "metatheory".
Require Export Coq.Program.Equality.
Require Export PLC_inf.

(* Notations *)
Notation "[ e2 / x ] e1" := (subst_term e2 x e1) (at level 25).
Notation "e1 '→' e2" := (red1 e1 e2) (at level 20).
Notation "e1 '⇒' e2" := (para_red e1 e2) (at level 20).
Notation "e1 '⋆' = e2" := (can e1 e2) (at level 20).

(* Mutual induction principles *)
Scheme pval_mut_ind_aux := Induction for pval Sort Prop
with   val_mut_ind_aux  := Induction for val  Sort Prop.
Combined Scheme pval_val_mut_ind from pval_mut_ind_aux, val_mut_ind_aux.

(* Administrative lemmas *)
Lemma pval_val_regular :
  (forall p, pval p -> lc_term p) /\ (forall v, val v -> lc_term v).
Proof.
apply pval_val_mut_ind; eauto.
Qed.

Lemma pval_regular : forall p, pval p -> lc_term p.
Proof.
intros; destruct pval_val_regular as [H1 _]; auto.
Qed.

Lemma val_regular : forall v, val v -> lc_term v.
Proof.
intros; destruct pval_val_regular as [_ H2]; auto.
Qed.
Hint Resolve pval_regular val_regular.

Lemma red0_regular1 : forall e1 e2, red0 e1 e2 -> lc_term e1.
Proof.
intros e1 e2 H; destruct H; auto.
Qed.

Lemma red0_regular2 : forall e1 e2, red0 e1 e2 -> lc_term e2.
Proof.
intros e1 e2 H; destruct H; auto with lngen.
Qed.
Hint Resolve red0_regular1 red0_regular2.

Lemma red1_regular1 : forall e1 e2, e1 → e2 -> lc_term e1.
Proof.
intros e1 e2 H; induction H; eauto.
Qed.

Lemma red1_regular2 : forall e1 e2, e1 → e2 -> lc_term e2.
Proof.
intros e1 e2 H; induction H; eauto.
Qed.
Hint Resolve red1_regular1 red1_regular2.

Lemma para_red_regular1 : forall e1 e2, e1 ⇒ e2 -> lc_term e1.
Proof.
intros e1 e2 H; induction H; eauto.
Qed.

Lemma para_red_regular2 : forall e1 e2, e1 ⇒ e2 -> lc_term e2.
Proof.
intros e1 e2 H; induction H; eauto.
pick fresh x.
replace (open_term_wrt_term e1' e2') with e1'.
  eauto.
  symmetry; eauto with lngen.
Qed.
Hint Resolve para_red_regular1 para_red_regular2.

Lemma can_regular1 : forall e1 e2, e1⋆ = e2 -> lc_term e1.
Proof.
intros e1 e2 H; induction H; auto.
Qed.

Lemma can_regular2 : forall e1 e2, e1⋆ = e2 -> lc_term e2.
Proof.
intros e1 e2 H; induction H; auto.
pick fresh x; replace (open_term_wrt_term e1' e2') with e1'.
  eauto.
  symmetry; eauto with lngen.
Qed.


(* Lemmas about canonize *)
Lemma can_fv : forall e1 e2, e1⋆ = e2 -> fv_term e2 [<=] fv_term e1.
Proof.
intros e1 e2 H; induction H; simpl; try fsetdec.
Case "app1".
  pick fresh x.
  assert (fv_term (open_term_wrt_term e' (term_var_f x)) [<=]
    fv_term (open_term_wrt_term e (term_var_f x))) by auto.
  assert (fv_term (open_term_wrt_term e (term_var_f x)) [<=]
    fv_term (term_var_f x) `union` fv_term e) by auto with lngen.
  assert (fv_term e' [<=] fv_term (open_term_wrt_term e' (term_var_f x)))
    by auto with lngen.
  simpl in *; fsetdec.
Case "app2".
  assert (fv_term (open_term_wrt_term e1' e2')
    [<=] union (fv_term e2') (fv_term e1')) by auto with lngen.
  pick fresh x.
  intros y Hy.
  assert (y `in` union (fv_term e2') (fv_term e1')) as Hy' by auto.
(* ICI *)
  apply union_1 in Hy'; destruct Hy'.
    assert (y = x) by fsetdec termvar; subst; assert False by fsetdec termvar; contradiction.
    assumption.
assert (fv_ex (open_ex t2' t1') [<=] fv_ex t2' `union` fv_ex t1') by auto with lngen.
  fsetdec termvar.

Lemma can_total : forall e1, lc_term e1 -> exists e2, e1⋆ = e2.
Proof.
intros e1 Hlc; induction Hlc; eauto.
pick fresh x. destruct (H0 x) as [e2 H2]. exists (term_abs e2).
