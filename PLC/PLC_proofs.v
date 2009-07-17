Add LoadPath "metatheory".
Require Export Coq.Program.Equality.
Require Export PLC_inf.

(* Notations *)
Notation "[ e2 / x ] e1" := (subst_term e2 x e1) (at level 25).
Notation "e1 '→' e2" := (red1 e1 e2) (at level 20).
(* Notation "e1 '→⋆' e2" := (clos_refl_trans _ red1 e1 e2) (at level 20). *)
Notation "e1 '⇒' e2" := (para_red e1 e2) (at level 20).
Notation "e1 '⋆' = e2" := (can e1 e2) (at level 20).

(* Tactics *)
Tactic Notation "absurdity" "with" tactic(tac) :=
  assert False by tac; contradiction.
Ltac absurdity := absurdity with auto.
Ltac size_absurd size t :=
  assert (1 <= size t) by auto with lngen; absurdity with omega.
Ltac size_term_absurd t := size_absurd size_term t.

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
Qed.
Hint Resolve para_red_regular1 para_red_regular2.

Lemma can_regular1 : forall e1 e2, e1⋆ = e2 -> lc_term e1.
Proof.
intros e1 e2 H; induction H; auto.
Qed.

Lemma can_regular2 : forall e1 e2, e1⋆ = e2 -> lc_term e2.
Proof.
intros e1 e2 H; induction H; auto.
pick fresh x; auto with lngen.
Qed.
Hint Resolve can_regular1 can_regular2.

Lemma can_renaming : forall e1 e2 x y,
  e1 ⋆ = e2 ->
  (subst_term (term_var_f y)  x e1) ⋆ = (subst_term (term_var_f y) x e2).
Proof.
assert (forall n e1, size_term e1 <= n -> forall e2 (x y: termvar),
  can e1 e2 -> can (subst_term (term_var_f y) x e1) (subst_term (term_var_f y) x e2)) as Th.
intro n; induction n; intros e1 Hsize e2 x y H.
size_term_absurd e1.
destruct H; simpl in *.
Case "var". destruct (x0 == x); subst; auto.
Case "abs". apply can_abs with (L := L `union` {{ x }}); intros.
  replace (term_var_f x0) with (subst_term (term_var_f y) x (term_var_f x0)) by auto with lngen.
  repeat rewrite <- subst_term_open_term_wrt_term; auto.
  apply IHn; auto; autorewrite with lngen; omega.
Case "app1". apply can_app1; try solve [apply IHn; auto; omega].
  intro; destruct e1; simpl; try congruence. destruct (t == x); congruence.
Case "app2".
  rewrite subst_term_open_term_wrt_term; auto.
  apply can_app2 with (L := L `union` {{x}}); intros.
  replace (term_var_f x0) with (subst_term (term_var_f y) x (term_var_f x0)) by auto with lngen.
  repeat rewrite <- subst_term_open_term_wrt_term; auto.
  apply IHn; auto; autorewrite with lngen; omega.
  apply IHn; auto; omega.

intros e1 e2 x y H; apply Th with (n := size_term e1); auto.
Qed.

(* Lemmas about values *)
Lemma value_is_normal_aux :
  (forall v, pval v -> ~ exists e, v → e) /\
  (forall v, val v -> ~ exists e, v → e).
Proof.
apply pval_val_mut_ind; intros; intros [e0 Hred]; inversion Hred; subst; eauto.
inversion H.
inversion H1; subst. inversion p.
inversion H0.
pick fresh x. eapply H; eauto.
Qed.

Lemma value_is_normal : forall v, val v -> ~ exists e, v → e.
Proof.
destruct value_is_normal_aux as [_ Th]. intuition auto.
Qed.

(* Lemmas about canonize *)
Lemma can_deterministic : forall e e1 e2,
  e⋆ = e1 -> e⋆ = e2 -> e1 = e2.
Proof.
intros e e1 e2 H. generalize dependent e2. induction H; intros.
inversion H; reflexivity.
inversion H1; subst; f_equal; pick fresh x;
  apply open_term_wrt_term_inj with (x1 := x); auto.
inversion H2; subst.
  erewrite IHcan1; eauto; erewrite IHcan2; eauto.
  edestruct H; eauto.
inversion H2; subst.
  edestruct H5; eauto.
  f_equal; auto.
  pick fresh x; eauto using open_term_wrt_term_inj.
Qed.

Lemma can_total : forall e1, lc_term e1 -> exists e2, e1⋆ = e2.
Proof.
intros e1 Hlc; induction Hlc; eauto.
Case "abs". pick fresh x; destruct (H0 x) as [e2 H2].
  exists (term_abs (close_term_wrt_term x e2)).
  apply can_abs with (L := {{x}}); intros.
  rewrite <- (close_term_wrt_term_open_term_wrt_term e x); auto.
  repeat rewrite <- subst_term_spec.
  auto using can_renaming.
Case "app". destruct IHHlc1 as [e1' H1]. destruct IHHlc2 as [e2' H2].
destruct Hlc1; try solve [exists (term_app e1' e2'); apply can_app1; auto; congruence].
SCase "abs".
inversion H1; subst. exists (open_term_wrt_term e' e2'). apply can_app2 with (L := L); auto.
Qed.

(*
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
  intros y Hy. pick fresh x.
  assert (fv_term e1' [<=] fv_term (open_term_wrt_term e1' (term_var_f x))) as H3 by auto with lngen.
  assert (fv_term (open_term_wrt_term e1 (term_var_f x)) [<=] fv_term (term_var_f x) `union` fv_term e1) as H4 by auto with lngen.
  assert (fv_term (open_term_wrt_term e1' (term_var_f x)) [<=] fv_term (open_term_wrt_term e1 (term_var_f x))) as H5 by auto.
  assert (fv_term e1' [<=] fv_term (term_var_f x) `union` fv_term e1) as H6 by fsetdec; clear H3 H4 H5.
  assert (y `in` fv_term (term_var_f x) `union` fv_term e1 `union` fv_term e2) as H3 by fsetdec; clear H6.
  simpl in *; fsetdec.
Qed.
Hint Resolve can_fv.
*)

(* Lemmas about red_star *)
(*
Lemma red_star_context_app : forall e1 e1' e2 e2',
  lc_term e1 -> lc_term e2 ->
  e1 →⋆ e1' -> e2 →⋆ e2' ->
  term_app e1 e2 →⋆ term_app e1' e2'.
Proof.
(* TODO *)
Admitted.
*)


(* Lemmas about para_red *)
Lemma para_red_refl : forall e, lc_term e -> e ⇒ e.
Proof.
intros e H. induction H; try solve [constructor; auto].
apply para_red_abs with (L := fv_term e); auto.
Qed.
Hint Resolve para_red_refl.

Lemma red0_para_red : forall e1 e2, red0 e1 e2 -> e1 ⇒ e2.
Proof.
intros e1 e2 H. inversion H; subst.
apply para_red_app2 with (L := fv_term e0); eauto.
Qed.
Hint Resolve red0_para_red.

Lemma red1_para_red : forall e1 e2, e1 → e2 -> e1 ⇒ e2.
Proof.
intros e1 e2 H. induction H; auto.
apply para_red_abs with (L := L); auto.
Qed.

Lemma para_red_subst : forall e1 e1' e2 e2' x,
  e1 ⇒ e1' -> e2 ⇒ e2' ->
  (subst_term e2 x e1) ⇒ (subst_term e2' x e1').
Proof.
intros e1 e1' e2 e2' x H.
assert (lc_term e1) as Hlc by eauto.
generalize dependent e1'.
generalize dependent e2.
generalize dependent e2'.
generalize dependent x.
induction Hlc; intros y f2' f2 e1' Htt' Huu'; inversion Htt'; subst; simpl.
destruct (x == y); auto.
apply para_red_abs with (L := L `union` singleton y); intros.
  assert (term_var_f x = subst_term f2 y (term_var_f x)) as H3. autorewrite with lngen; reflexivity.
  assert (term_var_f x = subst_term f2' y (term_var_f x)) as H4. autorewrite with lngen; reflexivity.
  rewrite H3 at 1; clear H3.
  rewrite H4 at 2; clear H4.
  repeat rewrite <- subst_term_open_term_wrt_term; eauto.
apply para_red_app1; auto.
rewrite subst_term_open_term_wrt_term; eauto.
  assert (para_red (subst_term f2 y (term_abs e0)) (subst_term f2' y (term_abs e1'0))) as Ht.
    apply IHHlc1; auto;
    apply para_red_abs with (L := L); auto.
  simpl in Ht; inversion Ht; subst; clear Ht.
  apply para_red_app2 with (L := L `union` L0 `union` {{y}}); auto.
Qed.

Lemma para_red_canonize : forall e1 e2 e1',
  e1 ⇒ e2 -> e1 ⋆ = e1' -> e2 ⇒ e1'.
Proof.
intros e1 e2 e1' Hpara Hcan. generalize dependent e1'.
induction Hpara; intros v Hcan.
inversion Hcan; subst; constructor.
inversion Hcan; subst; apply para_red_abs with (L := L `union` L0); intros; auto.
inversion Hcan; subst.
  constructor; auto.
  inversion Hpara1; subst; pick fresh x; assert (para_red (term_abs e') (term_abs e1'0)) as H by eauto.
    inversion H; subst; apply para_red_app2 with (L := L1); intros; auto.
inversion Hcan; subst.
  absurdity with congruence.
  pick fresh x for (fv_term e1' `union` fv_term e1'0 `union` L `union` L0).
  rewrite <- (close_term_wrt_term_open_term_wrt_term e1' x); auto.
  rewrite <- (close_term_wrt_term_open_term_wrt_term e1'0 x); auto.
  repeat rewrite <- subst_term_spec.
  apply para_red_subst; auto.
Qed.

Lemma para_red_diamond : forall e e1 e2,
  e ⇒ e1 -> e ⇒ e2 -> exists e', e1 ⇒ e' /\ e2 ⇒ e'.
Proof.
intros e e1 e2 H1 H2.
destruct (can_total e) as [e' H']; eauto.
eauto using para_red_canonize.
Qed.

(*
Lemma para_red_red_star : forall e1 e2, e1 ⇒ e2 -> e1 →⋆ e2.
Proof.
intros e1 e2 H.
assert (lc_term e1) as Hlc by eauto.
generalize dependent e2.
induction Hlc; intros e0 Hpara; inversion Hpara; subst.
apply rt_refl.
pick fresh x for (L `union` fv_term e `union` fv_term e').
  assert (open_term_wrt_term e (term_var_f x) ⇒ open_term_wrt_term e' (term_var_f x)) by auto.
  assert (open_term_wrt_term e (term_var_f x) →⋆ open_term_wrt_term e' (term_var_f x)) by auto.
(* TODO *)

  assert (red_star (open_ex x e) (open_ex x e20)) as Hpara' by auto.
  replace (term_abs e) with (inject (CAbs x CEmpty) (open_ex x e)).
  replace (term_abs e20) with (inject (CAbs x CEmpty) (open_ex x e20)).
  apply red_star_context_closed; auto.
  simpl; rewrite close_ex_open_ex; auto.
  simpl; rewrite close_ex_open_ex; auto.
assert (red_star e e20) as He by auto. assert (red_star e1 u') as He1 by auto.
  clear IHHlc1 IHHlc2 H1 H3 Hpara.
  inversion He; subst.
    replace (term_app e20 e1) with (inject (CAppR e20 CEmpty) e1) by reflexivity.
    replace (term_app e20 u') with (inject (CAppR e20 CEmpty) u') by reflexivity.
    apply red_star_context_closed; auto.
  inversion He1; subst.
    replace (term_app e u') with (inject (CAppL CEmpty u') e) by reflexivity.
    replace (term_app e20 u') with (inject (CAppL CEmpty u') e20) by reflexivity.
    apply red_star_context_closed; auto.
  apply red_star_trans with (t2 := term_app e20 e1).
    replace (term_app e e1) with (inject (CAppL CEmpty e1) e) by reflexivity.
    replace (term_app e20 e1) with (inject (CAppL CEmpty e1) e20) by reflexivity.
    apply red_star_context_closed; auto.
    replace (term_app e20 e1) with (inject (CAppR e20 CEmpty) e1) by reflexivity.
    replace (term_app e20 u') with (inject (CAppR e20 CEmpty) u') by reflexivity.
    apply red_star_context_closed; auto.
assert (red_star (term_abs e1) (term_abs e20)) as Ht.
    apply IHHlc1. apply ParaAbs with (S := S `union` fv_term e1 `union` fv_term e1 `union` fv_term u' `union` fv_term e20). auto.
  assert (red_star e1 u') as He1 by auto.
  apply red_star_trans with (t2 := term_app (term_abs e20) e1).
    replace (term_app (term_abs e1) e1) with (inject (CAppL CEmpty e1) (term_abs e1)) by reflexivity.
    replace (term_app (term_abs e20) e1) with (inject (CAppL CEmpty e1) (term_abs e20)) by reflexivity.
    apply red_star_context_closed; auto.
  apply red_star_trans with (t2 := term_app (term_abs e20) u').
    replace (term_app (term_abs e20) e1) with (inject (CAppR (term_abs e20) CEmpty) e1) by reflexivity.
    replace (term_app (term_abs e20) u') with (inject (CAppR (term_abs e20) CEmpty) u') by reflexivity.
    apply red_star_context_closed; auto.
    replace (term_app (term_abs e20) u') with (inject CEmpty (term_app (term_abs e20) u')) by reflexivity.
    replace (open_ex u' e20) with (inject CEmpty (open_ex u' e20)) by reflexivity.
    apply RedSome. apply RedOne. constructor. constructor.
Qed.
*)