(* Testing the swapping of two bindings *)

Add LoadPath "../metatheory".
Require Import STLC_init.

Inductive swap : term -> term -> Prop :=
| Swap_var : forall x y, swap (term_var_f x) (term_var_f y)
| Swap_app : forall e1 e2 e1' e2',
  swap e1 e1' -> swap e2 e2' ->
  swap (term_app e1 e2) (term_app e1' e2')
| Swap_abs : forall L τ e1 e2 t1 t2,
  e1 = term_abs τ (term_abs τ t1) ->
  e2 = term_abs τ (term_abs τ t2) ->
  (forall x y, x ∉ L -> y ∉ L ∪ {{ x }} ->
    forall e1' e1'' e2' e2'',
      term_abs τ e1' = (term_abs τ t1) ^ x ->
      e1'' = e1' ^ y ->
      term_abs τ e2' = (term_abs τ t2) ^ y ->
      e2'' = e2' ^ x ->
      swap e1'' e2'') ->
  swap e1 e2.

Check swap_ind.

Lemma swap_lc1 : forall e1 e2,
  swap e1 e2 -> lc_term e1.
Proof.
intros e1 e2 H; induction H; eauto.
subst.
pick fresh x; pick fresh y.
  apply (lc_term_abs_exists x);
    unfold open_term_wrt_term; simpl.
  apply (lc_term_abs_exists y);
    unfold open_term_wrt_term; simpl.
eapply (H2 x y); auto; reflexivity.
Qed.  

Lemma swap_lc2 : forall e1 e2,
  swap e1 e2 -> lc_term e2.
Proof.
intros e1 e2 H; induction H; eauto.
subst.
pick fresh x; pick fresh y.
  apply (lc_term_abs_exists y);
    unfold open_term_wrt_term; simpl.
  apply (lc_term_abs_exists x);
    unfold open_term_wrt_term; simpl.
eapply (H2 x y); auto; reflexivity.
Qed.

