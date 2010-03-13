Add LoadPath "../metatheory".
Require Export Relations.
Require Export FzipCore_inf.
Require Export Utf8.
Require Export Coq.Program.Equality.

(** Notations *)
(*
Notation "[ e2 / x ] e1" := (subst_term e2 x e1) (at level 67).
Notation "[ y → x ] e" := (subst_term (term_var_f y) x e) (at level 67).
*)
Notation "e1 ^^ e2" := (open_term_wrt_term e1 e2) (at level 67).
Notation "e ^ x" := (e ^^ (term_var_f x)).
Notation "e1 '⇝' e2" := (red1 e1 e2) (at level 68).
Notation "e1 '⇝⋆' e2" := (clos_refl_trans _ red1 e1 e2) (at level 68).
Notation "G '⊢' t 'ok'" := (wftyp G t) (at level 67).
Notation "G '⊢' 'ok'" := (wfenv G) (at level 67).
Notation "G '⊢' e ':' t" := (wfterm G e t) (at level 67).
Notation "x '∉' L" := (x `notin` L) (at level 70).
Notation "x '∈' L" := (x `in` L) (at level 70) : set_hs_scope.
Notation "E '∪' F" := (E `union` F) (at level 65, right associativity, format "E '∪' '/' F") : set_hs_scope.

(** Tactics *)
Tactic Notation "absurdity" "with" tactic(tac) :=
  assert False by tac; contradiction.
Ltac absurdity := absurdity with auto.
Ltac size_absurd size t :=
  assert (1 <= size t) by auto with lngen; absurdity with omega.
Ltac size_term_absurd t := size_absurd size_term t.

(** env_map *)
Definition tag_map {A B : Set} (f : A → B) (t : @tag A) :=
  match t with
    | U => U
    | E => E
    | T a => T (f a)
    | Eq a => Eq (f a)
  end.
Hint Unfold tag_map.

Definition env_map {A : Set} (f : typ → A) (env : typing_env) :=
  map (tag_map f) env.
Hint Unfold env_map.

(** Additional lemmas *)
Lemma var_subst : forall e x, subst_term e x (term_var_f x) = e.
Proof.
intros e x; simpl; destruct (x == x); congruence.
Qed.
Hint Rewrite var_subst : lngen.

Lemma tvar_tsubst : forall t a, tsubst_typ t a (typ_var_f a) = t.
Proof.
intros t a; simpl; destruct (a == a); congruence.
Qed.
Hint Rewrite tvar_tsubst : lngen.
