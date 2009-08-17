Require Export Relations.
Require Export PLC_inf.
Require Export Utf8.
Require Export Coq.Program.Equality.

(* Notations *)
Notation "[ e2 / x ] e1" := (subst_term e2 x e1) (at level 67).
Notation "[ y → x ] e" := (subst_term (term_var_f y) x e) (at level 67).
Notation "e1 ^^ e2" := (open_term_wrt_term e1 e2) (at level 67).
Notation "e ^ x" := (e ^^ (term_var_f x)).
Notation "e1 '⇝' e2" := (red1 e1 e2) (at level 68).
Notation "e1 '⇝⋆' e2" := (clos_refl_trans _ red1 e1 e2) (at level 68).
Notation "e1 '⇒' e2" := (para_red e1 e2) (at level 68).
Notation "e1 '⇒⁺' e2" := (clos_trans _ para_red e1 e2) (at level 68).
Notation "e1 '↓' = e2" := (can e1 e2) (at level 68).

(* Tactics *)
Tactic Notation "absurdity" "with" tactic(tac) :=
  assert False by tac; contradiction.
Ltac absurdity := absurdity with auto.
Ltac size_absurd size t :=
  assert (1 <= size t) by auto with lngen; absurdity with omega.
Ltac size_term_absurd t := size_absurd size_term t.
