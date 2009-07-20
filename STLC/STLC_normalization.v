Add LoadPath "metatheory".
Require Export STLC_soundness.
Require Import Ensembles.

Definition sn e := Acc red1 e.

Inductive neutral : term → Prop :=
| neutral_var : forall x, neutral (term_var_f x)
| neutral_app : forall e e', neutral (term_app e e').

Fixpoint reduce τ : Ensemble term := match τ with
| typ_base => 

Inductive reduce (e: term) : typ → Prop :=
| reduce_base : forall Γ,
  wfterm Γ e typ_base → sn e ->
  reduce e typ_base
| reduce_arrow : forall Γ τ₁ τ₂,
  wfterm Γ e (typ_arrow τ₁ τ₂) ->
  (forall e', reduce e' τ₁ → reduce (term_app e e') τ₂) →
  reduce e (typ_arrow τ₁ τ₂).


Theorem strong_normalization : well_founded red1.