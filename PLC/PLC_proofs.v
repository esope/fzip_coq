Add LoadPath "metatheory".
Require Export Coq.Program.Equality.
Require Export PLC_inf.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_term x) in
  constr:(A \u B \u C).

Notation "[ e2 / x ] e1" := (subst_term e2 x e1) (at level 25).
Notation "e1 '→' e2" := (red1 e1 e2) (at level 20).
Notation "e1 '⇒' e2" := (para_red e1 e2) (at level 20).

