From Stdlib Require Import Logic.Classical_Prop.

Tactic Notation "check" constr(P) "as" ident(p) ident(np) := 
  destruct (classic P) as [p | np].

Notation "( x ; p )" := (ex_intro _ x p).
Notation "'L' x" := (or_introl x) (at level 0).
Notation "'R' x" := (or_intror x) (at level 0).

(* Definition L {A B} (x : A) : A \/ B := or_introl x.
Definition R {A B} (y : B) : A \/ B := or_intror y. *)
Definition Case {P Result : Prop} (yes : P -> Result) (no : ~P -> Result) : Result :=
  or_ind yes no (classic P).

