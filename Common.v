From Stdlib Require Import Logic.Classical_Prop.

Tactic Notation "check" constr(P) "as" ident(p) ident(np) := 
  destruct (classic P) as [p | np].

Notation "( x ; p )" := (ex_intro _ x p).

Definition Case {P Result : Prop} (yes : P -> Result) (no : ~P -> Result) : Result :=
  or_ind yes no (classic P).

