From Stdlib Require Import Logic.Classical_Prop.

Tactic Notation "check" constr(P) "as" ident(p) ident(np) := 
  destruct (classic P) as [p | np].
