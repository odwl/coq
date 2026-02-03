
From Stdlib Require Import Bool.Bool.

Definition andb3 (b1 b2 b3:bool) : bool := b1 && (b2 && b3).

Example test_andb31: (andb3 true true true) = true.
Proof. easy. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. easy. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. easy. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. easy. Qed.



(* 
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.


Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(* Compute (next_working_day friday). *)
Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
Proof. easy. Qed. *)
