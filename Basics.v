
From Coq Require Import ssreflect ssrbool.
Require Import Coq.Arith.PeanoNat.

Definition nandb (b1 b2:bool) : bool := negb b1 || negb b2.
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1 b2 b3:bool) : bool := b1 && (b2 && b3).

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat := 
  if n is S p then n * factorial p else 1.

Example test_factorial1: factorial 3 = 6.
Proof. reflexivity. Qed.
Example test_factorial2: factorial 5 = 10 * 12.
Proof. reflexivity. Qed.

Definition pred (n : nat) : nat :=
 if n is S p then p else 0.
Example test_pred_0 : pred(0) = 0. 
Proof. reflexivity. Qed.
Example test_pred_1 : pred(0) = 0. 
Proof. reflexivity. Qed.

Definition is_0 (n : nat) : bool := 
  Nat.eqb n 0.

Example test_is_0_0: (is_0 0) = true.
Proof. reflexivity. Qed.
Example test_is_0_1: (is_0 1) = false.
Proof. reflexivity. Qed.
Example test_is_0_2: (is_0 2) = false.
Proof. reflexivity. Qed.

Fixpoint double (n : nat) : nat :=
  if n is S p then S (S (double p)) else 0.

(* Lemma double_is_plus : forall n, double n = n + n.
Proof.
  intros. 
  (* Need induction*)
Qed. *)

Example test_double_0: double 0 = 0.
Proof. reflexivity. Qed.
Example test_double_1: double 1 = 2.
Proof. reflexivity. Qed.
Example test_double_2: double 2 = 4.
Proof. reflexivity. Qed.
Example test_double_3: double 3 = 6.
Proof. reflexivity. Qed.
Example test_double_4: double 4 = 8.
Proof. reflexivity. Qed.

Fixpoint sum_n (n : nat) : nat :=
  if n is S p then n + sum_n(p) else 0.

Example test_sum_n_0: sum_n 0 = 0.
Proof. reflexivity. Qed.
Example test_sum_n_1: sum_n 1 = 1.
Proof. reflexivity. Qed.
Example test_sum_n_2: sum_n 2 = 3.
Proof. reflexivity. Qed.
Example test_sum_n_3: sum_n 3 = 6.
Proof. reflexivity. Qed.
Example test_sum_n_4: sum_n 4 = 10.
Proof. reflexivity. Qed.

Fixpoint power_2 (n: nat) : nat := 
  if n is S p then 2 * power_2(p) else 1.

Example test_power_2_0: power_2 0 = 1.
Proof. reflexivity. Qed.
Example test_power_2_1: power_2 1 = 2.
Proof. reflexivity. Qed.
Example test_power_2_2: power_2 2 = 4.
Proof. reflexivity. Qed.
Example test_power_2_3: power_2 3 = 8.
Proof. reflexivity. Qed.
Example test_power_2_4: power_2 4 = 16.
Proof. reflexivity. Qed.
Example test_power_2_5: power_2 5 = 32.
Proof. reflexivity. Qed.

Definition swap {A B : Type} (p : A * B) : B * A :=
  let '(a, b) := p in (b, a).
Example test_swap_1: swap (1, 2) = (2, 1).
Proof. reflexivity. Qed.
Example test_swap_2: swap (3, 5) = (5, 3).
Proof. reflexivity. Qed.
Example test_swap_3: swap (0, 7) = (7, 0).
Proof. reflexivity. Qed.
Example test_swap_4: swap (10, 20) = (20, 10).
Proof. reflexivity. Qed.

Definition add_vec '(x1, y1) '(x2, y2) := (x1 + x2, y1 + y2).
Example test_add_vec_1: add_vec (1, 2) (3, 4) = (4, 6).
Proof. reflexivity. Qed.
Example test_add_vec_2: add_vec (0, 0) (5, 5) = (5, 5).
Proof. reflexivity. Qed.
Example test_add_vec_3: add_vec (10, 20) (5, 10) = (15, 30).
Proof. reflexivity. Qed.
Example test_add_vec_4: add_vec (2, 3) (2, 3) = (4, 6).
Proof. reflexivity. Qed.

Definition minus_two (n: nat): nat :=
  if n is S (S p) then p else 0.
Example test_minustwo_0: minus_two(0) = 0.
Proof. reflexivity. Qed.
Example test_minustwo_1: minus_two(1) = 0.
Proof. reflexivity. Qed.
Example test_minustwo_2: minus_two(2) = 0.
Proof. reflexivity. Qed.
Example test_minustwo_3: minus_two(3) = 1.
Proof. reflexivity. Qed.

(* Definition swap {A B : Type} (p : A * B) : B * A :=
  match p with
  | (a, b) => (b, a)
  end. *)

Fixpoint even (n: nat): bool :=
  if n is S (S p) then even p else Nat.eqb n 0.

Example test_even_0: even(0) = true.
Proof. reflexivity. Qed.
Example test_even_1: even(1) = false.
Proof. reflexivity. Qed.
Example test_even_2: even(2) = true.
Proof. reflexivity. Qed.
Example test_even_11: even(11) = false.
Proof. reflexivity. Qed.

Definition odd (n: nat): bool :=
negb (even n).
Example test_odd_0: odd(0) = false.
Proof. reflexivity. Qed.
Example test_odd_1: odd(1) = true.
Proof. reflexivity. Qed.
Example test_odd_2: odd(2) = false.
Proof. reflexivity. Qed.
Example test_odd_11: odd(11) = true.
Proof. reflexivity. Qed.

Fixpoint plus (x y: nat) : nat :=
  if (x, y) is (S p, _) then S (plus p y) else y.

Lemma test_plus_x_0 : forall x, plus x 0 = x.
Proof.
  now intros.
(* Need induction here*)
Qed.

Lemma test_plus_0 : forall x, plus 0 x = x.
Proof.
  now intros. 
Qed.

Example plus_0_0: plus 0 0 = 0.
Proof. reflexivity. Qed.
Example plus_3_4: plus 3 4 = 7.
Proof. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
if n is S p then 
    if m is S q then eqb p q else false
    else Nat.eqb m 0.

Example test_eqb_0_0: eqb 0 0 = true.
Proof. reflexivity. Qed.
Example test_eqb_0_1: eqb 0 1 = false.
Proof. reflexivity. Qed.
Example test_eqb_1_0: eqb 1 0 = false.
Proof. reflexivity. Qed.
Example test_eqb_1_1: eqb 1 1 = true.
Proof. reflexivity. Qed.
Example test_eqb_3_3: eqb 3 3 = true.
Proof. reflexivity. Qed.
Example test_eqb_3_5: eqb 3 5 = false.
Proof. reflexivity. Qed.










  





