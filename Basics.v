From Stdlib Require Import Bool.Bool.
Open Scope bool_scope.

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

Fixpoint factorial (n:nat) : nat := match n with
  | 0 => 1
  | S p => n * factorial p
end.
Example test_factorial1: factorial 3 = 6.
Proof. reflexivity. Qed.
Example test_factorial2: factorial 5 = 10 * 12.
Proof. reflexivity. Qed.
(* Example test_large: factorial 10 = 3628800%nat.
Proof.
  vm_compute. (* Much faster than 'simpl' or 'easy'*)
  reflexivity.
Qed. *)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S p => p
end.
Example test_pred_0 : pred(0) = 0. 
Proof. reflexivity. Qed.
Example test_pred_1 : pred(0) = 0. 
Proof. reflexivity. Qed.

Definition pred_combinator (n : nat) : nat :=
  nat_rec (fun _ => nat) 0 (fun p _ => p) n.

Example pred_combinator_0 : pred(0) = 0. 
Proof. reflexivity. Qed.
Example pred_combinator_1 : pred(0) = 0. 
Proof. reflexivity. Qed.
Example pred_combinator_3 : pred(3) = 2.
Proof. reflexivity. Qed.

(* Definition minus_two (n: nat) : nat :=
  match  *)


Definition is_0 (n : nat) : bool := 
  nat_rec _ true (fun p _ => false) n.
(* match n with 
  | 0 => true | _ => false  
end.*)

Example test_is_0_0: (is_0 0) = true.
Proof. reflexivity. Qed.
Example test_is_0_1: (is_0 1) = false.
Proof. reflexivity. Qed.
Example test_is_0_2: (is_0 2) = false.
Proof. reflexivity. Qed.

Definition double (n : nat) : nat :=
  nat_rec (fun _ => nat) 0 (fun _ res  => res+2) n.

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

Definition sum_n (n : nat) : nat :=
  nat_rec _ 0 (fun p res => res + S p) n.

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

Definition power_2 (n: nat) : nat := 
  nat_rec _ 1 (fun _ => Nat.mul 2) n.

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

Definition swap (p: nat * nat) : nat * nat := 
  prod_rec _ (fun a b => (b, a)) p.

Example test_swap_1: swap (1, 2) = (2, 1).
Proof. reflexivity. Qed.
Example test_swap_2: swap (3, 5) = (5, 3).
Proof. reflexivity. Qed.
Example test_swap_3: swap (0, 7) = (7, 0).
Proof. reflexivity. Qed.
Example test_swap_4: swap (10, 20) = (20, 10).
Proof. reflexivity. Qed.





  





