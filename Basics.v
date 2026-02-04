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

(* Question. How to move intern to. inner add_vec*)
Definition intern (x y: nat) (p: nat * nat) : nat * nat :=  
  (* match p with |  (a, b) => (a + x, b + y) end. *)
  prod_rec _ (fun a b => (x + a, y + b)) p.

(* WRONG I think. prod_rec is use to define a function from Z -> nat * nat 
  instead you give two functions Z -> nat which are. In the match 
  they are f1: (a, b) -> a + x et f2: (a, b) -> b + y.
  Similar to universal property (product are limit = terminal object). 

  For the prod_rec is a bit different. instead of (a, b) in Z we define
  the step function with two arguments because prod as one constructor with two
  arguments.  Bizarre. Or not.
*)

Definition add_vec (p1 p2 : nat * nat) : nat * nat := 
 prod_rec _ (fun x1 y1 => intern x1 y1 p2) p1.

Example test_add_vec_1: add_vec (1, 2) (3, 4) = (4, 6).
Proof. reflexivity. Qed.
Example test_add_vec_2: add_vec (0, 0) (5, 5) = (5, 5).
Proof. reflexivity. Qed.
Example test_add_vec_3: add_vec (10, 20) (5, 10) = (15, 30).
Proof. reflexivity. Qed.
Example test_add_vec_4: add_vec (2, 3) (2, 3) = (4, 6).
Proof. reflexivity. Qed.


Definition minus_two (n: nat): nat :=
nat_rec _ 0 (fun p res => match p with |0 => 0 |1 => 0 |_ => S res end) n.

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

Definition even (n: nat): bool :=
fst(
  Nat.iter n swap (true, false)
).
Example test_even_0: even(0) = true.
Proof. reflexivity. Qed.
Example test_even_1: even(1) = false.
Proof. reflexivity. Qed.
Example test_even_2: even(2) = true.
Proof. reflexivity. Qed.
Example test_even_11: even(11) = false.
Proof. reflexivity. Qed.



(* 
1. 0, true -> false 
2. 1. false -> true *)


(* Fixpoint even (n: nat): bool :=
match n with 
| 0 => true
| (S p) => negb (even p)
end. *)
(* 
Definition even (n: nat): bool :=
match n with 
| 0 => true
| 1 => false
| S (S p) => even p
end. *)

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

Definition plus (x y: nat) : nat :=
nat_rec _ y (fun _ res => S res) x.

Example plus_0_0: plus 0 0 = 0.
Proof. reflexivity. Qed.
Example plus_3_4: plus 3 4 = 7.
Proof. reflexivity. Qed.









  





