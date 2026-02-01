Require Import List.
Import ListNotations.

Fixpoint last {A : Type} (l : list A) (d : A) : A :=
  match l with
  | [] => d            (* Case 1: List is empty, return default *)
  | x :: nil => x       (* Case 2: List has one element, return it *)
  | x :: xs => last xs d (* Case 3: Recursion on the tail *)
  end.
  
Goal last [1; 2; 3] 0 = 3.
Proof. reflexivity. Qed.
  
Goal last [1; 2; 3] 0 = 3 
  /\ last [] 99 = 99 
  /\ last [5] 0 = 5.
Proof.
  repeat split.
(*   repeat split; reflexivity. *)
Qed.
  

