(* Require Import Coq.Program.Basics.
Open Scope program_scope. *)

Parameter X Y : Set.
Parameters A B : X -> Prop.
Parameter R : X -> Y -> Prop.

Lemma ex1 : (forall x, A x /\ B x) <-> (forall x, A x) /\ (forall x, B x).
Proof.
  split.
  - intro f. split; intro x; destruct (f x); assumption.
  - intros [f g] x. split. exact(f x). exact(g x).
Qed. 

Lemma ex1_fun : (forall x, A x /\ B x) <-> (forall x, A x) /\ (forall x, B x).
Proof.
  split.
  - intro f. split; intro x; apply f. 
  - intros [f g]. exact(fun x => conj (f x) (g x)).

  (* exact (fun f =>  conj 
  (fun x => proj1(f x)) 
  (fun x => proj2(f x))). *)
  
  (* - exact (fun '(conj f g) => (fun x => conj (f x) (g x))). *)
Qed. 





(* 

Parameters A B C : Prop.
Goal (A -> B -> C) -> (A -> B) -> A -> C.
  intros ABC AB A0.
  apply ABC.
    exact A0.
    apply AB.
    assumption.


Lemma Exa1 : A -> A.
  intros. exact H.
Qed.

Lemma Ex12 : (A -> B) -> (B -> C) -> A -> C.
  intros. apply H0. apply H. exact H1.
Qed. *)
