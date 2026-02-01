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

Require Import Coq.Logic.ClassicalChoice.
Lemma ex2 : (forall x, exists y, R x y) <-> exists f : X -> Y, forall x, R x (f x).
Proof.
  split.
  - intro f. apply choice. assumption.
  - intros [g cond] x. exists (g x). exact (cond x). 
Qed.

Lemma ex3 : (exists y, forall x, R x y) -> forall x, exists y, R x y.
Proof.
  intros [y cond] x. exists y. exact (cond x).
Qed.


  (* - intros [g cond] x.  exact (ex_intro _ (g x) (cond x) ).

  - intros [g cond]. exact( fun x => ex_intro _ (g x) (cond x) ). *)
  (* - intro f. destruct f as [g cond]. exact( fun x => ex_intro _ (g x) (cond x) ). *)
  (* - intros f. intros x. destruct f as [g h]. exact(@ex_intro Y (fun y => R x y) (g x) (h x)).
  - intros f. intros x. destruct f as [g h]. exact(ex_intro _ (g x) (h x)). *)


  
  (* - intros f x. destruct f as [g h]. exists (g x). exact(h x). *)
  