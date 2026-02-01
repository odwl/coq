Section Minimal_Logic.
  Variables A B C : Prop.
  Goal (A -> B -> C) -> (A -> B) -> A -> C.
  intros ABC AB A0.
  apply ABC.
    exact A0.
    apply AB.
    assumption.
  Save trivial_lemma.
End Minimal_Logic.


Parameters A B C : Prop.
Lemma Exa1 : A -> A.
  intro H. exact H.
Qed.

Lemma Exa1_fun : A -> A.
  exact (fun x => x).
Qed.

Lemma Ex12 : (A -> B) -> (B -> C) -> A -> C.
  intros H H0 H1. apply H0. apply H. exact H1.
Qed.

Lemma Ex12_functional : (A -> B) -> (B -> C) -> A -> C.
Proof.
  Definition my_composer (f : A -> B) (g : B -> C) (x : A) : C := g (f x).
  exact(my_composer).
Qed.

Lemma Ex12_lambda : (A -> B) -> (B -> C) -> A -> C.
Proof.
  (* Definition ploc : (A -> B) -> (B -> C) -> A -> C := fun f g x => g (f x).
  exact(ploc). *)
  exact(fun f g x => g (f x)).
Qed.


Require Import Coq.Program.Basics.
Lemma Ex12_library : (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros f g.
  exact (compose g f).
Qed.

Lemma Ex12_golf : (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros f g x. apply g, f, x. 
Qed.


Lemma Ex13 : A /\ B <-> B /\ A.
  split; intro H; destruct H; split; assumption.
Qed.

Lemma Ex13_clean : A /\ B <-> B /\ A.
Proof.
  pose (
    swap := fun (X Y : Prop) (p : X /\ Y) => 
      match p with 
        | conj x y => conj y x 
      end
    ).
  exact (conj (swap A B) (swap B A)).
Qed.

Lemma Ex13_super_short : A /\ B <-> B /\ A.
Proof.
  pose (swap := (fun {X Y} '(conj x y) => conj y x) : forall {X Y}, X /\ Y -> Y /\ X).
  exact (conj (swap A B) (swap B A)).
Qed.


Notation "'L' x" := (or_introl x) (at level 0).
Notation "'R' x" := (or_intror x) (at level 0).
Lemma Ex14 : A \/ B <-> B \/ A.
Proof.
  pose (swap_or := fun (X Y : Prop) (p : X \/ Y) =>
    match p with
    | L x => R x (* If we have Left X, put it in Right *)
    | R y => L y (* If we have Right Y, put it in Left *)
    end).
  exact (conj (swap_or A B) (swap_or B A)).
Qed.

Lemma Ex15 : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
 exact (conj 
  (fun '(conj (conj a b) c) => conj a (conj b c))
  (fun '(conj a (conj b c)) => conj (conj a b) c)
  ).
Qed.

Lemma Ex16 : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
 exact (conj 
  (fun '(conj (conj a b) c) => conj a (conj b c))
  (fun '(conj a (conj b c)) => conj (conj a b) c)
  ).
Qed.


 



