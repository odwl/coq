From Stdlib Require Import Program.Basics.

Section Ex1.

Definition comp {A B C: Type} (g: B->C) (f: A->B) : A->C :=
    fun a => g (f a).

Notation "g \o f" := (comp g f) (at level 40, left associativity).

Theorem mycompose_assoc : forall (A B C D: Type) (f: A->B) (g: B->C) (h: C-> D), 
  h \o (g \o f) = h \o g \o f.
Proof.
  reflexivity.
Qed.
End Ex1.

Section Ex2.
(* Show that having a Recursor <-> having projections.*)
Variables A B : Type.
Definition RecursorType := forall C : Type, (A -> B -> C) -> (A * B -> C).
Definition Projection1Type := A * B -> A.
Definition Projection2Type := A * B -> B.
Theorem projs_rec : Projection1Type * Projection2Type -> RecursorType.
Proof.
  intros [p1 p2] C. exact(fun g p => g (p1 p) (p2 p)).
Qed. 
Theorem rec_projs : RecursorType -> Projection1Type * Projection2Type.
Proof.  
  intro rec. exact(pair (rec A const) (rec B (const id))).
Qed.

(*the recursor can be derived from the projections and vice-versa.
Assume that fst and snd exists.*)
Definition my_rec (C: Type) (g: A -> B -> C) (p: A * B) :=  
  g (fst p) (snd p).
Definition my_proj1 {A B : Type} (p: A * B) :=  
  prod_rect (fun _ => A) (fun a _ => a) p.
  (* Goal fst = my_rec A (fun a b => a) *)
End Ex2.



Parameter rec : forall {A B C : Type}, (A -> B -> C) -> A * B -> C.
Section RecToProj.
  Context {A B : Type}.
  (* Definition rec : forall {C: Type}, (A->B->C) -> A * B -> C := prod_rec _ f p. *)
  Definition proj1 : A*B -> A := rec (fun a b => a).
  Definition proj2 : A*B -> B := rec (fun a b => b).
End RecToProj.

Section Verification.
  Definition my_rec {A B C : Type} (f : A -> B -> C) (p : A * B) : C :=
    prod_rect _ f p.
  
  Definition proj11 {A B : Type} (p : A * B) : A :=
    my_rec (fun a b => a) p.
  Definition proj22 {A B : Type} (p : A * B) : B :=
    my_rec (fun a b => b) p.
  
  Example proj1_10_20 := proj11 (10, 20) = 10.
  Example proj2_10_20 := proj22 (10, 20) = 20.

  Lemma proj1_is_correct : forall (A B : Type) (a : A) (b : B),
    proj11 (a, b) = a.
  Proof.
    now cbn.
    (* intros. unfold proj11, my_rec. change ((fun a0 _ => a0) a b = a). change (a=a). *)
  Qed.
End Verification.

(* Theorem th : rec : forall {A B C : Type}, (A -> B -> C) -> A * B -> C *)
