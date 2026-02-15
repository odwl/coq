From Stdlib Require Import Program.Basics.
From Coq Require Import ssreflect ssrbool ssrfun.

Section Ex1.

Definition comp {A B C: Type} (g: B->C) (f: A->B) : A->C :=
    fun a => g (f a).

(* Notation "g \o f" := (comp g f) (at level 40, left associativity). *)

Theorem mycompose_assoc : forall (A B C D: Type) (f: A->B) (g: B->C) (h: C-> D), 
  h \o (g \o f) = h \o g \o f.
Proof.
  reflexivity.
Qed.
End Ex1.

Section Ex2.

Definition Projection1Type := forall {A B: Type}, A * B -> A.
Definition Projection2Type := forall {A B: Type}, A * B -> B.
Definition RecursorType := forall (X Y Z : Type), (X -> Y -> Z) -> (X * Y -> Z).

(* Prove that Projections can be derived from a recursor. *)
Theorem rec_projs : RecursorType -> Projection1Type * Projection2Type.
Proof.  
  move=> rec. split; move=> ? ?; 
  by apply: rec.
Defined.
(* Prove that a recursor can be derived from projections. *)
Theorem projs_rec : Projection1Type * Projection2Type -> RecursorType.
Proof.
  move=> [p1 p2] X Y ? g p.
  exact: g (p1 X Y p) (p2 X Y p).
Defined.
(* Prove one side of the iso. *)
Definition rec_rec (rec : RecursorType) : RecursorType := 
    projs_rec (rec_projs rec).
Definition prod_rec_adapter : RecursorType := 
      fun A B C f p => prod_rect (fun _ => C) f p.
(* Example test_rec_rec := rec_rec (prod_rec_adapter) = prod_rec_adapter. *)


Example test_rec_rec_behavior : forall A B C f p,
  rec_rec prod_rec_adapter A B C f p = prod_rec_adapter A B C f p.
Proof.
  move=> A B C f p. case: p => a b. reflexivity.
Qed.

Definition Counit := forall (M N : Type), (M -> N) * M -> N.
(* Prove that a a counit can be derived from a recursor. *)
Theorem rec_counit : RecursorType -> Counit.
Proof.
  move=> rec M N; 
  by apply: rec.
Qed.

Section Verification.
  
(* Proof that I have the projections associated with prod_rect are behaving as expected *)

Definition my_proj1 : Projection1Type := fst (rec_projs prod_rec_adapter).
Definition my_proj2 : Projection2Type := snd (rec_projs prod_rec_adapter).
Arguments my_proj1 {A B} _.
Arguments my_proj2 {A B} _.
Example test_proj1_10_true : my_proj1 (10, true) = 10. 
Proof. reflexivity. Qed.
Example test_proj2_10_true : my_proj2 (10, true) = true. 
Proof. reflexivity. Qed.
End Verification.

End Ex2.



  (* Example test_id1 : Projection1Type * Projection2Type -> Projection1Type * Projection2Type :rec_projs proj_rec  *)
 
  (* Example test_implicit : my_proj1 nat bool (10, true) = 10.
  Proof. reflexivity. Qed. *)

  Definition projs : Projection1Type * Projection2Type := rec_projs (prod_rec_adapter).
  (* proj1 nat nat (10,20). *)

  (* Example proj1_10_20 := proj1 (10, 20) = 10. *)
  (* Example proj2_10_20 := proj (10, 20) = 20. *)

 (* Definition prod_rec_adapter {A B : Type} : 
  forall (C : Type), (A -> B -> C) -> (A * B -> C) :=
    fun (C : Type) (f : A -> B -> C) (p : A * B) =>
      prod_rect (fun _ => C) f p. *)
(*  
Definition prod_rec_adapter : RecursorType :=

  fun (C : Type) (f : A -> B -> C) (p : A * B) =>
    prod_rect (fun _ => C) f p. *)


(*the recursor can be derived from the projections and vice-versa.
Assume that fst and snd exists.*)
Variables A B C: Type.
Definition my_rec (C: Type) (g: A -> B -> C) (p: A * B) :=  
  g (fst p) (snd p).
(* Definition my_proj1 {A B : Type} (p: A * B) :=  
  prod_rect (fun _ => A) (fun a _ => a) p.
  (* Goal fst = my_rec A (fun a b => a) *)
End Ex2. *)


Parameter rec : forall {A B C : Type}, (A -> B -> C) -> A * B -> C.

Section RecToProj.
  Context {A B : Type}.
  (* Definition rec : forall {C: Type}, (A->B->C) -> A * B -> C := prod_rec _ f p. *)
  Definition proj1 : A*B -> A := rec (fun a b => a).
  Definition proj2 : A*B -> B := rec (fun a b => b).
End RecToProj.

Section Verification.
  (* Definition my_rec {A B C : Type} (f : A -> B -> C) (p : A * B) : C := *)
    (* prod_rect _ f p. *)
  
  
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
