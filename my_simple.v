(* Simply Typed Lambda Calculus *)

Require Import String List.
Import ListNotations. Open Scope string_scope.
Require Import Coq.Program.Basics.

(* 1. Types *)
Inductive type : Type :=
  | Base : string -> type
  | Arrow : type -> type -> type.

Inductive term: Type := 
  | var : string -> term
  | abs : string -> type -> term -> term
  | app : term -> term -> term.

Definition Context := list (string * type).
Fixpoint lookup (x : string) (Gamma : Context) : option type :=
    match Gamma with 
    | [] => None
    | (y, T) :: rest => if string_dec x y then Some T else lookup x rest
    end.

Section TestScope.
    Let A := Base "A".
    Example test_lookup_found : lookup "x" [("x",  Arrow A A)] = Some (Arrow A A) := eq_refl.
    Example test_lookup_missing : lookup "x" [("y",  Arrow A A)] = None := eq_refl.
End TestScope.

(* To understand later.*)
Lemma type_neq_arrow : forall T U, T <> Arrow T U.
Proof.
  (* We use induction on the structure of T *)
  induction T; intros U H.

  - (* Case 1: T is Base s *)
    (* H : Base s = Arrow (Base s) U *)
    (* Here, the constructors 'Base' and 'Arrow' are different. *)
    (* discriminate works here! *)
    discriminate H.

  - (* Case 2: T is Arrow T1 T2 *)
    (* H : Arrow T1 T2 = Arrow (Arrow T1 T2) U *)
    (* The constructors are BOTH 'Arrow', so discriminate FAILS here. *)
    (* Instead, we use 'injection' to peel off the Arrow wrapper. *)
    injection H as H1 H2.
    
    (* H1 : T1 = Arrow T1 T2 *)
    (* Now we have a smaller loop! We can use the Induction Hypothesis (IHT1). *)
    apply IHT1 in H1.
    
    (* H1 is now False, so we are done. *)
    contradiction.
Qed.

  
Inductive has_type : Context -> term -> type -> Prop :=
| T_Var : forall Gamma x T, lookup x Gamma = Some T -> has_type Gamma (var x) T
| T_Abs : forall Gamma x T1 T2 t, has_type ((x, T1) :: Gamma) t T2 -> has_type Gamma (abs x T1 t) (Arrow T1 T2)
| T_App : forall Gamma t1 t2 T11 T12, has_type Gamma t1 (Arrow T11 T12) -> has_type Gamma t2 T11 -> has_type Gamma (app t1 t2) T12.

Section TestScope.
    Let A := Base "A".
    Let B := Base "B".
    Let C := Base "C".

    Example test_var : has_type [("x",  Arrow A A)] (var "x") (Arrow A A).
        Proof. repeat constructor. Qed.
   
    Let IdentityFunction := abs "y" A (var "y").
    Example test_id : has_type [] IdentityFunction (Arrow A A).
        Proof. repeat constructor. Qed.

    Let Second := abs "f" (Arrow A A) (abs "x" A ( app (var "f") (app (var "f") (var "x")))).
    Example second_typeable : has_type [] Second (Arrow (Arrow A A) (Arrow A A)).
        Proof. repeat (econstructor; try reflexivity). Qed.
    
    Let K := abs "x" A (abs "y" B (var "x")). 
    Example K_typeable : has_type [] K (Arrow A (Arrow B A)).
    Proof. repeat (econstructor; try reflexivity). Qed.
    
    Let Comp := abs "f" (Arrow B C) (
                abs "g" (Arrow A B) (
                abs "x" A (app (var "f") (app (var "g") (var "x") ))
        )).
    Example test_comp: has_type [] Comp (Arrow (Arrow B C) (Arrow (Arrow A B) (Arrow A C))).
    (* (Arrow (Arrow B C) (Arrow (Arrow A B) (Arrow A C))) *)
    Proof. repeat (econstructor; try reflexivity). Qed.
End TestScope.

Definition A := Base "A".
Definition B := Base "B".
Definition C := Base "C".

(*     
(* Types *)
Inductive type : Type :=
    | base : type
    | arrow : type -> type -> type.

(* Terms *)
Inductive term : Type :=
    | var : nat -> term
    | abs : type -> term -> term
    | app : term -> term -> term.

(* Type context *)
Definition context := nat -> option type.

Definition empty_context : context := fun _ => None.

Definition extend (ctx : context) (T : type) : context :=
    fun n => match n with
                        | 0 => Some T
                        | S n' => ctx n'
                        end.

(* Typing judgment *)
Inductive typing : context -> term -> type -> Prop :=
    | T_Var : forall ctx n T,
            ctx n = Some T ->
            typing ctx (var n) T
    | T_Abs : forall ctx t T U,
            typing (extend ctx T) t U ->
            typing ctx (abs T t) (arrow T U)
    | T_App : forall ctx t1 t2 T U,
            typing ctx t1 (arrow T U) ->
            typing ctx t2 T ->
            typing ctx (app t1 t2) U.

(* λf.λx.f(f x) has type (α → α) → α → α *)
Lemma example_typeable :
    typing empty_context
        (abs (arrow base base) (abs base (app (var 1) (app (var 1) (var 0)))))
        (arrow (arrow base base) (arrow base base)).
Proof.
    apply T_Abs.
    apply T_Abs.
    apply T_App with (T := base).
    - apply T_Var. simpl. reflexivity.
    - apply T_App with (T := base).
        + apply T_Var. simpl. reflexivity.
        + apply T_Var. simpl. reflexivity.
Qed. *)