(* Simply Typed Lambda Calculus *)

Require Import String List.
Import ListNotations. Open Scope string_scope.

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

Inductive has_type : Context -> term -> type -> Prop :=
  | T_Var : forall Gamma x T, lookup x Gamma = Some T -> has_type Gamma (var x) T
  | T_Abs : forall Gamma x T1 T2 t, has_type ((x, T1) :: Gamma) t T2 -> has_type Gamma (abs x T1 t) (Arrow T1 T2)
  | T_App : forall Gamma t1 t2 T11 T12, has_type Gamma t1 (Arrow T11 T12) -> has_type Gamma t2 T11 -> has_type Gamma (app t1 t2) T12.

Definition A := Base "A".
Definition B := Base "B".
Definition C := Base "C".

Definition my_context := [("x", A)].
Lemma has_type_test : has_type my_context (var "x") A.
Proof.
    unfold my_context.
    apply T_Var. 
    reflexivity.
Qed.

Definition IdentityFunction := abs "y" A (var "y").
Lemma identity : has_type [] IdentityFunction (Arrow A A).
Proof.
    unfold IdentityFunction.
    apply T_Abs.
    apply T_Var.
    reflexivity.

Definition Second := abs "f" (Arrow A A) (abs "x" A ( app (var "f") (app (var "f") (var "x")))).
Lemma second_typeable : has_type [] Second (Arrow (Arrow A A) (Arrow A A)).
Proof.
  apply T_Abs.
  apply T_Abs.
  eapply T_App.
  - apply T_Var. reflexivity.
  - eapply T_App; apply T_Var. reflexivity.

Definition K := abs "x" A (abs "y" B (var "x")). 
Lemma K_typeable : has_type [] K (Arrow A (Arrow B A)).
Proof.
    apply T_Abs. apply T_Abs. apply T_Var. auto.
Qed.

Definition Comp := abs "f" (Arrow B C) (
    abs "g" (Arrow A B) (
        abs "x" A (
        app (var "f") (
            app (var "g") (var "x")
        )
        )
        )
        ).
Lemma Comp_typeable: has_type [] Comp (Arrow (Arrow B C) (Arrow (Arrow A B) (Arrow A C))).
Proof.
    apply T_Abs. apply T_Abs. apply T_Abs. eapply T_App. 
    - now apply T_Var. 
    -  eapply T_App; now apply T_Var. 
Qed.


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