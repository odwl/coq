Require Import Program.

Class Functor (F : Type -> Type) := {
  fmap : forall {A B : Type}, (A -> B) -> F A -> F B;
  functor_id : forall {A : Type} (fa : F A), 
        fmap (@id A) fa = fa;
  functor_comp : forall {A B C: Type} (f: B -> C) (g: A -> B) (fa: F A),
        fmap (fun x => f (g x)) fa = fmap f (fmap g fa)
}.

(* Notice 'Program Instance' instead of just 'Instance' *)
Program Instance OptionFunctor : Functor option := {
  fmap := fun {A B} (f : A -> B) (x : option A) =>
    match x with
    | Some val => Some (f val)
    | None => None
    end
}.

(* Now we use 'Next Obligation' to prove the missing laws *)
Next Obligation.
  (* Proof of Identity: fmap id x = x *)
  destruct fa; reflexivity.
Defined.

Next Obligation.
(* Proof of Composition: fmap (g . f) x = fmap g (fmap f x) *)
  destruct fa; reflexivity.
Defined.

