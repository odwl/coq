Require Import Classical.
  
  (* Redefine A and B as simple Propositions *)
  Parameters A B : Prop. 
  

  (* Now Coq knows this is a logical formula, not a function type *)
  (* Definition peirce_fun : ((A -> B) -> A) -> A :=
    fun (h : (A -> B) -> A) => 
      NNPP (fun (notA : ~A) => 
        notA (h (fun (a : A) => 
          match notA a with end
        ))
      ). *)





(* 

Parameter X Y : Set.
Parameter A B : X -> Prop.
Parameter R : X -> Y -> Prop.

Lemma ex1 : (forall x, A x /\ B x) <-> (forall x, A x) /\ (forall x, B x).
Proof.
  split. intro f.  *)
