From Stdlib Require Import Logic.Classical.

Section Peirce_Fix.
  Variables A B : Prop.

  Definition peirce_fun : ((A -> B) -> A) -> A :=
    fun (h : (A -> B) -> A) => 
      @NNPP A (fun (notA : ~A) => 
        notA (h (fun (a : A) => 
          match notA a return B with end
        ))
      ).
End Peirce_Fix.

Require Import Classical.


Parameters A B : Prop.
Lemma peirce : ((A -> B) -> A) -> A.
Proof.
intros f. apply NNPP. intros na. apply na. apply f. intro a.
 contradiction.
Qed.

Lemma peirce2 : ((A -> B) -> A) -> A.

  Proof.
    intros h.        
    apply NNPP. 
    
    exact(
      fun notA => 
        let AB := (fun a => @absurd A B a notA) in 
        notA (h AB)). 
  
      
      (* 
    intro notA.                  
    assert (AB : A -> B). intro a. contradiction.
    assert (A). exact(h AB).
    contradiction. *)
    
    (* apply notA.                  (* We need a contradiction... *)
(*       exact (fun a : A => @absurd A B a notA). *)
    exact(h AB).
    
(*     pose (AB := (fun a : A => @absurd A B a notA) : A->B). *)

    apply h.                     (* ...which we get from h... *)
(*     exact (fun a : A => @absurd A B a notA). *)
(*     (exact (fun a => False_ind B (notA a)). *)
    intro a.                     (* ...if we can prove A -> B. *)
(*     exact (@absurd A B a notA). *)
    apply False_ind.             (* To prove B, we use Ex Falso... *)
(*     exact (notA a).*)
    apply notA.                  (* ...from the contradiction of A and ~A *) *
    exact a. *)
  Qed. 
  
Lemma peirce3 : ((A -> B) -> A) -> A.
Proof.
  intros h.        (* We take the hypothesis h *)
  apply NNPP.                  (* We switch to classical logic *)
  exact (fun notA => notA (h (fun a => False_ind B (notA a)))).
Qed.

Section For.


End For.