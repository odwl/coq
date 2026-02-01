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
Qed.
