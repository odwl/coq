Parameters X Y : Prop.
Parameters A : X -> Y -> Prop.

Lemma ex21a :  (forall x, forall y, A x y) <-> (forall y, forall x, A x y).
Proof.
    split; intros f a b; exact (f b a).
Qed.