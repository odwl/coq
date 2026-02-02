Section Ex2.
Parameters X Y : Prop.
Parameters A : X -> Y -> Prop.

Lemma ex21a :  (forall x, forall y, A x y) <-> (forall y, forall x, A x y).
Proof.
    split; intros f a b; exact (f b a).
Qed.

Lemma ex21b :  (exists x, exists y, A x y) <-> (exists y, exists x, A x y).
Proof.
    split; intros [a[b ?]]; exists b, a; assumption.
Qed.

Lemma ex22a : (exists x, forall y, A x y) -> (forall y, exists x, A x y).
Proof.
    intros [x f]y. exists x. exact (f y).
Qed.
End Ex2.


Section Ex3.

Inductive Heart (A B : Prop) : Prop :=
  | heart_intro : A -> B -> Heart A B.
  
  
Parameters U V : Prop.
Lemma heart_and : (Heart U V) <-> (U /\ V).
Proof. 
split; intros [??]; now constructor.
Qed. 

Inductive Diamond (A B : Prop) : Prop :=
    | left_intro : A -> Diamond A B
    | right_intro : B -> Diamond A B.

Lemma diamond_or : (Diamond U V) <-> (U \/ V).
Proof.
    split; intros [?|?]; first [ now left | now right ].
Qed.

(* This is actually using -> so just a wrapper. *)
Inductive Club (A B : Prop) : Prop := 
    | club_intro : (A -> B) -> Club A B.

Lemma club_imp : (Club U V) <-> (U -> V).
Proof.
    split.
    - now intros [?]. 
    - intros. now constructor.
Qed.

Inductive Tau : Prop :=
    | J : Tau.

Inductive Bot : Prop := .

Lemma tau_true : Tau <-> True.
Proof.
    split; intro; constructor.
Qed.

Lemma bot_false : Bot <-> False.
Proof.
    split; now intro.
Qed.

Variable X : Type.
Inductive MyExists (P : X -> Prop) : Prop :=
  | my_ex_intro x (proof : P x) : MyExists P.

Variable P : X -> Prop.
Lemma exists_equiv : MyExists P <-> exists x, P x.    
Proof.
    split; intros [x?]; now exists x. 
Qed.

(* This is actually using -> so just a wrapper. *)
Inductive MyForall (P : X -> Prop) : Prop :=
    | my_forall_intro (proof : forall x, P x) : MyForall P.

Lemma forall_equiv : MyForall P <-> (forall x, P x).
Proof.
    split. 
    - now intros [?]. 
    - intro. now constructor.
Qed.
End Ex3.
