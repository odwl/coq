Require Import MyProject.Common.
From Stdlib Require Import Classical_Prop.

Section Ex2.
Parameters X Y : Type.
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
Parameters U V : Prop.

Inductive Heart (A B : Prop) : Prop :=
  | heart_intro : A -> B -> Heart A B.
  
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


Section Ex4.
Variable A B : Prop.
Variable X : Type.

Lemma double_neg : ~~A -> A.
Proof.
    intro nna. exact(NNPP A nna).
    (* now apply NNPP.  *)
Qed.

Lemma tiers_excl : A \/ ~A.
Proof.
    exact( classic A).
Qed.    

Lemma not_tau2: ~A <-> (A -> False).
Proof.
    reflexivity.
Qed.

Lemma not_tau: ~True <-> False.
Proof. 
    easy. 
Qed.

Lemma not_bot: ~False <-> True.
Proof. 
    split; easy. 
Qed.

(* tricky side *)
Lemma de_morgan_and : (~A \/ ~B) <-> ~(A /\ B).
Proof. 
    split. 
    - now intros [?|?][? ?].
    - intros nab; destruct (classic A).
        + right; now contradict nab.
        + now left.
Qed.

Lemma de_morgan_or : (~A /\ ~B) <-> ~(A \/ B).
Proof.
    split.
    - now intros[? ?] [?|?].
    - intros nab. split; contradict nab; [now left | now right].
Qed.

Parameter P : X -> Prop.
Lemma not_forall_equiv : ~ (forall x : X, P x) <-> exists x : X, ~ P x.
Proof.
split. 
- intros nf. apply NNPP. contradict nf. intro x. apply NNPP. exact(fun np => nf (x ; np)).
(* contradict nf. exact(x ; nf). *)
(* now exists x.  *)
- intros [x np] fp. exact(np (fp x)).
 (* intros [x np] fp. now contradict np. *)
Qed.

Lemma not_forall_equiv2 : ~ (forall x : X, P x) <-> exists x : X, ~ P x.
Proof.
split. 
- intros nf. apply NNPP. contradict nf. intro x. check (P x) as px npx. 
    + assumption.
    + case (nf (x ; npx)).  
- intros [x np] fp. exact(np (fp x)).
Qed.

Lemma not_exists_equiv : ~ (exists x : X, P x) <-> forall x : X, ~ P x.
Proof.
split.
- intros ne x px. exact(ne (x;px)).
- intros fnp [x px]. exact(fnp x px).
Qed.

Lemma imp_equiv : (A -> B) <-> (~A \/ B).
Proof.
    split. 
    - intros ab. check A as a na.
        + exact(R (ab a)).
        + exact(L na).
    - now intros [?|?] ?. 
Qed.

Lemma imp_equiv2 : (A -> B) <-> (~A \/ B).
Proof.
    split. 
    - intros ab. exact(Case (fun a:A => R (ab a))(fun na => L na)).
    - now intros [?|?] ?. 
Qed.
End Ex4.

