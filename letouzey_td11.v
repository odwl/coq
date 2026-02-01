Parameters A B C : Prop.

Lemma ex11a : A -> A.
Proof.
  (* intros. assumption. *)
  exact(fun a => a).
Qed.

Lemma ex11b: (A -> B) /\ (B -> C) -> (A -> C).
Proof.
    intros [AB BC] a. exact (BC (AB a)).
    (* intros [AB BC]. exact(fun a => BC (AB a)). *)
Qed.

Lemma ex12: (A /\ B -> C) <-> (A -> B -> C).
Proof.
    split.
    - intros f a b. exact(f (conj a b)).
    - intros f [a b]. exact(f a b).
Qed.

Lemma ex13a: (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
    split.
    - intros [[a b] c]. exact(conj a (conj b c)).
    - intros [a [b c]]. exact(conj (conj a b) c).
Qed.

Lemma ex13b: A /\ B <-> B /\ A.
Proof.
    assert (gen: forall P Q : Prop, P /\Q -> Q/\ P). 
    intros ? ? [p q]. exact(conj q p).

    split; apply gen.
Qed.
    (* intros ? ? [|]; [right | left]; assumption.

    split.
    - intros [a b]. exact (conj b a).
    - intros [b a]. exact (conj a b). *)

Lemma ex13c: (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
    split. 
    - intros [[a|b]|c]; [left|right;left|right;right]; assumption. 
    - intros [a|[b|c]]; [left;left|left;right|right]; assumption.
Qed.

Lemma ex13d: A \/ B <-> B \/ A.
Proof.
    assert (gen: forall P Q : Prop, P \/ Q -> Q \/ P). 
    intros ? ? [|]; [right | left]; assumption.

    split; apply gen. 
Qed.
    (* destruct 1; [right | left]; assumption. *)
    (* intros ? ? H. destruct H; [right | left]; assumption. *)
    (* intros P Q [p | q]; [right | left]; assumption. *)
    (* split; destruct 1; [right|left|right|left]; assumption. *)
    (* split; intros [|]; [right | left | right | left]; assumption. *)
    (* - intros [a | b]. right.  assumption. left. assumption.
     split; [intros [a | b] | intros [b | a]]; [right | left | right | left]; assumption.
    - intros [a | b]. right.  assumption. left. assumption.
    - intros [b | a]. right. assumption. left. assumption. *)

Lemma ex14a: A /\ True <-> A.
Proof.
    split.
    - apply proj1. 
    - exact(fun a => conj a I).
Qed.
(* -intros a. exact(conj a I). *)
(* - intros [a _]. assumption.  *)

Lemma ex14b: A /\ False <-> False.
Proof.
    split.
    - apply proj2.
    - exact (False_ind _).
Qed.
    (* - exact(fun f => match f with end). *)

Lemma ex14c: A \/ False <-> A.
Proof.
    split. 
    - intros [a | f]. assumption. exact (False_ind _ f).
    -intro a. left. assumption.
Qed.

Lemma ex14d: A \/ True <-> True.
Proof.
    split; intros _; [|right]; exact I.
Qed.

Lemma ex15a: A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
    split.
    - intros [?[?|?]]; [left|right]; split; assumption. 
    - intros [[??]|[??]]; split; [|left| |right]; assumption.
Qed.

Lemma ex15b: (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
Proof.
    split.
    - intros [[?|?]?]; [left|right]; split; assumption.
    - intros [[??]|[??]]; split; [left| |right|]; assumption.
Qed.

Parameters X Y : Set.
Parameters D E : X -> Prop.
Lemma ex16_mystery: (forall x, D x /\ E x) <-> (forall x, D x) /\ (forall x, E x).
Proof.
    split.
    - intro f. split; intro x; destruct (f x); assumption.
    - intros [f g] x. exact (conj (f x) (g x)).
Qed.

(* - intros f. 
     pose (left_part := fun x => proj1 (f x)).
     pose (right_part := fun x => proj2 (f x)).
     exact (conj left_part right_part). *)
    (* - intros f; split; intro x; destruct (f x); assumption. *)
    (* - intros f; split. exact(fun x => proj1 (f x)). exact(fun x => proj2 (f x)). *)
    (* - exact(fun '(conj f g) x => conj (f x) (g x)). *)

Lemma ex16b: (exists x, D x \/ E x) <-> (exists x, D x) \/ (exists x, E x).
Proof.
    split.
    - intros [x[?|?]]; [left|right]; exists x; assumption.
    - intros [[x?]|[x?]]; exists x; [left|right]; assumption.
Qed.

Lemma ex17a: (A -> (B /\ C)) <-> ((A -> B) /\ (A -> C)).
Proof.
    split. 
    - intros f. split; intro a; destruct (f a); assumption.  
    - intros [f g] a; exact ( conj (f a) (g a)). 
