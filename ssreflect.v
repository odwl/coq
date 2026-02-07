
From Coq Require Import ssreflect ssrbool ssrfun.

Section Tauto.
Variables A B C : Prop.

Lemma tauto1 : A -> A.
Proof.
    (* now intro. *)
    (* move=> ?. exact: a. *)
    (* by move=>?. *)
    (* by []. *)
    exact: id.
Qed.

Lemma tauto2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
move=> ab bc. exact: (bc \o ab).
(* move=> ab bc a. exact: bc (ab a).
move=> ab bc a. by bc (ab a). *)
Qed.

Lemma ploc: A->A.


(* Lemma tauto3 : A /\ B <-> B /\ A.
Proof.
  (* split. intro. case H => u v.  *)
  split; by case=> ? ?.
  split; by move=> [a b].
  split; exact: (fun '(conj a b) => conj b a).

Qed.
End Tauto. *)
