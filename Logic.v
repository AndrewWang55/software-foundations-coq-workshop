Require Export "Prop".

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Check conj (1=2) (3=4).

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem and_example :
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  apply b_0.
  apply b_3.
Qed.

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
  apply ev_0.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros.
  inversion H as [HP HQ].
  apply HP.
Qed.

Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros.
  inversion H as [HP HQ].
  apply HQ.
Qed.


Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H as [HP HQ].
  split.
  apply HQ.
  apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.
