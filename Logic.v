Require Export "Prop".

Check nat->Prop.

Inductive and (P Q:Prop) : Prop :=
  conj : P -> Q -> and P Q.

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem and_example :
  (beautiful 0) /\ (beautiful 3).
  apply conj.
  apply b_0.
  apply b_3.
Qed.

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
  apply ev_0.
  apply ev_4.
Qed.


Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP.
Qed.


Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
  apply HQ.
  apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.


Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R:Prop) (HPQ:P/\Q) (HQR:Q/\R) => 
     conj P R (proj1  P Q HPQ) (proj2  Q R HQR).

Definition iff (P Q:Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity) : type_scope.


Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
  intros P Q HPQ HP.
  inversion HPQ as [HA HB].
  apply HA in HP.
  apply HP.
Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H as [HA HB].
  split.
  apply HB.
  apply HA.
  
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  intro HP.
  apply HP.
  intro HP.
  apply HP.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P -> R).
Proof.
  intros P Q R HPQ HQR.
  intros HP.
  inversion HPQ.
  inversion HQR.
  apply H1.
  apply H.
  apply HP.
Qed.

Definition beautiful_iff_gorgeous : forall n, beautiful n <-> gorgeous n :=
  fun (n:nat) =>
    conj (beautiful n -> gorgeous n) (gorgeous n -> beautiful n)
    (beautiful__gorgeous n) 
    (gorgeous__beautiful n).