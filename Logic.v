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
Proof.
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
Qed.
  
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
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HEPQ HEQR.
  inversion  HEPQ as [HPQ HQP].
  inversion HEQR as [HQR HRQ].
  split.
  intros HP. apply HQR. apply HPQ. apply HP.
  intros HR. apply HQP. apply HRQ. apply HR.
Qed.

Definition beautiful_iff_gorgeous : forall n, beautiful n <-> gorgeous n :=
  fun (n:nat) =>
    conj (beautiful n -> gorgeous n) (gorgeous n -> beautiful n)
    (beautiful__gorgeous n) 
    (gorgeous__beautiful n).


Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [ HP | HQ ].
  apply or_intror.
  apply HP.
  apply or_introl.
  apply HQ.
Qed.


Theorem or_commut' : forall P Q : Prop,
  P \/ Q -> Q \/ P.
  intros P Q H.
  inversion H as [HP | HQ].
  right.
  apply HP.
  left.
  apply  HQ.
Qed.
  

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R H.
  inversion H as [ HP | [ HQ HR ] ].
  split.
  left. apply HP.
  left. apply HP.
  split.
  right.  apply HQ.
  right. apply HR.
Qed.


Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [HPQ HPR].
  inversion HPQ as [ HP | HQ ].
  left. apply HP.
  inversion HPR as [ HP | HR ].
  left. apply HP.
  right.
  apply conj.
  apply HQ.
  apply HR.
Qed.

Print andb.

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  split.
  destruct b.
  reflexivity.
  simpl in H.
  inversion H.
  destruct c.
  reflexivity.
  destruct b.
  inversion H.
  inversion H.

Qed.


Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity.
Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
  simpl in H.
  right. apply H.
  left. reflexivity.

Qed.  

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c. intro H.
  destruct b.
  left. reflexivity.
  destruct c. right. reflexivity.
  inversion H.
Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b.
  inversion H.
  split. reflexivity.
  destruct c.
  inversion H.
  reflexivity.
Qed.

Inductive False : Prop := .

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros.
  inversion H.
Qed.  


Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros H.
  simpl in H.
  inversion H.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.

Inductive True : Prop :=
  tt : True.
Check tt.

Theorem xx : False \/ True.
  right.
  apply tt.
Qed.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.


Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intro contra.
  inversion contra.
Qed.  


Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros p q contra.
  inversion contra as [HP HNP].
  unfold not in HNP.  (* Dragan: novo *)
  apply HNP in HP.
  inversion HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P HP.
  unfold not.
  intro H.
  apply H in HP.
  inversion HP.
Qed.


Theorem contrapositive : forall P Q : Prop, 
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  intro HNQ.
  unfold not.
  intro HP.
  apply H in HP.
  apply contradiction_implies_anything with (P:=Q).
  split.
  apply HP.
  apply HNQ.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not.
  intros P contra.
  apply contradiction_implies_anything with (P:=P).
  apply contra.
Qed.

Theorem five_not_even :
  ~ ev 5.
Proof.
  unfold not.
  intro contra.
  inversion contra.
  inversion H0.
  inversion H2.
Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  intros n E.
  induction E  as [ | n' E' ].
  unfold not.
  intros contra. inversion contra.
  unfold not.
  intros ES.
  inversion ES.
  unfold not in IHE'.
  apply IHE' in H0.
  inversion H0.
Qed.

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition classic := forall P:Prop,
  ~~P -> P.

Definition excluded_middle := forall P:Prop,
  P \/ ~P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q)  ->  (~P \/ Q).

Theorem peirce_eq_excluded_middle : peirce <-> excluded_middle.
  split.
  unfold peirce.
  unfold excluded_middle.
  intros peirceH.
  intros P.
  apply peirceH with (Q:=False).
  intros H.
  right.
  unfold not.
  intro HP.
  apply H.
  left.
  apply HP.
  unfold excluded_middle.
  unfold peirce.
  
  intros excluded_middleH.
  intros P Q H.
  
  assert (P \/ ~P).
  apply excluded_middleH.
  inversion H0.
  apply H1.
  apply H.
  intros HP.
  unfold not in H1.
  apply H1 in HP.
  inversion HP.
Qed.


Notation "x <> y" := (~ (x = y)) : type_scope.




Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
  Proof.
    intros b H.
    destruct b.
    reflexivity.
    apply ex_falso_quodlibet.
    unfold not in H.
    apply H.
    reflexivity.
Qed.

Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof.
  intros n.
  induction n.
  intros n' H.
  destruct n' as [| n''].
  simpl.
  apply ex_falso_quodlibet.
  apply H.
  reflexivity.
  simpl.
  reflexivity.
  intros n' H.
  destruct n' as [| n''].
  simpl.
  reflexivity.
  simpl.
  apply IHn.
  unfold not.
  intros H'.
  unfold not in H.
  apply H.
  rewrite H'.
  reflexivity.
Qed.  

Print beq_nat.

Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  intro n.
  induction n as [| n' H].
  intros m H0.
  destruct m as [| m'].
  unfold not.
  simpl in H0.
  inversion H0.
  unfold not.
  intro contra.
  inversion contra.
  intros m H'.
  destruct m as [| m'].
  unfold not.
  intro contra.
  inversion contra.
  unfold not.
  intro H''.
  simpl in H'.
  apply H in H'.
  unfold not in H'.
  apply H'.
  inversion H''.
  reflexivity.
Qed.


Inductive ex (A:Type) (P: A -> Prop) : Prop :=
  ex_intro : forall (witness : A), P witness -> ex A P.


Definition some_nat_is_even : Prop :=
  ex nat ev.

Definition snie : some_nat_is_even := 
   ex_intro nat ev 2  (ev_SS 0 (ev_0)).

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.  

Check exists x, ev x.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness := 2).
  reflexivity.
Qed.

Example exists_example_1' : exists n,
  n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.
Qed.


Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).  
  rewrite Hm.
  reflexivity.
Qed.  


Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intro E.
  inversion E as [ x Hx ].
  apply Hx.
  apply H.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros excl_mid.
  intros X P H.
  intros x.
  assert ( P x \/ ~ P x).
  apply excl_mid.
  inversion H0.
  apply H1.
  apply ex_falso_quodlibet.
  unfold not in H.
  apply H.
  unfold not in H1.
  exists x.
  apply H1.
Qed.