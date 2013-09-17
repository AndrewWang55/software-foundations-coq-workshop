Require Export Imp.

Definition Assertion := state -> Prop. 

  
Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.


Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
    c / st || st' ->
    P st ->
    Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(*

   1) {{True}} c {{X = 5}}

   2) {{X = m}} c {{X = m + 5)}}

   3) {{X <= Y}} c {{Y <= X}}

   4) {{True}} c {{False}}

   5) {{X = m}} 
      c
      {{Y = real_fact m}}.

   6) {{True}} 
      c 
      {{(Z * Z) <= m ∧ ~ (((S Z) * (S Z)) <= m)}} 
*)

(*

   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}

   4) {{X = 2 ∧ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE True DO SKIP END {{False}}

   8) {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}

   9) {{X = 1}}
      WHILE X <> 0 DO X ::= X + 1 END
      {{X = 100}}
*)

Theorem ex_loop_quodlibet : forall P Q, hoare_triple P loop Q.
  intros p q.
  unfold hoare_triple.
  intros.
  apply ex_falso_quodlibet.
  apply loop_doesnt_stop with st.
  exists st'.
  assumption.
Qed. 

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
  intros P Q c H.
  unfold hoare_triple.
  intros st st' Hc HP.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
  intros P Q c H st st' HC HP.
  apply H in HP. contradiction.
Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).


Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
  intros Q X a.
  unfold hoare_triple.
  intros st st' Hc HQ.
  inversion Hc.
  unfold assn_sub in HQ.
  subst.
  assumption.
Qed.



Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn.
Qed.  

Theorem asgn_example_1 :
{{ (fun st => (st X) <= 5)  [ X |-> (APlus (AId X) (ANum 1)) ] }}
X ::=  (APlus (AId X) (ANum 1))
{{ (fun st => (st X) <= 5)  }}.
  apply hoare_asgn.
Qed.


Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c HP' HPP'.
  intros st st' Hc HP.
  unfold hoare_triple in HP'.
  apply HP' with (st := st).
  assumption.
  apply HPP'.
  assumption.

Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
  intros P Q Q' H HQ' HQ'Q.
  intros z w Hc HP.
  unfold hoare_triple in HQ'.
  apply HQ'Q.
  apply HQ' with (st := z); assumption.
Qed.
