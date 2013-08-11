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
