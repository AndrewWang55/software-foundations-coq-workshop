Require Export SfLib.

Module AExp.

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.
  
  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.
  
Fixpoint aeval (e : aexp) : nat :=
  match e with
    | ANum n => n
    | APlus n m => (aeval n) + (aeval m)
    | AMinus n m => (aeval n) - (aeval m)
    | AMult n m => (aeval n) * (aeval m)
  end.


Fixpoint beval (e : bexp) : bool :=
  match e with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (e:aexp) : aexp := 
  match e with 
    | ANum n => e
    | APlus (ANum 0) e => (optimize_0plus e)
    | APlus n m => APlus (optimize_0plus n) (optimize_0plus m)
    | AMinus n m => AMinus (optimize_0plus n) (optimize_0plus m)
    | AMult n m => AMult (optimize_0plus n) (optimize_0plus m)
  end.
 Tactic Notation "aexp_cases" tactic(first) ident(c) :=
   first;
     [ Case_aux c "ANum" | Case_aux c "APlus"
       | Case_aux c "AMinus" | Case_aux c "AMult" ].

Theorem optimize_0plus_sound: forall e,
  aeval (optimize_0plus e) = aeval e.
  intro e.
  induction e.
  Case "Anum". simpl. reflexivity.
  Case "APlus".
    destruct e1.
    SCase "e1 = Anum n".
    destruct n.
      SSCase "e1 = 0".
      simpl. rewrite IHe2. reflexivity.
      SSCase "e1 = S n".
      simpl. rewrite IHe2. reflexivity.
  SCase "e1 = Aplus e1_1 e2_1".
    simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
    SCase "e1 = Aminus e1_1 e2_1".
    simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
    SCase "e1 = AMult e1_1 e2_1".
    simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMinus e1 e2".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "e = AMult e1 e2".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Theorem ev100 : ev 100.
Proof.
  repeat (apply ev_SS).
  apply ev_0.
Qed.

Theorem ev100' : ev 100.
Proof.
  repeat (apply ev_0). (* doesn't fail, applies ev_0 zero times *)
  repeat (apply ev_SS). apply ev_0. (* we can continue the proof *)
Qed.


Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof.  try reflexivity. Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intro P.
  intro Dokaz_Pa.
  apply Dokaz_Pa.
Qed.


Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intro n.
  destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intro n.
  destruct n ; simpl; reflexivity.
Qed.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "ANum" | Case_aux c "APlus"
      | Case_aux c "AMinus" | Case_aux c "AMult" ].


Theorem optimize_0plus_sound': forall e,
  aeval (optimize_0plus e) = aeval e.
  intros e.
  aexp_cases (induction e) Case;
    try (simpl; rewrite IHe1; (rewrite IHe2); reflexivity);
    try (Case "ANum"; reflexivity). 
    Case "APlus".
      aexp_cases (destruct e1) SCase;
        try (simpl; rewrite IHe2; simpl in IHe1; rewrite IHe1; reflexivity).
      SCase "ANum". destruct n;
        simpl; rewrite IHe2; reflexivity. 
Qed.

Fixpoint optimize_0bool (b : bexp) : bexp :=
  match b with
    | BTrue => b
    | BFalse => b
    | BEq n m => BEq (optimize_0plus n) (optimize_0plus m)
    | BLe n m => BLe (optimize_0plus n) (optimize_0plus m)
    | BNot _ => b
    | BAnd _ _ => b
  end.

Theorem optimize_0bool_sound : forall (b:bexp),
  beval (optimize_0bool b) = beval b.
  intro b.
  induction b;
    try (simpl; repeat (rewrite optimize_0plus_sound); reflexivity);
    try (reflexivity).
  Qed.

   
Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  where "e '||' n" := (aevalR e n) : type_scope.

End AExp.

Module Id.
  
  Inductive id : Set :=
    Id : nat -> id.

  Definition beq_id (X1 : id) (X2 : id) : bool :=
    match (X1, X2) with
      (Id x1, Id x2) => beq_nat x1 x2
    end.
 
  Theorem beq_id_refl : forall X,
    true = beq_id X X.
  Proof.
    intros X.
    destruct X.
    unfold beq_id.
    apply beq_nat_refl.
Qed.

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros i1 i2. intro H.
  destruct i1.
  destruct i2.
  unfold beq_id in H.
  apply beq_nat_eq in H.
  replace n.
  reflexivity.
Qed.

Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros i1 i2 H.
  unfold not.
  intro contra.
  rewrite contra  in H.
  rewrite <- beq_id_refl in H.
  inversion H.
Qed.

Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros i1 i2 H.
  destruct i1.
  destruct i2.
  unfold beq_id.
  apply beq_nat_false_iff.
  intro H1.
  rewrite H1 in H.
  unfold not in H.
  apply H.
  reflexivity.
Qed.

Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros i1 i2.
  destruct i1. destruct i2.
  unfold beq_id.
  apply beq_nat_sym.
Qed.

End Id.


Definition state := id -> nat.

Definition empty_state : state := 
  fun _ => 0.


Definition update (st : state) (X : id) (n : nat) : state :=
  fun (X1 : id) => if (beq_id X X1) then n else st X1.


Theorem update_eq : forall (s : state) (X : id) (n : nat), 
  (update s X n) X = n.
  intros s X n.
  unfold update.
  Check beq_id_refl.
  rewrite <- beq_id_refl.
  reflexivity.
Qed  .

Theorem update_neq : forall (s : state) (X1 X2 : id) (n : nat),
  beq_id X1 X2 = false ->
  (update s X1 n) X2 = s X2.
  intros s X1 X2 n.
  intros H.
  unfold update.
  rewrite H.
  reflexivity.
Qed.


Theorem update_shadow : forall x1 x2  k1 k2 (f : state),
   (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
  intros x1 x2 k1 k2 f.
  unfold update.
  destruct (beq_id k2 k1).
  reflexivity.
  reflexivity.
Qed.
  

Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
  intros x1 k1 k2 f.
  intros H.
  unfold update.
  remember (beq_id k1 k2).
  destruct b.
  apply beq_id_eq in Heqb.
  replace k2.
  symmetry.
  assumption.
  reflexivity.

Qed.  
  

Theorem update_permute : forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false ->
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  intros x1 x2 k1 k2 k3 f H.
  unfold update.
  remember (beq_id k1 k3).
  remember (beq_id k2 k3).
  destruct b.
  destruct b0.
  apply beq_id_eq in Heqb.
  apply beq_id_eq in Heqb0.
  rewrite Heqb in H.
  rewrite <- Heqb0 in H.
  rewrite <- beq_id_refl in H.
  inversion H.
  reflexivity.
  reflexivity.
Qed.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition X := Id 0.
Definition Y := Id 1.
Definition Z := Id 2.
  
Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
    | ANum n =>  n
    | AId id => st id
    | APlus e1 e2 => (aeval st e1) + (aeval st e2)
    | AMinus e1 e2 => (aeval st e1) - (aeval st e2)
    | AMult e1 e2 => (aeval st e1) * (aeval st e2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Eval compute in aeval (update empty_state X 100) (APlus (AId X) (ANum 1)).

Inductive com : Set :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Definition example_prog_1 := CSeq
        (CSkip)
        (CIf (BEq (AId X) (ANum 1))
           CSkip
           (CAss X (ANum 3))).

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).

Check SKIP ;
      IFB (BEq (AId X) (ANum 1))
        THEN
          SKIP
        ELSE
          X ::= ANum 3 FI.

Definition fact_in_coq : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition loop : com :=
  WHILE BTrue DO
     SKIP
  END.

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z) ;
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X ;
  Y ::= ANum 1;
  fact_loop.

Theorem imp_example : forall P:Prop, P -> P.
  intros P.
  intros HP.
  apply HP.
Qed.


(* 
Fixpoint ceval_fun (st : state) (c : com) : state :=
  match c with
    | SKIP => st
    | l ::= a1 => update st l (aeval st a1)
    | c1 ; c2 =>  let st' :=  (ceval_fun st c1) in
                  (ceval_fun st' c2)
    | IFB b THEN c1 ELSE c2 FI => if beval st b then ceval_fun st c1 else ceval_fun st c2
    | WHILE b DO c1 END => if (beval st b) then
      let st' := (ceval_fun st c1) in ceval_fun st' c
       else st
  end.
  *)
        

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall (st : state),
      SKIP / st || st
  | E_Ass : forall (st : state) (a : aexp) (n : nat) (X : id),
       aeval st a = n ->  (X ::= a) / st || (update st X n)
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
       (c1 / st || st') -> (c2 / st' || st'') -> (c1 ; c2) / st || st''
  | E_IfTrue : forall (st st': state) (c1 c2 : com) (b : bexp),
       beval st b = true -> c1 / st || st' -> (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st': state) (c1 c2 : com) (b : bexp),
       beval st b = false -> c2 / st || st' -> (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (st : state) (c1 : com) (b : bexp),
       beval st b = false -> (WHILE b DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'': state) (c1 : com) (b : bexp),
       beval st b = true -> 
       c1 / st || st' ->
       (WHILE b DO c1 END) / st' || st'' -> 
       (WHILE b DO c1 END) / st || st''
  where "c1 '/' st '||' st'" := (ceval c1 st st').

Example ceval_example1 :
  ( X ::= ANum 2 ;
    IFB BLe (AId X) (ANum 1)
      THEN Y ::= ANum 3
      ELSE Z ::= ANum 4
    FI ) / empty_state || (update (update empty_state X 2) Z 4).
  apply E_Seq with (st' := (update empty_state X 2)).
  apply E_Ass.
  reflexivity.
  
  apply E_IfFalse.
  reflexivity.
  apply E_Ass.
  reflexivity.
Qed.

