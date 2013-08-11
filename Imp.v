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


Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].


Theorem ceval_deterministic :  forall c st st1 st2 ,
  c / st || st1 ->
  c / st || st2 ->
  st1 = st2.
  intros c st st1 st2.
  intros E1.
  generalize dependent st2.
  induction E1.
    intros. inversion H; reflexivity.
    intros. inversion H0. subst. reflexivity.
    intros st2. intros H.
    inversion H.
    subst.
    apply IHE1_1 in H2.
    rewrite <- H2 in H5.
    apply IHE1_2 in H5.
    subst. reflexivity.
    intros.
    inversion H0.
    apply IHE1 in H7.
    
    assumption.
    rewrite H in H6.
    inversion H6.
    
    intros.
    inversion H0.
    rewrite H in H6.
    inversion H6.
    apply IHE1 in H7.
    assumption.
    intros.
    inversion H0.
    reflexivity.
    rewrite H in H3.
    inversion H3.
    intros.
    inversion H0.
    subst.
    rewrite H in H5.
    inversion H5.
    apply IHE1_1 in H4.
    rewrite <- H4 in H7.
    apply IHE1_2 in H7.
    assumption.
Qed.


Print fact_body. Print fact_loop. Print fact_com.


Theorem loop_doesnt_stop : forall s,
  ~ exists s', loop / s || s'.
  intro s.
  intro contra.
  unfold loop in contra.
  inversion contra.
  remember (WHILE BTrue DO SKIP END) as loop.
  induction H; try (inversion Heqloop).
  subst. inversion H.
  subst.
  apply IHceval2. reflexivity.
  exists st''.
  apply H1.
Qed.  

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

Definition fact_invariant (x : nat) (st : state) :=
  (st Y) * (real_fact (st Z)) = real_fact x.

Theorem fact_body_preserves_invariant : forall x st st',
   fact_invariant x st ->
   (st Z) <> 0 ->
   fact_body / st || st' ->
   fact_invariant x st'.
  unfold fact_invariant, fact_body.
  intros x st st' Hm HZnz He.
  inversion He. subst. clear He.
  inversion H1. subst. clear H1.
  inversion H4. subst. clear H4.
  simpl.
  unfold update. simpl.
   rewrite <- Hm.
   destruct (st Z). apply ex_falso_quodlibet. apply HZnz. reflexivity.
   replace (S n - 1) with n by omega.
   rewrite <- mult_assoc.
   simpl. reflexivity.
Qed.

Theorem fact_loop_preserves_invariant : forall st st' x,
   fact_invariant x st ->
   fact_loop / st || st' ->
   fact_invariant x st'.
  intros st st' x H Hce.
  remember fact_loop as c.
  induction Hce; inversion Heqc.
  assumption.
  assert (fact_invariant x st').
  apply fact_body_preserves_invariant with st.
  assumption.
  subst.
  simpl in H0.
  destruct (st Z).
  simpl in H0.
  inversion H0.
  omega.
  subst.
  assumption.
  apply IHHce2.
  assumption.
  assumption.
  Qed.


Theorem guard_false_after_loop: forall b c st st',
     (WHILE b DO c END) / st || st' ->
     beval st' b = false.
  intros b c st st' Hce.
  remember (WHILE b DO c END) as cloop.
  induction Hce; inversion Heqcloop.
  subst. assumption. apply IHHce2. assumption.
Qed.

Theorem fact_com_correct : forall st st' x,
   st X = x ->
   fact_com / st || st' ->
   (st' Y) = real_fact x.
  intros st st' x  Hx Hce.
  unfold fact_com  in Hce.
  inversion Hce. subst. clear Hce.
  inversion H1. subst. clear H1.
  inversion H4. subst. clear H4. 
  inversion H1. subst. clear H1.
  rename st' into st''.
  simpl in H5.
  remember (update (update st Z (st X)) Y 1) as st'.
  assert (fact_invariant (st X)  st').
  subst. unfold fact_invariant, update. simpl. omega.
  assert (fact_invariant (st X) st'').
  apply fact_loop_preserves_invariant with st'.
  assumption. assumption.
  unfold fact_invariant in H0.
  apply guard_false_after_loop in H5.
  simpl in H5.
  destruct (st'' Z).
  simpl in H0.
  omega.
  simpl in H5.
  inversion H5.
Qed.

Inductive  instr : Set :=
  | SPush : nat -> instr
  | SLoad : id -> instr
  | SPlus : instr
  | SMinus : instr
  | SMult : instr.


(*
Fixpoint s_execute' (st : state) (stack : list nat) (prog : list instr) : list nat :=
  match prog with
    | [] => stack
    | SPush n :: prog' => s_execute st (n :: stack) prog'
    | SLoad var :: prog' => s_execute st ((st var) :: stack) prog'
    | SPlus :: prog' => match stack with
                          | n :: m :: stack' =>  s_execute st ((m + n) :: stack') prog'
                          | _  =>  s_execute st stack prog'
                        end
    | SMinus :: prog' => match stack with
                          | n :: m :: stack' =>  s_execute st ((m - n) :: stack') prog'
                          | _  =>  s_execute st stack prog'
                        end
    | SMult :: prog' => match stack with
                          | n :: m :: stack' =>  s_execute st ((m * n) :: stack') prog'
                          | _  =>  s_execute st stack prog'
                        end
  end.
*)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list instr)
                 : list nat :=
let newstack := 
  match prog with
    | [] => stack
    | (SPush n)::_ => n::stack
    | (SLoad id)::_ => (st id)::stack
    | SPlus::_  => match stack with
                        | n::(m::rest) => (m+n)::rest
                        | _ => stack
                      end
    | SMinus::_  => match stack with
                         | n::m::rest => (m-n)::rest
                         | _ => stack
                       end
    | SMult::_  => match stack with
                        | n::m::rest => (m*n)::rest
                        | _ => stack
                      end
  end in
  match prog with
    | [] => stack
    | instr::rest => s_execute st newstack rest
  end.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5, SPush 3, SPush 1, SMinus] = [2,  5].
reflexivity.
Qed.

Example s_execute2 :
     s_execute (update empty_state X 3) [3, 4]
       [SPush 4, SLoad X, SMult, SPlus]
   = [15,  4].
reflexivity.
Qed.

Fixpoint s_compile (e : aexp) : list instr :=
  match e with
    | ANum n => [ SPush n ]
    | AId ident => [ SLoad ident ]
    | APlus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [ SPlus ]
    | AMinus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [ SMinus ]
    | AMult e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [ SMult ]
  end.


Lemma s_execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
  intros st p1.
  induction p1.
  intros; reflexivity.
  intros.
  simpl.
  apply IHp1.
Qed. 


Theorem s_compile_correct_gen : forall (e : aexp) (st : state) (stack : list nat),
   s_execute st stack (s_compile e) = aeval st e :: stack.
  intros e st.
  induction e; try (intros; reflexivity);
  try (
  intros;
  simpl;
  rewrite s_execute_app;
  rewrite s_execute_app;
  rewrite IHe1;
  rewrite IHe2;
  reflexivity
  ).
Qed.

Theorem s_compile_correct : forall (e : aexp) (st : state),
   s_execute st [] (s_compile e) = [aeval st e].
  intros.
  apply s_compile_correct_gen.
Qed.

Module BreakImp.
  
Inductive com : Type :=
  | CSkip : com
  | CBreak : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.



Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).


Inductive status : Type :=
  | SContinue : status
  | SBreak : status.

Reserved Notation "c1 '/' st '||' s '/' st'"
                  (at level 40, st, s at level 39).

Inductive ceval : com -> state -> status -> state -> Prop :=
  | E_Skip : forall (st : state),
      SKIP / st || SContinue / st
  | E_Break : forall (st : state),
      BREAK / st || SBreak / st
  | E_Ass : forall (st : state) (a : aexp) (n : nat) (X : id),
       aeval st a = n ->  (X ::= a) / st || SContinue / (update st X n)
  | E_Seq_SBreak : forall (c1 c2 : com) (st st' : state),
       (c1 / st || SBreak / st') -> (c1 ; c2) / st || SBreak / st'
  | E_Seq_SCont : forall (c1 c2 : com) (st st' st'': state) (s : status),
       (c1 / st || SContinue / st') -> (c2 / st' || s / st'') -> (c1 ; c2) / st || s / st''
         
  | E_IfTrue : forall (st st': state) (s : status) (c1 c2 : com) (b : bexp),
       beval st b = true -> c1 / st || s / st' -> (IFB b THEN c1 ELSE c2 FI) / st || s / st'
  | E_IfFalse : forall (st st': state) (s : status) (c1 c2 : com) (b : bexp),
       beval st b = false -> c2 / st || s / st' -> (IFB b THEN c1 ELSE c2 FI) / st || s / st'
  | E_WhileEnd : forall (st : state) (c1 : com) (b : bexp),
       beval st b = false -> (WHILE b DO c1 END) / st || SContinue / st
  | E_WhileLoop_SBreak : forall (st st' : state) (c1 : com) (b : bexp),
       beval st b = true -> 
       c1 / st || SBreak / st' ->
       (WHILE b DO c1 END) / st || SContinue / st'
  | E_WhileLoop_SCont : forall (st st' st'': state) (s:status) (c1 : com) (b : bexp),
       beval st b = true -> 
       c1 / st || SContinue / st' ->
       (WHILE b DO c1 END) / st' || SContinue / st'' ->
       (WHILE b DO c1 END) / st || SContinue / st''
  where "c1 '/' st '||' s / st'" := (ceval c1 st s st').

Theorem break_ignore : forall c st st' s,
     (BREAK; c) / st || s / st' ->
     st = st'.
  intros.
  inversion H.
  subst.
  clear H.
  inversion H5; reflexivity.
  inversion H2.
  Qed.

  Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st || s / st' ->
  s = SContinue.
    intros.
    inversion H; try reflexivity.
  Qed.
  
Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st || SBreak / st' ->
  (WHILE b DO c END) / st || SContinue / st'.
  intros.
  apply E_WhileLoop_SBreak; assumption.
Qed.

Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st  || SContinue / st' ->
  beval st' b = true ->
  exists (st'' : state), c / st'' || SBreak / st'.
  intros.
  remember (WHILE b DO c END) as loop.
  induction H; try (inversion  Heqloop); try subst.
  rewrite H in H0; inversion H0.
  exists st; assumption.
  apply IHceval2; assumption.
Qed.

End BreakImp.