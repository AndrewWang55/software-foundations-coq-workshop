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


Theorem optimize_0plus_sound: forall e,
  aeval (optimize_0plus e) = aeval e.
  intro e.
  induction e.
  Case "e = Anum n". reflexivity.
  Case "e = APlus e1 e2".
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
  Case "e = AMinus e1 e2".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "e = AMult e1 e2".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.