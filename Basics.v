(* ix:2DW *)

Inductive day : Type :=
    | monday : day
    | tuesday : day
    | wednesday : day
    | thursday : day
    | friday : day
    | saturday : day
    | sunday : day.


Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).

Eval simpl in (next_weekday (next_weekday saturday)).

Definition test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.


Proof.
  simpl.
  reflexivity.
Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.


Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.



Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).


Example test_nandb1:               (nandb true false) = true.
simpl. reflexivity.
Qed.

Example test_nandb2:               (nandb false false) = true.
simpl. reflexivity.
Qed.

Example test_nandb3:               (nandb false true) = true.
simpl. reflexivity.
Qed.

Example test_nandb4:               (nandb true true) = false.
simpl. reflexivity.
Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | true =>
      match b2 with
        | true => b3
        | false => false
      end
    | false => false
  end.

Example test_andb31:                 (andb3 true true true) = true.
simpl. reflexivity.
Qed.
Example test_andb32:                 (andb3 false true true) = false.
simpl. reflexivity.
Qed.


Example test_andb33:                 (andb3 true false true) = false.
simpl. reflexivity.
Qed.

Example test_andb34:                 (andb3 true true false) = false.
simpl. reflexivity.
Qed.


Check true.

Check (negb true).

Check negb.

(* naturals *)


Module Playground1.

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.


  Definition pred (n:nat) : nat :=
    match n with
      | O => O
      | S m => m
    end.

End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S m) => m
  end.


Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S m) => evenb m
  end.

Definition oddb (n:nat) : bool :=
  negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof.
  reflexivity.
Qed.

Module Playground2.

  Fixpoint plus (n:nat) (m:nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.


  Fixpoint mult (n:nat) (m:nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.


  Fixpoint minus (n:nat) (m:nat) : nat :=
    match n, m with
      | _, O =>  n
      | O, _ => O
      | S n', S m' => minus n' m'
    end.

  Eval compute in minus 8 1.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => 1
    | S power' => mult (exp base power') base
  end.

Fixpoint beq_nat n m :=
  match n, m  with
    | O, O => true
    | O, _ => false
    | S n', O => false
    | S n', S m' => beq_nat n' m'
  end.


Fixpoint ble_nat n m  :=
  match n, m  with
    | O, _ => true
    | S n', O => false
    | S n', S m' => ble_nat n' m'
  end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. simpl. reflexivity.  Qed.


Definition blt_nat (n m : nat) : bool :=
  ble_nat (S n) m.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem orb_true_b : forall b:bool, orb true b = true.
  intro b.
  reflexivity.
Qed.

Theorem plus_O_n'' : forall n:nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat,
  n = m -> n + n = m + m.

Proof.
  intros n m H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intro H1.
  intro H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
   intros n m.
   rewrite plus_O_n.
   reflexivity.
Qed.

Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  intros.
  rewrite -> plus_1_l.
  simpl.
  trivial.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
  Proof.
    intros.
    destruct n as [| n'].
    (* case n = 0 *) reflexivity.
    (* case n = S n' *) reflexivity.
  Qed.


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
  Proof.
    destruct b.
    reflexivity.
    reflexivity.
  Qed.


Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  destruct n.
  reflexivity.
  reflexivity.
Qed.    

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  trivial.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
  Proof.
    intro n.
    induction n.
    reflexivity.
    simpl.
    assumption.
  Qed.
 
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
  Proof.
    intro n.
    induction n.
    reflexivity.
    simpl.
    assumption.
  Qed.
  
Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
  Proof.
    intros n m.
    Print plus.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHn.
    reflexivity.
  Qed.
  
Fixpoint double (n:nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

(*
double (S (S (S O)))
=> S (S (double (S (S O))))
=> S (S (S (S (double (S O)))))
=> S (S (S (S (S (S (double O))))))
=> S (S (S (S (S (S (O))))))
*)

Lemma double_plus : forall n, double n = n + n.
  Proof.
    intro n.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHn.
    SearchRewrite (_ + S _).
    rewrite -> plus_n_Sm.
    reflexivity.
  Qed.