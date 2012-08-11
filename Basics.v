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

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

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
  
Theorem plus_comm : forall n m : nat, n + m = m + n.
  Proof.
    intros n m.
    induction n.
    rewrite -> plus_0_r.
    reflexivity.
    simpl.
    rewrite <- plus_n_Sm.
    rewrite -> IHn.
    reflexivity.
Qed.    
Print plus_comm.

Fixpoint double (n:nat) : nat :=
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
  
Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
  Proof.
    intros n m p.
    induction n.
    reflexivity.
    simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
  Proof.
    intro n.
    induction n.
    reflexivity.
    simpl.
    rewrite <- IHn.
    reflexivity.
Qed.


Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
  Proof.
    intros n m.
    assert (H: 0 + n = n).
    reflexivity.
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_rearrange:
  forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
  intros n m p q.
  assert (H: n + m = m + n).
  rewrite -> plus_comm.
  reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
  Proof.
    intros n m p.
    rewrite -> plus_assoc.
    Check plus_assoc.
    rewrite -> plus_assoc. 
    assert (H: n + m = m + n).
    rewrite plus_comm.
    reflexivity.
    rewrite H.
    reflexivity.
Qed.

Theorem mult_n_Sm : forall n m : nat, n * S m = n + n * m.
  Proof.
    intros n m.
    induction n.
    reflexivity.
    simpl.
    rewrite -> IHn.
    rewrite plus_swap.
    reflexivity.
  Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
  Proof.
    intros m n.
    induction n as [| n'].
    Case "n + 0 = n".
      rewrite mult_0_r.
      reflexivity.
    Case "n = S n'".
      simpl.
      rewrite <- IHn'.
      rewrite -> mult_n_Sm.
      reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
  Proof.
    intros n.
    induction n.
    reflexivity.
    simpl.
    rewrite -> IHn.
    rewrite negb_involutive.
    destruct n as [| n'].
    reflexivity.
    simpl.
    reflexivity.
Qed.

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
  Proof.
    intros.
    induction n as [| n'].
    reflexivity.
    simpl.
    exact IHn'.
    Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
  Proof.
    intros n.
    reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p.
  intro H.
  induction p.
  simpl.
  exact H.
  simpl.
  exact IHp.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros.
  simpl.
  rewrite plus_0_r.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
  Proof.
    intros.
    destruct b.
    destruct c.
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.
  
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite mult_plus_distr_r.
  reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  rewrite plus_assoc.
  replace (n + m) with (m + n).
  reflexivity.
  rewrite plus_comm.
  reflexivity.
Qed.

Module binnats.

  Inductive bin : Set :=
  | O : bin
  | D : bin -> bin
  | P : bin -> bin.

  Fixpoint bininc (b:bin) : bin :=
    match b with
      | O => P O
      | D b' => P b'
      | P b' => D (bininc b')
    end.

  Fixpoint bin2nat (b:bin) : nat :=
    match b with
      | O => 0
      | D b' => double (bin2nat b')
      | P b' => S (double (bin2nat b'))
    end.

  Theorem bin2nat_bininc_comm : forall b:bin,
    bin2nat (bininc b) = S (bin2nat b).
    Proof.
      intros b.
      induction b.
      reflexivity.
      reflexivity.
      simpl.
      rewrite IHb.
      reflexivity.
    Qed.

    Fixpoint nat2bin (n:nat) : bin :=
      match n with
        | 0 => O
        | S n' => bininc (nat2bin n')
      end.

    Theorem nat2bin2nat_id : forall n:nat,
      bin2nat (nat2bin n) = n.
      intros n.
      induction n.
      reflexivity.
      simpl.
      rewrite bin2nat_bininc_comm.
      rewrite IHn.
      reflexivity.
    Qed.

    Eval simpl in (nat2bin (bin2nat O)).
    Eval simpl in (nat2bin (bin2nat (D (D (D O))))).

    Fixpoint normalize (b:bin) : bin :=
      match b with
        | O => O
        | D b' => match normalize b' with
                    | O => O
                    | nb => D nb
                  end
        | P b' => P (normalize b')
      end.

Definition imp_id_proof := fun (p:Prop) => (fun (d:p) => d).

Check imp_id_proof (3=3).
Check imp_id_proof (3=3) (refl_equal 3).

Theorem imp_id : forall P:Prop, P -> P.
  intro p.
  intro d.
  exact d.
Qed.

Print imp_id.

Eval simpl in bininc (normalize (D (P (D O)))) = (normalize (P (P (D O)))).

(*
Theorems and definitions below taken from
http://staff.ustc.edu.cn/~bjhua/courses/theory/2012/slides/lec1notes.html
*)

Definition bindouble (b:bin) : bin :=
  match b with
    | O => O
    | D n' => D (D n')
    | P n' => D (P n')
  end.

Lemma bininc_twice : forall b:bin,
  bininc (bininc (bindouble b)) = bindouble (bininc b).
  Proof.
    destruct b.
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.

Lemma double_bindouble : forall n:nat,
  nat2bin (double n) = (bindouble (nat2bin n)).
  Proof.
    intro n.
    induction n.
    reflexivity.
    simpl.
    rewrite IHn.
    rewrite bininc_twice.
    reflexivity.
  Qed.

Lemma bininc_bindouble: forall b:bin,
  bininc (bindouble b) = P b.
  intro b.
  destruct b.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Theorem bin2nat2bin_n_eq_norm_n : forall b:bin,
  nat2bin (bin2nat b) = normalize b.
  Proof.
    intro b.
    induction b.
    reflexivity.
    simpl.
    rewrite double_bindouble.
    rewrite IHb.
    unfold bindouble.
    reflexivity.
    simpl.
    rewrite double_bindouble.
    rewrite IHb.
    rewrite bininc_bindouble.
    reflexivity.
  Qed.
