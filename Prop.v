(* ix: 3Nv *)
Require Export Poly.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.


Inductive beautiful : nat -> Prop :=
  | b_0 : beautiful 0
  | b_3 : beautiful 3
  | b_5 : beautiful 5
  | b_sum : forall (n m : nat), beautiful n -> beautiful m -> beautiful (n + m).
  

Theorem beautiful_3 : beautiful 3.
  apply b_3.
Qed.

Theorem beautiful_8 : beautiful 8.
  apply b_sum with (n:=3) (m:=5).
  apply b_3.
  apply b_5.
Qed.


Theorem eight_is_beautiful': beautiful 8.
  apply (b_sum 3 5 b_3 b_5).
Qed.

Theorem eight_is_beautiful'': beautiful 8.
Proof.
   Show Proof.
   apply b_sum with (n:=3) (m:=5).
   Show Proof.
   apply b_3.
   Show Proof.
   apply b_5.
   Show Proof.
Qed.

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  apply b_sum with (n:=3) (m:=3).
  apply b_3.
  apply b_3.
Qed.


Definition six_is_beautiful' : beautiful 6 :=
  b_sum 3 3  b_3 b_3.

Theorem nine_is_beautiful :
  beautiful 9.
Proof.
  apply b_sum with (n:=6) (m:=3).
  apply six_is_beautiful.
  apply b_3.
Qed.


Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
  intro n.
  intro H.
  apply b_sum.
  apply b_3.
  apply H.
Qed.


Definition b_plus3' : forall n, beautiful n -> beautiful (3+n)  :=
  fun (n:nat) => fun (H : beautiful n) => b_sum 3 n b_3 H.

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) := 
  b_sum 3 n b_3 H.

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros n H.
  simpl.
  apply b_sum.
  apply H.
  apply b_sum.
  apply H.
  apply b_0.
Qed.

Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m H.
  induction m as [| m'].
  apply b_0.
  simpl.
  apply b_sum.
  apply H.
  apply IHm'.
Qed.

Fixpoint b_timesm' (n m :nat) (H : beautiful n) : beautiful (m*n) :=
  match m return beautiful (m * n) with
    | O => b_0
    | S m' => b_sum n (m' * n) H (b_timesm' n m' H)
  end.
