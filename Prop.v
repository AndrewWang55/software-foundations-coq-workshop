(* ix: 3Nv *)
Require Export Poly.



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



Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).




Theorem gorgeous__beautiful : forall n,
  gorgeous n -> beautiful n.
Proof.
   intros.
   
   (*
gorgeous_ind
     : forall P : nat -> Prop,
       P 0 ->
       (forall n : nat, gorgeous n -> P n -> P (3 + n)) ->
       (forall n : nat, gorgeous n -> P n -> P (5 + n)) ->
       forall n : nat, gorgeous n -> P n
*)
   induction H as [| n' | n'].
   apply b_0.
   apply b_sum.
   apply b_3.
   apply IHgorgeous.
   apply b_sum.
   apply b_5.
   apply IHgorgeous.
Qed.

Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
Proof.
  intros n H.
  apply g_plus5 with (n := (8+n)).
  apply g_plus5 with (n := (3+n)).
  apply g_plus3.
  apply H.
  Show Proof.
Qed.

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m Gn Gm.
  induction Gn as [ | n' | n'].
  apply Gm.
  apply g_plus3 with (n:=(n'+m)).
  apply IHGn.
  apply g_plus5 with (n:=(n'+m)).
  apply IHGn.
Qed.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n B.
  induction B.
  apply g_0.
  apply g_plus3 with (n:=0).
  apply g_0.
  apply g_plus5 with (n:=0).
  apply g_0.
  apply gorgeous_sum.
  apply IHB1.
  apply IHB2.
Qed.

Definition even (n:nat) : Prop :=
  evenb n = true.


Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).


Theorem ev_4 : ev 4.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.


Theorem double_even : forall n, ev (double n).
Proof.
  induction n  as [| n'].
  apply ev_0.
  simpl.
  apply ev_SS.
  apply IHn'.
Qed.

Definition double_even' : forall n, ev (double n) :=
  nat_ind
  (fun n => ev (double n))
  ev_0
  (fun n' => fun IHn' => (ev_SS (double n') IHn')).


Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
  Proof.
    intros n E.
    destruct E as [| n' E'].
    simpl.
    apply ev_0.
    simpl.
    apply E'.
Qed.


Theorem ev__even : forall n,
  ev n -> even n.
  intros n E.
  induction E as [| n' E IHE].
  unfold even.
  simpl.
  reflexivity.
  Print even.
  unfold even.
  simpl.
  unfold even in IHE.
  apply IHE.
Qed.


Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros n m En Em.
  induction En as [| n' En' EIHn'].
  simpl.
  apply Em.
  simpl.
  apply ev_SS.
  apply EIHn'.
Qed.


Theorem SSev_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n H.
  inversion H as [| n' H'].
  apply H'.
Qed.


Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros contra.
  inversion contra.
  inversion H0.
  inversion H2.
Qed.


Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Enplusm En.
  induction En as [| n' IHn'].
  simpl in Enplusm.
  apply Enplusm.
  simpl in Enplusm.
  inversion Enplusm.
  apply IHIHn'.
  apply H0.
Qed.  

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp.
  apply ev_sum with (n:=n+m) (m:=n+p) in Enm.
  (* (n + m) + (n + p) *)
  replace ((n+m) + (n+p)) with ((n + n) + (m + p)) in Enm.
  replace (n+n) with (double n) in Enm.
  apply ev_ev__ev with (m:=m+p) in Enm.
  apply Enm.
  replace (double n + (m + p) + (m + p)) with (double n + ((m + p) + (m + p))).
  replace  (m + p + (m + p)) with (double (m + p)).
  apply ev_sum.
  apply double_even.
  apply double_even.
  apply double_plus with (n:=m+p).
  apply plus_assoc with (n:=double n).
  apply double_plus.
  rewrite <- plus_assoc.
  replace (n+(m+p)) with (m+(n+ p)).
  rewrite plus_assoc.
  reflexivity.
  apply plus_swap'.
  apply Enp.
Qed.


Theorem ev_plus_plus' : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hm Hp.
  apply ev_sum with (n:=n+m) (m:=n+p) in Hm.
  replace (n + m + (n + p)) with ((n+n)+(m+p)) in Hm.
  apply ev_ev__ev with (n:=n+n) in Hm. 
  apply Hm.
  rewrite <- double_plus.
  apply double_even.
  rewrite <- plus_assoc.
  replace (n + (m + p)) with  (m + (n + p)).
  rewrite <- plus_assoc.
  reflexivity.
  apply plus_swap'.
  apply Hp.
Qed.