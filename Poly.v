(* ix:30b *)

Require Export Lists.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length X t)
  end.

Example test_length1 :

  length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity.  Qed.

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity.  Qed.

Fixpoint app (X : Type) (l1 l2 : list X) : list X  :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) := 
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X := 
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.


Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat))) 
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity.  Qed.

Example test_rev2: 
  rev bool (nil bool) = nil bool.
Proof. reflexivity.  Qed.

Fixpoint app' X l1 l2 :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint length' (X:Type) (l:list X) : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

Check cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Check cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Fixpoint length'' {X:Type} (l: list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length'' t)
  end.

Definition mynil : list nat := nil.

Definition mynil' := @nil.

Notation "x :: y" := (cons x y) 
                     (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) .. ).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).

Definition list123''' := [1, 2, 3].

Fixpoint repeat {X:Type} (v:X) (count:nat) :=
  match count with 
    | O => nil
    | S count' => cons v (repeat v count') 
  end.

Eval compute in repeat 1 5.
Eval compute in repeat true 8.

Theorem nil_app : forall X:Type, forall l:list X, 
  app [] l = l.
Proof.
  intros X l.
  reflexivity.
Qed.

Theorem rev_snoc : forall X : Type, 
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
  intros X v s.
  induction s.
  reflexivity.
  simpl.
  rewrite IHs.
  reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros X l.
  induction l.
  reflexivity.
  simpl.
  rewrite rev_snoc.
  rewrite IHl.
  reflexivity.
Qed.

Theorem rev_injective: forall (X:Type) (l1 l2 : list X),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite rev_involutive.
  reflexivity.
Qed.


Theorem snoc_with_append : forall X : Type, 
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
  intros X l1 l2 v.
  induction l1.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Inductive prod (X Y:Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).

Notation " X * Y " := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X := 
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y := 
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match (l1, l2) with
    | ([], _) => []
    | (_, []) => []
    | (h1 :: t1, h2 :: t2) => (h1, h2) :: (combine t1 t2)
  end.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
    | [] => ([], [])
    | (x, y)::t =>  let t' := split t in (x::(fst t'), (y::(snd t')))
  end.

Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof.
  reflexivity.
Qed.

Theorem split_combine_inverse : forall (X Y:Type) (l: list (X * Y)),
  combine (fst (split l)) (snd (split l)) = l.
Proof.
  intros.
  induction l.
  reflexivity.
  destruct x.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.


Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (i : nat) (l : list X) :=
  match (i, l) with
    | (_, []) => None
    | (O, h::t) => Some h
    | (S i', h::t) => index i' t
  end.

Fixpoint index' {X : Type} (i : nat) (l : list X) :=
  match l with
    | [] => None
    | h :: t => if beq_nat i O then Some h else index (pred i) t
  end.

Example test_index1 :    index 0 [4,5,6,7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index  1 [[1],[2]]  = Some [2].
Proof. reflexivity.  Qed.
Example test_index3 :    index  2 [true]  = None.
Proof. reflexivity.  Qed.

Definition hd_opt {X : Type} (l : list X)  : option X :=
  match l with 
    | [] => None
    | h :: t => Some h
  end.


Definition doit3times  {X:Type} (f : X -> X) (v : X) : X :=
  f (f (f v)).

(* doit3times :    forall X:Type, (X -> X) ->  X -> X  *)

Check plus.


Definition prod_curry {X Y Z:Type} (f : (X * Y) -> Z) (x:X) (y:Y) :=
  f (x,y).

Definition plus_pair (p:nat * nat) :=
  (fst p) + (snd p).

Check prod_curry plus_pair.

Definition prod_uncurry {X Y Z : Type } (f : X -> Y -> Z) (p: X * Y) : Z :=
  f (fst p) (snd p).

Definition plus3 := plus 3.

(* function identity *)
Definition plus'' x y := x + y.
Definition plus' z w := (fun o:nat => z + w) O.
Theorem identity_by_reduction : plus' = plus''.
  reflexivity.
Qed.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) (x:X) (y:Y),
  prod_curry (prod_uncurry f) x y  = f x y.
  Proof.
    reflexivity.
  Qed.


Theorem curry_uncurry : forall (X Y Z : Type) 
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
  Proof.
    intros.
    destruct p as [x y].
    reflexivity.
  Qed.

Fixpoint filter  {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
    | [] => []
    | h :: t => if test h then h :: (filter test t) else (filter test t)
  end.

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof.
  reflexivity.
Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2: 
    filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof.
  reflexivity.
Qed.

Example test_anon_fun': 
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

Definition gt7 x := negb (ble_nat x 7).

Definition filter_even_gt7 (l:list nat):=
  filter (fun x => (andb (evenb x) (negb (ble_nat x 7)))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof.
  reflexivity.
Qed.

Fixpoint partition  {X:Type} (test : X -> bool) (l : list X) : (list X) * (list X) :=
  match l with
    | [] => ([], [])
    | h :: t => let (ok,notok) := (partition test t) in
      if test h
        then (h :: ok, notok)
        else (ok, h :: notok)
  end.

Definition partition'  {X:Type} (test : X -> bool) (l : list X) : (list X) * (list X) :=
  (filter test l, filter (fun x => negb (test x)) l).

  
(* TODO : proove that partition' l and partition l are equal *)

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof.
  reflexivity.
Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) :=
  match l with
    | []  => []
    | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity.  Qed.

Lemma map_snoc : forall (X Y:Type) (l : list X) (f : X -> Y) (v : X),
  map f (snoc l v) = (snoc (map f l) (f v)).
  intros X Y l f v.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  reflexivity.
  simpl.
  rewrite <- IHl.
  rewrite-> map_snoc.
  rewrite IHl.
  reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) : (list Y) := 
  match l with
    | [] => []
    | h :: t =>  (f h) ++ (flat_map f t)
  end.

Example test_flat_map1: 
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof.
  reflexivity.
Qed.

Fixpoint fold {X Y:Type} (f : X -> Y -> Y) (l : list X)  (i : Y) : Y :=
  match l with
    | [] => i
    | h :: t => f h (fold f t i)
  end.

Eval compute in fold andb [true, false, true] true.

Eval compute in fold (fun l c => (length l) + c)  [[1],[],[2,3],[4]] 0.

Definition constfun  {X:Type}  (v:X) : nat -> X :=
  fun _ => v.

Definition ftrue := constfun true.
Check ftrue.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X:Type} (f: nat -> X)  (v:nat) (x:X) : nat -> X :=
  fun n => if beq_nat v n then x else f n.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.


Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p.
  intros H1 H2.
  rewrite <- H1.
  apply H2. 
Qed.


Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
     [n,o] = [m,p].
Proof.
  intros n m o p H1 H2.
  apply H2.
  apply H1.
Show Proof.
Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.


Theorem silly_ex :
     (forall n,  evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H eq1.
  apply H.
  apply eq1.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
  Proof.
    intros n H.
    simpl.
    symmetry.
    apply H.
    Show Proof.
    Print eq_sym.
  Qed.



Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  apply rev_injective.
  symmetry.
  rewrite <- H.
  apply rev_involutive.
Qed.

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite H.
  reflexivity.
Qed.


Theorem override_eq : forall {X:Type} x k (f:nat -> X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  beq_nat k2 k1 = false -> 
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H neq.
  unfold override.
  rewrite neq.
  apply H.
Qed.

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  intro b.
  unfold override.
  simpl.
  unfold constfun.
  reflexivity.
Qed.


Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq.
  inversion eq.
  reflexivity.
Qed.


Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n m eq.
  inversion eq.
  reflexivity.
Qed.

Theorem silly5 : forall (n m o : nat),
     [n,m] = [o,o] ->
     [n] = [m].
Proof.
  intros n m o eq.
  inversion eq.
  reflexivity.
Qed.


Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j.
  intros H1 H2.
  inversion H2.
  reflexivity.
Qed.


  
Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra.
  inversion contra.
Qed.

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros X x y z l j contra eq.
 inversion contra.
Qed.
 
Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
  intros n m eq.
  rewrite eq.
  reflexivity.
Qed.


Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l.
  induction l as [|x' l'].
  Case "l = []". simpl. intros n H. rewrite H. reflexivity.
  Case "l = x::l'".
  simpl.
  intros n H.
  rewrite <- H.
  apply eq_remove_S.
  apply IHl'.
  reflexivity.
Qed.

Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    destruct m as [|m'].
    SCase "m = 0". intro H. reflexivity.
    SCase "m = S m'". simpl. intro contra. inversion contra.
  Case "n = S n'".
     destruct m as [|m'].
     SCase "m = 0". simpl. intro contra. inversion contra.
     SCase "m = S m'".
       simpl.
       intro.
       apply eq_remove_S.
       apply IHn'.
       apply H.
Qed.  



Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m'].
  destruct n.
  auto.
  simpl.
  intro. inversion H.
  destruct n.
  simpl.
  intro. inversion H.
  simpl.
  intros.
  apply eq_remove_S.
  apply IHm'.
  apply H.
Qed.


Theorem beq_nat_0_l : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  intro n.
  destruct n.
  intro. 
  reflexivity.
  simpl.
  intro. 
  inversion  H.
Qed.


Theorem beq_nat_0_r : forall n,
  true = beq_nat n 0 -> n = 0.
Proof.
  intros.
  destruct  n.
  reflexivity.
  simpl in H.
  inversion  H.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intro n.
  induction n as [|n'].
  destruct m.
  reflexivity.
  reflexivity.  
  destruct m.
  reflexivity.  
  simpl. apply IHn'.
Qed.


Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros  n m b.
  intro H.
  simpl in H.
  apply H.
Qed.


Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n H1 H2.
  symmetry in H2.
  apply H1 in H2.
  symmetry in H2.
  apply H2.
Qed.


Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n.
  induction n as [|n'].
  destruct m.
  intro H. reflexivity.
  simpl. intro contra. inversion contra.
  destruct m as [|m'].
  intros contra. inversion contra.
  intro H. apply eq_remove_S.
  apply IHn'.
  simpl in H.
  inversion H.
  rewrite <- plus_n_Sm in H1. 
  rewrite <- plus_n_Sm in H1. 
  inversion H1.
  reflexivity.
Qed.


Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intro n.
  unfold sillyfun.
  simpl.
  destruct (beq_nat n 3).
  reflexivity.
  destruct (beq_nat n 5).
  reflexivity. reflexivity.
Qed.

Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f : nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
  reflexivity.
  reflexivity.
Qed.

Lemma eq_remove_cons : forall (X:Type) (l1 l2: list X) (x: X),
  l1 = l2 -> x :: l1 = x :: l2.
  intros X l1 l2 x.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| [x y] l'].
  intros l1 l2.
  simpl.
  intro H.
  inversion H.
  reflexivity.
  intros l1 l2.
  simpl.
  intro H.
  inversion H.
  simpl.
  apply eq_remove_cons.
  apply IHl'.
  destruct (split l').
  reflexivity.
Qed. 

Theorem split_combine: forall (X:Type) (l1 l2: list X),
   (length l1 = length l2) -> split (combine l1 l2) = (l1,l2).
  intros X l1.
  induction l1.
  simpl.
  intros l2 H.
  destruct l2.
  reflexivity.
  inversion H.
  intros l2 H.
  simpl in H.
  destruct l2 as [|y l2'].
  simpl.
  inversion H.
  simpl in H.
  inversion H.
  apply IHl1 in H1.
  simpl.
  rewrite H1.
  reflexivity.
Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [|x  l'].
  reflexivity.
  unfold fold_length.
  simpl.
  unfold fold_length in IHl'.
  apply eq_remove_S.
  apply IHl'.
Qed.

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x rest => (f x) :: rest) l [].

Theorem fold_map_correct : forall (X Y:Type) (f : X -> Y) (l:list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l as [|x l'].
  reflexivity.
  unfold fold_map in IHl'.
  unfold fold_map.
  simpl.
  rewrite IHl'.
  reflexivity.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) :=
  match l with
    | [] => true
    | h :: t => andb (test h) (forallb test t)
  end.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) :=
  match l with
    | [] => false
    | h :: t => orb (test h) (existsb test t)
  end.


Definition existsb' {X:Type} (test : X -> bool) (l : list X) :=
  negb (forallb (fun x => negb (test x)) l).
 
 
Theorem x_law_1: forall (p q: bool),
  (negb (andb p q)) = (orb (negb p) (negb q)).
  intros p q.
  destruct p.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

  
Theorem existsb_correct : forall (X Y:Type) (test : X -> bool) (l:list X),
  existsb' test l = existsb test l.
Proof.
  intros X Y test l.
  induction l as [| x l'].
  reflexivity.
  simpl.
  unfold existsb'.
  unfold existsb' in IHl'.
  simpl.
  rewrite x_law_1.
  rewrite  negb_involutive.
  rewrite IHl'.
  reflexivity.
Qed.

Theorem app_nil_r : forall (X:Type) (l : list X),
  (l ++ []) = l.
intros X l.
induction l.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Theorem length_app_sym : forall (X:Type) (l1 l2 : list X) (x:X) (n:nat),
   length (l1 ++ l2) = n ->  length (l1 ++ (x::l2)) = S n.
Proof.
  intros X l1.
  induction l1.
  simpl.
  intros.
  rewrite H.
  reflexivity.
  simpl.
  intros.
  apply eq_remove_S.
  destruct n.
  inversion H.
  apply IHl1.
  inversion H.
  reflexivity.
Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l.
  simpl.
  intros.
  rewrite <- H.
  reflexivity.
  simpl.
  intros n H.
  destruct n.
  inversion H.
  simpl.
  inversion H.
  simpl.
  apply eq_remove_S.
  rewrite <- plus_n_Sm.
  rewrite H1.
  apply length_app_sym.
  apply IHl.
  apply H1.
Qed.

(*

Unset Printing Notations.

Fixpoint  pedja_plus_right_0 (n:nat) :  n + 0 = n :=
  match n return (n+0 = n) with
    | O => eq_refl O
    | S n' => match (pedja_plus_right_0  n') in (eq _ x) return (S (n' + 0) =  S x) with
                | eq_refl => eq_refl ( S (plus n' O))
              end
      (* n' + 0 = n' *)
      (* S n' + 0 = S n' *)
(*match pedja_plus_right_0 n' in (eq _ x) return (S x = S n') with
                | eq_refl => eq_refl (plus (S n') O)
              end*)
  end.
  *)