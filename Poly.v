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
  