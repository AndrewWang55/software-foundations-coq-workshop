(* ix:2I7 *)

Require Export Basics.

Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
    pair x _ => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
    pair _ y => y
  end.

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
    (x, y) => (y, x)
  end.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
  Proof.
    intro p.
    destruct p as [x y].
    reflexivity.
  Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
  Proof.
    intro p.
    destruct p as [x y].
    reflexivity.
  Qed.

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Check [1,2,3].
Check 1::2::3::nil.
Check (cons 1 (cons 2 (cons 3 nil))).

Fixpoint repeat (n count : nat) : natlist  :=
  match count with
    | O => []
    | S count' => n::(repeat n count')
  end.

(*  repeat 0 3
   =>  repeat 0 (S (S (S O)))
   =>  0::(repeat 0 (S (S O)))
   => 0::0::(repeat 0 (S O))
   => 0::0::0::(repeat 0 0)
   => 0::0::0::[]
   ~ [0,0,0]
*)

Fixpoint length (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

(* length [1,2]
   (* [1,2] = 1::[2] = 1::2::nil = cons 1 (cons 2 nil) *)
   => S ( length [2] )
   => S ( S (length nil))
   => (S (S O)
*)

Eval simpl in length [1,2].


(* app [1,2,3,4] [3,4] = [1,2,3,4] *)
Fixpoint app (l1 l2 : natlist) :=
  match l1 with
    | [] => l2
    | h::t => cons h (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Eval simpl in  [1,2] ++ [3,4].

Definition hd (default: nat) (l:natlist) :=
  match l with
    | nil => default
    | h::t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
    | [] => []
    | _::t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | [] => []
    | O::t => nonzeros t
    | h::t => h::(nonzeros t)
  end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof.
  reflexivity.
Qed.

Fixpoint oddmembers (l:natlist) : natlist  :=
  match l with
    | [] => []
    | h::t => match (oddb h) with
                | true =>  h::(oddmembers t)
                | false => oddmembers t
              end
  end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof.
  reflexivity.
Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
    | [] => O
    | h::t => match (oddb h) with
                | true =>  S (countoddmembers t)
                | false => countoddmembers t
              end
  end.

(* "if" can be used with any two-constuctor type such as "bool" *)
Fixpoint countoddmembers' (l:natlist) : nat :=
  match l with
    | [] => O
    | h::t => if (oddb h) then S (countoddmembers t) else countoddmembers t
  end.

Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof.
  reflexivity.
Qed.

(* HOMEWORK *)
(*
   
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
 (* FILL IN HERE *) Admitted.
Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
 (* FILL IN HERE *) Admitted.
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
 (* FILL IN HERE *) Admitted.
Example test_alternate4: alternate [] [20,30] = [20,30].
 (* FILL IN HERE *) Admitted.

*)

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
    | [] => O
    | h::t => if beq_nat v h then S (count v t) else count v t
  end.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof.
  reflexivity.
Qed.

Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof.
  reflexivity.
Qed.


Definition sum : bag -> bag -> bag :=  app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof.
  reflexivity.
Qed.


Definition add (v:nat) (b:bag) := cons v b.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
reflexivity.
Example test_add2: count 5 (add 1 [1,4,1]) = 0.
reflexivity.

Definition member (v:nat) (s:bag) : bool :=
  negb (beq_nat (count v s) O).

Example test_member1: member 1 [1,4,1] = true.
reflexivity.
Qed.

Example test_member2: member 2 [1,4,1] = false.
  reflexivity.
Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h::t => if (beq_nat h v) then t else h::(remove_one v t)
  end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
reflexivity.
Qed.
Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
reflexivity.
Qed.
Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
reflexivity.
Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
reflexivity.
Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h::t => if (beq_nat h v) then (remove_all v t) else h::(remove_all v t)
  end.

Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
reflexivity.
Qed.

Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
reflexivity.
Qed.

Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
reflexivity.
Qed.

Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
reflexivity.
Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | [] => true
    | h::t => if (member h s2) then (subset t (remove_one h s2)) else false
  end.


Example test_subset1: subset [1,2] [2,1,4,1] = true.
Proof.
reflexivity.
Qed.

(* subset cannot be longer than the set *)
Example test_subset2: subset [1,2,2] [4,1] = false.
reflexivity.
Qed.

(* permutation *)
Example test_subset3: subset [1,2,2] [2,1,2] = true.
reflexivity.
Qed.

(* HOMEWORK
Exercise: 3 stars, recommended (bag_theorem)

Write down an interesting theorem about bags involving the functions
count and add, and prove it. Note that, since this problem is somewhat
open-ended, it's possible that you may come up with a theorem which is
true, but whose proof requires techniques you haven't learned
yet. Feel free to ask for help if you get stuck!
*)
