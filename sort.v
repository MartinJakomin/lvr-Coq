Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Recdef.
Require Import sort_lectures.

(* Local Open Scope Z_scope. *)


(* Inserts an element in to a sorted list *)
Function insert (x : Z) (lst : list Z) :=
   match lst with
      | nil => x :: nil
      | hd :: tl => if (x <=? hd)%Z then x :: hd :: tl else hd :: insert x tl
   end.

(* Insertion sort *)
Function insertionSort (lst : list Z) :=
   match lst with
      | nil => nil
      | hd :: tl => insert hd (insertionSort tl)     
   end.

Eval compute in (insertionSort (12 :: 2 :: 7 :: 46 :: 5 :: 6 :: 7 :: 28 :: 19 :: nil)%Z).



(* The first element in a sorted list is the smallest *)
Lemma first_element_is_the_smallest (a : Z) (tl : list Z):
   forall x , In x tl -> urejen (a :: tl) -> (a <= x)%Z.
Proof.
   intros.
   admit.
Qed.


(* Adding bigger element doesnt change upper Lemma *)
Lemma smaller_than_x (a x : Z) (tl : list Z):
   urejen (a :: tl) /\ (a <= x)%Z -> forall y, In y (insert x tl) -> (a <= y)%Z.
Proof.
   intros.
   destruct H.
   admit.
Qed.


(* TODO: Other lemmas you need for insert_is_sorted *)


(* Insertion of an element keeps list sorted *)
Lemma insert_is_sorted (x : Z) (lst : list Z):
   urejen lst -> urejen (insert x lst).
Proof.
   intros.
   induction lst.
   - auto.
   - simpl.
     case_eq (x <=? a)%Z.
     + intro.
       simpl.
       firstorder.
       apply Z.leb_le.
       auto.
     + intro.
       admit.       
Qed.


(* InsertionSort always returns sorted list *)
Theorem sorted (l : list Z):
   forall l, urejen (insertionSort l).
Proof.
   admit.
Qed.

(* TODO: Other theorems that program works correctly *)



