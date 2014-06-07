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




(* Insertion of an element keeps the list sorted *)
Lemma insert_keeps_list_sorted (x : Z) (lst : list Z):
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
       now apply Z.leb_le.       
     + intro.
       apply Z.leb_gt in H0.
       simpl.       
       destruct lst; simpl.       
       * firstorder.
       * firstorder.
         case_eq (x <=? z)%Z.
         proof.
         intro.
         firstorder.         
         now apply Zle_bool_imp_le.
         end proof.
         proof.
         intro.
         firstorder.
         replace (z :: insert x lst) with (insert x (z :: lst)).
         assumption.
         simpl.
         case_eq (x <=? z)%Z.
         proof.
         intro.
         absurd ((x <=? z)%Z = false); auto.         
         now rewrite <- not_false_iff_true in H4.         
         end proof.
         auto.
         end proof.  
Qed.



(* InsertionSort always returns sorted list *)
Theorem sorted (l : list Z):
   forall l, urejen (insertionSort l).
Proof.
   admit.
Qed.

(* TODO: Other theorems that program works correctly *)


