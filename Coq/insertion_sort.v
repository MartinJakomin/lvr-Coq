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
Lemma returns_sorted_list :
   forall l : list Z, urejen (insertionSort l).
Proof.
   intro.
   induction l.
   + simpl; auto.
   + simpl.
     apply insert_keeps_list_sorted; assumption. 
Qed.


(* Number of occurrences of x increases if we insert another x into a list*)
Lemma occurrence_of_x (x : Z) (l : list Z) :
    pojavi x (insert x l) = S (pojavi x l).
Proof.
   (* TODO *)
   induction l.
   - simpl.
     now rewrite Z.eqb_refl.
   - admit.
     (* TODO *)
Qed.

(* Number of occurrences of x does not change if we insert a different element into a list *)
Lemma occurrence_of_x_2 (x y : Z) (l : list Z) :
    ((x =? y)%Z = false) -> pojavi x (insert y l) = pojavi x l.
Proof.
   intro.
   induction l.
   - simpl.
     now replace (x =? y)%Z with false.
   - (* TODO *)
   admit.
Qed.


(* InsertionSort always returns same list (permutation of a list) *)
Lemma returns_permuted_list :
   forall l : list Z, permutiran l (insertionSort l).
Proof.
   intro.
   induction l.
   - firstorder.
   - intro.
     simpl.
     case_eq (x =? a)%Z.
     + intro.
       replace a with x.
       * rewrite (occurrence_of_x x (insertionSort l)).
         rewrite IHl.
         auto.       
       * (* SearchAbout [(_ =? _)%Z]. *)
         now apply Z.eqb_eq.
     + intro.
       rewrite (occurrence_of_x_2 x a).
       * rewrite IHl.
         auto.
       * assumption.  
Qed.

