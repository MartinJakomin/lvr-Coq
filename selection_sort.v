Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Recdef.
Require Import sort_lectures.

(* Local Open Scope Z_scope. *) 




Function minimum (lst : list Z) := 
   match lst with      
      | m :: nil => m
      | hd :: tl => let minimum_tail := minimum tl in if (hd <=? minimum_tail)%Z then hd else minimum_tail
      | _ => 0%Z (* Error has occured *)
   end.

Function remove (x : Z) (lst : list Z) :=
   match lst with
      | nil => nil
      | hd :: tl => if (hd =? x)%Z then tl else hd :: (remove x tl)
   end.


Function selectionSort (lst : list Z) :=
   match lst with
      | nil => nil
      (* TODO: "Recursive definition of selectionSort is ill-formed." *)
      | _ => let min := minimum lst in min :: (selectionSort (remove min lst))       
   end.
               

Eval compute in (selectionSort (12 :: 2 :: 7 :: 46 :: 5 :: 6 :: 7 :: 28 :: 19 :: nil)%Z).





(* selectionSortMergeSort always returns sorted list *)
Lemma returns_sorted_list :
   forall l : list Z, urejen (selectionSortmergeSort l).
Proof.
   admit.
Qed.

(* selectionSortMergeSort always returns same list (permutation of a list) *)
Lemma returns_permuted_list :
   forall l : list Z, permutiran l (selectionSortmergeSort l).
Proof.
   admit.
Qed.
