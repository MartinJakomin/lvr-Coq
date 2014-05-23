Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Recdef.
Require Import sort_lectures.

Function sort (l : list Z) :=
   match l with
      | nil => nil
      | x :: nil => x :: nil
      | hd :: tl => hd :: tl
   end.

Eval compute in (sort (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil)%Z).

