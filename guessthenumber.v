Require Import NArith List.
Import ListNotations.

(** 
*** Guess a number between 1 and 100 *** 
*)

(** 0. List all numbers between 0 and 100. *)

Fixpoint list_all_aux (acc : list N) (n : nat) : list N := 
  match n with
  | O => N0 :: acc
  | S n' => list_all_aux (N.of_nat n :: acc) n'
  end.

Definition list_all := list_all_aux [] 100.

Compute list_all.

(** 1. Return the list of all numbers between 0 and 100 
       inclusive with binary digit [i] set to [b]. 

       Digit 0 is the LEAST SIGNIFICANT BIT. *)

Definition has_digit (i : nat) (b : bool) (n : N) : bool :=
  Bool.eqb (N.testbit n (N.of_nat i)) b.

Fixpoint filter_digit (i : nat) (b : bool) : list N :=
  filter (has_digit i b) list_all.

Compute filter_digit 0 false.
Compute filter_digit 0 true.
Compute filter_digit 6 true.

(** 2. Given a bitstring [bs] representing in binary a nonzero 
       positive integer with least significant digits first, 
       construct the corresponding integer. 

       E.g., N_of_bitstring [false; true] = 2%N. (*= 0b10*)
       E.g., N_of_bitstring [false; false; false; true] = 8%N. (*= 0b1000*)
       E.g., N_of_bitstring [true; false; true; true] = 13%N. (*= 0b1101*) *)

Fixpoint N_of_bitstring_aux (acc : N) (n : nat) (bs : list bool) : N :=
  match bs with
  | nil => acc
  | false :: bs' => N_of_bitstring_aux (N.clearbit acc (N.of_nat n)) (S n) bs'
  | true :: bs' => N_of_bitstring_aux (N.setbit acc (N.of_nat n)) (S n) bs'
  end.

Definition N_of_bitstring (bs : list bool) :N :=
  N_of_bitstring_aux N0 O bs.

Compute N_of_bitstring [false; true].
Compute N_of_bitstring [false; false; false; true].
Compute N_of_bitstring [true; false; true; true].

(** 3. Produce a pseudo-random bit sequence, given an 
       initial 16-bit random seed. *)

Fixpoint lfsr_aux (acc : list bool) (x : N) (n : nat) : list bool :=
  match n with
  | O => acc
  | S n' =>
    let output_bit :=
        xorb (N.testbit x (N.of_nat 10))
             (xorb (N.testbit x (N.of_nat 12))
                   (xorb (N.testbit x (N.of_nat 13))
                         (N.testbit x (N.of_nat 15))))
    in lfsr_aux
         (output_bit :: acc)
         (let x' := N.shiftl_nat x 1
          in if output_bit then N.setbit x' 0%N
             else N.clearbit x' 0%N)
         n'
  end.

Definition lfsr (seed : N) (num_bits : nat) : list bool :=
  lfsr_aux [] seed num_bits.

Definition seed : N :=
  N_of_bitstring
    [true;true;false;false;true;false;false;true;
     false;true;false;true;false;true;false;false].

Compute seed.
Compute lfsr seed 23.

(** 4. Generate 7 sets of numbers, each with bit [i] set or 
       not, depending on the pseudo-random numbers generated 
       by function [lfsr]. The first set in the list matches 
       the first digit in the pseudo-random sequence [lfsr seed 7]. *)

Fixpoint build_sets_aux
         (acc : list (list N))
         (n : nat)         
         (prns : list bool)
  : option (list (list N)) :=
  match n, prns with 
  | O, [] => Some acc
  | S n', b :: prns' =>
    build_sets_aux (filter_digit n' b :: acc) n' prns'
  | _, _ (*error*) => None
  end.

Definition build_sets := build_sets_aux [] 7 (rev (lfsr seed 7)).

Compute build_sets.

(** 5. Convenience functions for displaying the sets. *)

Local Open Scope positive_scope.

Fixpoint display_set_aux
         {T : Type}
         (n : nat)
         (l : list (list T))
  : option (list T) :=
  match n, l with
  | O, x :: l' => Some x
  | S n', _ :: l' => display_set_aux n' l'
  | _, _ => None
  end.

Definition display_set (n : nat) : option (list N) :=
  match build_sets with
  | None => None
  | Some l => display_set_aux n l
  end.

Compute display_set 0.
Compute display_set 1.
Compute display_set 6.
Compute display_set 7. (*= None*)

(** 6. Guess the number, given a string of 7 booleans corresponding 
       to the YES/NO questions: Is the number in set [i] of [build_sets]? *)

Fixpoint zip {A B : Type} (l1 : list A) (l2 : list B) : list (A*B) :=
  match l1, l2 with
  | nil, _ => nil
  | _, nil => nil
  | x::l1', y::l2' => (x,y) :: zip l1' l2'
  end.

Definition guess_the_number (choices : list bool) : N :=
  N_of_bitstring
    (map (fun p : bool*bool =>
            let (choice, prbit) := p
            in if prbit then choice else negb choice)
         (zip choices (lfsr seed 7))).

(* Let's try 57 ... *)

Compute display_set 0. (*true*)
Compute display_set 1. (*false*)
Compute display_set 2. (*true*)
Compute display_set 3. (*false*)
Compute display_set 4. (*false*)
Compute display_set 5. (*false*)
Compute display_set 6. (*false*)

Definition choices57 := [true;false;true;false;false;false;false].
Compute guess_the_number choices57.

(* Let's try 78 ... *)

Compute display_set 0. (*false*)
Compute display_set 1. (*true*)
Compute display_set 2. (*false*)
Compute display_set 3. (*false*)
Compute display_set 4. (*true*)
Compute display_set 5. (*true*)
Compute display_set 6. (*true*)

Definition choices78 := [false;true;false;false;true;true;true].
Compute guess_the_number choices78.

(* Let's try 100 ... *)

Compute display_set 0. (*false*)
Compute display_set 1. (*false*)
Compute display_set 2. (*false*)
Compute display_set 3. (*true*)
Compute display_set 4. (*true*)
Compute display_set 5. (*false*)
Compute display_set 6. (*true*)

Definition choices100 := [false;false;false;true;true;false;true].
Compute guess_the_number choices100.

(* Let's try 0 ... *)

Compute display_set 0. (*false*)
Compute display_set 1. (*false*)
Compute display_set 2. (*true*)
Compute display_set 3. (*true*)
Compute display_set 4. (*true*)
Compute display_set 5. (*true*)
Compute display_set 6. (*false*)

Definition choices0 := [false;false;true;true;true;true;false].
Compute guess_the_number choices0.

