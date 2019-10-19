From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

(*** Exercise 1 *)

(** 1a. Define [orb_my] function implementing boolean disjunction *)

(** 1b. Figure out the implementation of [orb] function in the standard library
        using Coq's interactive query mechanism *)

(** 1c. What's the difference between the standard implementation and
        the following one? *)

Definition orb_table (b c : bool) : bool :=
  match b, c with
  | true,  true  => true
  | true,  false => true
  | false, true  => true
  | false, false => false
  end.

(** Note: the above translates into nested pattern-matching, check this *)

Check orb_table.

(** 1d. Define [addb_my] function implementing exclusive boolean disjunction.
        {The name [addb] comes from the fact this operation behaves like addition modulo 2}
        If you are already familiar with proofs in Coq, think of a prover friendly
        definition, if you are not -- experiment with how different implementations
        behave under symbolic execution. *)

Definition addb_my (m n : bool) : bool :=
  match m with 
    | true => negb n
    | false => n
  end. 

(*** Exercise 2 *)

(** 2a. Implement power function of two arguments [x] and [n],
        raising [x] to the power of [n] *)

Fixpoint pow (x n : nat) : nat :=
 match n with 
   | 0 => 1
   | S n' => x * pow x n'
 end.

Locate ">=".

(*** Exercise 3 *)



(** 3a. Implement division on unary natural numbers *)

Fixpoint div2 (a b : nat) : nat :=
 match b with 
  | 0 => 0
  | S b' => match a with 
    | 0 => 0
    | S a' => 
       if a' >= b' 
       then S (div2 (a' - b') b)
       else 0
    end
 end.

(* Fixpoint subp (a b : nat) : nat :=
  match a with  -*)

Fixpoint subp (a b : nat) : nat :=
  match a with 
    | 0 => a
    | S a' => match b with
      | 0 => a
      | b'.+1 => subp a' b'
    end
  end.


Fixpoint div_s (a b : nat) : nat :=
  if subp a b is x.+1 then S (div_s x b) else 0.

Definition div (a b : nat) : nat :=
  if b is b'.+1 then div_s a b' else 0.

(** 3b. Provide several unit tests using [Compute] vernacular command *)

Lemma test_div_1 : div 1 2 = 0 .
Proof. simpl. reflexivity. Qed.

Lemma test_div_2 : div 17 2 = 8 .
Proof. reflexivity. Qed.

Lemma test_div_3 : div 19 5 = 3 .
Proof. reflexivity. Qed.

Lemma test_div_4 : div 0 5 = 0 .
Proof. reflexivity. Qed.

Lemma test_div_5 : div 5 0 = 0 .
Proof. reflexivity. Qed.

Lemma test_div_6 : div 13 1 = 13 .
Proof. reflexivity. Qed.



(*** Exercise 4 *)

(** Use the [applyn] function defined during the lecture
    (or better its Mathcomp sibling called [iter]) define
    4a. addition on natural numbers
    4b. multiplication on natural numbers
    Important: don't use recursion, i.e. no [Fixpoint] / [fix] should be in your solution.
*)

(** Here is out definition of [applyn]: *)
Definition applyn (f : nat -> nat) :=
  fix rec (n : nat) (x : nat) :=
    if n is n'.+1 then rec n' (f x)
    else x.

Check iter.

Definition add1 (n m : nat) : nat := iter n S m.
Definition mul1 (n m : nat) : nat := iter n (add1 m) 0.