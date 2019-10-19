From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section LeftPad.

(**
What is "leftpad"?

Leftpad is a function that takes a character, a length, and a string, and pads the string to that length.
It pads it by adding the character to the left.

Compute leftpad 0 5 [:: 1; 2; 3]. (* = [:: 0; 0; 1; 2; 3] *)
Compute leftpad 0 2 [:: 1; 2; 3]. (* = [:: 1; 2; 3]  *)
*)


(* [def] is the default value, i.e. type T is not empty *)
Variables (T : Type) (def : T).

(** Define the leftpad function, modeling strings as sequences of elements of type [T] *)

Locate "++".
About ncons.

Compute (nseq 3 5 ++ nseq 2 6).

Definition leftpad (c : T) (n : nat) (s : seq T) : seq T :=
  ncons (n - size s) c s.
  

Search "addnC".

(** The following properties of the leftpad function *)

Lemma length_max_spec c n s :
  size (leftpad c n s) = maxn n (size s).
Proof.
  by rewrite size_ncons maxnC maxnE addnC.
Qed.




(** Local alias for the [nth] function returning the n-th element of the input sequence *)
Local Notation nth := (nth def).

Search "nth".

Lemma prefix_spec c n s :
  forall i, i < n - size s -> nth (leftpad c n s) i = c.
Proof.
move => m Ihm. by rewrite nth_ncons Ihm.
Qed.

Search "lt" "add".

Lemma suffix_spec c n s :
  forall i, i < size s -> nth (leftpad c n s) (n - size s + i) = nth s i.
Proof.
move => i Ihm. rewrite nth_ncons.  
               have : ((n - size s) + 0 = (n - size s)) . 
               by rewrite addn0. move => Ihs. 
               rewrite <- Ihs at 2.
               rewrite ltn_add2l.
               simpl.
               have: (n - size s + i - (n - size s)) = i.
               by rewrite addKn.
               move => Ihi.
               by rewrite Ihi.
Qed.

End LeftPad.
(* = [:: 1; 2; 3]  *)


Section MoreInductionExercises.

(** Implement a recursive function performing integer division by 2 *)
Fixpoint div2 (n : nat) : nat := 
  if n is m.+1.+1 then (div2 m).+1 else 0. 
(* You might want to uncomment the following: *)
Arguments div2 : simpl nomatch.

Lemma nat_ind2' (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+2) ->
  forall n, P n.
Proof.
Admitted.

Lemma div2_le n : div2 n <= n.
Proof.
Admitted.

Lemma div2_correct n :
  div2 n = n./2.
Proof.
Admitted.



(** Strong induction principle *)
Lemma lt_wf_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, (k < m) -> P k) -> P m) ->
  forall n, P n.
Proof.
Admitted.


Fixpoint divn_my (n m : nat) {struct n} : nat :=
  if m is m'.+1 then
    if n - m' is d.+1 then
      (divn_my d m).+1
    else 0
  else 0.

Lemma divn_my_correct n m :
  divn_my n m = divn n m.
Proof.
Admitted.




Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.
Arguments fib n : simpl nomatch.

Lemma fib3 n :
  fib (3*n).+1 = (fib n.+1)^3 + 3 * fib n.+1 * (fib n)^2 - (fib n)^3.
Proof.
Admitted.

End MoreInductionExercises.


