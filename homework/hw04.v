(**
Exercises on Generalizing the Induction Hypothesis
https://homes.cs.washington.edu/~jrw12/InductionExercises.html
by James Wilcox (2017)

Adapted to SSReflect syntax and Mathcomp library.
*)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint sum (l : seq nat) : nat :=
  if l is (x :: xs) then x + sum xs
  else 0.

Fixpoint sum_iter' (l : seq nat) (acc : nat) : nat :=
  if l is (x :: xs) then sum_iter' xs (x + acc)
  else acc.

Definition sum_iter (l : seq nat) : nat :=
  sum_iter' l 0.

Lemma sum_iter'_additive l x y: 
  sum_iter' l (x + y) = sum_iter' l x + y.
Proof.
move : x y.
elim l => //= => a l1 Hi x y. rewrite addnA. apply Hi.
Qed.


Lemma sum_iter'_correct l x0 :
  sum_iter' l x0 = x0 + sum l.
Proof.
move: x0.
elim l => /= => x0. by rewrite addn0. 
- move => a Ih x1 => /=. by rewrite Ih addnA (addnC x0 x1). 
Qed.

Theorem sum_iter_correct l :
  sum_iter l = sum l.
Proof.
  by rewrite /sum_iter sum_iter'_correct. 
Qed.


(** Continuation-passing style
    https://en.wikipedia.org/wiki/Continuation-passing_style
 *)
Fixpoint sum_cont' {A} (l : seq nat) (k : nat -> A) : A :=
  if l is (x :: xs) then sum_cont' xs (fun ans => k (x + ans))
  else k 0.

Definition sum_cont (l : seq nat) : nat :=
  sum_cont' l (fun x => x).

Lemma sum_cont'_correct A l (k : nat -> A) :
  sum_cont' l k = k (sum l).
Proof.
move: k.
elim l => //= => a l0 Hi k. by rewrite Hi.
Qed.

Theorem sum_cont_correct l :
  sum_cont l = sum l.
Proof.
by rewrite /sum_cont sum_cont'_correct.
Qed.


Fixpoint rev_rec {A : Type} (xs : seq A) : seq A :=
  if xs is (x::xs') then
    rev_rec xs' ++ [:: x]
  else xs.

Lemma rev_correct A (l1 l2 : seq A) :
  catrev l1 l2 = rev_rec l1 ++ l2.
Proof.
move : l2.
elim l1 => //= => a l Hi l2. 
  by rewrite Hi - catA => /=.
Qed.

Theorem rev_iter_correct A (l : seq A) :
  rev l = rev_rec l.
Proof.
by rewrite /rev rev_correct cats0.
Qed.

Fixpoint map_iter' {A B}
    (f : A -> B) (l : seq A) (acc : seq B) : seq B :=
  if l is (x :: l') then map_iter' f l' (f x :: acc)
  else rev acc.

Definition map_iter {A B} (f : A -> B) l := map_iter' f l [::].

Lemma map_iter'_correct A B (f : A -> B) l1 l2 :
  map_iter' f l1 l2 = rev l2 ++ (map f l1).
Proof.
move : l2.
elim l1 => //=. 
 - by move => l2 ;rewrite cats0.
 - move => a l Hi l2. 
   rewrite Hi - cat1s rev_cat /(rev [:: f a]) => /=. 
   by rewrite - catA cat_cons cat0s.
Qed.

Theorem map_iter_correct A B (f : A -> B) l :
  map_iter f l = map f l.
Proof.
by rewrite /map_iter map_iter'_correct .
Qed.


Inductive expr : Type :=
| Const of nat
| Plus of expr & expr.

Fixpoint eval_expr (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => eval_expr e1 + eval_expr e2
  end.

Fixpoint eval_expr_iter' (e : expr) (acc : nat) : nat :=
  match e with
  | Const n => n + acc
  | Plus e1 e2 => eval_expr_iter' e2 (eval_expr_iter' e1 acc)
  end.

Definition eval_expr_iter e := eval_expr_iter' e 0.

Lemma eval_expr_iter'_correct e acc :
  eval_expr_iter' e acc = acc + eval_expr e.
Proof.
move : acc.
elim e => /=.
  - move => n acc. by rewrite addnC.
  - move => d0 Hi1 e1 Hi2 acc. 
    by rewrite Hi1 Hi2 addnA.
Qed.

Theorem eval_expr_iter_correct e :
  eval_expr_iter e = eval_expr e.
Proof.
by rewrite /eval_expr_iter eval_expr_iter'_correct.
Qed.

Fixpoint eval_expr_cont' {A} (e : expr) (k : nat -> A) : A :=
  match e with
  | Const n => k n
  | Plus e1 e2 => eval_expr_cont' e2 (fun n2 =>
                  eval_expr_cont' e1 (fun n1 => k (n1 + n2)))
  end.

Definition eval_expr_cont (e : expr) : nat :=
  eval_expr_cont' e (fun n => n).

Lemma eval_expr_cont'_correct A e (k : nat -> A) :
  eval_expr_cont' e k = k (eval_expr e).
Proof.
move : k.
elim e => //= => e0 Hi1 e1 Hi2 k.
by rewrite Hi2 Hi1.
Qed.

Theorem eval_expr_cont_correct e :
  eval_expr_cont e = eval_expr e.
Proof.
by rewrite /eval_expr_cont eval_expr_cont'_correct.
Qed.

Inductive instr := Push (n : nat) | Add.

Definition prog := seq instr.

Definition stack := seq nat.

Fixpoint run (p : prog) (s : stack) : stack :=
  if p is (i :: p') then
    let s' :=
        match i with
        | Push n => n :: s
        | Add => if s is (a1 :: a2 :: s') then a2 + a1 :: s'
                 else s
        end
    in
    run p' s'
  else s.

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [:: Push n]
  | Plus e1 e2 => compile e1 ++ compile e2 ++ [:: Add]
  end.

Lemma run_append p1 p2 s :
  run (p1 ++ p2) s = run p2 (run p1 s).
Proof.
move : p2 s.
elim p1 => //=.
Qed.



Lemma compile_correct_generalized e s :
  run (compile e) s = (eval_expr e) :: s.
Proof.
move : s.
elim e => //= => e0 Hi1 e1 Hi2 s.
by rewrite !run_append Hi1 Hi2 /run.
Qed.


Theorem compile_correct e :
  run (compile e) [:: ] = [:: eval_expr e].
Proof.
apply compile_correct_generalized.
Qed.


