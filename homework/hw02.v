From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section IntLogic.

Variables A B C : Prop.

Lemma notTrue_iff_False : (~ True) <-> False.
Proof.
split => //.
Qed.

Lemma dne_False : ~ ~ False -> False.
Proof.
by move => f; apply f.
Qed.
(* dne_False = @^~ id *)

Lemma dne_True : ~ ~ True -> True. 
Proof.
by move => _.
Qed.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
move => abaa. apply abaa => aba. apply aba => a. by apply abaa.
Qed.


Lemma imp_trans : (A -> B) -> (B -> C) -> (A -> C).
Proof.
move => ab bc a. by apply bc, ab.
Qed. 
End IntLogic.


(** Let's familiarize ourselves with some lemmas from [ssrbool] module.
    The proofs are very easy, so the lemma statements are more important here.
 *)
Section BooleanLogic.

Variables (A B : Type) (x : A) (f : A -> B) (a b : bool) (vT vF : A).

Lemma negbNE : ~~ ~~ b -> b.
Proof.
by case b.
Qed.

(** Figure out what [involutive] and [injective] mean
    using Coq's interactive queries. Prove the lemmas.
    Hint: to unfold a definition in the goal use [rewrite /definition] command.
*)
Lemma negbK : involutive negb.
Proof.
rewrite /involutive /cancel => c. by case c.
Qed.

Lemma negb_inj : injective negb.
Proof.
rewrite /injective => c d. by case c, d.
Qed.


Lemma ifT : b -> (if b then vT else vF) = vT.
Proof.
by case b.
Qed.

Lemma ifF : b = false -> (if b then vT else vF) = vF.
Proof.
by case b.
Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof.
by case b.
Qed.

Lemma if_neg : (if ~~ b then vT else vF) = if b then vF else vT.
Proof.
by case b.
Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof.
by case b.
Qed.

Lemma if_arg (fT fF : A -> B) :
  (if b then fT else fF) x = if b then fT x else fF x.
Proof.
by case b.
Qed.

Lemma andbK : a && b || a = a.
Proof.
by case a, b.
Qed.


(** Find out what [left_id], [right_id] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma addFb : left_id false addb.    (* [addb] means XOR (eXclusive OR operation) *)
Proof.
rewrite /left_id => c. by case c.
Qed. 

Lemma addbF : right_id false addb.
Proof.
rewrite /right_id => c. by case c.
Qed.

Lemma addbC : commutative addb.
Proof.
rewrite /commutative => c d. by case c, d.
Qed.

Lemma addbA : associative addb.
Proof.
rewrite /associative => c d e. by case c, d, e.
Qed.


(** Formulate analogous laws (left/right identity, commutativity, associativity)
    for boolean AND and OR and proove those.
    Find the names of corresponding lemmas in the standard library using
    [Search] command. For instance: [Search _ andb left_id.]
    Have you noticed the naming patterns?
 *)

End BooleanLogic.



Section NaturalNumbers.
(** Figure out what [cancel], [succn], [predn] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma succnK : cancel succn predn.
Proof.
by rewrite /cancel /predn.
Qed.

Lemma add0n : left_id 0 addn.
Proof.
rewrite /left_id => x. by case x.
Qed.

Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof.
move => //.
Qed.

Lemma add1n n : 1 + n = n.+1.
Proof.
move => //.
Qed.

Lemma add2n m : 2 + m = m.+2.
Proof.
move => //.
Qed.

Lemma subn0 : right_id 0 subn.
Proof.
move => x. by case x.
Qed.

End NaturalNumbers.
