From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section EqType.
Search "eq_sym".

Print eq_sym.
(* Print eq_xor_neq. *)

Lemma eq_sym (T : eqType) (x y : T) :
  (x == y) = (y == x).
Proof.
by apply/eqP/eqP ; move => p ; case p. 
Qed. 
(* ^ Hint: use apply/view1/view2 mechanism *)


(** Define equality type for the following datatype *)
Inductive tri :=
| Yes | No | Maybe.

Definition tri_eq (a b : tri) : bool :=
match a, b with 
  | Yes, Yes  => true
  | No,  No => true
  | Maybe, Maybe => true
  | _, _ => false
end.

Check prod nat tri.

Print Bool.reflect.
Lemma triEqP (a b: tri): reflect (a = b) (tri_eq a b).
Proof.
by case a , b; constructor.
Qed.

Canonical tri_eqType := EqType tri (EqMixin triEqP).


Print Equality.type.


(** This should not fail! *)
Check (1, Yes) == (1, Maybe).

Definition empty_eq (a b : Empty_set) : bool :=
  match a with end.

Lemma empty_eqP (a b : Empty_set) : reflect (a = b) (empty_eq a b).
Proof.
done.
Qed.
(** Define equality type for the [Empty_set] datatype *)
(** This should not fail! *)

Canonical empty_eqType := EqType Empty_set (EqMixin empty_eqP).

Check fun v : Empty_set => (1, v) == (1, v).


Lemma predU1P (T : eqType) (x y : T) (b : bool) :
  reflect (x = y \/ b) ((x == y) || b).
Proof.
case E: (x == y). 
Check idP.
constructor. left. move: E. apply/eqP.
case b ; constructor. 
by right.
case => //. move /eqP. by rewrite E.
Qed.

Variables (A B : eqType) (f : A -> B) (g : B -> A).

Lemma inj_eq : injective f -> forall x y, (f x == f y) = (x == y).
Proof.
move => injf x y. apply/eqP/eqP. by apply injf.
move => e. by case e.
Qed.  

Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof.
move => cfg x y. apply/eqP/eqP.
move => e.
rewrite -(cfg x) -(cfg y). by case e.
move => e. by case e.
Qed.

Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof.
elim: p => //.
Qed.


Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Proof.
apply/idP/idP.

elim: e => //. move => n p . rewrite expnS muln_eq0. 
move/orP. case => m0. by apply/andP.
apply/andP. split => //. move : (p m0). move /andP. case. move -> => //.
move/andP. case. move /eqP -> => pe. rewrite exp0n => //.
Qed.   


Lemma seq_last_notin (s : seq A) x :
        last x s \notin s = (s == [::]).
Proof.
Locate "a \notin b".
Check in_mem.
Print mem_pred.
Print pred.
End EqType.

