From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section IntLogic.

Variables A B C : Prop.

Lemma notTrue_iff_False : (~ True) <-> False.
Proof. done. Qed.

(* Set Printing Coercions. *)
(* Goal true -> true. Print Coercions. *)


Lemma dne_False : ~ ~ False -> False.
(* dne_False = @^~ id *)
Proof. exact. Qed.


Lemma dne_True : ~ ~ True -> True.
Proof. done. Qed.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
move=> H. apply: (H). (* have:= H. *)
apply.
move=> ?. apply: H.
done.
Qed.

Lemma imp_trans : (A -> B) -> (B -> C) -> (A -> C).
Proof.
move=> X Y a. apply: Y (X a).
Qed.

End IntLogic.


(** Let's familiarize ourselves with some lemmas from [ssrbool] module.
    The proofs are very easy, so the lemma statements are more important here.
 *)
Section BooleanLogic.

Variables (A B : Type) (x : A) (f : A -> B) (a b : bool) (vT vF : A).

Lemma negbNE : ~~ ~~ b -> b.
Proof.
by case: b.
Qed.

(** Figure out what [involutive] and [injective] mean
    using Coq's interactive queries. Prove the lemmas.
    Hint: to unfold a definition in the goal use [rewrite /definition] command.
*)
Lemma negbK : involutive negb.
Proof. by case. Qed.

Lemma negb_inj : injective negb.
Proof. by case; case. Qed.

Lemma ifT : b -> (if b then vT else vF) = vT.
Proof. by move->. Qed.

Lemma ifF : b = false -> (if b then vT else vF) = vF.
Proof. by move->. Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof. by case: b. Qed.

Lemma if_neg : (if ~~ b then vT else vF) = if b then vF else vT.
Proof. by case: b. Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof. by case: b. Qed.

Lemma if_arg (fT fF : A -> B) :
  (if b then fT else fF) x = if b then fT x else fF x.
Proof. by case: b. Qed.

Lemma andbK : a && b || a = a.
Proof. by case: a; case: b. Qed.

(** Find out what [left_id], [right_id] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma addFb : left_id false addb.    (* [addb] means XOR (eXclusive OR operation) *)
Proof. done. Qed.

Lemma addbF : right_id false addb.
Proof. by case. Qed.

Lemma addbC : commutative addb.
Proof. by case; case. Qed.

Lemma addbA : associative addb.
Proof. by case; case; case. Qed.


(** Formulate analogous laws (left/right identity, commutativity, associativity)
    for boolean AND and OR and proove those.
    Find the names of corresponding lemmas in the standard library using
    [Search] command. For instance: [Search _ andb left_id.]
    Have you noticed the naming patterns?
 *)

Lemma andTb : left_id true andb. done. Qed.
Lemma andbT : right_id true andb. by case. Qed.
Lemma andbC : commutative andb. by case; case. Qed.
Lemma andbA : associative andb. by case; case; case. Qed.

Lemma orFb : left_id false orb. done. Qed.
Lemma orbF : right_id false orb. by case. Qed.
Lemma orbC : commutative orb. by case; case. Qed.
Lemma orbA : associative orb. by case; case; case. Qed.

End BooleanLogic.



Section NaturalNumbers.
(** Figure out what [cancel], [succn], [predn] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma succnK : cancel succn predn.
Proof. rewrite/cancel. done. Qed.

Lemma add0n : left_id 0 addn.
Proof. done. Qed.

Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof. done. Qed.

Lemma add1n n : 1 + n = n.+1.
Proof. done. Qed.

Lemma add2n m : 2 + m = m.+2.
Proof. done. Qed.

Lemma subn0 : right_id 0 subn.
Proof. rewrite/right_id. by case. Qed.

End NaturalNumbers.
