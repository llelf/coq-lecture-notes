From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Odd and even numbers *)


Structure odd_nat := Odd {
  oval :> nat;
  oprop : odd oval
}.

(** Prove the main property of [odd_nat] *)
Lemma oddP (n : odd_nat) : odd n.
Proof.
case: n. done.
Qed.

Structure even_nat := Even {
  eval :> nat;
  eprop : ~~ (odd eval)
}.

(* Prove the main property of [even_nat] *)
Lemma evenP (n : even_nat) : ~~ (odd n).
by case: n. Qed.


(** ** Part 1: Arithmetics *)

(* Coercion nat_of_even '(Even n _) := n. *)
(* Coercion nat_of_odd '(Odd n _) := n. *)

Coercion nat_of_even := eval.
Coercion nat_of_odd := oval.


Definition swap {A B} '((x,y) : A*B) := (y,x).
Definition foo '(Even n _ : _) := n.

(** The objective is to make it work: knowing that
    [n] is [odd] Coq should infer that [n * 3]
    is also [odd], and that [6] is even *)
Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. Fail by rewrite oddP evenP. Abort.

(* Let's start by telling Coq that 0 is even *)
Canonical even_0 : even_nat := @Even 0 isT.

Lemma oddS n : ~~ (odd n) -> odd n.+1.
Proof. by rewrite -addn1 odd_add /= addbT. Qed.

Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Proof. by rewrite -addn1 odd_add addbT negbK. Qed.

(** Here we teach Coq that if [m] is even,
    then [m.+1] is [odd] *)

Canonical odd_even (m : even_nat) : odd_nat :=
  @Odd m.+1 (oddS (eprop m)).


(** Implement the dual, teach Coq that if [m]
    is [odd] then [m.+1] is [even] *)

Canonical even_odd (m : odd_nat) : even_nat :=
  @Even m.+1 (evenS (oprop m)).


(** Now let's deal with multiplication *)
Lemma odd_mulP (n m : odd_nat) : odd (n * m).
Proof.
(* have [n' odd_n] := n. *)
(* have [m' odd_m] := m. *)

(* (oprop n) (oprop m). *)
by rewrite odd_mul !oddP. 
Qed.


(** Teach Coq that [*] preserves being [odd] *)
Canonical oddmul_Odd (n m : odd_nat) : odd_nat :=
  @Odd (n*m) (odd_mulP n m).


(* It should work now! *)
Example test_odd (n : odd_nat) :
  ~~ (odd 6) && odd (n * 3).
Proof. by rewrite oddP evenP. Qed.


(** ** Part 2: Equality *)

(** We can't use [==] on [odd] natural numbers because
   [odd_nat] is not an [eqType] *)
Fail Check forall n : odd_nat, n == n.

(** Use the [subType] machinery in order
   to teach Coq that [odd_nat] is an [eqType] *)

Canonical odd_subType := [subType for nat_of_odd].
Definition odd_eqMixin := [eqMixin of odd_nat by <:].
Canonical odd_eqType := EqType odd_nat odd_eqMixin.
(* Canonical odd_eqType := [eqType of _ for _  ]. *)

Canonical even_subType := [subType for nat_of_even].
Definition even_eqMixin := [eqMixin of even_nat by <:].
Canonical even_eqType := EqType even_nat even_eqMixin.


(* This should work now *)
Check forall n : odd_nat, n == n.
Lemma odd_nat_eq_refl (n : odd_nat): n == n.
Proof. by rewrite eq_refl. Qed.

(** Now deal with [even_nat] *)
Check forall (m : even_nat), m == m.

Check forall (m : even_nat), m == m.

Lemma even_nat_eq_refl (n : even_nat): n == n.
Proof. by rewrite eq_refl. Qed.

