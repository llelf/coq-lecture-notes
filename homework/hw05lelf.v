From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Hammer Require Import Hammer Reconstr.

Section BooleanReflection.

(** A spec for boolean equality *)
Variant eq_xor_neq (T : eqType) (x y : T) : bool -> bool -> Set :=
  | EqNotNeq of x = y : eq_xor_neq x y true true
  | NeqNotEq of x != y : eq_xor_neq x y false false.

(* Unset Maximal Implicit Insertion. *)
(* Arguments eqP [T x y]. *)

Lemma eqVneq (T : eqType) (x y : T) :
  eq_xor_neq x y (y == x) (x == y).
Proof.

case XY: (x==y); case YX: (y==x).
 constructor. apply/eqP. done.
 move/eqP: YX. move/eqP: XY.  move->. done.
 move/eqP: XY. move/eqP: YX.  move->. done.
 constructor. move/eqP: XY.
Restart.
(* rewrite eq_sym. *)
(* case: eqP. constructor.  Undo. *)
(* case: (@eqP _ x y). *)
Abort.

(* Use eqVneq to prove the following lemma.
   Hint: use [case: eqVneq] *)
Lemma eqVneq_example (T : eqType) (w x y z : T) :
  w == x -> z == y ->
  (x == w) /\ (y == z) /\ (z == y).
Proof.
by do 2 move/eqP->.
Qed.



Lemma andX (a b : bool) : reflect (a * b) (a && b).
Proof.
by case: a; case: b; constructor=> //; case.
Qed.


Arguments andX {a b}.

(** Solve the following lemma using [andX] lemma
    and [rewrite] tactic *)
Lemma andX_example a b :
  a && b -> b && a && a && b.
Proof.                                   (* LELF WHY ANDX???  *)
rewrite [b&&a]andbC -andbA.
move->. done.
Qed.

(* one can rewrite with andX *)

End BooleanReflection.


Section RecursionSchemes.




Lemma foldr_fusion {A B C} (f : A -> B -> B) (v : B)
      (g : A -> C -> C) (w : C) (h : C -> B) :
  h w = v ->
  (forall x y, h (g x y) = f x (h y)) ->
  (h \o foldr g w) =1 foldr f v.
Proof.
move=> HW HG x.
by elim: x => //= a l; rewrite HG => ->.  (* apply: congr1. *)
Qed.

Definition flip {A B C} (f : A -> B -> C) := fun x y => f y x.

(* Variables (a b c x0 : nat) (Φ: nat->nat->nat). *)
(* Eval simpl in sumn [::a;b;c]. *)

Goal forall T (s: seq T), s = [::] <-> (nilp s).
intros.
apply: rwP. apply: nilP.
Qed.


Lemma foldl_rev' T R (f : R -> T -> R) (z : R) (s : seq T) :
  foldl f z (rev s) = foldr (fun x => f^~ x) z s.
exact: foldl_rev. Qed.

Lemma foldr_rev T R (f : T -> R -> R) (z : R) (s : seq T) :
  foldr f z (rev s) = foldl (fun x => f^~ x) z s.
by rewrite -[s in RHS]revK foldl_rev.
Qed.


Lemma foldl_cat T R (f: R->T->R) z s1 s2 : foldl f z (s1 ++ s2) = foldl f (foldl f z s1) s2.
Proof.
elim: s1 z => //=.
Qed.




Lemma foldl_via_foldr A B (f : B -> A -> B) :
  flip (foldr (fun x rec => rec \o (flip f x)) id) =2 foldl f.
  (* (flip \o foldr (fun x rec => rec \o (flip f x))) id =2 foldl f. *)
  (* forall x0,  *)
  (*   flip (foldr (fun x rec => rec \o (flip f x)) id) x0 =1 foldl f x0. *)
  (* forall x0 s,  *)
  (*   foldr (fun x rec => rec \o (flip f x)) id ^~ x0 s = foldl f x0 s. *)
  (* forall x0 s,  *)
  (*   foldr (fun x rec => rec \o (f^~ x)) id s x0 = foldl f x0 s. *)
  (* forall x0 s,  *)
  (*   foldr (fun x rec => rec \o (f^~ x)) id s x0 = foldl f x0 s. *)
  (* forall x0 s,  *)
  (*   foldr (fun x rec a => rec (f a x)) id s x0 = foldl f x0 s. *)
Proof.
move=> x0 s.
rewrite /flip.
elim: s x0 => //=.
Qed.



Lemma foldl_via_foldr2 {A B} (f : B -> A -> B) v :
  (foldr (flip f) v) \o rev =1 foldl f v.
Proof.
move=> s.
by rewrite/comp -foldl_rev revK.
Qed.

(* Let's generalize left and right folds over lists.
   We do that by factoring out the recursive call.
   So, instead of the combining function of type
   A -> B -> B we use
   A -> B -> (B -> B) -> B,
   where (B -> B) represents the recursive calls.
   See a couple of lemmas below explaining how it works.
   *)
Definition foldk {A B : Type} (f : A -> B -> (B -> B) -> B) :=
  fix rec (acc : B) (xs : list A) :=
    if xs is x :: xs' then
      f x acc (fun acc2 => rec acc2 xs')
    else acc.
(* The "k" suffix suggests "continuation" here *)

Lemma foldr_via_foldk A B (f : A -> B -> B) :
  foldk (fun a b k => f a (k b)) =2 foldr f.
Proof.
move=> x₀. elim=> //= a s. exact: congr1.
Qed.

Lemma foldl_via_foldk A B (f : B -> A -> B) :
  foldk (fun a b k => k (f b a)) =2 foldl f.
Proof.
move=> x₀. by elim.
Qed.


End RecursionSchemes.



Section IntLogic.

(* Prove that having a general fixed-point combinator in Coq
   would be incosistent *)
Definition FIX := forall A : Type, (A -> A) -> A.

Lemma not_fix :
  FIX -> False.
Proof. by move/(_ False id). Qed.


End IntLogic.


