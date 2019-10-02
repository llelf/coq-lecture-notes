From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

Definition Answer := True.  Hint Unfold Answer.
Tactic Notation "would" "be" string(s) := idtac s; auto.


(*** Exercise 1 *)

(** 1a. Define [orb_my] function implementing boolean disjunction *)
Definition orb_my (a b : bool) : bool :=
  if a then true else b.
  (* match a, b with *)
  (* | false, false => false *)
  (* | _, _ => true *)
  (* end. *)



(** 1b. Figure out the implementation of [orb] function in the standard library
        using Coq's interactive query mechanism *)
Print orb.

(** 1c. What's the difference between the standard implementation and
        the following one? *)

Definition orb_table (b c : bool) : bool :=
  match b, c with
  | true,  true  => true
  | true,  false => true
  | false, true  => true
  | false, false => false
  end.

Print orb_table.

Goal Answer. would be
 "only 1 level of match, easier in proofs, more efficient". Qed.

(** Note: the above translates into nested pattern-matching, check this *)


(** 1d. Define [addb_my] function implementing exclusive boolean disjunction.
        {The name [addb] comes from the fact this operation behaves like addition modulo 2}
        If you are already familiar with proofs in Coq, think of a prover friendly
        definition, if you are not -- experiment with how different implementations
        behave under symbolic execution. *)
Definition addb_my (a b : bool) : bool :=
  if a then negb b else b.


Section AddB.
  Variable A B : bool.
  Compute addb_my true B.
  Compute addb_my false B.
  Compute addb_my A true.
  Compute addb_my A false.
End AddB.

(*** Exercise 2 *)

(** 2a. Implement power function of two arguments [x] and [n],
        raising [x] to the power of [n] *)

Fixpoint pown_my (x n : nat) := if n is n'.+1 then x * pown_my x n' else 1.


(*** Exercise 3 *)

(** 3a. Implement division on unary natural numbers *)

Fixpoint divn_my (n m : nat) : nat. Abort.

(* Unit tests: *)
Compute divn_my 0 0.  (* = 0 *)
Compute divn_my 1 0.  (* = 0 *)
Compute divn_my 0 3.  (* = 0 *)
Compute divn_my 1 3.  (* = 0 *)
Compute divn_my 2 3.  (* = 0 *)
Compute divn_my 3 3.  (* = 1 *)
Compute divn_my 8 3.  (* = 2 *)
Compute divn_my 42 1. (* = 42 *)
Compute divn_my 42 2. (* = 21 *)
Compute divn_my 42 3. (* = 14 *)
Compute divn_my 42 4. (* = 10 *)


From mathcomp Require Import div.

(* Fixpoint divn_my2' (a b q : nat) : nat := *)
(*   match a,q with *)
(*   | 0,0 => 1 *)
(*   | 0, S _       => 0 *)
(*   | S a', S q' => divn_my2' a' b q' *)
(*   | S a' as a, O    => 1 + divn_my2' a b b *)
(*   end. *)

(* Definition divn_my2 a b := divn_my2' a b b. *)

(* Compute divn_my2 6 3. *)

Fixpoint subn_my (n m : nat) : nat :=
  match n,m with
  | k.+1, l.+1 => subn_my k l
  | _, _ => n (* LELF if 0 *)
  end.


  (* match a, b with *)
  (* | a'.+1, b'.+1 => subn_my a' b' *)
  (* | a'.+1, 0 => a *)
  (* | 0, _ => 0 *)
  (* end. *)

Fixpoint divn_my' (a b : nat) : nat :=
  match subn a b with
  | a'.+1 => 1 + divn_my' a' b
  | 0 => 0
  end.

Definition divn_my (a b : nat) : nat :=
  if b is b'.+1 then divn_my' a b' else 0.

Definition divn_my2' b := fix loop a r :=
  match subn a b with
  | a'.+1 => loop a' r.+1
  | 0 => r
  end.


Definition divn_my2 (a b : nat) : nat :=
  if b is b'.+1 then divn_my2' b' a 0 else 0.

Definition divn_my3' b := fix loop a :=
  match subn a b with
  | a'.+1 => 1 + loop a'
  | 0 => 0
  end.

Definition divn_my3 (a b : nat) : nat :=
  if b is b'.+1 then divn_my3' b' a else 0.


Print divn_my2'.




(** 3b. Provide several unit tests using [Compute] vernacular command *)
Check erefl : divn_my 2 2 = 1.
Check erefl : divn_my 0 0 = 0.
Check erefl : divn_my 1 0 = 0.
Check erefl : divn_my 0 3 = 0.
Check erefl : divn_my 1 3 = 0.
Check erefl : divn_my 2 3 = 0.
Check erefl : divn_my 3 3 = 1.
Check erefl : divn_my 8 3 = 2.
Check erefl : divn_my 42 1 = 42.
Check erefl : divn_my 42 2 = 21.
Check erefl : divn_my 42 3 = 14.
Check erefl : divn_my 42 4 = 10.



(* From Hammer Require Import Hammer Reconstr. *)
From QuickChick Require QuickChick.



Definition is_divn_ok a b := eqn (divn_my a b) (Nat.div a b).
QuickChick is_divn_ok.

(*
Lemma halp_me : forall a b h,
  (fix loop (m q : nat) :=
     match m - b with
     | 0 => q
     | m'.+1 => loop m' q.+1
     end) a h =
  ((fix loop (m q : nat) :=
      match m - b with
      | 0 => (q, 0)
      | m'.+1 => loop m' q.+1
      end) a h).1.
  elim => //.
Abort.
*)


Lemma divn_ok (a b : nat) : divn_my2 a b =  a %/ b.
Proof.
  rewrite /divn_my2 /divn_my2' /divn /edivn /edivn_rec //=.
  rewrite /Nat.div /Nat.divmod /=.

  case: b => //= b.


  (* move=> ->. *)

  (* rewrite -/edivn_rec. *)
  
(*
  case: a => //=.
  case: (a-b).
  rewrite subn_if_gt.

  elim: b  => //=. elim: a => //=.
  move=> n. rewrite !divn1 add1n => ->. done.
  move=> ->.

  rewrite subn_if_gt.
  rewrite ltnS !subn_if_gt; case: (d <= m) => //. (* le_mn. *)
*)

Abort.  



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


From mathcomp Require Import eqtype.

(* Section Ex4. *)


Definition addn_my (a b : nat) : nat := iter a S b.


Definition is_addn_ok (a b : nat) := eqn (addn_my a b) (a + b).
QuickChick is_addn_ok.


Lemma addn_ok' (a b : nat) : is_addn_ok a b.
Proof.
  by rewrite /is_addn_ok; apply /eqP;
     elim: a => //= => a ->; rewrite addSn.
Qed.


Lemma addn_ok (a b : nat) : addn_my a b = a + b.
Proof.
   by elim: a => //= => a ->; rewrite addSn.
Qed.

Definition muln_my (a b : nat) : nat := iter a (fun x => x+b) 0.

Definition is_muln_ok a b := eqn (addn_my a b) (a + b).
QuickChick is_muln_ok.


Lemma muln_ok (a b : nat) : muln_my a b = a * b.
Proof.
  by elim: a => //= => a ->; rewrite mulSnr.
Qed.


(* End Ex4. *)

