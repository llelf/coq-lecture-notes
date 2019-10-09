From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Coq Require Import Omega Lia.
From Hammer Require Import Hammer Reconstr.
From QuickChick Require Import QuickChick Tactics.
Set Bullet Behavior "None".


Section InductionExercises.

Fixpoint triple (n : nat) : nat :=
  if n is n'.+1 then (triple n').+3
  else n.

Lemma triple_mul3 n :
  triple n = 3 * n.
Proof.
by elim: n=> //= n ->; rewrite mulnS.
Restart.
elim: n=> //= n ->. rewrite mulnS. done.

Qed.

Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.

elim: m n=> [| m IHm] [] => //.
move=> n.
do 2!rewrite addSn addnC addSn.
case.
move=> H. f_equal. apply IHm. done.
Qed.





(** Write a tail-recursive variation of the [addn] function
    (let's call it [addn_iter]). *)
Fixpoint add_iter (n m : nat) {struct n}: nat :=
  if n is S n' then add_iter n' m.+1 else m.

Lemma add_iter_correct m n :
  add_iter m n = m + n.
Proof.
by elim: m n => [|m Im] n //=; rewrite Im addnC !addSn addnC.
Qed.




Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.
Arguments fib n : simpl nomatch.


Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Proof.
(* Hint Rewrite subn_eq0. *)
(* Hint Resolve leq0n. *)
(* Hint Rewrite leq_subLR. *)

move/leP=> H. apply /leP. rewrite -plusE. lia.
Restart.
----Restart.
by move/(leq_add (leq0n _)); apply.
----Restart.
by move/(leq_add (leq0n p)) ->.
Qed.




Lemma fib_monotone m n :
  m <= n -> fib m <= fib n.
Proof with auto.

elim: n. by case: m.
elim.
simpl.
case: m... case...

move=> /= n I' I.

rewrite leq_eqVlt => /orP.
case.
move/eqP->. done.
move/I. apply: leq_add1l.

Restart.

elim: n. by case: m.
elim.
simpl.
case: m => //; case => //.

rewrite/fib. 

move=> /= n I' I.

rewrite leq_eqVlt => /orP.
case.
move/eqP->. done.
move/I. apply: leq_add1l.


(* Restart. *)

(* elim: n m=> [|n I] m. by case: m. *)
(* elim. *)
(* simpl. case: m. done. *)

(* move=> /= n'.  *)
(* rewrite leq_eqVlt. => /orP. *)
(* case. *)
(* move/eqP->. done. *)



Restart.



------Restart.

elim: n=> [|[|n] IHn]; first by case: m.
- by case: {IHn}m=> [|[]].
rewrite /= leq_eqVlt => /orP[/eqP->// | /IHn].
by apply: leq_add1l.
Qed.






Goal forall n, fib (0 + n.+1).+1 = fib 1 * fib n.+2 + fib 0 * fib n.+1.
cbn. move=> n.
autorewrite with yhints.
trivial.
Qed.


Lemma fib_add_succ m n :
  fib (m + n).+1 = fib m.+1 * fib n.+1 + fib m * fib n.
Proof.


  (* 


  IHm : forall n : nat,
        fib (m + n).+1 = fib m.+1 * fib n.+1 + fib m * fib n
  n : nat
  ============================
  fib (m + n.+1)%Nrec + fib (m.+1 + n.+1) =
  (fib m + fib m.+1) * (fib n + fib n.+1) + fib m.+1 * fib n.+1

A m : nat
  IHm : forall n : nat,
        fib (m + n).+1 = fib m.+1 * fib n.+1 + fib m * fib n
  ============================
  forall n : nat,
  fib (m + n.+1) + (fib m.+1 * (fib n + fib n.+1) + fib m * fib n.+1) =
  (fib m + fib m.+1) * (fib n + fib n.+1) + fib m.+1 * fib n.+1

  m : nat
  IHm : forall n : nat,
        fib (m + n).+1 = fib m.+1 * fib n.+1 + fib m * fib n
  n : nat
  ============================
  fib (m.+1 + n.+1).+1 = fib m.+2 * fib n.+2 + fib m.+1 * fib n.+1



 *)

elim: m n=> [|m IHm] [//|n]; try by rewrite ?muln0 !addn0 ?mul1n ?muln1.
rewrite addSn /= IHm addnS IHm /= -!plusE -!multE; lia.


--------Restart.
elim: m n=> [|m IHm] [//|n] .
- by rewrite addn0 mul1n. 
- by rewrite muln0 !addn0 muln1.
rewrite addSn /= IHm addnS IHm /=.
rewrite -!plusE -!multE; lia.


--------Restart.
elim: m n=> [|m IHm] [|n] //. 
- by rewrite addn0 mul1n. 
- by rewrite muln0 !addn0 muln1.

rewrite addSn /= IHm addnS IHm /=.
rewrite -!plusE -!multE; lia.


--------Restart.
elim: m n=> [|m IHm] n; first by rewrite mul1n addn0.
rewrite addSn /= IHm.
case: n=> [|n].
- by rewrite !muln0 !addn0 !muln1.
rewrite addnS {}IHm /= mulnDl !mulnDr !addnA.
rewrite -!plusE; omega.
Qed.


End InductionExercises.


(* Thanks to Mike Potanin for pointing me to this example *)
(* https://en.wikipedia.org/wiki/Eckmann–Hilton_argument *)

Section EckmannHilton.

Context {X : Type}.
Variables f1 f2 : X -> X -> X.

Variable e1 : X.
Hypothesis U1 : left_id e1 f1 * right_id e1 f1.

Variables e2 : X.
Hypothesis U2 : left_id e2 f2 * right_id e2 f2.

Hypothesis I : interchange f1 f2.

Lemma units_same :
  e1 = e2.
Proof.
move: I. clear I. rewrite/interchange => I.
move: U1 U2. clear U1 U2. rewrite/left_id/right_id => U1 U2.
move: (I e1 e2 e2 e1).
rewrite ?U1 ?U2 ?U1.
done.
Qed.

Lemma operations_equal :
  f1 =2 f2.
Proof. by move=> a b; move: (I a e1 e1 b); rewrite !U1 units_same !U2. Qed.

Lemma I1 : interchange f1 f1.
Proof. by move=> a b c d; move: (I a b c d); rewrite -!operations_equal. Qed.

Lemma operations_comm :
  commutative f1.
Proof. by move=> a b; move: (I1 e1 a b e1); rewrite !U1. Qed.

Lemma operations_assoc :
  associative f1.
Proof. by move=> a b c; move: (I1 a e1 b c); rewrite !U1. Qed.

End EckmannHilton.
