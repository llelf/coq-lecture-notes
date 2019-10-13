From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Hammer Require Import Hammer.


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
(*
Fixpoint leftpad' (c : T) (n : nat) (s : seq T) (r : seq T) : seq T :=
  if n is n'.+1 then
    if s is a::s'
    then leftpad' c n' s' (a::r)
    else c :: leftpad' c n' nil r
  else rev r.

Definition leftpad_1 (c : T) (n : nat) (s : seq T) : seq T :=
  leftpad' c n s nil.
*)

Definition leftpad (c : T) (n : nat) (s : seq T) : seq T :=
  ncons (n - size s) c s.



(** The following properties of the leftpad function *)

Lemma length_max_spec c n s :
  size (leftpad c n s) = maxn n (size s).
Proof.
by rewrite maxnC maxnE size_ncons addnC.
Qed.

(** Local alias for the [nth] function returning the n-th element of the input sequence *)
Local Notation nth := (nth def).

Lemma prefix_spec c n s :
  forall i, i < n - size s -> nth (leftpad c n s) i = c.
Proof.
move=> i. 
by rewrite nth_ncons => ->.
(* by case: ltngtP. *)
Qed.

Lemma suffix_spec c n s :
  forall i, i < size s -> nth (leftpad c n s) (n - size s + i) = nth s i.
Proof.
move=> i _.
by rewrite nth_ncons addKn ifN // -leqNgt leq_addr.
Qed.




Goal forall x y, x + y < x = false.
Proof.
move=> x y.
by rewrite ltnNge leq_addr.
Undo.
by rewrite -{2}[x]addn0 ltn_add2l.
Undo.
rewrite/leq subSn addnC. rewrite addnK. done. exact: leq_addl.
Qed.



End LeftPad.

Compute ncons 3 0 [:: 1].



Section MoreInductionExercises.

(** Implement a recursive function performing integer division by 2 *)
Fixpoint div2 (n : nat) : nat :=
  if n is n.+2 then (div2 n).+1 else 0.


Check erefl : div2 42 = 21.
Check erefl : div2 41 = 20.

(* You might want to uncomment the following: *)
Arguments div2 : simpl nomatch.



From mathcomp Require Import eqtype.



Definition nat_ind2'' (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+2) ->
  forall n, P n
 :=
  fun p0 p1 step => fix loop n :=
    match n with
    | n'.+2 => step n' (loop n')
    | 1 => p1
    | 0 => p0
    end.



Lemma nat_ind2' (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+2) ->
  forall n, P n.
Proof.
intros.
enough (P n /\ P (S n)) by easy.
induction n.
- easy.
destruct IHn; split.
- assumption. 
- now apply H1.
*********** Restart.
move=> p0 p1 step; fix nat_ind2' 1.
case=> [|[|n]]; [ exact: p0 | exact: p1 | exact: step (nat_ind2' n) ].
*********** Restart.
move=> p0 p1 step; fix nat_ind2' 1.
case=> [|[|n]]; [ exact: p0 | exact: p1 | apply: step; exact: nat_ind2' ].
*********** Restart.
move=> p0 p1 step n.
suff: P n /\ P n.+1 by case.
elim: n=> // n [IHn1 IHn2].
split=> //.
by apply: step.
*********** Restart.
move=> ? ? step n.
suffices: P n /\ P n.+1 by case.
elim: n => // ? [].
split => //.
by apply: step.
*********** Restart.
move=> ? ? step n.
suff: P n /\ P n.+1 by case.
by elim: n=> // ? [ /step ].
Qed.




Lemma div2_le n : div2 n <= n.
Proof.
elim/nat_ind2': n => //= n I. exact: leqW.
Qed.

Lemma div2_correct n :
  div2 n = n./2.
Proof.
elim/nat_ind2': n => //= n I. exact: eq_S.
Qed.



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


