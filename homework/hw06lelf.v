From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Hammer Require Import Hammer Reconstr.
From QuickChick Require QuickChick.
Set Bullet Behavior "None".

(** Implement an instance of equality type for the [seq] datatype *)



(** Take apart the following proof: *)
Lemma size_eq0 (T : eqType) (s : seq T) :
  (size s == 0) = (s == [::]).
Proof.
apply/nilP. by case: s.
---Restart.
apply/eqP. by case: s.
---Restart.
by case: s.
---Restart.
exact: (sameP nilP eqP).
Qed.



Lemma filter_all T (a : pred T) s :
  all a (filter a s).
Proof.
elim: s => //= s0 s. case A: (a s0) => //=. by rewrite A.
Qed.

Lemma filter_id T (a : pred T) s :
  filter a (filter a s) = filter a s.
Proof.
elim: s => //= s0 s. case A: (a s0) => //=. by rewrite A => ->.
Qed.

Goal 1 != 2.
apply/ negPf. apply: negPf.
Abort.

Goal 1 == 2 = false.
apply/ idP. apply/idP. apply/idP.
Abort.

Goal 1 == 2 = false.
apply: negPf.
Abort.

Require Import Arith Lia Omega.
From QuickChick Require Import Tactics.


Lemma foo : forall {a b}, a+b = b+a. exact: addnC. Qed.
Fail Check foo : forall {a b}, _ + _ = _ + _.


Section ORB.
Check andbT : forall a, a && true = a.

Variable a : bool.
Eval hnf in a && true = a.
Print andb.
Check orbF : forall a, (if a then true else false) = a.


Lemma andbT' : right_id true andb. exact: orbF. Qed.

Lemma addnC' : commutative addn.
move=>>. by rewrite -> PeanoNat.Nat.add_comm. Qed.

End ORB.



Goal forall n m, n <= m -> n != m.+1.
by move=>> Le; apply/eqP=> nSm; move: Le; rewrite nSm ltnn. -----Restart.
by move=>>; rewrite leqNgt; apply/contraNN; move/eqP->.     -----Restart.
by move=>>; case: ltngtP=>//->; rewrite ltnn.               -----Restart.
move=>>/leP=>Le; apply/eqP; omega.                          -----Restart.
by move=>>; rewrite -ltnS neq_ltn => ->.
Qed.



Lemma all_count T (a : pred T) s :
  all a s = (count a s == size s).
Proof.
elim: s => //= s0 s ->.
case A: (a s0) => //=. rewrite add0n.
have:= count_size a s. move=> H. apply: esym. apply:negPf. move: H.
move=> X. apply/eqP=> Y. move: X. rewrite Y ltnn. done.
Qed.





Lemma all_predI T (a1 a2 : pred T) s :
  all (predI a1 a2) s = all a1 s && all a2 s.
Proof.
  (* apply: (can_inj negbK). *)
  (* rewrite negb_and. *)
  (* rewrite has_predC has_predU. *)

  elim: s => //= a s; case: (a1 _); case: (a2 _) => //=.
  by rewrite andbF.
Qed.




Lemma allP (T : eqType) {a : pred T} {s : seq T} :
  reflect {in s, forall x, a x} (all a s).
(* Hint 1: *)
(* rewrite /prop_in1. *)

(* Hint 2a and 2b: *)
(* Check erefl : 1 \in [:: 3; 2; 1; 0] = true. *)
(* Check erefl : 42 \in [:: 3; 2; 1; 0] = false. *)
Proof.
apply/allPP=> x. exact: idP.

Restart.

rewrite /prop_in1.
elim: s => /= [|s0 s I]; first by left.
apply/(iffP andP).
- case=> A0 All x. rewrite in_cons. move/orP.
  case; by [move/eqP->|apply: I].
move=> A. split. apply: A; exact: mem_head.
apply/I=> x XS. apply: A. rewrite in_cons. apply/orP. by right.
Qed.


Lemma sub_find T (a1 a2 : pred T) s :
  subpred a1 a2 ->
  find a2 s <= find a1 s.
Proof.
elim: s => //= a s I.
rewrite/subpred in I * => SP.
case A1: (a1 a); case A2: (a2 a) => //.
- by move/SP: A1; rewrite A2.
exact: I. (* move/I: SP. *)
Qed.

Lemma take_nseq T n m (x : T) : take n (nseq m x) = nseq (minn n m) x.
Proof.
by elim: m n => //= m + [//|n]; rewrite minnSS => ->.
Restart.
by elim: m n => //= m I [//|n]; rewrite minnSS I.
Qed.



Lemma rev_nseq A n (x : A) : rev (nseq n x) = nseq n x.
Proof.
elim: n => //= n.
rewrite rev_cons => ->.
elim: n => //= n ->.
done.
Qed.


(* Hint: use mapP *)
Lemma mem_map (T1 T2 : eqType) (f : T1 -> T2) x s :
  injective f ->
  (f x \in map f s) = (x \in s).
Proof.
move=> Inj. apply/mapP.
case XS: (x \in s). by exists x.
case=> x' + /Inj XX'. by rewrite -XX' XS.
Qed.


(* Double induction principle *)
Lemma seq_ind2 {S T} (P : seq S -> seq T -> Type) :
    P [::] [::] ->
    (forall x y s t, size s = size t -> P s t -> P (x :: s) (y :: t)) ->
  forall s t, size s = size t -> P s t.
Proof.
move=> Pnil Pcons.
elim=> [t|a l I t]; first by move/esym/size0nil->.
case: t => //= b t [SS].
by apply/Pcons/I.
----Restart.
move=> Pnil Pcons.
elim=> [|a l I] [|b t] //= [SS]. by apply/Pcons/I.
Qed.


(* Hint: use seq_ind2 to prove the following *)
Lemma rev_zip S T (s : seq S) (t : seq T) :
  size s = size t -> rev (zip s t) = zip (rev s) (rev t).
move: s t.
apply: seq_ind2 => //= s0 t0 s' t' SS I.
rewrite !rev_cons zip_rcons. rewrite I//. rewrite !size_rev//.
----Restart.
move: s t; apply: seq_ind2 => //= x y s t eq_sz IHs.
by rewrite !rev_cons IHs zip_rcons ?size_rev.
Qed.




Lemma last_ind T (P : seq T -> Prop) :
  P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
Proof.
move=> Pnil Pstep s. rewrite -[s]cat0s.
elim: s [::] Pnil => [|a l IH] l' Pl'; first by rewrite cats0.
by rewrite -cat_rcons; apply/IH/Pstep.
Qed.


Lemma nm0 m n : n<m -> 0<m. elim: m => //. Qed.


Lemma leqS' m n q : q<m ->  m - n.+1 < m.
move=> H.  rewrite -{2}(subn0 m). apply: ltn_sub2l.
- apply: nm0 H.
done.
Qed.

Lemma leqS m n : 0<m -> m - n.+1 < m.
exact: leqS'. Restart.
move=> H.  rewrite -{2}(subn0 m). exact: ltn_sub2l.
(* Restart. move=> H. *)

(* rewrite subnSK. apply: leq_subr.  *)

(* move=> H. *)
(* (* rewrite -[m - n.+1 < m]/( (m - n.+1).+1 < m.+1 ). *) *)
(* rewrite subnSK. apply: leq_subr. give_up. *)
Qed.

(* axiom nosmt lez_addl (x y : int) : (x <= x + y) = (0 <= y). *)
(* axiom nosmt lez_addr (x y : int) : (x <= y + x) = (0 <= y). *)

(* axiom nosmt ltz_addl (x y : int) : (x < x + y) = (0 < y). *)
(* axiom nosmt ltz_addr (x y : int) : (x < y + x) = (0 < y). *)

(* leq_addr : forall m n : nat, n <= n + m. *)
(* ltn_addr : forall m n p : nat, m < n -> m < n + p *)
(* Lemma leq_addr' : forall m n : nat, n <= n + m *)




Lemma nth_rcons_last T (x0 a: T) (s: seq T) :
  nth x0 (rcons s a) (size s) = a.
Proof. by elim: s. Qed.

(* Hint: use last_ind to prove the following *)
Lemma nth_rev T (x0 : T) n (s : seq T) :
  n < size s -> nth x0 (rev s) n = nth x0 s (size s - n.+1).
Proof.
elim/last_ind: s n => // s a E n.
rewrite size_rcons subSS. 
case: n => [|n].
move=>_. rewrite subn0.
rewrite nth0 rev_rcons /=.
by rewrite nth_rcons_last.

simpl.
rewrite -[_<_]/(n < _) => I.

rewrite rev_rcons/=. rewrite E//.
rewrite nth_rcons.
have: size s - n.+1 < size s by rewrite subnSK//; exact: leq_subr.
by move->.

(* apply/ltP. rewrite -minusE. move/ltP: I. lia. *)

Qed.

