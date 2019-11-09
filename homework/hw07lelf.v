From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From QuickChick Require Import QuickChick.
Set Bullet Behavior "None".
From Hammer Require Import Hammer Reconstr.




(** Properties of arbitrary binary relations (not necessarily decidable) *)
(** A functional or deterministic relation *)
Definition functional {X : Type} (R : X -> X -> Prop) : Prop :=
  forall (s s1 s2 : X), R s s1 -> R s s2 -> s1 = s2.

Lemma func1 :
  functional (fun x y => x.*2 == y).
Proof.
by move=> s s1 s2 /eqP <- /eqP <-.
Qed.


Lemma func2 :
  ~ functional (fun x y => (x.*2 == y) || ((x, y) == (0,1))).
Proof.
by move/(_ 0 0 1 isT erefl).
Qed.




(** Define a notation such that {In C, functional R} restricts the domain of the relation like so:

  forall (s s1 s2 : X), C s -> R s s1 -> R s s2 -> s1 = s2

And prove the following lemma:
*)



Notation "{ 'In' C , 'functional' R }" :=
  (forall X (s s1 s2 : X), C s -> R s s1 -> R s s2 -> s1 = s2) (at level 0).

(* Lemma func3 : *)
(*   {In (fun n => 0 < n), functional (fun x y => (x.*2 == y) || ((x, y) == (0,1)))}. *)




Goal forall (X:Type) U (x: X) (F: X->Prop), U. intros* x.

move/(_ x). Undo.
move=> XP. move/XP: (x).
Abort.


Lemma impl_trans B A C :
  (A -> B) -> (B -> C) -> (A -> C).
Proof. exact: catcomp.
Restart.
 by move=> ab bc /ab/bc.
Qed.

Goal forall A B C, (B->C) -> (A->C) -> (A->B).
intros*bc.
(* move=> a. apply: H. move: a. *)
intros ac a.
 apply: catcomp a.

Abort.


Goal forall P A B, (P -> A=B) -> P -> A-B=0.
move=> P A B W. (* /apply ->. *)

(* move/W->. *)
move=> p; rewrite W => // ; move: p.

Abort.



(* prove without using [case] or [elim] tactics *)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.

have N3: forall a, a || ~~a by exact: orbN.

rewrite !implybE.
rewrite negb_or. rewrite negbK.
rewrite andb_orl andb.


(* apply/implyP.  *)


(* move/implyP. *)


(* move=> /implyP PQP.  *)
(* apply: (PQP). *)
(* apply/implyP. *)


(* rewrite -implybNN => H. *)

(* rewrite !implybE. *)


(* apply/orP. *)
(* apply/negP. *)




(*  move/implyP => H. *)

(*  apply: (H). apply/implyP. *)
Admitted.



(* prove without using [case] or [elim] tactics *)
Lemma addb_neq12 p q :  ~~ p = q -> p (+) q.
by move/addbP.
Qed.

Lemma div_fact_plus1 m p : 1 < p -> p %| m `! + 1 -> m < p.
Proof.
elim: m p=>[|m I] p. rewrite fact0. move=> P1 _. exact: ltn_trans P1.
move=> p1.
rewrite factS.
move /(@dvdn_add_eq _ _ 1). rewrite dvdn1.
move: p1. rewrite ltn_neqAle. move/andP=>[]+_.
move/negPf. rewrite eq_sym=> ->.

Admitted.



(* Prove [8x = 6y + 1] has no solutions in [nat] *)
Lemma no_solution x y :
  8*x != 6*y + 1.
Proof.
apply/eqP. move/(congr1 odd). by rewrite !(odd_mul,odd_add).
Qed.


Lemma iota_add m n1 n2 :
  iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Proof.
elim: n1 m => /= [|n1 I] m. by rewrite add0n addn0.
(* rewrite -addnE. *)
by rewrite I addSnnS.
Qed.




Definition mysum m n F := (foldr (fun i a => F i + a) 0 (iota m (n - m))).

(* "big" operator *)
Notation "\mysum_ ( m <= i < n ) F" := (mysum m n (fun i => F))
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \mysum_ ( m  <=  i  <  n ) '/  '  F ']'").


Corollary mysum_rr z ls (F:nat->nat) :
  foldr (fun i a => F i + a) z ls = z + foldr (fun i a => F i + a) 0 ls.
Proof.
elim: ls=> /= [|a ls I]; first by rewrite addn0.
by rewrite I addnCA.
Qed.



Lemma mysum_recl m n F :
  m <= n ->
  \mysum_(m <= i < n.+1) F i = \mysum_(m <= i < n) F i + F n.
Proof.
rewrite/mysum => MN.
rewrite subSn//.
rewrite -addn1 iota_add /= subnKC//.
rewrite foldr_cat/= addn0 addnC.

elim: iota => /= [|a ls I]; first by rewrite addn0.
by rewrite I addnCA.
Qed.



Lemma sum_odds n :
  \mysum_(0 <= i < n) (2 * i + 1) = n ^ 2.
Proof.

elim: n=> //= n.
rewrite !multE !plusE.

rewrite mysum_recl// => ->.
rewrite !muln1 -[n.+1]addn1 -[(n+_).+1]addn1.
rewrite mulnDr muln1.
rewrite [n+_]addnA. rewrite addnC.
rewrite -[n+_+n]addnAC. rewrite addnn mul2n.
rewrite addnAC.
done.

Qed.

