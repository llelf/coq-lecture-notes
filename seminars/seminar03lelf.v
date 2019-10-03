From Hammer Require Import Hammer Reconstr.
(* From QuickChick Require QuickChick. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "None".

Section IntLogic.

(* Frobenius rule: existential quantifiers and conjunctions commute *)
Lemma frobenius A (P : A -> Prop) Q :
  (exists x, Q /\ P x) <-> Q /\ (exists x, P x).
split.
case=> ? [q ph]. split=> //.
- exact: ex_intro ph .
move=> [? [??]].
apply: ex_intro. split=> //. eassumption.
Qed.



Lemma exist_conj_commute A (P Q : A -> Prop) :
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
case=> x. case=> Px Qx. split.
- apply: ex_intro Px.
apply: ex_intro Qx.
Qed.

Print Graph.
(*
"'exists' x , p" := ex (fun x => p)
*)
Check ex_intro (fun x => x=true) true _ : exists x, x=true.
Check ex_intro (fun x => x = true) true _.

Lemma ex_t : exists x:bool, x=true. by exists true. Defined.
Print ex_t.

Definition ex_t' : exists x:bool, x=true :=
  ex_intro (fun x => x=true) true erefl.


Lemma conj_exist_does_not_commute :
  ~ (forall A (P Q : A -> Prop),
       (exists x, P x) /\ (exists x, Q x) -> (exists x, P x /\ Q x)).
Proof.

intro H. 
assert (exists x:bool, x)  as Et by now exists true.
assert (exists x:bool, ~x) as Ef by now exists false.
assert (Sep := conj Et Ef).
apply H in Sep.
destruct Sep as [x].
now destruct x.

Restart.

move=> H.
have Et: exists x:bool,  x by exists true.
have Ef: exists x:bool, ~x by exists false.
have Sep:= conj Et Ef.
move/H: Sep => {H}.
by case=> [x]; case: x; case.
Qed.



(* helper lemma *)
Lemma curry_dep A (P : A -> Prop) Q :
  ((exists x, P x) -> Q) -> (forall x, P x -> Q).
Proof. move=> f x px. exact: (f (ex_intro _ x px)).
Restart.
intros. apply X. exists x. done.
Qed.

Definition not_forall_exists :=
  forall A (P : A -> Prop),
    ~ (forall x, ~ P x) -> (exists x, P x).

(* Double negation elimination *)
Definition DNE := forall (P : Prop), ~ ~ P -> P.


Lemma dneg_imp : forall (P Q : Prop), (P->Q) -> ~ ~P -> ~ ~Q.
unfold not.
intros. apply: H0. move/H. assumption.
Qed.


Lemma not_for_all_is_exists_iff_dne :
  not_forall_exists <-> DNE.
Proof.
rewrite/not_forall_exists/DNE.
split.
- move=> H P NNP.
  have:= H unit _ (fun f => NNP (f tt)).
  case. done.

move=> NNP A P NNPx.
apply: NNP=> R.
apply: NNPx=> a Pa.
apply: R. exists a.
done.

Qed.

End IntLogic.



Section BooleanLogic.

(** [==] is decidable equality operation for types with dec. eq.
    In case of booleans it means [if and only if]. *)
Fixpoint mostowski_equiv (a : bool) (n : nat) :=
  if n is n'.+1 then mostowski_equiv a n' == a
  else a.

(* ((a == a ...) == a) == a *)

Lemma mostowski_equiv_even_odd a n :
  mostowski_equiv a n = a || odd n.
Proof.
elim: n; case: a => //= => n -> //; exact: eqbF_neg.
Qed.

End BooleanLogic.

Section Arithmetics.

Lemma addnCB m n : m + (n - m) = m - n + n.
Proof.
by rewrite -maxnE maxnC maxnE addnC.
Qed.

Lemma addnBC m n : n - m + m = m - n + n.
Proof.
by rewrite addnC addnCB.
Qed.

Lemma addnBC' : commutative (fun m n => m - n + n).
Proof. 
move=> ??; exact: addnBC.
Qed.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof. exact: subn_sqr.
Restart.
by rewrite -!mulnn mulnBl !mulnDr subnDA mulnC addnK.
Qed.


Search _ (_ = _ -> _ = _).

Lemma leq_sub_add n m p : n - m <= n + p.
Proof.
have: n <= n+p by apply leq_addr.
have: n-m <= n by apply leq_subr.
apply: leq_trans.
Restart.
have: n-m <= n <= n+p by rewrite leq_addr leq_subr.
move/andP => []; exact: leq_trans.
Qed.

(* prove by induction *)
Lemma odd_exp m n : odd (m ^ n) = (n == 0) || odd m.
Proof. exact: odd_exp.

Restart.
elim: n => // n; rewrite expnS odd_mul => ->; exact: orKb.

Restart.
elim: n => // n In; rewrite expnS odd_mul In orbC; case odd; done.
Qed.

End Arithmetics.




Section Misc.
(** Exlpain why the folloing statement is unprovable *)

Definition const {A B} : A -> B -> A := fun a _ => a.

Lemma const_eq A B (x y : A) :
  @const A B x = const y -> x = y.
Abort.

Check fun x _ => x : forall A B, A->B->A.

Definition fun1 (a _ : bool) := a.
Definition fun2 (a _ : bool) := ~~ ~~a.


Lemma no_const_eq A B (x y : A) :
  ~(@const A B x = const y -> x = y).
Proof.
rewrite/const.
move=> H.
Abort.




End Misc.
