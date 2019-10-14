From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Hammer Require Import Hammer Reconstr.


Section Classical_reasoning.

(** We assert the classical principle of double negation elimination *)
Variable DNE : forall A : Prop, ~ ~ A -> A.



Theorem PNP_not_forall_exists: forall S, forall P: S -> Prop, 
      (forall P: Prop, P \/ ~P) -> 
          ( ~(forall x: S, P x) -> (exists x: S, ~P x) ).
Proof.
  intros.
  apply: DNE.

  move=> H1.
  suff: forall x: S, P x. done.
  { move=> x. apply: DNE.
    move=> H2. 
    have: exists x : S, ~ P x by by exists x. done.
  }
Qed.

Lemma PNP P : P \/ ~P.

have X:= @DNE P.
apply: DNE.
rewrite /not.
move=> H. apply: (H).
right=> p.
apply: H. left. done.

Qed.



(* https://en.wikipedia.org/wiki/Drinker_paradox *)
Lemma drinker_paradox {T} (P : T -> Prop) :
  inhabited T -> exists x, P x -> forall y, P y.
Proof.

  have pnp:= PNP.
  move: (PNP (forall y, P y)) => H.
  move=> [x].
  case H => O.
  - exists x. done.
  - apply PNP_not_forall_exists in O.
    + destruct O. exists x0. done.
    + done.

Restart.

  move=> Ex.
  case: (PNP (exists z, ~ P z)) => C.
  -  case: C => x. exists x. done.
  case: Ex => x. exists x.
  move=> H y.
  case: (PNP (P y)) => //.
  move=> ?. exfalso.  apply C. exists y. done.

Qed.






(* This closes the section, discharging over DNE *)
End Classical_reasoning.

Check drinker_paradox.



Section Misc.

Variables A B : Type.
Implicit Types x y : A * B.



Lemma pair_eqE (Aeq Beq: eqType) (p1 p2 : Aeq * Beq) :
  (p1 == p2) = (p1.1 == p2.1) && (p1.2 == p2.2).
Proof.
case: p1 p2 => [a b] [c d] /=. apply/idP/idP.
by move=>/eqP [] -> ->; rewrite !eqxx.
by move=>/andP[] /eqP -> /eqP ->.

  *** Restart.
case Eq: (p1==p2).
move/eqP: Eq.
move->. symmetry. apply/andP. done. done.

  *** Restart.
by case Eq: (p1==p2).

  *** Restart.
done.
Qed.






Lemma prod_inj x y :
  x = y <-> (x.1, x.2) = (y.1, y.2).
Proof.
by case: x; case: y.
  *** Restart.
split; first by move->.
case. case: x; case: y => ???? /= -> ->. done.
Restart.

by move: x y => [??] [??].
Restart.
by case x,y.
Restart.
by case: x; case: y.
Qed.

(* split=> [-> //|]. *)


End Misc.



From QuickChick Require Import QuickChick.
Require Import Lia.


Definition divn_ltn_mono n m k := andb (andb (n < m) ((k %| m))) (~~ (k==0)) ==> (n %/ k < m %/ k).
QuickChick divn_ltn_mono.


Section Arithmetics.


Lemma leq_addr' m n p : m <= n -> m <= n + p.
Proof. 
move/leq_trans. move => ->//. apply: leq_addr.
Qed.


Lemma min_plus_r  n m p  :
  minn n m = n -> minn n (m + p) = n.
Proof.
move/minn_idPl=> H. apply/minn_idPl. move: H.
exact: leq_addr'.
Qed.


Lemma min_plus_minus m n p :
  minn n m + minn (n - m) p = minn n (m + p).
Proof.
Admitted.

Fixpoint zero (n : nat) : nat :=
  if n is n'.+1 then zero n'
  else 0.

Lemma zero_returns_zero n :
  zero n = 0.
Proof. by elim: n. Qed.

(**
Claim: every amount of postage that is at least 12 cents can be made
       from 4-cent and 5-cent stamps. *)
(** Hint: no need to use induction here *)
Lemma stamps n : 12 <= n -> exists s4 s5, s4 * 4 + s5 * 5 = n.
Proof.
exists (n %/ 4 - n %% 4), (n %% 4).
rewrite mulnBl. 
have X: n %/ 4 * 4 + n %% 4 = n by admit.

rewrite -addnABC.
rewrite -mulnBr /=. simpl. rewrite subSnn muln1. done.

have: 3 <= n %/ 4. change (3 <= n%/4) with (12%/4 <= n %/ 4). by apply leq_div2r.

admit.

rewrite [_ * 5]mulnS. apply: leq_addl.

Restart.

move=> /leq_div2r leq12n; exists (n %/4 - n %% 4), (n %% 4).
rewrite mulnBl -addnABC -?mulnBr ?muln1 ?leq_mul -?divn_eq //.
by rewrite (leq_trans _ (leq12n 4)) // -ltnS ltn_pmod.
Qed.


End Arithmetics.

(* ======================================== *)

(** Bonus track: properties of functions and their composition.
    Feel free to skip this part.
 *)

(** Solutions for the exercises in seminar02.v, we are going to need them later *)
Section eq_comp.
Variables A B C D : Type.

(** Note: [rewrite !compA] would fail because it keeps adding [id \o ...]
    this is due to the fact that [compA] is a convertible rule,
    so it clashes with Miller pattern unification *)
Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Proof. by []. Qed.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof. by move=> f_id g12f a; move: (g12f a)=> /=; rewrite !f_id. Qed.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof. by move=> g_id f12g a; move: (f12g a)=> /=; rewrite g_id. Qed.

End eq_comp.



(** You might want to use the lemmas from seminar02.v, section [eq_comp] *)
Section PropertiesOfFunctions.

Section SurjectiveEpic.
Context {A B : Type}.

(* https://en.wikipedia.org/wiki/Surjective_function *)
(** Note: This definition is too strong in Coq's setting, see [epic_surj] below *)
Definition surjective (f : A -> B) :=
  exists g : B -> A, f \o g =1 id.

(** This is a category-theoretical counterpart of surjectivity:
    https://en.wikipedia.org/wiki/Epimorphism *)
Definition epic (f : A -> B) :=
  forall C (g1 g2 : B -> C), g1 \o f =1 g2 \o f -> g1 =1 g2.

Lemma surj_epic f : surjective f -> epic f.
Proof.
  rewrite/surjective/epic.

Lemma epic_surj f : epic f -> surjective f.
  (** Why is this not provable? *)
Abort.

End SurjectiveEpic.


Section EpicProperties.
Context {A B C : Type}.

Lemma epic_comp (f : B -> C) (g : A -> B) :
  epic f -> epic g -> epic (f \o g).
Proof.
Admitted.

Lemma comp_epicl (f : B -> C) (g : A -> B) :
  epic (f \o g) -> epic f.
Proof.
Admitted.

Lemma retraction_epic (f : B -> A) (g : A -> B) :
  (f \o g =1 id) -> epic f.
Proof.
Admitted.

End EpicProperties.


(** The following section treats some properties of injective functions:
    https://en.wikipedia.org/wiki/Injective_function *)

Section InjectiveMonic.

Context {B C : Type}.

(** This is a category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)
Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

Lemma inj_monic f : injective f -> monic f.
Proof.
Admitted.

Lemma monic_inj f : monic f -> injective f.
Proof.
Admitted.

End InjectiveMonic.


Section MonicProperties.
Context {A B C : Type}.

Lemma monic_comp (f : B -> C) (g : A -> B) :
  monic f -> monic g -> monic (f \o g).
Proof.
Admitted.

Lemma comp_monicr (f : B -> C) (g : A -> B) :
  monic (f \o g) -> monic g.
Proof.
Admitted.

Lemma section_monic (f : B -> A) (g : A -> B) :
  (g \o f =1 id) -> monic f.
Proof.
Admitted.

End MonicProperties.

End PropertiesOfFunctions.
