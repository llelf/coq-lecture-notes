From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Some basic functions *)

Definition const {A B} (a : A) := fun _ : B => a.

Definition flip {A B C} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Arguments const {A B} a _ /.
Arguments flip {A B C} f b a /.


(* move to logic_exercises *)
Section IntLogic.

Variables A B C D : Prop.

Lemma axiomK :
  A -> B -> A.
Proof. exact: const. Qed.


(* note: flip is more general *)
Lemma contraposition :
  (A -> ~ B) -> (B -> ~ A).
Proof. exact: flip. Qed.                            (* LELF flip *)


Lemma p_imp_np_iff_np : (A -> ~A)  <->  ~A.
Proof.
 split; rewrite /not.
 - move=> H a. apply: (H a a).
  done. (* const *)
Qed.


(* We can generalize the previous lemma into *)
Lemma p_p_q_iff_p_q : (A -> A -> B)  <->  (A -> B).
Proof.
split.
move=> H a. exact: (H a).
done.
Qed.


Lemma p_is_not_equal_not_p :
  ~ (A <-> ~ A).
Proof.
(* rewrite /not.  *)
(* case. *)
(* move=> H Q. *)
case.
move=> a_na na_a.
apply: (a_na).

apply: (na_a).
move=> a.
by apply: a_na.

apply: (na_a) => a.
by apply: a_na.

Qed.



Lemma not_not_lem :
  ~ ~ (A \/ ~ A).
Proof.
rewrite/not => H.
apply: (H). right.
move=> a. apply: H. by constructor.
Qed.


Lemma constructiveDNE :
  ~ ~ ~ A  ->  ~ A.
Proof.
  rewrite/not.
  move=> H ?. apply: H. done.
Qed.

End IntLogic.




(* Boolean logic (decidable fragment enjoys classical laws) *)
Require Import Utf8.

Section BooleanLogic.
Require Import Lia Omega Arith Bool.
(* From Hammer Require Import Reconstr Hammer. *)

Search _ (?a || ~~ ?a).
About orbN.






Lemma LEM_decidable a :
  a || ~~ a.
  (* refine (if a then is_true_true else _). *)
  (* cbv. *)
  (* by case: a. *)
  (* auto using orbN. *)
     exact:orbN.
  (* move:a;case=>//. *)
  (* rewrite /orb /negb /is_true. *)
Defined.
Eval compute in LEM_decidable.


Definition LEM_decidable' a : a || ~~ a :=
  (* if a as a return a || ~~a then erefl else erefl. *)
  match a with true => erefl | _ => erefl end.

Definition LEM_decidable'' a : a || ~~ a :=
  if a is true then erefl else erefl.

Definition LEM_decidable''' : forall a, a || ~~ a := orbN.




Lemma disj_implb a b :
  a || (a ==> b).
Proof.
  by case: a.
Qed.

Lemma iff_is_if_and_only_if a b :
  (a ==> b) && (b ==> a) = (a == b).
Proof.
  by case: a; case: b. 
Restart.
 by move: a b => [[]|[]].
Qed.


Lemma implb_trans : transitive implb.
Proof.
  by case; case.
Qed.

Lemma triple_compb (f : bool -> bool) :
  f \o f \o f =1 f.
Proof.
  by case; case E1:(f true) => /=; case E2:(f false); rewrite ?E1 ?E2.
Restart.
  by case=> /=; case E1:(f true); case E2:(f false); rewrite ?E1 ?E2.
Qed.

(* negb \o odd means "even" *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Proof.

  move=>x y /=.
  Search _ negb (~~ _ == _).
  rewrite eqb_negLR.
  Search _ (~~ ~~ _).
  Search _ involutive negb.
  rewrite negbK.
  Search _ odd addn.
  Search _ odd (_ + _).
  rewrite odd_add.
  rewrite negb_add.
  (* rewrite eqb_negLR. rewrite negbK. *)
  (* !!! *)
Restart.


  (* rewrite/morphism_2. *)
  rewrite/comp => x y.
  rewrite odd_add.
  rewrite negb_add.
  case: (odd x); case: (odd y); done.

Qed.
  


  
  
End BooleanLogic.


(* some properties of functional composition *)

Section eq_comp.
Variables A B C D : Type.

Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Proof.
  done.
Restart.
  Locate "\o". Print funcomp.
  rewrite/funcomp. done.
Qed.


Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Proof.
  (* rewrite /eqfun. *) 
  (* move=> H x. *)

  rewrite /comp => H x.
  rewrite H.
  done.
Qed.




Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Proof.
  (* rewrite !/(_ =1 _). *)
  move=> H x.
  exact: H.
Qed.



Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof. 
  (* rewrite /eqfun. *)
  move=> Fid.
  rewrite /comp => FG x. 
  move: (FG x). rewrite 2!Fid. done.
Qed.


Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof.

  rewrite /comp/eqfun.
  move=> Gid.
  move=> FF x.
  (* specialize FF with x. *)
  have:= FF x.
  rewrite Gid.
  done.
Qed.  

End eq_comp.





