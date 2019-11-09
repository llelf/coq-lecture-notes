From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Hammer Require Import Hammer Reconstr.



Goal forall n m,  n <= m = false -> m < n.
move=> n m.
by case: ltngtP.

---Restart.
Search _ (_ ?m ?n (?m <= ?n))  in ssrnat.
move=> n m.
by case: leqP.

---Restart.
move=> n m.
rewrite ltnNge. apply: negbT.
(* exact: ltn_geF. *)
Qed.


Section EqType.

Lemma eq_sym (T : eqType) (x y : T) :
  (x == y) = (y == x).
Proof.
done. Restart.
by apply/eqP/eqP.
Qed.
(* ^ Hint: use apply/view1/view2 mechanism *)


(** Define equality type for the following datatype *)
Inductive tri :=
| Yes | No | Maybe.

(* Structure type := Pack {sort}. *)
(* Local Coercion sort : type >-> Sortclass. *)




(** This should not fail! *)
Fail Check (1, Yes) == (1, Maybe).


(** Define equality type for the [Empty_set] datatype *)
(** This should not fail! *)
Fail Check fun v : Empty_set => (1, v) == (1, v).




Lemma predU1P (T : eqType) (x y : T) (b : bool) :
  reflect (x = y \/ b) ((x == y) || b).
Proof.
case: b; rewrite (orbT,orbF).
- constructor. by right.
case XY: (x==y); constructor.
- left. apply/eqP. done.
case=> //. move/eqP: XY. done.
Qed.



Variables (A B : eqType) (f : A -> B) (g : B -> A).

Lemma inj_eq : injective f -> forall x y, (f x == f y) = (x == y).
Proof.
move=> H x y.
by apply/eqP/eqP; [apply: H | move->].
Qed.


Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof.
rewrite/cancel.
move=> H x y.
apply/eqP/eqP; last by move->.
move /(f_equal g). by rewrite !H.
Qed.


Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof.
by apply/eqP/eqP; [exact: addnI | move->].
Qed.

Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Proof.
elim: e => [|e I]; first by case: m.
by rewrite expnS ltn0Sn andbT muln_eq0 {}I andbC andKb.
Restart.

case: (@eqP nat_eqType m 0).
    - move=> H. rewrite -> H. case: e=> //=. move=> n. rewrite -> exp0n => //.
    - move=> H. case: e.
      + rewrite expn0.



rewrite -[Equality.op (Equality.class nat_eqType)]/eqn.

exact: erefl.

Qed.


Lemma seq_last_notin (s : seq A) x :
        last x s \notin s = (s == [::]).
Proof.
case: s => //= a s.
Search _ (_ \notin _) last.

---Restart.
apply/memPn.
case: s => //= a s.
apply/memPn.
exact: mem_last.


Qed.


End EqType.

