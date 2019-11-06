From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Projection using phantoms.
    Implement [swap'] definition and [swap] notation
    so that the following works: *)

(** Strictly no pattern-matching! *)

Definition swap' A B (a:A) (b:B) & phantom (A*B) (a,b) := (b,a).
Notation "'swap' p" := (@swap' _ _ _ _ (Phantom _ p)) (at level 42).
(** Usage: *)
Eval hnf in swap (true || false, 41 + 1).
(**
= (41 + 1, true || false)
 *)



(** Design a unification tool so that the following
    typechecks iff X and Y can be unified *)

(* Definition unify' A B (a:A) (b:B) & phantom (a=b) erefl := tt. *)

Notation "[unify X 'with' Y ]" := (erefl : X=Y).


(** Usage: *)
Check [unify 1 with 0 + 1].
Check [unify 1 with 1 + 0].
Check (fun n : nat => [unify 0 + n with n]).
Fail Check (fun n : nat => [unify n + 0 with n]).  (** this should fail *)


Section LHS.
(** Design a tool for extracting the left-hand side expression
    from a term proving an equation *)

Definition lhs' T (lhs rhs: T) eq & phantom (lhs=rhs) eq := lhs.

Notation "[LHS 'of' proof_of_equation ]" :=
  (@lhs' _ _ _ _ (Phantom _ proof_of_equation)).


Notation "[LHS2 'of' proof_of_equation ]" :=
  (let l := _ in
   let _ := proof_of_equation : l=_
   in l).

Ltac LHS3 p := match type of p with ?x = ?y => idtac x end.

(* Ltac Notation "[LHS3 'of' p]" := (LHS3 p). *)

Variable prf_eq : true && false = false.

(* Set Printing All. *)
Check [LHS of prf_eq].

Eval red in [LHS of prf_eq].
Eval cbv zeta in [LHS2 of prf_eq].


Goal True. LHS3 prf_eq. Abort.


Eval red in true && false.


(* Compute [LHS of prf_eq]. *)
(** The desired result = true && false *)

End LHS.

