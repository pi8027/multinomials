From elpi.apps Require Import derive.std.
From Stdlib Require Import BinPos BinNat BinInt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

(* Parametricity *)

Elpi derive.param2 pred.
Elpi derive.param2 rel.
Elpi derive.param2 negb.
Elpi derive.param2 andb.
Elpi derive.param2 orb.

Lemma bool_R_refl b : bool_R b b.
Proof. by case: b; constructor. Qed.

Lemma bool_R_eq b1 b2 : bool_R b1 b2 -> b1 = b2.
Proof. by case. Qed.

Elpi derive.param2 Nat.add.

Lemma nat_R_refl n : nat_R n n.
Proof. by elim: n; constructor. Qed.

Lemma nat_R_eq n m : nat_R n m -> n = m.
Proof. by elim=> // _ ? _ ->. Qed.

Elpi derive.param2 positive.
Elpi derive.param2 Pos.eqb.
Elpi derive.param2 Pos.pred_double.
Elpi derive.param2 Pos.succ.
Elpi derive.param2 Pos.pred.
Elpi derive.param2 Pos.iter_op.
Elpi derive.param2 Pos.to_nat.

Lemma positive_R_refl p : positive_R p p.
Proof. by elim: p; constructor. Qed.

Lemma positive_R_eq p q : positive_R p q -> p = q.
Proof. by elim=> // _ ? _ ->. Qed.

Lemma Pos_add_R :
  forall p p' : positive, positive_R p p' ->
  forall q q' : positive, positive_R q q' ->
  positive_R (Pos.add p q) (Pos.add p' q').
Proof.
by move=> p _ /positive_R_eq <- q _ /positive_R_eq <-; apply/positive_R_refl.
Qed.

Elpi derive.param2.register Pos.add Pos_add_R.

Elpi derive.param2 N.

Elpi derive.param2 Z.
Elpi derive.param2 Z.double.
Elpi derive.param2 Z.pred_double.
Elpi derive.param2 Z.succ_double.
Elpi derive.param2 Z.pos_sub.
