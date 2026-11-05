From HB Require Import structures.
From Stdlib Require Import BinPos BinNat.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop nmodule rings_modules_and_algebras.
From mathcomp Require Import syntax cring_base ncring_base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

Local Open Scope ring_scope.

Import GRing.Theory.

(******************************************************************************)
(* Mixed non-commutative and commutative polynomials                          *)
(******************************************************************************)
Module Mixed.

Section EvalSemiRing.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C).
Context (R : pzSemiRingType) (CtoR : C -> R) (cvm ncvm : positive -> R).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (comm_ncvm_CtoR : forall i c, GRing.comm (ncvm i) (CtoR c)).
Context (comm_cvm : forall x i, GRing.comm x (cvm i)).

(* Commutative polynomials *)
Notation CPol := (CPol.t C).
Notation eqbCP := (@CPol.eqbP C eqbC).
Notation zeroCP := (@CPol.zeroP C zeroC).
Notation oneCP := (@CPol.oneP C oneC).
Notation addCP := (@CPol.addP C eqbC zeroC addC).
Notation mulCP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalCP := (@CPol.evalP C R CtoR cvm +%R *%R (@GRing.exp R) 1).

(* Non-commutative polynomials over commutative polynomials *)
Notation Pol := (NCPol.t (CPol.t C)).
Notation Pc := (fun c => @NCPol.Pc CPol (@CPol.Pc C c)).
Notation mkCXi := (fun i => @NCPol.Pc CPol (@CPol.mkXi C zeroC oneC i)).
Notation mkNCXi := (@NCPol.mkXi CPol zeroCP oneCP).
Notation zeroP := (@NCPol.zeroP CPol zeroCP).
Notation oneP := (@NCPol.oneP CPol oneCP).
Notation addP := (@NCPol.addP CPol eqbCP zeroCP addCP).
Notation mulP := (@NCPol.mulP CPol eqbCP zeroCP oneCP mulCP).
Notation powPN := (@NCPol.powPN CPol eqbCP zeroCP oneCP mulCP).
Notation evalP := (@NCPol.evalP CPol R evalCP ncvm).

Implicit Types (P Q : Pol).

Let eqbCPeq (P Q : CPol) : eqbCP P Q -> P = Q.
Proof. exact: CPol.eqbPcorrect. Qed.

Lemma evalDP P Q : evalP (addP P Q) = evalP P + evalP Q.
Proof. exact/NCPol.evalDP/CPol.evalDP. Qed.

Lemma evalMP P Q : evalP (mulP P Q) = evalP P * evalP Q.
Proof.
apply/NCPol.evalMP => //; first exact: CPol.evalMP.
by move=> x p; apply: CPol.comm_evalP.
Qed.

Lemma evalXPN P n : evalP (powPN P n) = evalP P ^+ N.to_nat n.
Proof.
rewrite NCPol.evalXPN //=; first exact: CPol.evalMP.
by move=> x p; apply: CPol.comm_evalP.
Qed.

(* Normalisation *)
Definition norm_semiring :=
  evalPE zeroP oneP addP mulP (fun=> zeroP) powPN Pc mkCXi mkNCXi.

Let evalPE := @evalPE C R 0 1 +%R *%R (fun=> 0) (fun x n => x ^+ N.to_nat n)
                CtoR cvm ncvm.

Lemma eval_norm_semiring pe : evalP (norm_semiring pe) = evalPE pe.
Proof.
elim: pe => //.
- by move=> ?; rewrite /= CPol.eval_mkXi// Pos.add_1_r Pos.pred_succ.
- by move=> ?; rewrite NCPol.eval_mkXi.
- by move=> /= ? <- ? <-; rewrite evalDP.
- by move=> /= ? <- ? <-; rewrite evalMP.
by move=> /= ? <- ?; rewrite evalXPN.
Qed.

End EvalSemiRing.

Section EvalRing.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).
Context (R : pzRingType) (CtoR : C -> R) (cvm ncvm : positive -> R).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_N : {morph CtoR : x / oppC x >-> - x}).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (comm_ncvm_CtoR : forall i c, GRing.comm (ncvm i) (CtoR c)).
Context (comm_cvm : forall x i, GRing.comm x (cvm i)).

(* Commutative polynomials *)
Notation CPol := (CPol.t C).
Notation eqbCP := (@CPol.eqbP C eqbC).
Notation zeroCP := (@CPol.zeroP C zeroC).
Notation oneCP := (@CPol.oneP C oneC).
Notation oppCP := (@CPol.oppP C oppC).
Notation addCP := (@CPol.addP C eqbC zeroC addC).
Notation mulCP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalCP := (@CPol.evalP C R CtoR cvm +%R *%R (@GRing.exp R) 1).

(* Non-commutative polynomials over commutative polynomials *)
Notation Pol := (NCPol.t (CPol.t C)).
Notation constP := (fun c => @NCPol.Pc CPol (@CPol.Pc C c)).
Notation mkCXi := (fun i => @NCPol.Pc CPol (@CPol.mkXi C zeroC oneC i)).
Notation mkNCXi := (@NCPol.mkXi CPol zeroCP oneCP).
Notation zeroP := (@NCPol.zeroP CPol zeroCP).
Notation oneP := (@NCPol.oneP CPol oneCP).
Notation oppP := (@NCPol.oppP CPol oppCP).
Notation addP := (@NCPol.addP CPol eqbCP zeroCP addCP).
Notation mulP := (@NCPol.mulP CPol eqbCP zeroCP oneCP mulCP).
Notation powPN := (@NCPol.powPN CPol eqbCP zeroCP oneCP mulCP).
Notation evalP := (@NCPol.evalP CPol R evalCP ncvm).

Lemma evalNP P : evalP (oppP P) = - evalP P.
Proof. exact/NCPol.evalNP/CPol.evalNP. Qed.

(* Normalisation *)
Definition norm_ring :=
  evalPE zeroP oneP addP mulP oppP powPN constP mkCXi mkNCXi.

Let evalPE :=
      @evalPE C R 0 1 +%R *%R -%R (fun x n => x ^+ N.to_nat n) CtoR cvm ncvm.

Lemma eval_norm_ring pe : evalP (norm_ring pe) = evalPE pe.
Proof.
elim: pe => //.
- by move=> ?; rewrite /= CPol.eval_mkXi// Pos.add_1_r Pos.pred_succ.
- by move=> ?; rewrite NCPol.eval_mkXi.
- by move=> /= ? <- ? <-; rewrite evalDP.
- by move=> /= ? <- ? <-; rewrite evalMP.
- by move=> /= ? <-; rewrite evalNP.
by move=> /= ? <- ?; rewrite evalXPN.
Qed.

End EvalRing.

End Mixed.
