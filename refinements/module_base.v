From HB Require Import structures.
From Stdlib Require Import BinPos BinNat BinInt.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop nmodule rings_modules_and_algebras.
From mathcomp Require Import syntax cring_base ncring_base ring_base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

Local Open Scope ring_scope.

Import GRing.Theory.

(******************************************************************************)
(* Computation-oriented representation of free (semi)modules                  *)
(******************************************************************************)
Module Mod.

Section Def.

Context (C : Type) (eqbC : C -> C -> bool).

Inductive t : Type :=
  | MO : t
  | MX : positive -> C -> t -> t.

End Def.

Arguments MO {C}.

Section OpsDef.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).

Notation t := (t C).

Implicit Types (v w : t).

Definition mkMinj i v : t :=
  if v is MX i' x v then MX (Pos.add i i') x v else MO.

Definition mkMX i x v : t := if eqbC x zeroC then mkMinj i v else MX i x v.

Definition mkXi i : t := MX i oneC MO.

(* Opposite *)
Fixpoint oppM v {struct v} : t :=
  if v is MX i x v then MX i (oppC x) (oppM v) else MO.

(* Addition *)
Fixpoint addM v w {struct v} : t :=
  if v is MX i x v then
    (* addM_X i x w = addM (MX i x v) w *)
    (fix addM_X i x w {struct w} : t :=
       if w is MX j y w then
         match Z.pos_sub i j with
         | Zpos k => MX j y (addM_X k x w)
         | Z0 => mkMX i (addC x y) (addM v w)
         | Zneg k => MX i x (addM v (MX k y w))
         end
       else MX i x v) i x w
  else w.

(* Scale *)
Fixpoint scaleM x v {struct v} : t :=
  if v is MX i y v then mkMX i (mulC x y) (scaleM x v) else MO.

End OpsDef.

(***********************)
(* Evaluation of Mod.t *)
(***********************)
Section EvalSemiModule.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C).
Context (R : pzSemiRingType) (U : lSemiModType R).
Context (CtoR : C -> R) (vm : positive -> U).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).

Notation t := (t C).
Notation mkMinj := (@mkMinj C).
Notation mkMX := (@mkMX C eqbC zeroC).
Notation mkXi := (@mkXi C oneC).
Notation addM := (@addM C eqbC zeroC addC).
Notation scaleM := (@scaleM C eqbC zeroC mulC).

Implicit Types (s : positive) (u v : t).

Fixpoint evalM s v : U :=
  if v is MX i x v then
    let s' := Pos.add i s in CtoR x *: vm (Pos.pred s') + evalM s' v
  else 0.

Lemma eval_mkMinj s j v : evalM s (mkMinj j v) = evalM (Pos.add j s) v.
Proof. by case: v => //= i x v; rewrite Pos.add_assoc (Pos.add_comm i). Qed.

Lemma eval_mkMX s i x v :
  evalM s (mkMX i x v) =
    CtoR x *: vm (Pos.pred (Pos.add i s)) + evalM (Pos.add i s) v.
Proof.
rewrite /mkMX; case: ifP => [/eqbCeq->|//].
by rewrite CtoR_0 scale0r add0r eval_mkMinj.
Qed.

Lemma eval_mkX s i : evalM s (mkXi i) = vm (Pos.pred (Pos.add i s)).
Proof. by rewrite /= CtoR_1 scale1r addr0. Qed.

Lemma evalDM s v w : evalM s (addM v w) = evalM s v + evalM s w.
Proof.
elim: v w s => [|i x v IHv] w s/=; first by rewrite add0r.
elim: w s i => [|j y w IHw] s i; first by rewrite addr0.
have [->|{}i->|{}j->]/= := Z_pos_subP.
- by rewrite eval_mkMX CtoR_D IHv scalerDl addrACA.
- by rewrite IHw Pos.add_assoc (Pos.add_comm i) addrCA.
by rewrite IHv/= Pos.add_assoc (Pos.add_comm i j) !addrA.
Qed.

Lemma eval_scaleM s x v : evalM s (scaleM x v) = CtoR x *: evalM s v.
Proof.
elim: v s => [|i y v IHv] s/=; first by rewrite scaler0.
by rewrite eval_mkMX IHv CtoR_M -scalerA -scalerDr.
Qed.

(* Normalisation *)
Context (CE : Type) (normCE : CE -> C) (evalCE : CE -> R).
Context (evalCE_E : forall e, CtoR (normCE e) = evalCE e).

Definition norm_semimodule :=
  evalME MO addM (fun=> MO) (fun e => scaleM (normCE e)) mkXi.

Let evalME_aux s :=
      @evalME CE U 0 +%R (fun=> 0) (fun e => GRing.scale (evalCE e))
        (fun i => vm (Pos.pred (Pos.add i s))).
Let evalME :=
      @evalME CE U 0 +%R (fun=> 0) (fun x => GRing.scale (evalCE x)) vm.

Lemma eval_norm_semimodule_aux s me :
  evalM s (norm_semimodule me) = evalME_aux s me.
Proof.
elim: me => //.
- by move => p; rewrite eval_mkX.
- by move=> /= ? <- ? <-; rewrite evalDM.
by move=> /= ? ? <-; rewrite eval_scaleM evalCE_E.
Qed.

Lemma eval_norm_semimodule me : evalM 1 (norm_semimodule me) = evalME me.
Proof.
rewrite eval_norm_semimodule_aux; elim: me => //=.
- by move => ?; rewrite Pos.add_1_r Pos.pred_succ.
- by move=> ? -> ? ->.
by move=> ? ? ->.
Qed.

End EvalSemiModule.

Section EvalModule.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).
Context (R : pzRingType) (U : lmodType R).
Context (CtoR : C -> R) (vm : positive -> U).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_N : {morph CtoR : x / oppC x >-> - x}).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).

Notation t := (t C).
Notation mkMinj := (@mkMinj C).
Notation mkMX := (@mkMX C eqbC zeroC).
Notation mkXi := (@mkXi C oneC).
Notation oppM := (@oppM C oppC).
Notation addM := (@addM C eqbC zeroC addC).
Notation scaleM := (@scaleM C eqbC zeroC mulC).
Notation evalM := (@evalM C R U CtoR vm).

Implicit Types (s : positive) (u v : t).

Lemma evalNM s v : evalM s (oppM v) = - evalM s v.
Proof.
elim: v s => [|i x v IHv] s/=; first by rewrite oppr0.
by rewrite CtoR_N scaleNr IHv opprD.
Qed.

(* Normalisation *)
Context (CE : Type) (normCE : CE -> C) (evalCE : CE -> R).
Context (evalCE_E : forall e, CtoR (normCE e) = evalCE e).

Definition norm_module := evalME MO addM oppM (fun e => scaleM (normCE e)) mkXi.

Let evalME_aux s :=
      @evalME CE U 0 +%R -%R (fun e => GRing.scale (evalCE e))
        (fun i => vm (Pos.pred (Pos.add i s))).
Let evalME := @evalME CE U 0 +%R -%R (fun x => GRing.scale (evalCE x)) vm.

Lemma eval_norm_module_aux s me : evalM s (norm_module me) = evalME_aux s me.
Proof.
elim: me => //.
- by move => p; rewrite eval_mkX.
- by move=> /= ? <- ? <-; rewrite evalDM.
- by move=> /= ? ? <-; rewrite eval_scaleM // evalCE_E.
by move=> /= ? <-; rewrite evalNM.
Qed.

Lemma eval_norm_module me : evalM 1 (norm_module me) = evalME me.
Proof.
rewrite eval_norm_module_aux; elim: me => //=.
- by move => ?; rewrite Pos.add_1_r Pos.pred_succ.
- by move=> ? -> ? ->.
- by move=> ? ? ->.
by move=> ? ->.
Qed.

End EvalModule.

(* Free (semi)module over commutative polynomials *)
Module CPol.

Section EvalSemiModule.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C).
Context (R : pzSemiRingType) (U : lSemiModType R) (CtoR : C -> R).
Context (vmR : positive -> R) (vmU : positive -> U).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (CtoR_comm : forall x c, GRing.comm x (CtoR c)).
Context (vm_comm : forall x i, GRing.comm x (vmR i)).

Notation PExpr := (PExpr C).
Notation evalPE :=
  (@evalPE C R 0 1 +%R *%R (fun=> 0) (fun x n => x ^+ N.to_nat n)
     CtoR vmR (fun=> 0)).

(* Commutative polynomials *)
Notation Pol := (CPol.t C).
Notation eqbP := (@CPol.eqbP C eqbC).
Notation zeroP := (@CPol.zeroP C zeroC).
Notation oneP := (@CPol.oneP C oneC).
Notation addP := (@CPol.addP C eqbC zeroC addC).
Notation mulP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalP := (@CPol.evalP C R CtoR vmR +%R *%R (@GRing.exp R) 1).
Notation normP := (@CPol.norm_semiring C eqbC zeroC oneC addC mulC).

(* Free semimodule *)
Notation Mod := (t Pol).
Notation mkXi := (@mkXi Pol oneP).
Notation addM := (@addM Pol eqbP zeroP addP).
Notation scaleM := (@scaleM Pol eqbP zeroP mulP).
Notation evalM := (@evalM Pol R U evalP vmU).

(* Normalisation *)
Definition norm_semimodule :=
  @evalME PExpr Mod MO addM (fun=> MO) (fun e => scaleM (normP e)) mkXi.

Let evalME :=
  @evalME PExpr U 0 +%R (fun=> 0) (fun x => GRing.scale (evalPE x)) vmU.

Lemma eval_norm_semimodule me : evalM 1 (norm_semimodule me) = evalME me.
Proof.
apply/eval_norm_semimodule => //.
- exact/CPol.eqbPcorrect.
- exact/CPol.evalDP.
- exact/CPol.evalMP.
exact/CPol.eval_norm_semiring.
Qed.

End EvalSemiModule.

Section EvalModule.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).
Context (R : pzRingType) (U : lmodType R) (CtoR : C -> R).
Context (vmR : positive -> R) (vmU : positive -> U).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_N : {morph CtoR : x / oppC x >-> - x}).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (CtoR_comm : forall x c, GRing.comm x (CtoR c)).
Context (vm_comm : forall x i, GRing.comm x (vmR i)).

Notation PExpr := (PExpr C).
Notation evalPE :=
  (@evalPE C R 0 1 +%R *%R (fun=> 0) (fun x n => x ^+ N.to_nat n)
     CtoR vmR (fun=> 0)).

(* Commutative polynomials *)
Notation Pol := (CPol.t C).
Notation eqbP := (@CPol.eqbP C eqbC).
Notation zeroP := (@CPol.zeroP C zeroC).
Notation oneP := (@CPol.oneP C oneC).
Notation oppP := (@CPol.oppP C oppC).
Notation addP := (@CPol.addP C eqbC zeroC addC).
Notation mulP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalP := (@CPol.evalP C R CtoR vmR +%R *%R (@GRing.exp R) 1).
Notation normP := (@CPol.norm_semiring C eqbC zeroC oneC addC mulC).

(* Free module *)
Notation Mod := (t Pol).
Notation mkXi := (@mkXi Pol oneP).
Notation oppM := (@oppM Pol oppP).
Notation addM := (@addM Pol eqbP zeroP addP).
Notation scaleM := (@scaleM Pol eqbP zeroP mulP).
Notation evalM := (@evalM Pol R U evalP vmU).

(* Normalisation *)
Definition norm_module :=
  @evalME PExpr Mod MO addM oppM (fun e => scaleM (normP e)) mkXi.

Let evalME :=
  @evalME PExpr U 0 +%R -%R (fun x => GRing.scale (evalPE x)) vmU.

Lemma eval_norm_module me : evalM 1 (norm_module me) = evalME me.
Proof.
apply/eval_norm_module => //.
- exact/CPol.eqbPcorrect.
- exact/CPol.evalNP.
- exact/CPol.evalDP.
- exact/CPol.evalMP.
exact/CPol.eval_norm_semiring.
Qed.

End EvalModule.

End CPol.

(* Free (semi)module over non-commutative polynomials *)
Module NCPol.

Section EvalSemiModule.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C).
Context (R : pzSemiRingType) (U : lSemiModType R) (CtoR : C -> R).
Context (vmR : positive -> R) (vmU : positive -> U).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (CtoR_comm : forall x c, GRing.comm x (CtoR c)).

Notation PExpr := (PExpr C).
Notation evalPE :=
  (@evalPE C R 0 1 +%R *%R (fun=> 0) (fun x n => x ^+ N.to_nat n)
     CtoR (fun=> 0) vmR).

(* Non-commutative polynomials *)
Notation Pol := (NCPol.t C).
Notation eqbP := (@NCPol.eqbP C eqbC).
Notation zeroP := (@NCPol.zeroP C zeroC).
Notation oneP := (@NCPol.oneP C oneC).
Notation addP := (@NCPol.addP C eqbC zeroC addC).
Notation mulP := (@NCPol.mulP C eqbC zeroC oneC mulC).
Notation evalP := (@NCPol.evalP C R CtoR vmR).
Notation normP := (@NCPol.norm_semiring C eqbC zeroC oneC addC mulC).

(* Free semimodule *)
Notation Mod := (t Pol).
Notation mkXi := (@mkXi Pol oneP).
Notation addM := (@addM Pol eqbP zeroP addP).
Notation scaleM := (@scaleM Pol eqbP zeroP mulP).
Notation evalM := (@evalM Pol R U evalP vmU).

(* Normalisation *)
Definition norm_semimodule :=
  @evalME PExpr Mod MO addM (fun=> MO) (fun e => scaleM (normP e)) mkXi.

Let evalME :=
  @evalME PExpr U 0 +%R (fun=> 0) (fun x => GRing.scale (evalPE x)) vmU.

Lemma eval_norm_semimodule me : evalM 1 (norm_semimodule me) = evalME me.
Proof.
apply/eval_norm_semimodule => //.
- exact/NCPol.eqbPcorrect.
- exact/NCPol.evalDP.
- exact/NCPol.evalMP.
exact/NCPol.eval_norm_semiring.
Qed.

End EvalSemiModule.

Section EvalModule.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).
Context (R : pzRingType) (U : lmodType R) (CtoR : C -> R).
Context (vmR : positive -> R) (vmU : positive -> U).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_N : {morph CtoR : x / oppC x >-> - x}).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (CtoR_comm : forall x c, GRing.comm x (CtoR c)).

Notation PExpr := (PExpr C).
Notation evalPE :=
  (@evalPE C R 0 1 +%R *%R -%R (fun x n => x ^+ N.to_nat n) CtoR (fun=> 0) vmR).

(* Non-commutative polynomials *)
Notation Pol := (NCPol.t C).
Notation eqbP := (@NCPol.eqbP C eqbC).
Notation zeroP := (@NCPol.zeroP C zeroC).
Notation oneP := (@NCPol.oneP C oneC).
Notation oppP := (@NCPol.oppP C oppC).
Notation addP := (@NCPol.addP C eqbC zeroC addC).
Notation mulP := (@NCPol.mulP C eqbC zeroC oneC mulC).
Notation evalP := (@NCPol.evalP C R CtoR vmR).
Notation normP := (@NCPol.norm_ring C eqbC zeroC oneC oppC addC mulC).

(* Free module *)
Notation Mod := (t Pol).
Notation mkXi := (@mkXi Pol oneP).
Notation oppM := (@oppM Pol oppP).
Notation addM := (@addM Pol eqbP zeroP addP).
Notation scaleM := (@scaleM Pol eqbP zeroP mulP).
Notation evalM := (@evalM Pol R U evalP vmU).

(* Normalisation *)
Definition norm_module :=
  @evalME PExpr Mod MO addM oppM (fun e => scaleM (normP e)) mkXi.

Let evalME := @evalME PExpr U 0 +%R -%R (fun x => GRing.scale (evalPE x)) vmU.

Lemma eval_norm_module me : evalM 1 (norm_module me) = evalME me.
Proof.
apply/eval_norm_module => //.
- exact/NCPol.eqbPcorrect.
- exact/NCPol.evalNP.
- exact/NCPol.evalDP.
- exact/NCPol.evalMP.
exact/NCPol.eval_norm_ring.
Qed.

End EvalModule.

End NCPol.

(* Free (semi)module over mixed non-commutative and commutative polynomials *)
Module Mixed.

Section EvalSemiModule.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C).
Context (R : pzSemiRingType) (U : lSemiModType R) (CtoR : C -> R).
Context (cvmR ncvmR : positive -> R) (vmU : positive -> U).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (CtoR_comm : forall x c, GRing.comm x (CtoR c)).
Context (cvm_comm : forall x i, GRing.comm x (cvmR i)).

Notation PExpr := (PExpr C).
Notation evalPE :=
  (@evalPE C R 0 1 +%R *%R (fun=> 0) (fun x n => x ^+ N.to_nat n)
     CtoR cvmR ncvmR).

(* Commutative polynomials *)
Notation CPol := (CPol.t C).
Notation eqbCP := (@CPol.eqbP C eqbC).
Notation zeroCP := (@CPol.zeroP C zeroC).
Notation oneCP := (@CPol.oneP C oneC).
Notation addCP := (@CPol.addP C eqbC zeroC addC).
Notation mulCP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalCP := (@CPol.evalP C R CtoR cvmR +%R *%R (@GRing.exp R) 1).

(* Non-commutative polynomials over commutative polynomials *)
Notation Pol := (NCPol.t (CPol.t C)).
Notation eqbP := (@NCPol.eqbP CPol eqbCP).
Notation Pc := (fun c => @NCPol.Pc CPol (@CPol.Pc C c)).
Notation mkCXi := (fun i => @NCPol.Pc CPol (@CPol.mkXi C zeroC oneC i)).
Notation mkNCXi := (@NCPol.mkXi CPol zeroCP oneCP).
Notation zeroP := (@NCPol.zeroP CPol zeroCP).
Notation oneP := (@NCPol.oneP CPol oneCP).
Notation addP := (@NCPol.addP CPol eqbCP zeroCP addCP).
Notation mulP := (@NCPol.mulP CPol eqbCP zeroCP oneCP mulCP).
Notation powPN := (@NCPol.powPN CPol eqbCP zeroCP oneCP mulCP).
Notation evalP := (@NCPol.evalP CPol R evalCP ncvmR).
Notation normP := (@Mixed.norm_semiring C eqbC zeroC oneC addC mulC).

(* Free semimodule *)
Notation Mod := (t Pol).
Notation mkXi := (@mkXi Pol oneP).
Notation addM := (@addM Pol eqbP zeroP addP).
Notation scaleM := (@scaleM Pol eqbP zeroP mulP).
Notation evalM := (@evalM Pol R U evalP vmU).

(* Normalisation *)
Definition norm_semimodule :=
  @evalME PExpr Mod MO addM (fun=> MO) (fun e => scaleM (normP e)) mkXi.

Let evalME :=
  @evalME PExpr U 0 +%R (fun=> 0) (fun x => GRing.scale (evalPE x)) vmU.

Lemma eval_norm_semimodule me : evalM 1 (norm_semimodule me) = evalME me.
Proof.
apply/eval_norm_semimodule => //.
- exact/NCPol.eqbPcorrect/CPol.eqbPcorrect.
- exact/Mixed.evalDP.
- exact/Mixed.evalMP.
exact/Mixed.eval_norm_semiring.
Qed.

End EvalSemiModule.

Section EvalModule.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).
Context (R : pzRingType) (U : lmodType R) (CtoR : C -> R).
Context (cvmR ncvmR : positive -> R) (vmU : positive -> U).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_N : {morph CtoR : x / oppC x >-> - x}).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (CtoR_comm : forall x c, GRing.comm x (CtoR c)).
Context (cvm_comm : forall x i, GRing.comm x (cvmR i)).

Notation PExpr := (PExpr C).
Notation evalPE :=
  (@evalPE C R 0 1 +%R *%R -%R (fun x n => x ^+ N.to_nat n) CtoR cvmR ncvmR).

(* Commutative polynomials *)
Notation CPol := (CPol.t C).
Notation eqbCP := (@CPol.eqbP C eqbC).
Notation zeroCP := (@CPol.zeroP C zeroC).
Notation oneCP := (@CPol.oneP C oneC).
Notation oppCP := (@CPol.oppP C oppC).
Notation addCP := (@CPol.addP C eqbC zeroC addC).
Notation mulCP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalCP := (@CPol.evalP C R CtoR cvmR +%R *%R (@GRing.exp R) 1).

(* Non-commutative polynomials over commutative polynomials *)
Notation Pol := (NCPol.t (CPol.t C)).
Notation eqbP := (@NCPol.eqbP CPol eqbCP).
Notation Pc := (fun c => @NCPol.Pc CPol (@CPol.Pc C c)).
Notation mkCXi := (fun i => @NCPol.Pc CPol (@CPol.mkXi C zeroC oneC i)).
Notation mkNCXi := (@NCPol.mkXi CPol zeroCP oneCP).
Notation zeroP := (@NCPol.zeroP CPol zeroCP).
Notation oneP := (@NCPol.oneP CPol oneCP).
Notation oppP := (@NCPol.oppP CPol oppCP).
Notation addP := (@NCPol.addP CPol eqbCP zeroCP addCP).
Notation mulP := (@NCPol.mulP CPol eqbCP zeroCP oneCP mulCP).
Notation powPN := (@NCPol.powPN CPol eqbCP zeroCP oneCP mulCP).
Notation evalP := (@NCPol.evalP CPol R evalCP ncvmR).
Notation normP := (@Mixed.norm_ring C eqbC zeroC oneC oppC addC mulC).

(* Free module *)
Notation Mod := (t Pol).
Notation mkXi := (@mkXi Pol oneP).
Notation oppM := (@oppM Pol oppP).
Notation addM := (@addM Pol eqbP zeroP addP).
Notation scaleM := (@scaleM Pol eqbP zeroP mulP).
Notation evalM := (@evalM Pol R U evalP vmU).

(* Normalisation *)
Definition norm_module :=
  @evalME PExpr Mod MO addM oppM (fun e => scaleM (normP e)) mkXi.

Let evalME := @evalME PExpr U 0 +%R -%R (fun x => GRing.scale (evalPE x)) vmU.

Lemma eval_norm_module me : evalM 1 (norm_module me) = evalME me.
Proof.
apply/eval_norm_module => //.
- exact/NCPol.eqbPcorrect/CPol.eqbPcorrect.
- exact/Mixed.evalNP.
- exact/Mixed.evalDP.
- exact/Mixed.evalMP.
exact/Mixed.eval_norm_ring.
Qed.

End EvalModule.

End Mixed.

End Mod.
