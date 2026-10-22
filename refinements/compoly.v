From elpi.apps Require Import derive.std.
From HB Require Import structures.
From Stdlib Require Import BinPos BinNat BinInt.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop nmodule rings_modules_and_algebras.
From mathcomp Require Import zify.
Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

Local Open Scope ring_scope.

Import GRing.Theory.

Local Arguments Pos.add : simpl never.

derive positive.

Variant Z_pos_sub_spec (x y : positive) : Z -> Set :=
  | Z_pos_sub_Eq : x = y -> Z_pos_sub_spec Z0
  | Z_pos_sub_Gt z : x = Pos.add y z -> Z_pos_sub_spec (Z.pos z)
  | Z_pos_sub_Lt z : y = Pos.add x z -> Z_pos_sub_spec (Z.neg z).

Lemma Z_pos_subP (x y : positive) : Z_pos_sub_spec x y (Z.pos_sub x y).
Proof.
case E : (Pos.compare x y); move: E.
- by move=> /Pos.compare_eq <-; rewrite Z.pos_sub_diag; constructor.
- move=> /Pos.compare_lt_iff /[dup] ltxy /Z.pos_sub_lt ->; constructor.
  by rewrite Pos.add_comm Pos.sub_add.
move=> /Pos.compare_gt_iff /[dup] ltyx /Z.pos_sub_gt ->; constructor.
by rewrite Pos.add_comm Pos.sub_add.
Qed.

Lemma Pos_add_pred_l (x y : positive) :
  (1 < x)%positive -> Pos.add (Pos.pred x) y = Pos.pred (Pos.add x y).
Proof. lia. Qed.

Lemma Pos_add_pred_r (x y : positive) :
  (1 < y)%positive -> Pos.add x (Pos.pred y) = Pos.pred (Pos.add x y).
Proof. lia. Qed.

(**********************************)
(* Reified polynomial expressions *)
(**********************************)
Section PExpr.

Context (C : Type).

Inductive PExpr : Type :=
  | PEO : PExpr
  | PEI : PExpr
  | PEc : C -> PExpr
  | PECX : positive -> PExpr (* commutative variables *)
  | PENCX : positive -> PExpr (* non-commutative variables *)
  | PEadd : PExpr -> PExpr -> PExpr
  | PEmul : PExpr -> PExpr -> PExpr
  | PEopp : PExpr -> PExpr
  | PEpow : PExpr -> N -> PExpr.

Context (R : Type).
Context (zeroR oneR : R) (addR mulR : R -> R -> R) (oppR : R -> R).
Context (powR : R -> N -> R).
Context (CtoR : C -> R) (cvm ncvm : positive -> R).

Fixpoint evalPE (pe : PExpr) {struct pe} : R :=
  match pe with
  | PEO => zeroR
  | PEI => oneR
  | PEc c => CtoR c
  | PECX j => cvm j
  | PENCX j => ncvm j
  | PEadd pe1 pe2 => addR (evalPE pe1) (evalPE pe2)
  | PEmul pe1 pe2 => mulR (evalPE pe1) (evalPE pe2)
  | PEopp pe1 => oppR (evalPE pe1)
  | PEpow pe1 n => powR (evalPE pe1) n
  end.

End PExpr.

(******************************)
(* Reified module expressions *)
(******************************)
Section MExpr.

Context (R : Type).

Inductive MExpr : Type :=
  | MEO : MExpr
  | MEX : positive -> MExpr
  | MEadd : MExpr -> MExpr -> MExpr
  | MEscale : R -> MExpr -> MExpr
  | MEopp : MExpr -> MExpr.

Context (U : Type).
Context (zeroU : U) (addU : U -> U -> U) (oppU : U -> U) (scaleU : R -> U -> U).
Context (vm : positive -> U).

Fixpoint evalME (me : MExpr) {struct me} : U :=
  match me with
  | MEO => zeroU
  | MEX j => vm j
  | MEadd me1 me2 => addU (evalME me1) (evalME me2)
  | MEscale x me1 => scaleU x (evalME me1)
  | MEopp me1 => oppU (evalME me1)
  end.

End MExpr.

(******************************************************************************)
(* Computation-oriented representation of (commutative) polynomials, also     *)
(* known as the Sparse Horner form (Grégoire and Mahboubi 2005)               *)
(******************************************************************************)
Module CPol.

derive Inductive t (C : Type) : Type :=
  | Pc : C -> t
  (* [PinjX i j P Q] represents [shift (i - 1) (X_0^j * P + shift 1 Q)], or   *)
  (* equivalently, [X_i^j * shift (i - 1) P + shift i Q]                      *)
  | PinjX : positive -> positive -> t -> t -> t.

Section OpsDef.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).

Notation t := (t C).
Notation t_eqb := (t_eqb eqbC).

Implicit Types (P Q : t).

(* Polynomial operations *)

Definition zeroP := Pc zeroC.
Definition oneP := Pc oneC.

Definition mkPinjS i P : t :=
  match P with
  | Pc _ => P
  | PinjX j P k Q => PinjX (Pos.add i j) P k Q
  end.

Definition mkPinjX i j P Q : t :=
  match P with
  | Pc c => if eqbC c zeroC then mkPinjS i Q else PinjX i j P Q
  | PinjX i' j' P' Q' =>
    if Pos.eqb i' 1 && t_eqb Q' zeroP then
      PinjX i (j + j') P' Q
    else
      PinjX i j (PinjX i' j' P' Q') Q
  end.

Definition mkXi i : t := PinjX i 1 oneP zeroP.

Definition mkX : t := mkXi 1.

(* Opposite *)
Fixpoint oppP P : t :=
  match P with
  | Pc c => Pc (oppC c)
  | PinjX i j P Q => PinjX i j (oppP P) (oppP Q)
  end.

(* Addition *)
Fixpoint addPC P (c : C) : t :=
  match P with
  | Pc c1 => Pc (addC c1 c)
  | PinjX i j P Q => PinjX i j P (addPC Q c)
  end.

Section addP.
Context (addP : t -> t -> t) (P : t).

(* [PinjX 1 j P zeroP + P'], i.e., [X_0^j * P + P'] *)
(* assuming [addP P .] is [P + .] *)
Fixpoint addPX (j : positive) P' {struct P'} : t :=
  match P' with
  | Pc _ => PinjX 1 j P P'
  | PinjX 1 j' P' Q' =>
    match Z.pos_sub j' j with
    | Zpos k => mkPinjX 1 j (addP P (PinjX 1 k P' zeroP)) Q'
    | Z0 => mkPinjX 1 j' (addP P P') Q'
    | Zneg k => mkPinjX 1 j' (addPX k P') Q'
    end
  | PinjX i' j' P' Q' => PinjX 1 j P (PinjX (Pos.pred i') j' P' Q')
  end.

Context (j : positive) (Q : t).

(* [PinjX i j P Q + P'], *)
(* i.e., [X_(i - 1)^j * shift (i - 1) P + shift i Q + P'] *)
(* assuming [addP P .] and [addP Q .] are [P + .] and [Q + .] *)
Fixpoint addPIX (i : positive) P' {struct P'} : t :=
  match P' with
  | Pc c => PinjX i j P (addPC Q c)
  | PinjX i' j' P' Q' =>
    match Z.pos_sub i' i with
    | Zpos k => PinjX i j P (addP Q (PinjX k j' P' Q'))
    | Z0 =>
      match Z.pos_sub j' j with
      | Zpos k => mkPinjX i j (addP P (PinjX 1 k P' zeroP)) (addP Q Q')
      | Z0 => mkPinjX i j (addP P P') (addP Q Q')
      | Zneg k => mkPinjX i j' (addPX k P') (addP Q Q')
      end
    | Zneg k => PinjX i' j' P' (addPIX k Q')
    end
  end.

End addP.

Fixpoint addP P P' {struct P} : t :=
  match P with
  | Pc c => addPC P' c
  | PinjX i j P Q => addPIX addP P j Q i P'
  end.

(* Multiplication *)
Fixpoint mapP (f : C -> C) P : t :=
  match P with
  | Pc c => Pc (f c)
  | PinjX i j P Q => PinjX i j (mapP f P) (mapP f Q)
  end.

Definition mulCP c P :=
  if eqbC c zeroC then zeroP else
  if eqbC c oneC then P else mapP (mulC c) P.

Definition mulPC P c :=
  if eqbC c zeroC then zeroP else
  if eqbC c oneC then P else mapP (mulC ^~ c) P.

Section mulPI.
Context (mulP : t -> t -> t) (P : t).

(* [mkPinjS i P * P'], i.e., [shift i P * P'], assuming [mulP P .] is [P * .] *)
Fixpoint mulPI (i : positive) P' {struct P'} : t :=
  match P' with
  | Pc c => mkPinjS i (mulPC P c)
  | PinjX i' j' P' Q' =>
    match Z.pos_sub i' i with
    | Zpos k => mkPinjS i (mulP P (PinjX k j' P' Q'))
    | Z0 => mkPinjX i' j' (mulPI 1 P') (mulP P Q')
    | Zneg k => mkPinjX i' j' (mulPI (Pos.succ k) P') (mulPI k Q')
    end
  end.

End mulPI.

Section mulPIX.
Context (mulP : t -> t -> t) (j : positive) (P Q : t).

(* [PinjX i j P Q * P'], *)
(* assuming [mulP P .] and [mulP Q .] are [P * .] and [Q * .] *)
Fixpoint mulPIX (i : positive) P' {struct P'} : t :=
  match P' with
  | Pc c => mulPC (PinjX i j P Q) c
  | PinjX i' j' P' Q' =>
    match Z.pos_sub i' i with
    | Zpos k =>
      mkPinjX i j (mulP P (PinjX (Pos.succ k) j' P' Q'))
                  (mulP Q (PinjX k j' P' Q'))
    | Z0 =>
      let PP'QQ' := mkPinjX i (Pos.add j j') (mulP P P') (mulP Q Q') in
      let PQ' := mkPinjX i j (mulP P (mkPinjS 1 Q')) zeroP in
      let P'Q := mkPinjX i j' (mulPI mulP Q 1 P') zeroP in
      addP PP'QQ' (addP PQ' P'Q)
    | Zneg k => mkPinjX i' j' (mulPIX (Pos.succ k) P') (mulPIX k Q')
    end
  end.

End mulPIX.

Fixpoint mulP P P' {struct P} : t :=
  match P with
  | Pc c => mulCP c P'
  | PinjX i j P Q => mulPIX mulP j P Q i P'
  end.

Fixpoint powPpos (res P : t) (p : positive) : t :=
  match p with
  | xH => mulP res P
  | xO p => powPpos (powPpos res P p) P p
  | xI p => mulP (powPpos (powPpos res P p) P p) P
  end.

Definition powPN P n := if n is Npos p then powPpos oneP P p else oneP.

End OpsDef.

(************************)
(* Evaluation of CPol.t *)
(************************)
Section EvalSemiRing.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C).
Context (R : pzSemiRingType) (CtoR : C -> R) (vm : positive -> R).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (comm_vm : forall x i, GRing.comm x (vm i)).

Notation t := (t C).
Notation zeroP := (@zeroP C zeroC).
Notation oneP := (@oneP C oneC).
Notation mkPinjS := (@mkPinjS C).
Notation mkPinjX := (@mkPinjX C eqbC zeroC).
Notation mkXi := (@mkXi C zeroC oneC).
Notation addPC := (@addPC C addC).
Notation addPX := (@addPX C eqbC zeroC).
Notation addPIX := (@addPIX C eqbC zeroC addC).
Notation addP := (@addP C eqbC zeroC addC).
Notation mapP := (@mapP C).
Notation mulPC := (@mulPC C eqbC zeroC oneC mulC).
Notation mulCP := (@mulCP C eqbC zeroC oneC mulC).
Notation mulPI := (@mulPI C eqbC zeroC oneC mulC).
Notation mulPIX := (@mulPIX C eqbC zeroC oneC addC mulC).
Notation mulP := (@mulP C eqbC zeroC oneC addC mulC).
Notation powPpos := (@powPpos C eqbC zeroC oneC addC mulC).
Notation powPN := (@powPN C eqbC zeroC oneC addC mulC).

Implicit Types (s : positive) (P Q : t).

Let mulrCA_vmX i n x y : vm i ^+ n * (x * y) = x * (vm i ^+ n * y).
Proof. by rewrite !mulrA commrX. Qed.

Let mulrAC_vmX x y i n : x * y * vm i ^+ n = x * vm i ^+ n * y.
Proof. by rewrite -!mulrA commrX. Qed.

Fixpoint evalP s P : R :=
  match P with
  | Pc c => CtoR c
  | PinjX i j P Q =>
    let s' := Pos.add i s in
    vm (Pos.pred s') ^+ Pos.to_nat j * evalP (Pos.pred s') P + evalP s' Q
  end.

Lemma eval_mkPinjS i' s P : evalP s (mkPinjS i' P) = evalP (Pos.add i' s) P.
Proof. by case: P => //= i j P Q; do ?[lia|f_equal]. Qed.

Lemma eval_mkPinjX s i j P Q :
  let s' := Pos.add i s in
  evalP s (mkPinjX i j P Q) =
    vm (Pos.pred s') ^+ Pos.to_nat j * evalP (Pos.pred s') P + evalP s' Q.
Proof.
case: P => [c|[i'|i'|] j' P' Q']/=; try by do ?[lia|f_equal].
- by have [/eqbCeq->|//=] := ifP; rewrite CtoR_0 mulr0 add0r eval_mkPinjS.
have [/(t_eqb_correct eqbCeq)->|]//= := ifP.
by rewrite Pos.add_1_l Pos.pred_succ CtoR_0 addr0 Pos2Nat.inj_add exprD mulrA.
Qed.

Lemma eval_mkXi s i : evalP s (mkXi i) = vm (Pos.pred (i + s)).
Proof. by rewrite /= CtoR_0 addr0 CtoR_1 mulr1. Qed.

(* Addition *)
Lemma evalDPC s c P : evalP s (addPC P c) = evalP s P + CtoR c.
Proof. by elim: P s => //= i j P _ Q IHQ s; rewrite IHQ addrA. Qed.

Lemma evalDPX s P j P' :
  (forall s P', evalP s (addP P P') = evalP s P + evalP s P') ->
  evalP s (addPX addP P j P') = vm s ^+ Pos.to_nat j * evalP s P + evalP s P'.
Proof.
move=> IHP.
elim: P' j => [c|[i'|i'|] j' P' IHP' Q' _] j /=; try by do ?[lia|f_equal].
have [->|{}j'->|{}j->] := Z_pos_subP.
- by rewrite eval_mkPinjX IHP Pos.add_1_l Pos.pred_succ mulrDr addrA.
- rewrite eval_mkPinjX IHP/= !Pos.add_1_l !Pos.pred_succ CtoR_0 addr0.
  by rewrite Pos2Nat.inj_add exprD mulrDr addrA mulrA.
rewrite eval_mkPinjX Pos.add_1_l Pos.pred_succ IHP'.
by rewrite Pos2Nat.inj_add exprD mulrDr addrA mulrA.
Qed.

Lemma evalDPIX s P j Q i P' :
  (forall s P', evalP s (addP P P') = evalP s P + evalP s P') ->
  (forall s Q', evalP s (addP Q Q') = evalP s Q + evalP s Q') ->
  evalP s (addPIX addP P j Q i P') = evalP s (PinjX i j P Q) + evalP s P'.
Proof.
move=> IHP IHQ/=; elim: P' i s => [c|i' j' P' _ Q' IHQ'] i s /=.
  by rewrite evalDPC addrA.
have [{IHQ'}->|{}i'->|{}i->]/= := Z_pos_subP; first last.
- by rewrite IHQ' addrCA Pos.add_assoc (Pos.add_comm i).
- by rewrite IHQ/= addrA Pos.add_assoc (Pos.add_comm i').
have [->|{}j'->|{}j ->]/= := Z_pos_subP.
- by rewrite eval_mkPinjX IHP IHQ mulrDr addrACA.
- rewrite eval_mkPinjX IHP IHQ/= mulrDr addrACA CtoR_0 addr0.
  by rewrite Pos.add_1_l Pos.pred_succ Pos2Nat.inj_add exprD mulrA.
rewrite eval_mkPinjX IHQ evalDPX//= mulrDr addrACA.
by rewrite Pos2Nat.inj_add exprD mulrA.
Qed.

Lemma evalDP s P P' : evalP s (addP P P') = evalP s P + evalP s P'.
Proof.
elim: P P' s => [c|i j P IHP Q IHQ] P' s/=; last by rewrite evalDPIX.
by rewrite evalDPC addrC.
Qed.

(* Multiplication *)
Lemma evalMPC s P c : evalP s (mulPC P c) = evalP s P * CtoR c.
Proof.
rewrite /mulPC; have [/eqbCeq->|_] := ifP; first by rewrite /= CtoR_0 mulr0.
have [/eqbCeq->|_] := ifP; first by rewrite /= CtoR_1 mulr1.
elim: P s => [c'|i j P IHP Q IHQ] s/=; first by rewrite CtoR_M.
by rewrite IHP IHQ mulrA mulrDl.
Qed.

Lemma evalMCP s c P : evalP s (mulCP c P) = CtoR c * evalP s P.
Proof.
rewrite /mulCP; have [/eqbCeq->|_] := ifP; first by rewrite /= CtoR_0 mul0r.
have [/eqbCeq->|_] := ifP; first by rewrite /= CtoR_1 mul1r.
elim: P s => [c'|i j P IHP Q IHQ] s/=; first by rewrite CtoR_M.
by rewrite IHP IHQ mulrCA_vmX mulrDr.
Qed.

Lemma evalMPI s P i P' :
  (forall s P', evalP s (mulP P P') = evalP s P * evalP s P') ->
  evalP s (mulPI mulP P i P') = evalP (i + s) P * evalP s P'.
Proof.
move=> IHP; elim: P' i s => [c'|i' j' P' IHP' Q' IHQ'] i s /=.
  by rewrite eval_mkPinjS evalMPC.
have [->|{}i'->|{}i->] := Z_pos_subP.
- rewrite eval_mkPinjX IHP' IHP mulrDr mulrCA_vmX; do ?[lia|f_equal].
- by rewrite eval_mkPinjS IHP/= Pos.add_assoc (Pos.add_comm i').
by rewrite eval_mkPinjX IHP' IHQ' mulrDr mulrCA_vmX; do ?[lia|f_equal].
Qed.

Lemma evalMPIX s P j Q i P' :
  (forall s P', evalP s (mulP P P') = evalP s P * evalP s P') ->
  (forall s Q', evalP s (mulP Q Q') = evalP s Q * evalP s Q') ->
  evalP s (mulPIX mulP j P Q i P') = evalP s (PinjX i j P Q) * evalP s P'.
Proof.
move=> IHP IHQ; elim: P' i s => [c'|i' j' P' IHP' Q' IHQ'] i s /=.
  by rewrite evalMPC.
have [->|{}i'->|{}i->] := Z_pos_subP.
- rewrite !evalDP !eval_mkPinjX !IHP IHQ eval_mkPinjS evalMPI//= CtoR_0 !addr0.
  rewrite !Pos.add_1_l Pos.succ_pred; first lia.
  rewrite Pos2Nat.inj_add exprD mulrA -mulrAC_vmX -mulrA.
  set XP := _ * evalP _ P; set XP' := _ * evalP _ P'.
  by rewrite mulrA mulrCA_vmX -/XP -/XP' addrACA -2!mulrDr -(addrC XP') -mulrDl.
- rewrite eval_mkPinjX IHP IHQ/= Pos.add_succ_l Pos_add_pred_r; first lia.
  rewrite Pos.pred_succ Pos.succ_pred; first lia.
  by rewrite Pos.add_assoc (Pos.add_comm i') mulrA -mulrDl.
rewrite eval_mkPinjX IHP' IHQ'/= Pos.add_succ_l Pos_add_pred_r; first lia.
rewrite Pos.pred_succ Pos.succ_pred; first lia.
by rewrite Pos.add_assoc (Pos.add_comm i) mulrCA_vmX mulrDr mulrA.
Qed.

Lemma evalMP s P P' : evalP s (mulP P P') = evalP s P * evalP s P'.
Proof.
elim: P P' s => [c|i j P IHP Q IHQ] P' s/=; last by rewrite evalMPIX.
by rewrite evalMCP.
Qed.

Lemma evalXPp s res P p :
  evalP s (powPpos res P p) = evalP s res * evalP s P ^+ Pos.to_nat p.
Proof.
elim: p res => [p IHp|p IHp|] res /=; last by rewrite evalMP.
  by rewrite evalMP 2!IHp Pos2Nat.inj_xI exprSr 2!exprD mulr1 !mulrA.
by rewrite 2!IHp Pos2Nat.inj_xO 2!exprD mulr1 !mulrA.
Qed.

Lemma evalXPN s P n : evalP s (powPN P n) = evalP s P ^+ N.to_nat n.
Proof.
case: n => [|p]/=; first by rewrite CtoR_1.
by rewrite evalXPp/= CtoR_1 mul1r.
Qed.

Lemma comm_evalP x s P :
  (forall c, GRing.comm x (CtoR c)) -> GRing.comm x (evalP s P).
Proof.
move=> Hx; elim: P s => //= i j P IHP Q IHQ s.
exact/commrD/IHQ/commrM/IHP/commrX.
Qed.

Arguments evalP : simpl never.

(* Normalisation *)
Definition norm_semiring :=
  evalPE zeroP oneP addP mulP (fun=> zeroP) powPN (@Pc C) mkXi (fun=> zeroP).

Let evalPE_aux s :=
      @evalPE C R 0 1 +%R *%R (fun=> 0) (fun x n => x ^+ N.to_nat n)
        CtoR (fun i => vm (Pos.pred (Pos.add i s))) (fun=> 0).
Let evalPE := @evalPE C R 0 1 +%R *%R (fun=> 0) (fun x n => x ^+ N.to_nat n)
                CtoR vm (fun=> 0).

Lemma eval_norm_semiring_aux s pe :
  evalP s (norm_semiring pe) = evalPE_aux s pe.
Proof.
elim: pe => //=.
- by move=> p; rewrite eval_mkXi.
- by move=> ? <- ? <-; rewrite evalDP.
- by move=> ? <- ? <-; rewrite evalMP.
by move=> ? <- ?; rewrite evalXPN.
Qed. 

Lemma eval_norm_semiring pe : evalP 1 (norm_semiring pe) = evalPE pe.
Proof.
rewrite eval_norm_semiring_aux; elim: pe => //=.
- by move => ?; rewrite Pos.add_1_r Pos.pred_succ.
- by move=> ? -> ? ->.
- by move=> ? -> ? ->.
by move=> ? ->.
Qed.

End EvalSemiRing.

Section EvalRing.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).
Context (R : pzRingType) (CtoR : C -> R) (vm : positive -> R).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_N : {morph CtoR : x / oppC x >-> - x}).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (vm_comm : forall x i, GRing.comm x (vm i)).

Notation t := (t C).
Notation zeroP := (@zeroP C zeroC).
Notation oneP := (@oneP C oneC).
Notation mkXi := (@mkXi C zeroC oneC).
Notation oppP := (@oppP C oppC).
Notation addP := (@addP C eqbC zeroC addC).
Notation mulP := (@mulP C eqbC zeroC oneC addC mulC).
Notation powPN := (@powPN C eqbC zeroC oneC addC mulC).
Notation evalP := (@evalP C R CtoR vm).

Lemma evalNP s P : evalP s (oppP P) = - evalP s P.
Proof.
elim: P s => [c|i j P IHP Q IHQ] s/=; first by rewrite CtoR_N.
by rewrite IHP IHQ opprD mulrN.
Qed.

Arguments CPol.evalP : simpl never.

(* Normalisation *)
Definition norm_ring :=
  evalPE zeroP oneP addP mulP oppP powPN (@Pc C) mkXi (fun=> zeroP).

Let evalPE_aux s := @evalPE C R 0 1 +%R *%R -%R (fun x n => x ^+ N.to_nat n)
                      CtoR (fun i => vm (Pos.pred (Pos.add i s))) (fun=> 0).
Let evalPE := @evalPE C R 0 1 +%R *%R -%R (fun x n => x ^+ N.to_nat n)
                CtoR vm (fun=> 0).

Lemma eval_norm_ring_aux s pe : evalP s (norm_ring pe) = evalPE_aux s pe.
Proof.
elim: pe => //=.
- by move=> p; rewrite eval_mkXi.
- by move=> ? <- ? <-; rewrite evalDP.
- by move=> ? <- ? <-; rewrite evalMP.
- by move=> ? <-; rewrite evalNP.
by move=> ? <- ?; rewrite evalXPN.
Qed.

Lemma eval_norm_ring pe : evalP 1 (norm_ring pe) = evalPE pe.
Proof.
rewrite eval_norm_ring_aux; elim: pe => //=.
- by move => ?; rewrite Pos.add_1_r Pos.pred_succ.
- by move=> ? -> ? ->.
- by move=> ? -> ? ->.
- by move=> ? ->.
by move=> ? ->.
Qed.

End EvalRing.

End CPol.

Arguments CPol.evalP : simpl never.

(******************************************************************************)
(* Computation-oriented representation of (non-commutative) polynomials       *)
(******************************************************************************)
Module NCPol.

Implicit Types (pre m : seq positive).

derive Inductive t (C : Type) : Type :=
  | Pc : C -> t
  | PX : seq positive -> t -> t -> t. (* [PX m P Q] represents [m * P + Q] *)

(* On normal forms:                                                           *)
(* - [m] in [PX m P Q] must be non-empty.                                     *)
(* - [PX m1 (PX m2 P zeroP) Q] can be normalised to [PX (m1 ++ m2) P Q].      *)
(* - For any [PX m1 P1 (PX m2 P2 P3)], the head of [m1] must be smaller than  *)
(*   the head of [m2].                                                        *)

(* comparison of two monomials [m1] and [m2] of type [seq positive] *)
Variant comparison_monom : Set :=
  (* m1 = m2 *)
  | EqMonom : comparison_monom
  (* m1 = m2 ++ m, i.e., m1 is divisible by m2 *)
  | DvdlMonom m : comparison_monom
  (* m1 ++ m = m2, i.e., m2 is divisible by m1 *)
  | DvdrMonom m : comparison_monom
  (* m1 = pre ++ m1', m2 = pre ++ m2', and m1' < m2' *)
  | LtMonom pre m1' m2' : comparison_monom
  (* m1 = pre ++ m1', m2 = pre ++ m2', and m1' > m2' *)
  | GtMonom pre m1' m2' : comparison_monom.

Fixpoint compare_monom m1 m2 : comparison_monom :=
  match m1, m2 with
  | [::], [::] => EqMonom
  | _, [::] => DvdlMonom m1
  | [::], _ => DvdrMonom m2
  | i :: m1', j :: m2' =>
    match Pos.compare i j with
    | Lt => LtMonom [::] m1 m2
    | Gt => GtMonom [::] m1 m2
    | Eq =>
      match compare_monom m1' m2' with
      | LtMonom p m1'' m2'' => LtMonom (i :: p) m1'' m2''
      | GtMonom p m1'' m2'' => GtMonom (i :: p) m1'' m2''
      | r => r
      end
    end
  end.

Variant compare_monom_spec :
  seq positive -> seq positive -> comparison_monom -> Set :=
  | EqMonom' m : compare_monom_spec m m EqMonom
  | DvdlMonom' m1 m2 : compare_monom_spec (m2 ++ m1) m2 (DvdlMonom m1)
  | DvdrMonom' m1 m2 : compare_monom_spec m1 (m1 ++ m2) (DvdrMonom m2)
  | LtMonom' pre i m1' j m2' :
    Pos.lt i j ->
    compare_monom_spec (pre ++ i :: m1') (pre ++ j :: m2')
      (LtMonom pre (i :: m1') (j :: m2'))
  | GtMonom' pre i m1' j m2' :
    Pos.lt j i ->
    compare_monom_spec (pre ++ i :: m1') (pre ++ j :: m2')
      (GtMonom pre (i :: m1') (j :: m2')).

Lemma compare_monomP m1 m2 : compare_monom_spec m1 m2 (compare_monom m1 m2).
Proof.
elim: m1 m2 => [|i m1 IH] [|j m2]//=; first by constructor.
- by rewrite -[j :: m2]cat0s; constructor.
- by rewrite -[i :: m1]cat0s; constructor.
case Eij: Pos.compare; first last.
- rewrite -[i :: _]cat0s -[j :: _]cat0s; constructor.
  exact/Pos.compare_gt_iff.
- rewrite -[i :: _]cat0s -[j :: _]cat0s; constructor.
  exact/Pos.compare_lt_iff.
rewrite -(Pos.compare_eq _ _ Eij).
by case: IH => *; rewrite -?cat_cons; constructor.
Qed.

Section OpsDef.
Context (C : Type).
Context (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).

Notation t := (t C).
Notation t_eqb := (t_eqb eqbC).

Implicit Types (P Q : t).

(* Polynomial operations *)

Definition zeroP := Pc zeroC.
Definition oneP := Pc oneC.

Definition mkXi i : t := PX [:: i] oneP zeroP.

Definition mkPX m P Q :=
  match P with
  | PX m' P' (Pc c) => if eqbC c zeroC then PX (m ++ m') P' Q else PX m P Q
  | _ => PX m P Q
  end.

(* Opposite *)
Fixpoint oppP P : t :=
  match P with
  | Pc c => Pc (oppC c)
  | PX m P Q => PX m (oppP P) (oppP Q)
  end.

Fixpoint addPC P (c : C) : t :=
  match P with
  | Pc c1 => Pc (addC c1 c)
  | PX m P Q => PX m P (addPC Q c)
  end.

(* Addition *)
Section addP.
Context (addP : t -> t -> t) (P : t).

(* PX mp P zeroP + Q *)
Fixpoint addPX mp Q : t :=
  match Q with
  | Pc c => PX mp P (Pc c)
  | PX mq Ql Qr =>
    match compare_monom mp mq with
    | EqMonom => mkPX mp (addP P Ql) Qr
    | DvdlMonom mp' => mkPX mq (addPX mp' Ql) Qr
    | DvdrMonom mq' => mkPX mp (addP P (PX mq' Ql zeroP)) Qr
    | LtMonom [::] _ _ => PX mp P Q
    | GtMonom [::] _ _ => PX mq Ql (addPX mp Qr)
    | LtMonom pre mp mq => PX pre (PX mp P (PX mq Ql zeroP)) Qr
    | GtMonom pre mp mq => PX pre (PX mq Ql (PX mp P zeroP)) Qr
    end
  end.

End addP.

Fixpoint addP P Q {struct P} : t :=
  match P with
  | Pc c => addPC Q c
  | PX mp Pl Pr =>
    let fix addP' Q {struct Q} :=
      match Q with
      | Pc c => addPC P c
      | PX mq Ql Qr =>
        match compare_monom mp mq with
        | EqMonom => mkPX mp (addP Pl Ql) (addP Pr Qr)
        | DvdlMonom mp' => mkPX mq (addPX addP Pl mp' Ql) (addP Pr Qr)
        | DvdrMonom mq' => mkPX mp (addP Pl (PX mq' Ql zeroP)) (addP Pr Qr)
        | LtMonom [::] _ _ => PX mp Pl (addP Pr Q)
        | GtMonom [::] _ _ => PX mq Ql (addP' Qr)
        | LtMonom pre mp mq => PX pre (PX mp Pl (PX mq Ql zeroP)) (addP Pr Qr)
        | GtMonom pre mp mq => PX pre (PX mq Ql (PX mp Pl zeroP)) (addP Pr Qr)
        end
      end
    in addP' Q
  end.

(* Multiplication *)
Fixpoint mulCP_aux c P : t :=
  match P with
  | Pc c' => Pc (mulC c c')
  | PX m Pl Pr => mkPX m (mulCP_aux c Pl) (mulCP_aux c Pr)
  end.

Definition mulCP c P : t :=
  if eqbC c zeroC then Pc zeroC else
    if eqbC c oneC then P else
      mulCP_aux c P.

Fixpoint mulP P Q {struct P} : t :=
  match P with
  | Pc c => mulCP c Q
  | PX m Pl Pr => mkPX m (mulP Pl Q) (mulP Pr Q)
  end.

Fixpoint powPpos (res P : t) (p : positive) : t :=
  match p with
  | xH => mulP res P
  | xO p => powPpos (powPpos res P p) P p
  | xI p => mulP (powPpos (powPpos res P p) P p) P
  end.

Definition powPN P n := if n is Npos p then powPpos oneP P p else oneP.

End OpsDef.

(*************************)
(* Evaluation of NCPol.t *)
(*************************)
Section EvalSemiRing.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C).
Context (R : pzSemiRingType) (CtoR : C -> R) (vm : positive -> R).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (comm_vm_CtoR : forall i c, GRing.comm (vm i) (CtoR c)).

Notation t := (t C).
Notation zeroP := (@zeroP C zeroC).
Notation oneP := (@oneP C oneC).
Notation mkPX := (@mkPX C eqbC zeroC).
Notation mkXi := (@mkXi C zeroC oneC).
Notation addPC := (@addPC C addC).
Notation addPX := (@addPX C eqbC zeroC).
Notation addP := (@addP C eqbC zeroC addC).
Notation mulCP_aux := (@mulCP_aux C eqbC zeroC mulC).
Notation mulCP := (@mulCP C eqbC zeroC oneC mulC).
Notation mulP := (@mulP C eqbC zeroC oneC mulC).
Notation powPpos := (@powPpos C eqbC zeroC oneC mulC).
Notation powPN := (@powPN C eqbC zeroC oneC mulC).

Implicit Types (P Q : t).

Let comm_vmprod_CtoR m c : GRing.comm (\prod_(i <- m) vm i) (CtoR c).
Proof.
elim: m => [|i m IHm]; first by rewrite big_nil; exact/commr_sym/commr1.
by rewrite big_cons; apply/commr_sym/commrM/commr_sym/IHm/commr_sym.
Qed.

Fixpoint evalP P : R :=
  match P with
  | Pc c => CtoR c
  | PX m P Q => \prod_(i <- m) vm i * evalP P + evalP Q
  end.

Lemma eval_mkPX m P Q :
  evalP (mkPX m P Q) = (\prod_(i <- m) vm i) * evalP P + evalP Q.
Proof.
case: P => [c|m' P [c'|m'' P' P'']]//=.
by have [/eqbCeq->|_]//= := ifP; rewrite CtoR_0 addr0 mulrA -big_cat.
Qed.

Lemma eval_mkXi i : evalP (mkXi i) = vm i.
Proof. by rewrite /= big_cons big_nil CtoR_1 CtoR_0 !mulr1 addr0. Qed.

(* Addition *)
Lemma evalDPC c P : evalP (addPC P c) = evalP P + CtoR c.
Proof.
elim: P => [c'|m Pl _ Pr IHPr]/=; first by rewrite CtoR_D.
by rewrite IHPr addrA.
Qed.

Lemma evalDPX P m Q :
  (forall Q, evalP (addP P Q) = evalP P + evalP Q) ->
  evalP (addPX addP P m Q) = (\prod_(i <- m) vm i) * evalP P + evalP Q.
Proof.
move=> IHP; elim: Q m => //= mq Ql IHQl Qr IHQr mp; case: compare_monomP.
- by move=> {mp mq}m; rewrite eval_mkPX IHP mulrDr addrA.
- by move=> {}mp {}mq; rewrite eval_mkPX IHQl big_cat/= mulrDr mulrA addrA.
- move=> {}mp {}mq.
  by rewrite eval_mkPX IHP/= CtoR_0 addr0 big_cat/= mulrDr mulrA addrA.
- move=> [|i pre] j {}mp k {}mq _ //.
  by rewrite 2!big_cat/= CtoR_0 addr0 mulrDr !mulrA addrA.
move=> [|i pre] j {}mp k {}mq _; first by rewrite /= IHQr addrCA.
by rewrite 2!big_cat/= CtoR_0 addr0 mulrDr !mulrA addrCA addrA.
Qed.

Lemma evalDP P Q : evalP (addP P Q) = evalP P + evalP Q.
Proof.
elim: P Q => [c|mp Pl IHPl Pr IHPr] Q/=; first by rewrite evalDPC addrC.
elim: Q mp => [c'|mq Ql IHQl Qr IHQr] mp/=; first by rewrite evalDPC addrA.
case: compare_monomP.
- by move=> {mp mq}m; rewrite eval_mkPX IHPl IHPr mulrDr addrACA.
- move=> {}mp {}mq.
  by rewrite eval_mkPX evalDPX// IHPr big_cat/= mulrDr !mulrA addrACA.
- move=> {}mp {}mq; rewrite eval_mkPX IHPl IHPr/=.
  by rewrite big_cat/= CtoR_0 addr0 mulrDr !mulrA addrACA.
- move=> [|i pre] j {}mp k {}mq _; first by rewrite /= IHPr/= !addrA.
  by rewrite !big_cat/= CtoR_0 addr0 IHPr mulrDr !mulrA addrACA.
move=> [|i pre] j {}mp k {}mq _; first by rewrite /= IHQr addrCA.
rewrite !big_cat/= CtoR_0 addr0 IHPr mulrDr !mulrA [RHS]addrACA.
by congr +%R; rewrite addrC.
Qed.

(* Multiplication *)
Lemma evalMCP_aux c P : evalP (mulCP_aux c P) = CtoR c * evalP P.
Proof.
elim: P => [c'|m P IHP Q IHQ]/=; first by rewrite CtoR_M.
by rewrite eval_mkPX IHP IHQ mulrDr !mulrA comm_vmprod_CtoR.
Qed.

Lemma evalMCP c P : evalP (mulCP c P) = CtoR c * evalP P.
Proof.
rewrite /mulCP; have [/eqbCeq->|_] := ifP; first by rewrite /=CtoR_0 mul0r.
by have [/eqbCeq->|_] := ifP; [rewrite CtoR_1 mul1r | rewrite evalMCP_aux].
Qed.

Lemma evalMP P Q : evalP (mulP P Q) = evalP P * evalP Q.
Proof.
elim: P => [c|mp Pl IHPl Pr IHPr]/=; first by rewrite evalMCP.
by rewrite eval_mkPX IHPl IHPr mulrDl mulrA.
Qed.

Lemma evalXPp res P p :
  evalP (powPpos res P p) = evalP res * evalP P ^+ Pos.to_nat p.
Proof.
elim: p res => [p IHp|p IHp|] res /=; last by rewrite evalMP.
  by rewrite evalMP 2!IHp Pos2Nat.inj_xI exprSr 2!exprD mulr1 !mulrA.
by rewrite 2!IHp Pos2Nat.inj_xO 2!exprD mulr1 !mulrA.
Qed.

Lemma evalXPN P n : evalP (powPN P n) = evalP P ^+ N.to_nat n.
Proof.
case: n => [|p]/=; first by rewrite CtoR_1.
by rewrite evalXPp/= CtoR_1 mul1r.
Qed.

(* Normalisation *)
Definition norm_semiring :=
  evalPE zeroP oneP addP mulP (fun=> zeroP) powPN (@Pc C) (fun=> zeroP) mkXi.

Let evalPE := @evalPE C R 0 1 +%R *%R (fun=> 0) (fun x n => x ^+ N.to_nat n)
                CtoR (fun=> 0) vm.

Lemma eval_norm_semiring pe : evalP (norm_semiring pe) = evalPE pe.
Proof.
elim: pe => //.
- by move=> ?; rewrite eval_mkXi.
- by move=> /= ? <- ? <-; rewrite evalDP.
- by move=> /= ? <- ? <-; rewrite evalMP.
by move=> /= ? <- ?; rewrite evalXPN.
Qed. 

End EvalSemiRing.

Section EvalRing.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).
Context (R : pzRingType) (CtoR : C -> R) (vm : positive -> R).
Context (eqbCeq : forall c c', eqbC c c' -> c = c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_N : {morph CtoR : x / oppC x >-> - x}).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).
Context (comm_vm_CtoR : forall i c, GRing.comm (vm i) (CtoR c)).

Notation t := (t C).
Notation zeroP := (@zeroP C zeroC).
Notation oneP := (@oneP C oneC).
Notation mkXi := (@mkXi C zeroC oneC).
Notation oppP := (@oppP C oppC).
Notation addP := (@addP C eqbC zeroC addC).
Notation mulP := (@mulP C eqbC zeroC oneC mulC).
Notation powPN := (@powPN C eqbC zeroC oneC mulC).
Notation evalP := (@evalP C R CtoR vm).

Lemma evalNP P : evalP (oppP P) = - evalP P.
Proof.
elim: P => [c|m Pl IHPl Pr IHPr]/=; first by rewrite CtoR_N.
by rewrite IHPl IHPr mulrN opprD.
Qed.

(* Normalisation *)
Definition norm_ring :=
  evalPE zeroP oneP addP mulP oppP powPN (@Pc C) (fun=> zeroP) mkXi.

Let evalPE := @evalPE C R 0 1 +%R *%R -%R (fun x n => x ^+ N.to_nat n)
                CtoR (fun=> 0) vm.

Lemma eval_norm_ring pe : evalP (norm_ring pe) = evalPE pe.
Proof.
elim: pe => //.
- by move=> ?; rewrite eval_mkXi.
- by move=> /= ? <- ? <-; rewrite evalDP.
- by move=> /= ? <- ? <-; rewrite evalMP.
- by move=> /= ? <-; rewrite evalNP.
by move=> /= ? <- ?; rewrite evalXPN.
Qed. 

End EvalRing.

End NCPol.

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
Notation eqbCP := (@CPol.t_eqb C eqbC).
Notation zeroCP := (@CPol.zeroP C zeroC).
Notation oneCP := (@CPol.oneP C oneC).
Notation addCP := (@CPol.addP C eqbC zeroC addC).
Notation mulCP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalCP := (@CPol.evalP C R CtoR cvm 1).

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
Proof. exact: CPol.t_eqb_correct. Qed.

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
Notation eqbCP := (@CPol.t_eqb C eqbC).
Notation zeroCP := (@CPol.zeroP C zeroC).
Notation oneCP := (@CPol.oneP C oneC).
Notation oppCP := (@CPol.oppP C oppC).
Notation addCP := (@CPol.addP C eqbC zeroC addC).
Notation mulCP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalCP := (@CPol.evalP C R CtoR cvm 1).

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

(******************************************************************************)
(* Computation-oriented representation of free (semi)modules                  *)
(******************************************************************************)
Module Mod.

derive Inductive t (R : Type) : Type :=
  | MO : t
  | MX : positive -> R -> t -> t.

Arguments MO {R}.

Section OpsDef.
Context (R : Type) (eqbR : R -> R -> bool).
Context (zeroR oneR : R) (oppR : R -> R) (addR mulR : R -> R -> R).

Notation t := (t R).
Notation t_eqb := (t_eqb R).

Implicit Types (v w : t).

Definition mkMinj i v : t :=
  if v is MX i' x v then MX (Pos.add i i') x v else MO.

Definition mkMX i x v : t := if eqbR x zeroR then mkMinj i v else MX i x v.

Definition mkXi i : t := MX i oneR MO.

(* Opposite *)
Fixpoint oppM v {struct v} : t :=
  if v is MX i x v then MX i (oppR x) (oppM v) else MO.

(* Addition *)
Fixpoint addM v w {struct v} : t :=
  if v is MX i x v then
    (* addM_X i x w = addM (MX i x v) w *)
    (fix addM_X i x w {struct w} : t :=
       if w is MX j y w then
         match Z.pos_sub i j with
         | Zpos k => MX j y (addM_X k x w)
         | Z0 => mkMX i (addR x y) (addM v w)
         | Zneg k => MX i x (addM v (MX k y w))
         end
       else MX i x v) i x w
  else w.

(* Scale *)
Fixpoint scaleM x v {struct v} : t :=
  if v is MX i y v then mkMX i (mulR x y) (scaleM x v) else MO.

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
Notation eqbP := (@CPol.t_eqb C eqbC).
Notation zeroP := (@CPol.zeroP C zeroC).
Notation oneP := (@CPol.oneP C oneC).
Notation addP := (@CPol.addP C eqbC zeroC addC).
Notation mulP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalP := (@CPol.evalP C R CtoR vmR 1).
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
- exact/CPol.t_eqb_correct.
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
Notation eqbP := (@CPol.t_eqb C eqbC).
Notation zeroP := (@CPol.zeroP C zeroC).
Notation oneP := (@CPol.oneP C oneC).
Notation oppP := (@CPol.oppP C oppC).
Notation addP := (@CPol.addP C eqbC zeroC addC).
Notation mulP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalP := (@CPol.evalP C R CtoR vmR 1).
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
- exact/CPol.t_eqb_correct.
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
Notation eqbP := (@NCPol.t_eqb C eqbC).
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
- exact/NCPol.t_eqb_correct.
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
Notation eqbP := (@NCPol.t_eqb C eqbC).
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
- exact/NCPol.t_eqb_correct.
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
Notation eqbCP := (@CPol.t_eqb C eqbC).
Notation zeroCP := (@CPol.zeroP C zeroC).
Notation oneCP := (@CPol.oneP C oneC).
Notation addCP := (@CPol.addP C eqbC zeroC addC).
Notation mulCP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalCP := (@CPol.evalP C R CtoR cvmR 1).

(* Non-commutative polynomials over commutative polynomials *)
Notation Pol := (NCPol.t (CPol.t C)).
Notation eqbP := (@NCPol.t_eqb CPol eqbCP).
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
- exact/NCPol.t_eqb_correct/CPol.t_eqb_correct.
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
Notation eqbCP := (@CPol.t_eqb C eqbC).
Notation zeroCP := (@CPol.zeroP C zeroC).
Notation oneCP := (@CPol.oneP C oneC).
Notation oppCP := (@CPol.oppP C oppC).
Notation addCP := (@CPol.addP C eqbC zeroC addC).
Notation mulCP := (@CPol.mulP C eqbC zeroC oneC addC mulC).
Notation evalCP := (@CPol.evalP C R CtoR cvmR 1).

(* Non-commutative polynomials over commutative polynomials *)
Notation Pol := (NCPol.t (CPol.t C)).
Notation eqbP := (@NCPol.t_eqb CPol eqbCP).
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
- exact/NCPol.t_eqb_correct/CPol.t_eqb_correct.
- exact/Mixed.evalNP.
- exact/Mixed.evalDP.
- exact/Mixed.evalMP.
exact/Mixed.eval_norm_ring.
Qed.

End EvalModule.

End Mixed.

End Mod.
