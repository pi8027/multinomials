From elpi.apps Require Import derive.std.
From HB Require Import structures.
From Stdlib Require Import BinPos BinNat BinInt.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice.
From mathcomp Require Import rings_modules_and_algebras.
Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory.

Local Arguments Pos.add : simpl never.

derive positive.
derive N.

Lemma positive_RP (x y : positive) : positive_R x y -> x = y.
Proof. by elim => // ? ? _ ->. Qed.

Lemma N_RP (n m : N) : N_R n m -> n = m.
Proof. by case => // ? ? /positive_RP ->. Qed.

Lemma positive_R_refl (x : positive) : positive_R x x.
Proof. by elim: x; constructor. Qed.

Lemma N_R_refl (n : N) : N_R n n.
Proof. by case: n; constructor; apply: positive_R_refl. Qed.

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
- move=> /Pos.compare_gt_iff /[dup] ltyx /Z.pos_sub_gt ->; constructor.
  by rewrite Pos.add_comm Pos.sub_add.
Qed.

(**********************************)
(* Reified polynomial expressions *)
(**********************************)
Section PExpr.
Context (C : Type) (R : Type).
Context (zeroR oneR : R) (addR mulR : R -> R -> R) (oppR : R -> R).
Context (powR : R -> N -> R).
Context (phiC : C -> R) (vm : positive -> R).

Inductive PExpr : Type :=
 | PEO : PExpr
 | PEI : PExpr
 | PEc : C -> PExpr
 | PEX : positive -> PExpr
 | PEadd : PExpr -> PExpr -> PExpr
 | PEmul : PExpr -> PExpr -> PExpr
 | PEopp : PExpr -> PExpr
 | PEpow : PExpr -> N -> PExpr.

Fixpoint evalPE (pe : PExpr) {struct pe} : R :=
  match pe with
  | PEO => zeroR
  | PEI => oneR
  | PEc c => phiC c
  | PEX j => vm j
  | PEadd pe1 pe2 => addR (evalPE pe1) (evalPE pe2)
  | PEmul pe1 pe2 => mulR (evalPE pe1) (evalPE pe2)
  | PEopp pe1 => oppR (evalPE pe1)
  | PEpow pe1 n => powR (evalPE pe1) n
  end.

End PExpr.

derive PExpr.
derive evalPE.

Lemma PExpr_R_refl C (CR : C -> C -> Type) (CR_refl : forall a, CR a a) pe :
  PExpr_R CR pe pe.
Proof.
by elim: pe; constructor=> //; [exact: positive_R_refl | exact: N_R_refl].
Qed.

(******************************************************************************)
(* Computation-oriented representation of (commutative) polynomials, also     *)
(* known as the Sparse Horner form (Grégoire and Mahboubi 2005)               *)
(******************************************************************************)
Module CPol.

derive Inductive t (C : Type) : Type :=
  | Pc : C -> t
  | Pinj : positive -> t -> t
  | PX : t -> positive -> t -> t.

Section Def.
Context (C : Type) (eqC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C) (oppC : C -> C).

Notation t := (t C).
Notation t_eqb := (t_eqb eqC).

Implicit Types (P Q : t).

(* Polynomial operations *)

Definition P0 := Pc zeroC.
Definition P1 := Pc oneC.

Definition mkPinj j P : t :=
  match P with
  | Pc _ => P
  | Pinj j' Q => Pinj (Pos.add j j') Q
  | _ => Pinj j P
  end.

Definition mkPinj_pred j P : t :=
  match j with
  | xH => P
  | xO j => Pinj (Pos.pred_double j) P
  | xI j => Pinj (xO j) P
  end.

Definition mkPX P i Q : t :=
  match P with
  | Pc c => if eqC c zeroC then mkPinj xH Q else PX P i Q
  | Pinj _ _ => PX P i Q
  | PX P' i' Q' => if t_eqb Q' P0 then PX P' (Pos.add i' i) Q else PX P i Q
  end.

Definition mkX : t := PX P1 xH P0.

Definition mkXi i : t := mkPinj_pred i mkX.

(* Opposite *)
Fixpoint oppP P : t :=
  match P with
  | Pc c => Pc (oppC c)
  | Pinj j Q => Pinj j (oppP Q)
  | PX P i Q => PX (oppP P) i (oppP Q)
  end.

(* Addition *)
Fixpoint addP_C P (c : C) : t :=
  match P with
  | Pc c1 => Pc (addC c1 c)
  | Pinj j Q => Pinj j (addP_C Q c)
  | PX P i Q => PX P i (addP_C Q c)
  end.

Section addP.
Context (addP : t -> t -> t) (Q : t).

(* [P + Pinj j Q], assuming [addP . Q] is [. + Q] *)
Fixpoint addP_I (j : positive) P : t :=
  match P with
  | Pc c => mkPinj j (addP_C Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k => mkPinj j (addP (Pinj k Q') Q)
      | Z0 => mkPinj j (addP Q' Q)
      | Zneg k => mkPinj j' (addP_I k Q')
      end
  | PX P i Q' =>
      match j with
      | xH => PX P i (addP Q' Q)
      | xO j => PX P i (addP_I (Pos.pred_double j) Q')
      | xI j => PX P i (addP_I (xO j) Q')
      end
  end.

(* [P + PX Q i' P0], assuming [addP . Q] is [. + Q] *)
Fixpoint addP_X (i' : positive) P : t :=
  match P with
  | Pc c => PX Q i' P
  | Pinj j Q' =>
      match j with
      | xH => PX Q i' Q'
      | xO j => PX Q i' (Pinj (Pos.pred_double j) Q')
      | xI j => PX Q i' (Pinj (xO j) Q')
      end
  | PX P i Q' =>
      match Z.pos_sub i i' with
      | Zpos k => mkPX (addP (PX P k P0) Q) i' Q'
      | Z0 => mkPX (addP P Q) i Q'
      | Zneg k => mkPX (addP_X k P) i Q'
      end
  end.

End addP.

Fixpoint addP P P' {struct P'} : t :=
  match P' with
  | Pc c' => addP_C P c'
  | Pinj j' Q' => addP_I addP Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => PX P' i' (addP_C Q' c)
      | Pinj j Q =>
          match j with
          | xH => PX P' i' (addP Q Q')
          | xO j => PX P' i' (addP (Pinj (Pos.pred_double j) Q) Q')
          | xI j => PX P' i' (addP (Pinj (xO j) Q) Q')
          end
      | PX P i Q =>
          match Z.pos_sub i i' with
          | Zpos k => mkPX (addP (PX P k P0) P') i' (addP Q Q')
          | Z0 => mkPX (addP P P') i (addP Q Q')
          | Zneg k => mkPX (addP_X addP P' k P) i (addP Q Q')
          end
      end
  end.

(* Multiplication *)
Fixpoint mulP_C_aux P c : t :=
  match P with
  | Pc c' => Pc (mulC c' c)
  | Pinj j Q => mkPinj j (mulP_C_aux Q c)
  | PX P i Q => mkPX (mulP_C_aux P c) i (mulP_C_aux Q c)
  end.

Definition mulP_C P c :=
  if eqC c zeroC then P0 else
  if eqC c oneC then P else mulP_C_aux P c.

Section mulP_I.
Context (mulP : t -> t -> t) (Q : t).

(* [P * Pinj j Q], assuming [mulP . Q] is [. * Q] *)
Fixpoint mulP_I (j : positive) P : t :=
  match P with
  | Pc c => mkPinj j (mulP_C Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k => mkPinj j (mulP (Pinj k Q') Q)
      | Z0 => mkPinj j (mulP Q' Q)
      | Zneg k => mkPinj j' (mulP_I k Q')
      end
  | PX P' i' Q' =>
      match j with
      | xH => mkPX (mulP_I xH P') i' (mulP Q' Q)
      | xO j' => mkPX (mulP_I j P') i' (mulP_I (Pos.pred_double j') Q')
      | xI j' => mkPX (mulP_I j P') i' (mulP_I (xO j') Q')
      end
   end.

End mulP_I.

Fixpoint mulP P P'' {struct P''} : t :=
  match P'' with
  | Pc c => mulP_C P c
  | Pinj j' Q' => mulP_I mulP Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => mulP_C P'' c
      | Pinj j Q =>
          let QQ' :=
            match j with
            | xH => mulP Q Q'
            | xO j => mulP (Pinj (Pos.pred_double j) Q) Q'
            | xI j => mulP (Pinj (xO j) Q) Q'
            end in
          mkPX (mulP P P') i' QQ'
      | PX P i Q =>
          let QQ' := mulP Q Q' in
          let PQ' := mulP_I mulP Q' xH P in
          let QP' := mulP (mkPinj xH Q) P' in
          let PP' := mulP P P' in
          addP (mkPX (addP (mkPX PP' i P0) QP') i' P0) (mkPX PQ' i QQ')
      end
  end.

Fixpoint powPpos (res P : t) (p : positive) : t :=
  match p with
  | xH => mulP res P
  | xO p => powPpos (powPpos res P p) P p
  | xI p => mulP (powPpos (powPpos res P p) P p) P
  end.

Definition powPN P n := match n with N0 => P1 | Npos p => powPpos P1 P p end.

End Def.

(*******************)
(* Evaluation of t *)
(*******************)
Section EvalSemiRing.
Context (C : pzSemiRingType) (R : comPzSemiRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Notation t := (t C).
Notation mkPinj := (@mkPinj C).
Notation mkPX := (@mkPX C eq_op 0).
Notation mkXi := (@mkXi C 0 1).
Notation addP_C := (@addP_C C +%R).
Notation addP_X := (@addP_X C eq_op 0).
Notation addP_I := (@addP_I C +%R).
Notation addP := (@addP C eq_op 0 +%R).
Notation oppP :=  (@oppP C id).
Notation mulP_C_aux := (@mulP_C_aux C eq_op 0 *%R).
Notation mulP_C := (@mulP_C C eq_op 0 1 *%R).
Notation mulP_I := (@mulP_I C eq_op 0 1 *%R).
Notation mulP := (@mulP C eq_op 0 1 +%R *%R).
Notation powPpos := (@powPpos C eq_op 0 1 +%R *%R).
Notation powPN := (@powPN C eq_op 0 1 +%R *%R).

Fixpoint evalP (s : positive) (P : t) : R :=
  match P with
  | Pc c => phiC c
  | Pinj i Q => evalP (Pos.add i s) Q
  | PX P i Q => evalP s P * vm s ^+ Pos.to_nat i + evalP (Pos.succ s) Q
  end.

Lemma eval_mkPinj j s P : evalP s (mkPinj j P) = evalP (Pos.add j s) P.
Proof. by case: P => //= i P; rewrite Pos.add_assoc (Pos.add_comm i). Qed.

Lemma eval_mkPinj_pred j s P :
  evalP s (mkPinj_pred j P) = evalP (Pos.pred (Pos.add j s)) P.
Proof.
case: j => [j|j|]/=.
- by rewrite Pos.xI_succ_xO Pos.add_succ_l Pos.pred_succ.
- by rewrite -Pos.succ_pred_double Pos.add_succ_l Pos.pred_succ.
by rewrite Pos.add_1_l Pos.pred_succ.
Qed.

Lemma eval_mkPX s P i Q :
  evalP s (mkPX P i Q) =
    evalP s P * vm s ^+ Pos.to_nat i + evalP (Pos.succ s) Q.
Proof.
case: P => [c||P j [c||]]//=; have [->|]//= := eqVneq.
  by rewrite eval_mkPinj rmorph0 mul0r add0r Pos.add_1_l.
by rewrite rmorph0 addr0 Pos2Nat.inj_add exprD mulrA.
Qed.

Lemma eval_mkXi s i : evalP s (mkXi i) = vm (Pos.pred (i + s)).
Proof. by rewrite eval_mkPinj_pred/= rmorph1 mul1r rmorph0 addr0. Qed.

(* Addition *)
Lemma evalDPC s c P : evalP s (addP_C P c) = evalP s P + phiC c.
Proof.
elim: P s => [c'||P IHP i P' IHP'] s //=; first by rewrite rmorphD.
by rewrite IHP' addrA.
Qed.

Lemma evalDPX s P Q i :
  (forall s P, evalP s (addP P Q) = evalP s P + evalP s Q) ->
  evalP s (addP_X addP Q i P) = evalP s Q * vm s ^+ Pos.to_nat i + evalP s P.
Proof.
move=> IHQ; elim: P i => [|[j|j|] P IHP|P IHP j P' IHP'] i //=.
- by rewrite Pos.add_succ_r -Pos.add_succ_l.
- by rewrite Pos.add_succ_r -Pos.add_succ_l Pos.succ_pred_double.
- by rewrite Pos.add_1_l.
have [->|{}j->|{}i->] := Z_pos_subP.
- by rewrite eval_mkPX IHQ/= addrA -mulrDl [evalP s P + _]addrC.
- rewrite eval_mkPX IHQ/= rmorph0 addr0 addrA [_ + evalP s Q]addrC.
  by rewrite mulrDl -mulrA -exprD addnC Pos2Nat.inj_add.
by rewrite eval_mkPX IHP addrA mulrDl -mulrA -exprD addnC Pos2Nat.inj_add.
Qed.

Lemma evalDPI s P Q i :
  (forall s P, evalP s (addP P Q) = evalP s P + evalP s Q) ->
  evalP s (addP_I addP Q i P) = evalP s P + evalP s (Pinj i Q).
Proof.
move=> IHQ; elim: P i s => [c|j P IHP|P IHP j P' IHP'] i s/=.
- by rewrite eval_mkPinj evalDPC addrC.
- have [->|{}j->|{}i->] := Z_pos_subP.
  + by rewrite eval_mkPinj IHQ.
  + by rewrite eval_mkPinj IHQ/= Pos.add_assoc (Pos.add_comm j).
  by rewrite eval_mkPinj IHP/= Pos.add_assoc (Pos.add_comm i).
case: i => [i|i|]/=.
- by rewrite IHP'/= addrA Pos.add_succ_r -Pos.add_succ_l.
- by rewrite IHP'/= addrA Pos.add_succ_r -Pos.add_succ_l Pos.succ_pred_double.
by rewrite IHQ addrA Pos.add_1_l.
Qed.

Lemma evalDP s P Q : evalP s (addP P Q) = evalP s P + evalP s Q.
Proof.
elim: Q P s => [c P|i Q IHQ P|Q IHQ i Q' IHQ' [c|[j|j|] P|P j P']] s/=.
- by rewrite evalDPC.
- by rewrite evalDPI.
- by rewrite evalDPC [RHS]addrC addrA.
- by rewrite IHQ' addrCA/= Pos.add_succ_r -Pos.add_succ_l.
- by rewrite IHQ' addrCA/= Pos.add_succ_r -Pos.add_succ_l Pos.succ_pred_double.
- by rewrite IHQ' addrCA Pos.add_1_l.
have [->|{}j->|{}i->] := Z_pos_subP.
- by rewrite eval_mkPX IHQ IHQ' addrACA -mulrDl.
- rewrite eval_mkPX IHQ IHQ'/= rmorph0 addr0 addrACA.
  by rewrite Pos.add_comm Pos2Nat.inj_add exprD mulrA -mulrDl.
rewrite eval_mkPX evalDPX// IHQ' addrACA [_ + evalP s P]addrC.
by rewrite Pos.add_comm Pos2Nat.inj_add exprD mulrA -mulrDl.
Qed.

Lemma evalNPid s P : evalP s (oppP P) = evalP s P.
Proof. by elim: P s => //= P IHP i Q IHQ s; rewrite IHP IHQ. Qed.

(* Multiplication *)
Lemma evalMPC' s c P : evalP s (mulP_C_aux P c) = evalP s P * phiC c.
Proof.
elim: P s => [c'|i P IHP|P IHP i Q IHQ] s/=; first by rewrite rmorphM.
  by rewrite eval_mkPinj IHP.
by rewrite eval_mkPX IHP IHQ mulrDl mulrAC.
Qed.

Lemma evalMPC s c P : evalP s (mulP_C P c) = evalP s P * phiC c.
Proof.
rewrite /mulP_C; have [->|_] := eqVneq; first by rewrite /= rmorph0 mulr0.
have [->|_] := eqVneq; first by rewrite /= rmorph1 mulr1.
by rewrite evalMPC'.
Qed.

Lemma evalMPI s P Q i :
  (forall s P, evalP s (mulP P Q) = evalP s P * evalP s Q) ->
  evalP s (mulP_I mulP Q i P) = evalP s P * evalP s (Pinj i Q).
Proof.
move=> IHQ; elim: P i s => [c i s|j P IHP i s|P IHP j P' IHP' [i|i|] s]/=.
- by rewrite eval_mkPinj evalMPC mulrC.
- have [->|{}j->|{}i->] := Z_pos_subP.
  + by rewrite eval_mkPinj IHQ.
  + by rewrite eval_mkPinj IHQ/= Pos.add_assoc (Pos.add_comm j).
  by rewrite eval_mkPinj IHP/= Pos.add_assoc (Pos.add_comm i).
- by rewrite eval_mkPX IHP IHP'/= mulrAC Pos.add_succ_r -Pos.add_succ_l -mulrDl.
- rewrite eval_mkPX IHP IHP'/= Pos.add_succ_r -Pos.add_succ_l.
  by rewrite Pos.succ_pred_double mulrAC -mulrDl.
- by rewrite eval_mkPX IHP IHQ/= Pos.add_1_l mulrAC -mulrDl.
Qed.

Lemma evalMP s P Q : evalP s (mulP P Q) = evalP s P * evalP s Q.
Proof.
elim: Q P s => [c P|i Q IHQ P|Q IHQ i Q' IHQ' [c|[j|j|] P|P j P']] s/=.
- by rewrite evalMPC.
- by rewrite evalMPI.
- by rewrite evalMPC mulrC.
- by rewrite eval_mkPX IHQ IHQ'/= Pos.add_succ_r -Pos.add_succ_l -mulrA -mulrDr.
- rewrite eval_mkPX IHQ IHQ'/= Pos.add_succ_r -Pos.add_succ_l.
  by rewrite Pos.succ_pred_double -mulrA -mulrDr.
- by rewrite eval_mkPX IHQ IHQ'/= Pos.add_1_l -mulrA -mulrDr.
rewrite !(evalDP, eval_mkPX) !IHQ IHQ' evalMPI// eval_mkPinj/= rmorph0 !addr0.
rewrite Pos.add_1_l mulrDl mulrAC addrACA -mulrDl -!mulrA -!mulrDr mulrAC.
by rewrite -mulrDl.
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
case: n => [|p]/=; first by rewrite rmorph1.
by rewrite evalXPp/= rmorph1 mul1r.
Qed.

End EvalSemiRing.

Section EvalRing.
Context (C : pzRingType) (R : comPzRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Notation oppP := (@oppP C -%R).

Lemma evalNP P i : evalP phiC vm i (oppP P) = - evalP phiC vm i P.
Proof.
elim: P i => [c|i p IHp|p IHp i q IHq] i' /=.
- by rewrite rmorphN.
- by rewrite IHp.
by rewrite IHp IHq opprD mulNr.
Qed.

End EvalRing.

(* Normalization function from PExpr to t *)
Definition norm C (eqC : C -> C -> bool)
  (zeroC oneC : C) (addC mulC : C -> C -> C) (oppC : C -> C) :=
  evalPE
    (Pc zeroC) (Pc oneC)
    (addP eqC zeroC addC) (mulP eqC zeroC oneC addC mulC) (oppP oppC)
    (powPN eqC zeroC oneC addC mulC) (@Pc C) (mkXi zeroC oneC).

Section NormAlmostRing.
Context (C : pzSemiRingType) (R : comPzSemiRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).
Context (oppR : R -> R) (oppC : C -> C).

Let evalPE_aux s := @evalPE C R 0 1 +%R *%R oppR (fun x n => x ^+ N.to_nat n)
                      phiC (fun i => vm (Pos.pred (Pos.add i s))).
Let evalPE := @evalPE C R 0 1 +%R *%R oppR (fun x n => x ^+ N.to_nat n) phiC vm.
Let norm := @norm C eq_op 0 1 +%R *%R oppC.
Notation evalP := (@evalP C R phiC vm).
Notation oppP := (@oppP C oppC).

Hypothesis evalNP' : forall P s, evalP s (oppP P) = oppR (evalP s P).

Lemma eval_normP_aring_aux s pe : evalP s (norm pe) = evalPE_aux s pe.
Proof.
apply: (@evalPE_R _ _ eq _ _ (fun x p => evalP s p = x)) => /=.
- by rewrite rmorph0.
- by rewrite rmorph1.
- by move=> _ P <- _ Q <-; rewrite evalDP.
- by move=> _ P <- _ Q <-; rewrite evalMP.
- by move=> _ P <-; rewrite evalNP'.
- by move=> _ ? <- _ ? /N_RP->; rewrite evalXPN.
- by move=> _ ? ->.
- by move => _ i /positive_RP->; rewrite eval_mkXi.
exact/PExpr_R_refl.
Qed.

Lemma eval_normP_aring pe : evalP 1 (norm pe) = evalPE pe.
Proof.
rewrite eval_normP_aring_aux; apply: (@evalPE_R _ _ eq _ _ eq) => //=.
- by move => _ ? -> _ ? ->.
- by move => _ ? -> _ ? ->.
- by move => _ ? ->.
- by move => _ ? -> _ ? /N_RP->.
- by move => _ ? ->.
- by move => _ ? /positive_RP->; rewrite Pos.add_1_r Pos.pred_succ.
exact/PExpr_R_refl.
Qed.

End NormAlmostRing.

Section NormSemiRing.
Context (C : pzSemiRingType) (R : comPzSemiRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Let evalPE := @evalPE C R 0 1 +%R *%R id (fun x n => x ^+ N.to_nat n) phiC vm.
Let norm := @norm C eq_op 0 1 +%R *%R id.
Notation evalP := (@evalP C R phiC vm).

Lemma eval_normP_semiring pe : evalP 1 (norm pe) = evalPE pe.
Proof. by apply: eval_normP_aring => P s; rewrite evalNPid. Qed.

End NormSemiRing.

Section NormRing.
Context (C : pzRingType) (R : comPzRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Let evalPE := @evalPE C R 0 1 +%R *%R -%R (fun x n => x ^+ N.to_nat n) phiC vm.
Let norm := @norm C eq_op 0 1 +%R *%R -%R.
Notation evalP := (@evalP C R phiC vm).

Lemma eval_normP_ring pe : evalP 1 (norm pe) = evalPE pe.
Proof. by apply: eval_normP_aring => P s; rewrite evalNP. Qed.

End NormRing.

End CPol.
