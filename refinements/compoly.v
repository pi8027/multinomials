From elpi.apps Require Import derive.std.
From HB Require Import structures.
From Stdlib Require Import BinPos BinNat BinInt.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop rings_modules_and_algebras.
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

(************************)
(* Evaluation of CPol.t *)
(************************)
Section EvalSemiRing.
Context (C : pzSemiRingType) (R : comPzSemiRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Notation t := (t C).
Notation mkPinj := (@mkPinj C).
Notation mkPX := (@mkPX C eq_op 0).
Notation mkXi := (@mkXi C 0 1).
Notation oppP :=  (@oppP C id).
Notation addP_C := (@addP_C C +%R).
Notation addP_X := (@addP_X C eq_op 0).
Notation addP_I := (@addP_I C +%R).
Notation addP := (@addP C eq_op 0 +%R).
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

(* Opposite *)
Lemma evalNPid s P : evalP s (oppP P) = evalP s P.
Proof. by elim: P s => //= P IHP i Q IHQ s; rewrite IHP IHQ. Qed.

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

(* Multiplication *)
Lemma evalMPC_aux s c P : evalP s (mulP_C_aux P c) = evalP s P * phiC c.
Proof.
elim: P s => [c'|i P IHP|P IHP i Q IHQ] s/=; first by rewrite rmorphM.
  by rewrite eval_mkPinj IHP.
by rewrite eval_mkPX IHP IHQ mulrDl mulrAC.
Qed.

Lemma evalMPC s c P : evalP s (mulP_C P c) = evalP s P * phiC c.
Proof.
rewrite /mulP_C; have [->|_] := eqVneq; first by rewrite /= rmorph0 mulr0.
have [->|_] := eqVneq; first by rewrite /= rmorph1 mulr1.
by rewrite evalMPC_aux.
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

Lemma evalNP s P : evalP phiC vm s (oppP P) = - evalP phiC vm s P.
Proof.
elim: P s => [c|i p IHp|p IHp i q IHq] s /=.
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
(* - [PX m1 (PX m2 P P0) Q] can be normalised to [PX (m1 ++ m2) P Q].         *)
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

Section Def.
Context (C : Type).
Context (eqC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C) (oppC : C -> C).

Notation t := (t C).
Notation t_eqb := (t_eqb eqC).

Implicit Types (P Q : t).

(* Polynomial operations *)

Definition P0 := Pc zeroC.
Definition P1 := Pc oneC.

Definition mkXi i : t := PX [:: i] P1 P0.

Definition mkPX m P Q :=
  match P with
  | PX m' P' (Pc c) => if eqC c zeroC then PX (m ++ m') P' Q else PX m P Q
  | _ => PX m P Q
  end.

(* Opposite *)
Fixpoint oppP P : t :=
  match P with
  | Pc c => Pc (oppC c)
  | PX m P Q => PX m (oppP P) (oppP Q)
  end.

Fixpoint addP_C P (c : C) : t :=
  match P with
  | Pc c1 => Pc (addC c1 c)
  | PX m P Q => PX m P (addP_C Q c)
  end.

(* Addition *)
Section addP.
Context (addP : t -> t -> t) (P : t).

(* PX mp P P0 + Q *)
Fixpoint addP_X mp Q : t :=
  match Q with
  | Pc c => PX mp P (Pc c)
  | PX mq Ql Qr =>
    match compare_monom mp mq with
    | EqMonom => mkPX mp (addP P Ql) Qr
    | DvdlMonom mp' => mkPX mq (addP_X mp' Ql) Qr
    | DvdrMonom mq' => mkPX mp (addP P (PX mq' Ql P0)) Qr
    | LtMonom [::] _ _ => PX mp P Q
    | GtMonom [::] _ _ => PX mq Ql (addP_X mp Qr)
    | LtMonom pre mp mq => PX pre (PX mp P (PX mq Ql P0)) Qr
    | GtMonom pre mp mq => PX pre (PX mq Ql (PX mp P P0)) Qr
    end
  end.

End addP.

Fixpoint addP P Q {struct P} : t :=
  match P with
  | Pc c => addP_C Q c
  | PX mp Pl Pr =>
    let fix addP' Q {struct Q} :=
      match Q with
      | Pc c => addP_C P c
      | PX mq Ql Qr =>
        match compare_monom mp mq with
        | EqMonom => mkPX mp (addP Pl Ql) (addP Pr Qr)
        | DvdlMonom mp' => mkPX mq (addP_X addP Pl mp' Ql) (addP Pr Qr)
        | DvdrMonom mq' => mkPX mp (addP Pl (PX mq' Ql P0)) (addP Pr Qr)
        | LtMonom [::] _ _ => PX mp Pl (addP Pr Q)
        | GtMonom [::] _ _ => PX mq Ql (addP' Qr)
        | LtMonom pre mp mq => PX pre (PX mp Pl (PX mq Ql P0)) (addP Pr Qr)
        | GtMonom pre mp mq => PX pre (PX mq Ql (PX mp Pl P0)) (addP Pr Qr)
        end
      end
    in addP' Q
  end.

(* Multiplication *)
Fixpoint mulP_C_aux P c : t :=
  match P with
  | Pc c' => Pc (mulC c' c)
  | PX m Pl Pr => mkPX m (mulP_C_aux Pl c) (mulP_C_aux Pr c)
  end.

Definition mulP_C P c : t :=
  if eqC c zeroC then Pc zeroC else
    if eqC c oneC then P else
      mulP_C_aux P c.

Fixpoint mulP P Q {struct Q} : t :=
  match Q with
  | Pc c => mulP_C P c
  | PX m Ql Qr => mkPX m (mulP P Ql) (mulP P Qr)
  end.

Fixpoint powPpos (res P : t) (p : positive) : t :=
  match p with
  | xH => mulP res P
  | xO p => powPpos (powPpos res P p) P p
  | xI p => mulP (powPpos (powPpos res P p) P p) P
  end.

Definition powPN P n := match n with N0 => P1 | Npos p => powPpos P1 P p end.

End Def.

(*************************)
(* Evaluation of NCPol.t *)
(*************************)
Section EvalSemiRing.
Context (C R : pzSemiRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Notation t := (t C).
Notation mkPX := (@mkPX C eq_op 0).
Notation mkXi := (@mkXi C 0 1).
Notation oppP :=  (@oppP C id).
Notation addP_C := (@addP_C C +%R).
Notation addP_X := (@addP_X C eq_op 0).
Notation addP := (@addP C eq_op 0 +%R).
Notation mulP_C_aux := (@mulP_C_aux C eq_op 0 *%R).
Notation mulP_C := (@mulP_C C eq_op 0 1 *%R).
Notation mulP := (@mulP C eq_op 0 1 *%R).
Notation powPpos := (@powPpos C eq_op 0 1 *%R).
Notation powPN := (@powPN C eq_op 0 1 *%R).

Fixpoint evalP (P : t) : R :=
  match P with
  | Pc c => phiC c
  | PX m P Q => (\prod_(i <- m) vm i) * evalP P + evalP Q
  end.

Lemma eval_mkPX m P Q :
  evalP (mkPX m P Q) = (\prod_(i <- m) vm i) * evalP P + evalP Q.
Proof.
case: P => [c|m' P [c'|m'' P' P'']]//=.
by have [->|]//= := eqVneq; rewrite rmorph0 addr0 mulrA -big_cat.
Qed.

Lemma eval_mkXi i : evalP (mkXi i) = vm i.
Proof. by rewrite /= big_cons big_nil rmorph1 rmorph0 !mulr1 addr0. Qed.

(* Opposite *)
Lemma evalNPid P : evalP (oppP P) = evalP P.
Proof.
Admitted.

(* Addition *)
Lemma evalDPC c P : evalP (addP_C P c) = evalP P + phiC c.
Proof.
elim: P => [c'|m Pl _ Pr IHPr]/=; first by rewrite rmorphD.
by rewrite IHPr addrA.
Qed.

Lemma evalDPX P m Q :
  (forall Q, evalP (addP P Q) = evalP P + evalP Q) ->
  evalP (addP_X addP P m Q) = (\prod_(i <- m) vm i) * evalP P + evalP Q.
Proof.
move=> IHP; elim: Q m => //= mq Ql IHQl Qr IHQr mp; case: compare_monomP.
- by move=> {mp mq}m; rewrite eval_mkPX IHP mulrDr addrA.
- by move=> {}mp {}mq; rewrite eval_mkPX IHQl big_cat/= mulrDr mulrA addrA.
- move=> {}mp {}mq.
  by rewrite eval_mkPX IHP/= rmorph0 addr0 big_cat/= mulrDr mulrA addrA.
- move=> [|i pre] j {}mp k {}mq _ //.
  by rewrite 2!big_cat/= rmorph0 addr0 mulrDr !mulrA addrA.
move=> [|i pre] j {}mp k {}mq _; first by rewrite /= IHQr addrCA.
by rewrite 2!big_cat/= rmorph0 addr0 mulrDr !mulrA addrCA addrA.
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
  by rewrite big_cat/= rmorph0 addr0 mulrDr !mulrA addrACA.
- move=> [|i pre] j {}mp k {}mq _; first by rewrite /= IHPr/= !addrA.
  by rewrite !big_cat/= rmorph0 addr0 IHPr mulrDr !mulrA addrACA.
move=> [|i pre] j {}mp k {}mq _; first by rewrite /= IHQr addrCA.
rewrite !big_cat/= rmorph0 addr0 IHPr mulrDr !mulrA [RHS]addrACA.
by congr +%R; rewrite addrC.
Qed.

(* Multiplication *)
Lemma evalMPC_aux c P : evalP (mulP_C_aux P c) = evalP P * phiC c.
Proof.
Admitted.

Lemma evalMPC c P : evalP (mulP_C P c) = evalP P * phiC c.
Proof.
Admitted.

Lemma evalMP P Q : evalP (mulP P Q) = evalP P * evalP Q.
Proof.
Admitted.

Lemma evalXPp res P p :
  evalP (powPpos res P p) = evalP res * evalP P ^+ Pos.to_nat p.
Proof.
Admitted.

Lemma evalXPN P n : evalP (powPN P n) = evalP P ^+ N.to_nat n.
Proof.
Admitted.

End EvalSemiRing.

Section EvalRing.
Context (C : pzRingType) (R : pzRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Notation oppP := (@oppP C -%R).

Lemma evalNP P : evalP phiC vm (oppP P) = - evalP phiC vm P.
Proof.
Admitted.

End EvalRing.

(* Normalization function from PExpr to t *)
Definition norm C (eqC : C -> C -> bool)
  (zeroC oneC : C) (addC mulC : C -> C -> C) (oppC : C -> C) :=
  evalPE
    (Pc zeroC) (Pc oneC)
    (addP eqC zeroC addC) (mulP eqC zeroC oneC mulC) (oppP oppC)
    (powPN eqC zeroC oneC mulC) (@Pc C) (mkXi zeroC oneC).

Section NormAlmostRing.
Context (C R : pzSemiRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).
Context (oppR : R -> R) (oppC : C -> C).

Let evalPE := @evalPE C R 0 1 +%R *%R oppR (fun x n => x ^+ N.to_nat n) phiC vm.
Let norm := @norm C eq_op 0 1 +%R *%R oppC.
Notation evalP := (@evalP C R phiC vm).
Notation oppP := (@oppP C oppC).

Hypothesis evalNP' : forall P, evalP (oppP P) = oppR (evalP P).

Lemma eval_normP_aring pe : evalP (norm pe) = evalPE pe.
Proof.
apply: (@evalPE_R _ _ eq _ _ (fun x p => evalP p = x)) => /=.
- by rewrite rmorph0.
- by rewrite rmorph1.
- by move=> _ P <- _ Q <-; rewrite evalDP.
- by move=> _ P <- _ Q <-; rewrite evalMP.
- by move=> _ P <-; rewrite evalNP'.
- by move=> _ ? <- _ ? /N_RP->; rewrite evalXPN.
- by move=> _ ? ->.
- move=> ? i /positive_RP->.
  by rewrite big_cons big_nil rmorph1 rmorph0 !mulr1 addr0.
exact/PExpr_R_refl.
Qed.

End NormAlmostRing.

Section NormSemiRing.
Context (C R : pzSemiRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Let evalPE := @evalPE C R 0 1 +%R *%R id (fun x n => x ^+ N.to_nat n) phiC vm.
Let norm := @norm C eq_op 0 1 +%R *%R id.
Notation evalP := (@evalP C R phiC vm).

Lemma eval_normP_semiring pe : evalP (norm pe) = evalPE pe.
Proof. by apply: eval_normP_aring => P; rewrite evalNPid. Qed.

End NormSemiRing.

Section NormRing.
Context (C R : comPzRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Let evalPE := @evalPE C R 0 1 +%R *%R -%R (fun x n => x ^+ N.to_nat n) phiC vm.
Let norm := @norm C eq_op 0 1 +%R *%R -%R.
Notation evalP := (@evalP C R phiC vm).

Lemma eval_normP_ring pe : evalP (norm pe) = evalPE pe.
Proof. by apply: eval_normP_aring => P; rewrite evalNP. Qed.

End NormRing.

End NCPol.
