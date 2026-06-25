From HB Require Import structures.
From Stdlib Require Import BinPos BinNat BinInt.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype tuple finfun bigop finset.
From mathcomp Require Import ssralg ssrnum ssrint.
From mathcomp Require Import monalg.
Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section Pol.

(* Coefficients *)
Context (C : Type).

Inductive Pol : Type :=
  | Pc : C -> Pol
  | Pinj : positive -> Pol -> Pol
  | PX : Pol -> positive -> Pol -> Pol.

Context (eqC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C) (oppC : C -> C).

Definition P0 := Pc zeroC.
Definition P1 := Pc oneC.

Fixpoint eqPol (P P' : Pol) {struct P'} : bool :=
  match P, P' with
  | Pc c, Pc c' => eqC c c'
  | Pinj j Q, Pinj j' Q' => Pos.eqb j j' && eqPol Q Q'
  | PX P i Q, PX P' i' Q' => Pos.eqb i i' && eqPol Q Q'
  | _, _ => false
  end.

Definition mkPinj j P :=
  match P with
  | Pc _ => P
  | Pinj j' Q => Pinj (Pos.add j' j) Q
  | _ => Pinj j P
  end.

Definition mkPinj_pred j P :=
  match j with
  | xH => P
  | xO j => Pinj (Pos.pred_double j) P
  | xI j => Pinj (xO j) P
  end.

Definition mkPX P i Q :=
  match P with
  | Pc c => if eqC c zeroC then mkPinj xH Q else PX P i Q
  | Pinj _ _ => PX P i Q
  | PX P' i' Q' => if eqPol Q' P0 then PX P' (Pos.add i' i) Q else PX P i Q
  end.

Definition mkXi i := PX P1 i P0.

Definition mkX := mkXi 1.

(** Polynomial operations *)

Fixpoint oppPol (P : Pol) : Pol :=
  match P with
  | Pc c => Pc (oppC c)
  | Pinj j Q => Pinj j (oppPol Q)
  | PX P i Q => PX (oppPol P) i (oppPol Q)
  end.

Fixpoint addPolC (P : Pol) (c : C) : Pol :=
  match P with
  | Pc c1 => Pc (addC c1 c)
  | Pinj j Q => Pinj j (addPolC Q c)
  | PX P i Q => PX P i (addPolC Q c)
  end.

Section PopI.
Context (Pop : Pol -> Pol -> Pol) (Q : Pol).

(** [P + Pinj j Q], assuming [Pop . Q] is [. + Q] *)
Fixpoint addPolI (j : positive) P : Pol :=
  match P with
  | Pc c => mkPinj j (addPolC Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k => mkPinj j (Pop (Pinj k Q') Q)
      | Z0 => mkPinj j (Pop Q' Q)
      | Zneg k => mkPinj j' (addPolI k Q')
      end
  | PX P i Q' =>
      match j with
      | xH => PX P i (Pop Q' Q)
      | xO j => PX P i (addPolI (Pos.pred_double j) Q')
      | xI j => PX P i (addPolI (xO j) Q')
      end
  end.

Variable P' : Pol.

(** [P + PX P' i' P0], assuming [Pop . P'] is [. + P'] *)
Fixpoint addPolX (i' : positive) P : Pol :=
  match P with
  | Pc c => PX P' i' P
  | Pinj j Q' =>
      match j with
      | xH => PX P' i' Q'
      | xO j => PX P' i' (Pinj (Pos.pred_double j) Q')
      | xI j => PX P' i' (Pinj (xO j) Q')
      end
  | PX P i Q' =>
      match Z.pos_sub i i' with
      | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
      | Z0 => mkPX (Pop P P') i Q'
      | Zneg k => mkPX (addPolX k P) i Q'
      end
  end.

End PopI.

Fixpoint addPol P P' {struct P'} : Pol :=
  match P' with
  | Pc c' => addPolC P c'
  | Pinj j' Q' => addPolI addPol Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => PX P' i' (addPolC Q' c)
      | Pinj j Q =>
          match j with
          | xH => PX P' i' (addPol Q Q')
          | xO j => PX P' i' (addPol (Pinj (Pos.pred_double j) Q) Q')
          | xI j => PX P' i' (addPol (Pinj (xO j) Q) Q')
          end
      | PX P i Q =>
          match Z.pos_sub i i' with
          | Zpos k => mkPX (addPol (PX P k P0) P') i' (addPol Q Q')
          | Z0 => mkPX (addPol P P') i (addPol Q Q')
          | Zneg k => mkPX (addPolX addPol P' k P) i (addPol Q Q')
          end
      end
  end.

(** Multiplication *)

Fixpoint mulPolC_aux P c : Pol :=
  match P with
  | Pc c' => Pc (mulC c' c)
  | Pinj j Q => mkPinj j (mulPolC_aux Q c)
  | PX P i Q => mkPX (mulPolC_aux P c) i (mulPolC_aux Q c)
  end.

Definition mulPolC P c :=
  if eqC c zeroC then P0 else
  if eqC c oneC then P else mulPolC_aux P c.

(** [P * Pinj j Q], assuming [mulPol . Q] is [. * Q] *)
Section mulPolI.
Context (mulPol : Pol -> Pol -> Pol) (Q : Pol).

Fixpoint mulPolI (j : positive) P : Pol :=
  match P with
  | Pc c => mkPinj j (mulPolC Q c)
  | Pinj j' Q' =>
      match Z.pos_sub j' j with
      | Zpos k => mkPinj j (mulPol (Pinj k Q') Q)
      | Z0 => mkPinj j (mulPol Q' Q)
      | Zneg k => mkPinj j' (mulPolI k Q')
      end
  | PX P' i' Q' =>
      match j with
      | xH => mkPX (mulPolI xH P') i' (mulPol Q' Q)
      | xO j' => mkPX (mulPolI j P') i' (mulPolI (Pos.pred_double j') Q')
      | xI j' => mkPX (mulPolI j P') i' (mulPolI (xO j') Q')
      end
   end.
End mulPolI.

Fixpoint mulPol P P'' {struct P''} : Pol :=
  match P'' with
  | Pc c => mulPolC P c
  | Pinj j' Q' => mulPolI mulPol Q' j' P
  | PX P' i' Q' =>
      match P with
      | Pc c => mulPolC P'' c
      | Pinj j Q =>
          let QQ' :=
            match j with
            | xH => mulPol Q Q'
            | xO j => mulPol (Pinj (Pos.pred_double j) Q) Q'
            | xI j => mulPol (Pinj (xO j) Q) Q'
            end in
          mkPX (mulPol P P') i' QQ'
      | PX P i Q =>
          let QQ' := mulPol Q Q' in
          let PQ' := mulPolI mulPol Q' xH P in
          let QP' := mulPol (mkPinj xH Q) P' in
          let PP' := mulPol P P' in
          addPol (mkPX (addPol (mkPX PP' i P0) QP') i' P0) (mkPX PQ' i QQ')
      end
  end.

Fixpoint Psquare P : Pol :=
  match P with
  | Pc c => Pc (mulC c c)
  | Pinj j Q => Pinj j (Psquare Q)
  | PX P i Q =>
      let twoPQ := mulPol P (mkPinj xH (mulPolC Q (addC oneC oneC))) in
      let Q2 := Psquare Q in
      let P2 := Psquare P in
      mkPX (addPol (mkPX P2 i P0) twoPQ) i Q2
  end.

Fixpoint Ppow_pos (res P : Pol) (p : positive) : Pol :=
  match p with
  | xH => mulPol res P
  | xO p => Ppow_pos (Ppow_pos res P p) P p
  | xI p => mulPol (Ppow_pos (Ppow_pos res P p) P p) P
  end.

Definition Ppow_N P n := match n with N0 => P1 | Npos p => Ppow_pos P1 P p end.

(*
Fixpoint Pol_is_norm P : bool :=
  match P with
  | Pc _ => true
  | Pinj _ (Pc _) | Pinj _ (Pinj _ _) => false
  | Pinj _ (P' as PX _ _ _) => Pol_is_norm P'
  | PX (Pc c) _ _
  end.
*)
End Pol.

(* Pol to a ring *)

Section PolSemiringTheory.

Local Open Scope ring_scope.

Context (C : pzSemiRingType) (R : comPzSemiRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).

Fixpoint phiPol (s : positive) (P : Pol C) : R :=
  match P with
  | Pc c => phiC c
  | Pinj i Q => phiPol (Pos.add i s) Q
  | PX P i Q => phiPol s P * (vm s ^+ Pos.to_nat i) + phiPol (Pos.succ s) Q
  end.

Notation Pol := (Pol C).
Notation mkPinj := (@mkPinj C).
Notation mkPX := (@mkPX C eq_op 0).
Notation addPolC := (@addPolC C +%R).
Notation mulPolC_aux := (@mulPolC_aux C eq_op 0 *%R).
Notation mulPolC := (@mulPolC C eq_op 0 1 *%R).
Notation addPolX := (@addPolX C eq_op 0).
Notation addPol := (@addPol C eq_op 0 +%R).
Notation mulPolI := (@mulPolI C eq_op 0 1 *%R).
Notation mulPol := (@mulPol C eq_op 0 1 +%R *%R).
Notation Ppow_N := (@Ppow_N C eq_op 0 1 +%R).

Arguments Pos.add : simpl never.

(* https://github.com/rocq-prover/stdlib/blob/0543892eea4b4eba4b809dea353b89a08910d222/theories/setoid_ring/Ring_polynom.v#L124 *)
(* Lemma mkPinj_ok j s P : phiPol s (mkPinj j P) = phiPol (Pos.add j s) P.
Proof. by case: P => //= i P; rewrite Pos.add_assoc. Qed. *)

(* Lemma mkPX_ok s P i Q :
  phiPol s (mkPX P i Q) =
    phiPol s P * vm s ^+ Pos.to_nat i + phiPol (Pos.succ s) Q.
Proof.
case: P => [c||P j [c||]]//=.
  by have [->|//] := eqVneq; rewrite mkPinj_ok rmorph0 mul0r add0r Pos.add_1_l.
by have [->|]//= := eqVneq; rewrite rmorph0 addr0 Pos2Nat.inj_add exprD mulrA.
Qed. *)

(* Lemma addPolC_ok c P s : phiPol s (addPolC P c) = phiPol s P + phiC c.
Proof.
elim: P s => [c'||P IHP i P' IHP'] s //=; first by rewrite rmorphD.
by rewrite IHP' addrA.
Qed.

Lemma mulPolC_aux_ok c P s : phiPol s (mulPolC_aux P c) = phiPol s P * phiC c.
Proof.
elim: P s => [c'|i P IHP|P IHP i Q IHQ] s/=; first by rewrite rmorphM.
  by rewrite mkPinj_ok IHP.
by rewrite mkPX_ok IHP IHQ mulrDl mulrAC.
Qed. *)

(* Lemma mulPolC_ok c P s : phiPol s (mulPolC P c) = phiPol s P * phiC c.
Proof.
rewrite /mulPolC; have [->|_] := eqVneq; first by rewrite /= rmorph0 mulr0.
have [->|_] := eqVneq; first by rewrite /= rmorph1 mulr1.
by rewrite mulPolC_aux_ok.
Qed.

Lemma addPolX_ok P P' k s :
  (forall P' s, phiPol s (addPol P' P) = phiPol s P' + phiPol s P) ->
  phiPol s (addPolX addPol P k P') =
    phiPol s P * vm s ^+ Pos.to_nat k + phiPol s P'.
Proof.
Abort. *)

Hypothesis addPol_ok : forall P' P i, phiPol i (addPol P P') = phiPol i P + phiPol i P'.
Hypothesis mulPol_ok : forall P P' i, phiPol i (mulPol P P') = phiPol i P * phiPol i P'.

End PolSemiringTheory.

Section Evaluation.

Local Open Scope ring_scope.
Context (C : Type). 
Context (R : Type).
Context (zeroR oneR : R) (addR mulR : R -> R -> R) (oppR : R -> R).
Context (powR : R -> N -> R).
Context (phiC : C -> R).
Context (vm : positive -> R).


Inductive PExpr : Type :=
 | PEO : PExpr
 | PEI : PExpr
 | PEc : C -> PExpr
 | PEX : positive -> PExpr
 | PEadd : PExpr -> PExpr -> PExpr
 | PEsub : PExpr -> PExpr -> PExpr
 | PEmul : PExpr -> PExpr -> PExpr
 | PEopp : PExpr -> PExpr
 | PEpow : PExpr -> N -> PExpr.

Fixpoint PEeval (pe:PExpr) {struct pe} : R :=
match pe with
| PEO => zeroR
| PEI => oneR
| PEc c => phiC c
| PEX j => vm j 
| PEadd pe1 pe2 => addR (PEeval pe1) (PEeval pe2)
| PEsub pe1 pe2 => addR (PEeval pe1) (oppR (PEeval pe2))
| PEmul pe1 pe2 => mulR (PEeval pe1) (PEeval pe2)
| PEopp pe1 => oppR (PEeval pe1)
| PEpow pe1 n => powR (PEeval pe1) n
end.
End Evaluation.
Check PEeval.

 Section NORM_SUBST_REC.
  Context (C : Type). 
  Context (zeroC oneC : C) (addC mulC : C -> C -> C) (oppC : C -> C).
  Context (eqC : C -> C -> bool).
  Context (powR : C -> N -> C).

  Let addPol := @addPol C eqC zeroC addC.
  Let mulPol := @mulPol C eqC zeroC oneC addC mulC.
  Let oppPol := @oppPol C oppC.
  Let powPol := @Ppow_N C eqC zeroC oneC addC mulC.
  Let mk_X j := mkPinj_pred j (@mkX C zeroC oneC).
  Definition norm := @PEeval C (Pol C) (Pc zeroC) (Pc oneC) addPol mulPol oppPol powPol (@Pc C) mk_X.
 End NORM_SUBST_REC.

  Section Thm.
Context (C : pzSemiRingType) (R : comPzSemiRingType).
Context (phiC : {rmorphism C -> R}) (vm : positive -> R).
Local Open Scope ring_scope. 
Let pow (x : R) (n : N) : R := x ^+ (N.to_nat n).
Let PEeval :=  @PEeval C R 0%R 1%R +%R *%R id pow phiC vm.
Let norm := @norm C 0%R 1%R +%R *%R id eq_op.
Lemma norm_aux_spec l pe :
    PEeval pe == phiPol phiC vm l (norm pe).
  Proof.
  Admitted.

End Thm.