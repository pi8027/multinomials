From HB Require Import structures.
From Stdlib Require Import BinPos BinNat BinInt.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop nmodule rings_modules_and_algebras.
From mathcomp Require Import syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

Local Open Scope ring_scope.

Import GRing.Theory.

(* Lists *)

Definition list_eqb (T : Type) (eqT : T -> T -> bool) :=
  fix list_eqb (xs ys : seq T) : bool :=
    match xs, ys with
    | [::], [::] => true
    | x :: xs, y :: ys => eqT x y && list_eqb xs ys
    | _, _ => false
    end.

Lemma list_eqb_correct (T : Type) (eqT : T -> T -> bool) :
  (forall x y : T, eqT x y -> x = y) ->
  forall xs ys : seq T, list_eqb eqT xs ys -> xs = ys.
Proof. by move=> HeqT; elim=> [|x xs IH] [|y ys] //= /andP[/HeqT-> /IH->]. Qed.

(******************************************************************************)
(* Computation-oriented representation of (non-commutative) polynomials       *)
(******************************************************************************)
Module NCPol.

Implicit Types (pre m : seq positive).

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
Context (C : Type) (eqbC : C -> C -> bool).

Inductive t : Type :=
  | Pc : C -> t
  | PX : seq positive -> t -> t -> t. (* [PX m P Q] represents [m * P + Q] *)

(* On normal forms:                                                           *)
(* - [m] in [PX m P Q] must be non-empty.                                     *)
(* - [PX m1 (PX m2 P zeroP) Q] can be normalised to [PX (m1 ++ m2) P Q].      *)
(* - For any [PX m1 P1 (PX m2 P2 P3)], the head of [m1] must be smaller than  *)
(*   the head of [m2].                                                        *)

Fixpoint eqbP (P P' : t) : bool :=
  match P, P' with
  | Pc c, Pc c' => eqbC c c'
  | PX m P Q, PX m' P' Q' => [&& list_eqb Pos.eqb m m', eqbP P P' & eqbP Q Q']
  | _, _ => false
  end.

Lemma eqbPcorrect : (forall c c' : C, eqbC c c' -> c = c') ->
  forall P P' : t, eqbP P P' -> P = P'.
Proof.
move=> HeqbC; elim=> [c|m P IHP Q IHQ] [c'|m' P' Q']//=.
  by move=> /HeqbC->.
by move=> /and3P[/(list_eqb_correct Peqb_true_eq)-> /IHP-> /IHQ->].
Qed.

End Def.

Section OpsDef.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).

Notation t := (t C).
Notation eqbP := (eqbP eqbC).

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
