From HB Require Import structures.
From Stdlib Require Import BinPos BinNat BinInt.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop nmodule rings_modules_and_algebras.
From mathcomp Require Import finmap zify.
From mathcomp Require Import syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

Local Open Scope ring_scope.

Import GRing.Theory.

Local Arguments Pos.add : simpl never.

HB.instance Definition _ := hasDecEq.Build positive Pos.eqb_spec.

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

(******************************************************************************)
(* Computation-oriented representation of (commutative) polynomials, also     *)
(* known as the Sparse Horner form (Grégoire and Mahboubi 2005)               *)
(******************************************************************************)
Module CPol.

Section Def.
Context (C : Type) (eqbC : C -> C -> bool).

Inductive t : Type :=
  | Pc : C -> t
  (* [PinjX i j P Q] represents [shift (i - 1) (X_0^j * P + shift 1 Q)], or   *)
  (* equivalently, [X_i^j * shift (i - 1) P + shift i Q]. This constructor    *)
  (* subsumes the [Pinj] and [PX] constructors in the original definition of  *)
  (* Sparse Horner form, and eliminates non-canonical terms of the shape      *)
  (* [Pinj _ (Pinj _ _)].                                                     *)
  | PinjX : positive -> positive -> t -> t -> t.

Fixpoint eqbP (P P' : t) : bool :=
  match P, P' with
  | Pc c, Pc c' => eqbC c c'
  | PinjX i j P Q, PinjX i' j' P' Q' =>
      [&& Pos.eqb i i', Pos.eqb j j', eqbP P P' & eqbP Q Q']
  | _, _ => false
  end.

Lemma eqbPcorrect : (forall c c' : C, eqbC c c' -> c = c') ->
  forall P P' : t, eqbP P P' -> P = P'.
Proof.
move=> HeqbC.
elim=> [c|i j P IHP Q IHQ][c'|i' j' P' Q']//=; first by move=> /HeqbC->.
by move=> /and4P[/Pos.eqb_eq-> /Pos.eqb_eq-> /IHP-> /IHQ->].
Qed.

Lemma eqbPrefl : reflexive eqbC -> reflexive eqbP.
Proof. by move=> ?; elim => //= i j _ -> _ ->; rewrite !Pos.eqb_refl. Qed.

End Def.

Lemma t_eqP (C : eqType) : Equality.axiom (@eqbP C eq_op).
Proof.
move=> P Q; apply/(iffP idP) => [|->]; last exact/eqbPrefl.
by apply/eqbPcorrect => ? ? /eqP->.
Qed.

HB.instance Definition _ (C : eqType) := hasDecEq.Build (t C) (@t_eqP C).

Section OpsDef.
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (oppC : C -> C) (addC mulC : C -> C -> C).

Notation t := (t C).
Notation eqbP := (eqbP eqbC).

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
    if Pos.eqb i' 1 && eqbP Q' zeroP then
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
Fixpoint mapP' (f : C -> C) P : t :=
  match P with
  | Pc c => Pc (f c)
  | PinjX i j P Q =>
      (* if C is an integral domain, [mkPinjX] can probably be [PinjX] *)
      mkPinjX i j (mapP' f P) (mapP' f Q)
  end.

Definition mulCP c P :=
  if eqbC c zeroC then zeroP else
  if eqbC c oneC then P else mapP' (mulC c) P.

Definition mulPC P c :=
  if eqbC c zeroC then zeroP else
  if eqbC c oneC then P else mapP' (mulC ^~ c) P.

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

(* The normal form condition of CPol.t *)

Definition is_norm_aux P : bool :=
  match P with
  | Pc c => ~~ eqbC c zeroC
  | PinjX i _ _ Q => ~~ Pos.eqb i 1 || ~~ eqbP Q zeroP
  end.

Fixpoint is_norm P : bool :=
  match P with
  | Pc _ => true
  | PinjX i j P Q => [&& is_norm_aux P, is_norm P & is_norm Q]
  end.

Context (oneCneq0 : ~~ eqbC oneC zeroC).
Context (opp_eq0 : forall c, eqbC (oppC c) zeroC = eqbC c zeroC).

Lemma norm_mkPinjS i P : is_norm P -> is_norm (mkPinjS i P).
Proof. by case: P. Qed.

Lemma norm_mkPinjX i j P Q :
  is_norm P -> is_norm Q -> is_norm (mkPinjX i j P Q).
Proof.
case: P => /=[c|i' j' P' Q'].
  by case: ifP => [_ _|/=->//]; apply/norm_mkPinjS.
case: ifP => [/andP[? ?]|Hi']/= /and3P[HP' -> HQ' ->];
  rewrite ?{}HP' ?{}HQ' !andbT//.
by case: i' Q' Hi' => []//= [c|]//= ->.
Qed.

Lemma norm_mkXi i : is_norm (mkXi i).
Proof. by rewrite /= oneCneq0. Qed.

Lemma norm_mkX : is_norm mkX.
Proof. exact: norm_mkXi. Qed.

Lemma normNP P : is_norm P -> is_norm (oppP P).
Proof.
elim: P => //= i j P IHP Q IHQ /and3P[+ {}/IHP-> {Q}/IHQ->].
by rewrite !andbT; case: P => [c|[i'|i'|] j' P' [c|]]//=; rewrite opp_eq0.
Qed.

Lemma normDPC P c : is_norm P -> is_norm (addPC P c).
Proof. by elim: P => //= _ _ P _ Q IHQ /and3P[+ -> /IHQ->]; rewrite !andbT. Qed.

Lemma normDPX j P P' :
  (forall P', is_norm P' -> is_norm (addP P P')) ->
  is_norm_aux P -> is_norm P -> is_norm P' -> is_norm (addPX addP P j P').
Proof.
move=> IHP HPaux HP.
elim: P' j => /=[c _ _|i' j' P' IHP' Q' _ j /and3P[HP'aux HP' HQ']].
  by rewrite HPaux HP.
case: i' => [i'|i'|]/=; try by apply/and5P.
have [_|{}j' _|{}j _] := Z_pos_subP.
- exact/norm_mkPinjX/HQ'/IHP.
- by rewrite norm_mkPinjX// IHP//= HP'aux HP'.
exact/norm_mkPinjX/HQ'/IHP'.
Qed.

Lemma normDPIX i j P Q P' :
  (forall P', is_norm P' -> is_norm (addP P P')) ->
  (forall P', is_norm P' -> is_norm (addP Q P')) ->
  is_norm_aux P -> is_norm P -> is_norm Q -> is_norm P' ->
  is_norm (addPIX addP P j Q i P').
Proof.
move=> IHP IHQ HPaux HP HQ.
elim: P' i => /=[c _ _|i' j' P' _ Q' IHQ' i /and3P[HP'aux HP' HQ']].
  by rewrite HPaux HP normDPC.
have [{IHQ'}_|{}i' _|{}i _] := Z_pos_subP; first last.
- by rewrite /= HP'aux HP' IHQ'.
- by rewrite /= HPaux HP IHQ//= HP'aux HP'.
have [_|{}j' _|{}j _] := Z_pos_subP.
- by rewrite norm_mkPinjX ?IHP ?IHQ.
- by rewrite norm_mkPinjX ?IHP ?IHQ //= HP'aux HP'.
exact/norm_mkPinjX/IHQ/HQ'/normDPX.
Qed.

Lemma normDP P P' : is_norm P -> is_norm P' -> is_norm (addP P P').
Proof.
elim: P P' => /=[c P' _|i j P + Q + P' /and3P[? HP HQ]]; first exact/normDPC.
by move=> /(_ _ HP) IHP /(_ _ HQ) IHQ; exact/normDPIX.
Qed.

Lemma norm_mapP f P : is_norm (mapP' f P).
Proof. by elim: P => //= i j P IHP Q IHQ; exact/norm_mkPinjX. Qed.

Lemma normMPC P c : is_norm P -> is_norm (mulPC P c).
Proof.
by rewrite /mulPC => HP; case: ifP => // _; case: ifP => // _; exact/norm_mapP.
Qed.

Lemma normMCP c P : is_norm P -> is_norm (mulCP c P).
Proof.
by rewrite /mulCP => HP; case: ifP => // _; case: ifP => // _; exact/norm_mapP.
Qed.

Lemma normMPI i P P' :
  (forall P', is_norm P' -> is_norm (mulP P P')) ->
  is_norm P -> is_norm P' -> is_norm (mulPI mulP P i P').
Proof.
move=> IHP HP.
elim: P' i => /=[c i _|i' j' P' IHP' Q' IHQ' i /and3P[HP'aux HP' HQ']].
  exact/norm_mkPinjS/normMPC.
have [_|{}i' _|{}i _] := Z_pos_subP.
- exact/norm_mkPinjX/IHP/HQ'/IHP'.
- by rewrite norm_mkPinjS// IHP//= HP'aux HP'.
exact/norm_mkPinjX/IHQ'/HQ'/IHP'.
Qed.

Lemma normMPIX i j P Q P' :
  (forall P', is_norm P' -> is_norm (mulP P P')) ->
  (forall P', is_norm P' -> is_norm (mulP Q P')) ->
  is_norm_aux P -> is_norm P -> is_norm Q -> is_norm P' ->
  is_norm (mulPIX mulP j P Q i P').
Proof.
move=> IHP IHQ HPaux HP HQ.
elim: P' i => /=[c i _|i' j' P' IHP' Q' IHQ' i /and3P[HP'aux HP' HQ']].
  by rewrite normMPC//= HPaux HP HQ.
have [_|{}i' _|{}i _] := Z_pos_subP.
- by rewrite !normDP// !norm_mkPinjX ?IHP ?IHQ ?norm_mkPinjS// normMPI.
- by rewrite !norm_mkPinjX ?IHP ?IHQ//= HP'aux HP' HQ'.
by rewrite norm_mkPinjX ?IHP' ?IHQ'.
Qed.

Lemma normMP P P' : is_norm P -> is_norm P' -> is_norm (mulP P P').
Proof.
elim: P P' => /=[c P' _|i j P + Q + Q' /and3P[? HP HQ]]; first exact/normMCP.
by move=> /(_ _ HP) IHP /(_ _ HQ) IHQ; exact/normMPIX.
Qed.

Lemma normXPpos P Q n : is_norm P -> is_norm Q -> is_norm (powPpos P Q n).
Proof. by elim: n P => [n IHn|n IHn|] P HP HQ/=; rewrite ?normMP// !IHn. Qed.

Lemma normXPN P n : is_norm P -> is_norm (powPN P n).
Proof. by case: n => //= n; exact/normXPpos. Qed.

End OpsDef.

(************************)
(* Evaluation of CPol.t *)
(************************)
Section EvalDef.
Context (C R : Type) (CtoR : C -> R) (vm : positive -> R).
Context (addR mulR : R -> R -> R) (expRn : R -> nat -> R).

Notation t := (t C).

Implicit Types (s : positive) (P Q : t).

Fixpoint evalP s P : R :=
  match P with
  | Pc c => CtoR c
  | PinjX i j P Q =>
    let s' := Pos.add i s in
    addR
      (mulR (expRn (vm (Pos.pred s')) (Pos.to_nat j)) (evalP (Pos.pred s') P))
      (evalP s' Q)
  end.

End EvalDef.

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

Notation evalP := (evalP CtoR vm +%R *%R (@GRing.exp R)).

Let mulrCA_vmX i n x y : vm i ^+ n * (x * y) = x * (vm i ^+ n * y).
Proof. by rewrite !mulrA commrX. Qed.

Let mulrAC_vmX x y i n : x * y * vm i ^+ n = x * vm i ^+ n * y.
Proof. by rewrite -!mulrA commrX. Qed.

Lemma eval_mkPinjS i' s P : evalP s (mkPinjS i' P) = evalP (Pos.add i' s) P.
Proof. by case: P => //= i j P Q; do ?[lia|f_equal]. Qed.

Lemma eval_mkPinjX s i j P Q :
  let s' := Pos.add i s in
  evalP s (mkPinjX i j P Q) =
    vm (Pos.pred s') ^+ Pos.to_nat j * evalP (Pos.pred s') P + evalP s' Q.
Proof.
case: P => [c|[i'|i'|] j' P' Q']/=; try by do ?[lia|f_equal].
- by have [/eqbCeq->|//=] := ifP; rewrite CtoR_0 mulr0 add0r eval_mkPinjS.
have [/(eqbPcorrect eqbCeq)->|]//= := ifP.
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
by rewrite eval_mkPinjX IHP IHQ mulrA mulrDl.
Qed.

Lemma evalMCP s c P : evalP s (mulCP c P) = CtoR c * evalP s P.
Proof.
rewrite /mulCP; have [/eqbCeq->|_] := ifP; first by rewrite /= CtoR_0 mul0r.
have [/eqbCeq->|_] := ifP; first by rewrite /= CtoR_1 mul1r.
elim: P s => [c'|i j P IHP Q IHQ] s/=; first by rewrite CtoR_M.
by rewrite eval_mkPinjX IHP IHQ mulrCA_vmX mulrDr.
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

Arguments CPol.evalP : simpl never.

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
Notation evalP := (evalP CtoR vm +%R *%R (@GRing.exp R)).

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
