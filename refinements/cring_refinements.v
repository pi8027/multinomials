From elpi.apps Require Import derive.std.
From HB Require Import structures.
From Stdlib Require Import BinPos BinNat BinInt.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop nmodule rings_modules_and_algebras.
From mathcomp Require Import finmap monalg.
From mathcomp Require Import zify.
From mathcomp Require Import param monalg_ext cring_base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

Local Open Scope ring_scope.

Import GRing.Theory.

Local Arguments Pos.add : simpl never.

(********************************************************)
(* Refinements for multivariate commutative polynomials *)
(********************************************************)
Module CPol.
Import CPol.

Local Arguments CPol.evalP : clear simpl.

Elpi derive.param2 t.
Elpi derive.param2 eqbP.
Elpi derive.param2 zeroP.
Elpi derive.param2 oneP.
Elpi derive.param2 mkPinjS.
Elpi derive.param2 mkPinjX.
Elpi derive.param2 mkXi.
Elpi derive.param2 mkX.
Elpi derive.param2 oppP.
Elpi derive.param2 addPC.
Elpi derive.param2 addPX.
Elpi derive.param2 addPIX.
Elpi derive.param2 addP.
Elpi derive.param2 mapP'.
Elpi derive.param2 mulCP.
Elpi derive.param2 mulPC.
Elpi derive.param2 mulPI.
Elpi derive.param2 mulPIX.
Elpi derive.param2 mulP.
Elpi derive.param2 powPpos.
Elpi derive.param2 powPN.
Elpi derive.param2 is_norm_aux.
Elpi derive.param2 is_norm.
Elpi derive.param2 evalP.

(* The map function for CPol.t *)
Section Map.
Context (C C' : Type) (f : C -> C').

Fixpoint mapP (P : t C) : t C' :=
  match P with
  | Pc c => Pc (f c)
  | PinjX i j P Q => PinjX i j (mapP P) (mapP Q)
  end.

Lemma t_R_mapP (P : t C) : t_R (fun x y => f y = x) (mapP P) P.
Proof.
by elim: P => [c|i j P IHP Q IHQ]/=;
  constructor => //; apply: positive_R_refl.
Qed.

Lemma mapP_t_R (P : t C') (P' : t C) :
  t_R (fun x y => f y = x) P P' -> mapP P' = P.
Proof.
elim; first by move=> _ c <-.
by move=> i _ /positive_R_eq <- j _ /positive_R_eq <- _ {}P _ <- _ {}Q _ <-.
Qed.

End Map.

(* Some naturality results *)
Section OpsMap.
Context (C C' : Type) (CtoC' : C -> C').
Context (eqbC : C -> C -> bool) (eqbC' : C' -> C' -> bool).
Context (CtoC'_eqb : forall x y, eqbC' (CtoC' x) (CtoC' y) = eqbC x y).
Context (zeroC : C) (zeroC' : C') (CtoC'_0 : CtoC' zeroC = zeroC').
Context (oneC : C) (oneC' : C') (CtoC'_1 : CtoC' oneC = oneC').
Context (oppC : C -> C) (oppC' : C' -> C').
Context (CtoC'_N : forall x, CtoC' (oppC x) = oppC' (CtoC' x)).
Context (addC : C -> C -> C) (addC' : C' -> C' -> C').
Context (CtoC'_D : forall x y, CtoC' (addC x y) = addC' (CtoC' x) (CtoC' y)).
Context (mulC : C -> C -> C) (mulC' : C' -> C' -> C').
Context (CtoC'_M : forall x y, CtoC' (mulC x y) = mulC' (CtoC' x) (CtoC' y)).

Let C_R (c' : C') (c : C) := CtoC' c = c'.

Let eqbC_R : forall c1' c1, C_R c1' c1 -> forall c2' c2, C_R c2' c2 ->
  bool_R (eqbC' c1' c2') (eqbC c1 c2).
Proof. by move=> _ ? <- _ ? <-; rewrite CtoC'_eqb; exact/bool_R_refl. Qed.

Let oppC_R : forall c' c, C_R c' c -> C_R (oppC' c') (oppC c).
Proof. by move=> _ ? <-; apply/CtoC'_N. Qed.

Let addC_R : forall c1' c1, C_R c1' c1 -> forall c2' c2, C_R c2' c2 ->
  C_R (addC' c1' c2') (addC c1 c2).
Proof. by move=> _ ? <- _ ? <-; apply/CtoC'_D. Qed.

Let mulC_R : forall c1' c1, C_R c1' c1 -> forall c2' c2, C_R c2' c2 ->
  C_R (mulC' c1' c2') (mulC c1 c2).
Proof. by move=> _ ? <- _ ? <-; apply/CtoC'_M. Qed.

Lemma mapP_N P : mapP CtoC' (oppP oppC P) = oppP oppC' (mapP CtoC' P).
Proof. exact/mapP_t_R/oppP_R/t_R_mapP. Qed.

Lemma mapP_D P Q :
  mapP CtoC' (addP eqbC zeroC addC P Q) =
  addP eqbC' zeroC' addC' (mapP CtoC' P) (mapP CtoC' Q).
Proof. exact/mapP_t_R/addP_R/t_R_mapP/t_R_mapP. Qed.

Lemma mapP_M P Q :
  mapP CtoC' (mulP eqbC zeroC oneC addC mulC P Q) =
  mulP eqbC' zeroC' oneC' addC' mulC' (mapP CtoC' P) (mapP CtoC' Q).
Proof. exact/mapP_t_R/mulP_R/t_R_mapP/t_R_mapP. Qed.

End OpsMap.

(* Refinements *)
Section RefinementsSemiRing.
Context (I : choiceType) (vm : positive -> I).
Context (C : Type) (eqbC : C -> C -> bool).
Context (zeroC oneC : C) (addC mulC : C -> C -> C).
Context (R : pzSemiRingType) (CtoR : C -> R).

Context (vm_inj : injective vm).
Context (CtoR_eqb : forall c c', (CtoR c == CtoR c') = eqbC c c').
Context (CtoR_0 : CtoR zeroC = 0).
Context (CtoR_1 : CtoR oneC = 1).
Context (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
Context (CtoR_M : {morph CtoR : x y / mulC x y >-> x * y}).

(* First we refine [{malg R[cmonom I]}] to [CPol.t R] *)
Notation pre_is_norm_aux := (@is_norm_aux R eq_op 0%R).
Notation pre_is_norm := (@is_norm R eq_op 0%R).

Definition pre_CPol_to_malg' (s : positive) : t R -> {malg R[cmonom I]} :=
  evalP malgC (fun i => << ucm (vm i) >>)
    +%R *%R (@GRing.exp {malg R[cmonom I]}) s.

Definition pre_CPol_to_malg := pre_CPol_to_malg' 1.

Definition pre_CPol_R (p : {malg R[cmonom I]}) (P : t R) : Type :=
  (pre_CPol_to_malg P = p) * pre_is_norm P.

Let lt_msupp_eval s s' k P : Pos.lt s s' ->
  k \in msupp (pre_CPol_to_malg' s' P) -> k (vm s) = 0%N.
Proof.
elim: P s' k => [c|i j P IHP Q IHQ] s' k ltss'/=.
  by move=> /(fsubsetP (msuppC_le _)) /[!inE] /eqP ->; rewrite cm1.
move=> /(fsubsetP (msuppD_le _ _)) /[!inE] /orP[|]; last by apply: IHQ; lia.
move=> /msuppM_le[k1 [k2 []]]; rewrite expUn.
move=> /(fsubsetP msuppU_le) /[!inE] /eqP-> /IHP + ->.
rewrite cmM => ->; first lia.
rewrite addn0 cmX ucmE; apply/eqP; rewrite muln_eq0 eqb0; apply/orP; right.
by apply/eqP => /vm_inj; lia.
Qed.

Let lt_msupp_eval_PinjX s s' k i j P Q : Pos.lt (Pos.succ s) (i + s') ->
  k \in msupp (pre_CPol_to_malg' s' (PinjX i j P Q)) -> k (vm s) = 0%N.
Proof.
move=> /= ltss' /(fsubsetP (msuppD_le _ _)) /[!inE] /orP[]; last first.
  by apply: lt_msupp_eval; lia.
move=> /msuppM_le[k1 [k2 []]]; rewrite expUn.
move=> /(fsubsetP msuppU_le) /[!inE] /eqP-> + ->.
rewrite cmM cmX ucmE; have [/vm_inj|_] := eqP; first lia.
by rewrite muln0 add0n; apply: lt_msupp_eval; lia.
Qed.

Let div_eval_small s s' P : Pos.lt s s' ->
  divfgm (ucm (vm s)) (pre_CPol_to_malg' s' P) = 0.
Proof.
move=> ltss'; apply/big1_seq => k /andP[] /[swap] /(lt_msupp_eval ltss').
by move=> + /dvdcmPleq /(_ (vm s)) => ->; rewrite cmUU.
Qed.

Let mod_eval_small s s' P : Pos.lt s s' ->
  modfgm (ucm (vm s)) (pre_CPol_to_malg' s' P) = pre_CPol_to_malg' s' P.
Proof.
move=> ltss'.
by rewrite [RHS](divfgm_eq (ucm (vm s))) div_eval_small// mul0r add0r.
Qed.

Let div_eval_PinjX_small s s' i j P Q :
  Pos.lt (Pos.succ s) (i + s') ->
  divfgm (ucm (vm s)) (pre_CPol_to_malg' s' (PinjX i j P Q)) = 0.
Proof.
move=> ltss'; apply/big1_seq => k /andP[] /[swap] /(lt_msupp_eval_PinjX ltss').
by move=> + /dvdcmPleq /(_ (vm s)) => ->; rewrite cmUU.
Qed.

Let mod_eval_PinjX_small s s' i j P Q :
  Pos.lt (Pos.succ s) (i + s') ->
  modfgm (ucm (vm s)) (pre_CPol_to_malg' s' (PinjX i j P Q)) =
    pre_CPol_to_malg' s' (PinjX i j P Q).
Proof.
move=> ltss'.
by rewrite [RHS](divfgm_eq (ucm (vm s))) div_eval_PinjX_small// mul0r add0r.
Qed.

Let div_eval_PinjX s i j P Q :
  divfgm (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j))
    (pre_CPol_to_malg' s (PinjX i j P Q)) =
  pre_CPol_to_malg' (Pos.pred (i + s)) P.
Proof.
rewrite /= expUn expr1n raddfD/= mulKfgm; have [j' ->] := Pos2Nat.is_succ j.
by rewrite expmnS divfgMm div_eval_small ?raddf0 ?addr0//; lia.
Qed.

Let mod_eval_PinjX s i j P Q :
  modfgm (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j))
    (pre_CPol_to_malg' s (PinjX i j P Q)) =
  pre_CPol_to_malg' (i + s) Q.
Proof.
rewrite /= expUn expr1n raddfD/= modfgmMr add0r.
rewrite [RHS](divfgm_eq (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j))).
have [j' ->] := Pos2Nat.is_succ j.
rewrite {1}[in RHS]expmnS divfgMm div_eval_small; first lia.
by rewrite raddf0 mul0r add0r.
Qed.

Let norm_aux_neq0 s P :
  pre_is_norm_aux P -> pre_is_norm P -> pre_CPol_to_malg' s P != 0.
Proof.
elim: P s => [c s + _|i j P IHP Q _ s].
  by apply/contra_neq => /malgP /(_ mone); rewrite mcoeffUU raddf0 => ->.
rewrite [pre_is_norm _]/= => Haux /and3P[HPaux HP HQ]; apply/eqP.
move=> /(f_equal (divfgm (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j)))).
by rewrite div_eval_PinjX raddf0; apply/eqP/IHP.
Qed.

Let norm_aux_mod_neq0 s P : pre_is_norm_aux P -> pre_is_norm P ->
  modfgm (ucm (vm s)) (pre_CPol_to_malg' s P) != 0.
Proof.
elim: P s => [/= c s c_neq0 _|i j P IHP Q _ s].
  rewrite modfgmU dvdcm1 cm1_eq1 -malgC0E.
  by apply/contra_neq: c_neq0 => /malgC_inj.
rewrite /is_norm_aux -/eq_op [pre_is_norm _]/=.
case: eqVneq => [-> /= Q_neq0|i_neq1 _] /and3P[HPaux HP HQ]; last first.
  rewrite mod_eval_PinjX_small; first by case: i i_neq1 => //; lia.
  apply/contra_neq: (IHP (Pos.pred (i + s)) HPaux HP).
  move/(f_equal (divfgm (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j)))).
  by rewrite div_eval_PinjX raddf0 => ->; rewrite raddf0.
rewrite /= Pos.add_1_l Pos.pred_succ; have [{}j ->] := Pos2Nat.is_succ j.
rewrite raddfD/= exprS -mulrA modfgmMr add0r mod_eval_small; first lia.
case: {i j P IHP HPaux HP} Q Q_neq0 HQ => [c|i j P Q] .
  by move=> + _ /=; apply/contra_neq; rewrite -malgC0E => /malgC_inj ->.
rewrite [pre_is_norm _]/= => _ /and3P[HPaux HP HQ]; apply/eqP.
move/(f_equal
  (divfgm (expmn (ucm (vm (Pos.pred (i + Pos.succ s)))) (Pos.to_nat j)))).
by rewrite div_eval_PinjX raddf0; apply/eqP/norm_aux_neq0.
Qed.

Let eqb_R_aux s c P :
  pre_is_norm P -> c%:MP = pre_CPol_to_malg' s P -> P = Pc c.
Proof.
case: P => [/=c' _ /malgC_inj->//|i j P Q].
rewrite [pre_is_norm _]/= => /and3P[HPaux HP HQ].
move=> /(f_equal (divfgm (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j)))).
rewrite div_eval_PinjX divfgmU dvdcm1; have [j' ->] := Pos2Nat.is_succ j.
case: ifP => [/cmP /(_ (vm (Pos.pred (i + s))))|_].
  by rewrite cmX cmUU muln1 cm1.
by move/esym/eqP; rewrite -[_ == _]negbK norm_aux_neq0.
Qed.

Let pre_eqb_R :
  forall p P, pre_CPol_R p P -> forall p' P', pre_CPol_R p' P' ->
  (p == p') = (P == P').
Proof.
move=> _ P [<- P_norm] _ P' [<- P'_norm]; apply/eqP/eqP => [|->//].
rewrite /pre_CPol_to_malg.
elim: P P' xH P_norm P'_norm => [c P'|i j P IHP Q IHQ [c'|i' j' P' Q']] s.
- by move=> _ ? /eqb_R_aux->.
- by move=> ? _ /esym /eqb_R_aux; apply.
rewrite [pre_is_norm _]/= => /and3P[HPaux HP HQ].
rewrite [pre_is_norm _]/= => /and3P[HP'aux HP' HQ'] Heq.
have {}IHP := IHP _ _ HP HP'.
have {HQ HQ'}IHQ := IHQ _ _ HQ HQ'.
have eqii': i = i'.
  apply/contra_eq: Heq => neqii' {IHP IHQ}.
  wlog ltii': i j P Q i' j' P' Q' HPaux HP HP'aux HP' {neqii'} / Pos.lt i i'.
    have [?|[eqii'|?]] := Pos.lt_total i i'.
    - exact.
    - by move: neqii'; rewrite eqii' eq_refl.
    by rewrite eq_sym; exact.
  apply/eqP.
  move/(f_equal (divfgm (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j)))).
  rewrite div_eval_PinjX; have [{}j ->] := Pos2Nat.is_succ j.
  rewrite expmnS divfgMm [in RHS]div_eval_PinjX_small; first lia.
  by rewrite raddf0; apply/eqP/norm_aux_neq0.
move: Heq; rewrite -{i'}eqii' => Heq.
have eqjj': j = j'.
  apply/contra_eq: Heq => neqjj' {IHP IHQ}.
  wlog ltjj': j P Q j' P' Q' HPaux HP HP'aux HP' {neqjj'} / Pos.lt j j'.
    have [?|[eqjj'|?]] := Pos.lt_total j j'.
    - exact.
    - by move: neqjj'; rewrite eqjj' eq_refl.
    by rewrite eq_sym; exact.
  apply/eqP.
  move/(f_equal (divfgm (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j)))).
  rewrite div_eval_PinjX /=.
  have {ltjj'} ->: j' = (j + (j' - j))%positive by lia.
  rewrite Pos2Nat.inj_add exprD -mulrA raddfD/= expUn expr1n mulKfgm.
  have [j'' ->] := Pos2Nat.is_succ j.
  rewrite expmnS divfgMm div_eval_small ?raddf0 ?addr0; first lia.
  have [{j' j''}j ->] := Pos2Nat.is_succ (j' - j).
  move/(f_equal (modfgm (ucm (vm (Pos.pred (i + s)))))).
  by rewrite exprS -mulrA modfgmMr; apply/eqP/norm_aux_mod_neq0.
move: Heq; rewrite -{j'}eqjj' => Heq.
move:
  (f_equal (divfgm (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j))) Heq)
  (f_equal (modfgm (expmn (ucm (vm (Pos.pred (i + s)))) (Pos.to_nat j))) Heq).
by rewrite !div_eval_PinjX !mod_eval_PinjX => /IHP -> /IHQ ->.
Qed.

(* We use the previous results and naturality to refine [malg R[cmonom I]] to *)
(* [CPol.t C]. *)
Notation zeroP := (@zeroP C zeroC).
Notation oneP := (@oneP C oneC).
Notation mkXi := (@mkXi C zeroC oneC).
Notation addP := (@addP C eqbC zeroC addC).
Notation mulP := (@mulP C eqbC zeroC oneC addC mulC).
Notation powPN := (@powPN C eqbC zeroC oneC addC mulC).
Notation is_norm := (@is_norm C eqbC zeroC).

Definition CPol_to_malg : t C -> {malg R[cmonom I]} :=
  evalP (malgC \o CtoR) (fun i => << ucm (vm i) >>)
    +%R *%R (@GRing.exp {malg R[cmonom I]}) 1.

Definition CPol_R (p : {malg R[cmonom I]}) (P : t C) : Type :=
  (CPol_to_malg P = p) * is_norm P.

Let CPol_to_malg_map P : pre_CPol_to_malg (mapP CtoR P) = CPol_to_malg P.
Proof.
apply/(@evalP_R R C (fun x y => CtoR y = x) _ _ eq)/t_R_mapP/positive_R_refl.
- by move=> /= _ ? <-.
- by move=> ? _ /positive_R_eq<-.
- by move=> ? _ <- ? _ <-.
- by move=> ? _ <- ? _ <-.
by move=> ? _ <- ? _ /nat_R_eq<-.
Qed.

Let CPol_R_map p P : pre_CPol_R p (mapP CtoR P) = CPol_R p P.
Proof.
congr ((_ = _) * Datatypes.is_true _)%type; first exact/CPol_to_malg_map.
apply/bool_R_eq/(@is_norm_R R C (fun x y => CtoR y = x))/t_R_mapP/CtoR_0.
by move=> _ ? <- _ ? <-; rewrite CtoR_eqb; exact/bool_R_refl.
Qed.

Lemma eqb_R : forall p P, CPol_R p P -> forall p' P', CPol_R p' P' ->
  (p == p') = (eqbP eqbC P P').
Proof.
move=> p P Hp p' P' Hp'; rewrite -!CPol_R_map in Hp Hp'.
rewrite (pre_eqb_R Hp Hp').
apply/bool_R_eq/eqbP_R/t_R_mapP/t_R_mapP => _ ? <- _ ? <-.
by rewrite CtoR_eqb; exact/bool_R_refl.
Qed.

Lemma add_R : forall p p', CPol_R p p' -> forall q q', CPol_R q q' ->
  CPol_R (p + q) (addP p' q').
Proof.
move=> _ p [<- p_norm] _ q [<- q_norm]; apply/pair/normDP => //.
rewrite -!CPol_to_malg_map (mapP_D CtoR_eqb CtoR_0 CtoR_D); apply/evalDP.
- by move=> ? ? /eqP.
- exact: rmorph0.
exact: rmorphD.
Qed.

Lemma mul_R : forall p p', CPol_R p p' -> forall q q', CPol_R q q' ->
  CPol_R (p * q) (mulP p' q').
Proof.
move=> _ p [<- p_norm] _ q [<- q_norm]; apply/pair/normMP => //.
rewrite -!CPol_to_malg_map (mapP_M CtoR_eqb CtoR_0 CtoR_1 CtoR_D CtoR_M).
apply/evalMP.
- by move=> ? ? /eqP.
- exact: rmorph0.
- exact: rmorph1.
- exact: rmorphD.
- exact: rmorphM.
move=> x i; rewrite /GRing.comm [LHS]fgmulgU [RHS]fgmulUg.
by apply/eq_bigr => /= j _; rewrite mul1r mulr1 mulmC.
Qed.

End RefinementsSemiRing.

End CPol.
