From Trocq Require Import Trocq.
From HB Require Import structures.
From Stdlib Require Import BinPos BinNat BinInt.
From mathcomp Require Import ssreflect ssrbool ssrfun choice.
From mathcomp Require Import rings_modules_and_algebras.
From mathcomp Require Import monalg.
From mathcomp Require Import cring_base cring_refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

Local Open Scope ring_scope.

Import CPol.
Import GRing.Theory.

Section Trocq.

Variable (I : choiceType) (vm : positive -> I).
Variable (C : Type) (eqbC : C -> C -> bool) (zeroC : C).
Variable (R : pzSemiRingType) (CtoR : C -> R).

(* To circumvent a Trocq limitation we need to define a constant for the types
   we want to define the refinement relation on.
   Trocq fails because it matches on the types being related expecting a
   syntactically equal structure, which is not true in this case.
   To recover from this we hide these types under a name so that Trocq can
   consider them an "atom".
 *)
Definition Pol := (CPol.t C).
(* If we don't force the type of pol to land in Type, then Trocq errors when
   declaring the refinement relation because it fails to make predArgType
   subtype of Type
    *)
Definition pol : Type := {malg R[{cmonom I}]}.

Definition Rel : Pol -> pol -> Type :=
  fun P p => CPol_R vm eqbC zeroC CtoR p P.

Definition Map : Pol -> pol := (CPol_to_malg vm CtoR).

Definition Rel_in_graph : forall P p, Rel P p -> Map P = p.
Proof. by move=> P p [<-]. Defined.

Definition RelParam : Hierarchy.Param2b0.Rel Pol pol.
Proof.
- eexists; last by constructor.
by econstructor; exact: Rel_in_graph.
Defined.

Definition RelParamSym : Hierarchy.Param02b.Rel pol Pol.
Proof. apply: Param2b0_sym; apply RelParam. Defined.

Trocq Use RelParam.
Trocq Use RelParamSym.
Trocq Use Param01_paths.

(* We can turn arguments of type Pol into arguments of type pol *)
Goal (forall (T : Type), Pol -> T).
Proof.
  trocq.
  suff : forall T, pol -> T by [].
  Abort.

(* We can turn conclusions in pol to conclusions in Pol. *)
Goal (pol).
Proof.
  trocq.
  suff : Pol by [].
  Abort.

Section operations.

  Hypothesis (CtoR_0 : CtoR zeroC = 0).
  Definition zeroP : Pol := (CPol.zeroP zeroC).
  Definition zero_pol : pol := 0.
  (* the type RelParam zeroP 0 fails in the use case afterwards *)
  Definition zero_R_sym : RelParamSym zero_pol zeroP := zero_R vm eqbC CtoR_0.
  Trocq Use zero_R_sym.
  Definition zero_RR : RelParam zeroP zero_pol := zero_R vm eqbC CtoR_0.
  Trocq Use zero_RR.

  (* we cannot turn this goal into forall p, p = p because we are missing a
     function of type pol -> Pol that is included in CPol_R *)
  Goal (forall (P : Pol), P = P).
  Proof.
    Fail trocq.
  (* It fails because the type of the goal is a dependent function,
     and for the proof transfer to work one needs the graph of CPol_to_malg to
     be included in CPol_R. That is, we need the refinement relation to be also
     of kind 2a. However, CPol_R cannot be proved 2a since it requires the
     polynomial P to be in normal form. We could compose with a normalization
     procedure by default to sort this out.
   *)
    Abort.

  (* This is not a dependent type, however we still fail since we need a map pol -> Pol
     that is included in CPol_R (a 2b relation in the other direction) to be
     able to transport over an equality in Pol.
  *)
  Goal zeroP = zeroP.
  Proof.
    Fail trocq.
    Abort.

  (* The following transport succeeds.
     We have zero_R which guarantees that the image of zero_pol under the map
     (CPol_to_malg) is zeroP and is included in CPol_R.
   *)
  Goal zero_pol = zero_pol.
  Proof.
    trocq.
    suff: zeroP = zeroP by [].
    Abort.

  Goal (forall (p : pol), p = p).
  Proof.
    Fail trocq.
    (* requires a map Pol -> pol s.t. the output is in the relation. *)
    Abort.

  Hypothesis (addC : C -> C -> C).
  Hypothesis (CtoR_D : {morph CtoR : x y / addC x y >-> x + y}).
  (* A definition fails if eqtype is imported *)
  Hypothesis (CtoR_eqb : forall c c', (eqtype.eq_op (CtoR c) (CtoR c')) = (eqbC c c')).

  Definition addPol : Pol -> Pol -> Pol := CPol.addP eqbC zeroC addC.
  Definition addpol : pol -> pol -> pol := fun p q => p + q.
  Definition add_R : forall P p, RelParam P p -> forall Q q, RelParam Q q ->
                                                  RelParam (addPol P Q) (addpol p q).
  Proof. by move=> P p pR Q q qR; apply add_R. Defined.
  Definition add_R_sym : forall p P, RelParamSym p P -> forall q Q, RelParamSym q Q ->
                                                  RelParamSym (addpol p q) (addPol P Q).
  Proof. by move=> P p pR Q q qR; apply add_R. Defined.

  Trocq Use add_R add_R_sym.

  Goal (addpol zero_pol zero_pol) = zero_pol.
  Proof.
    trocq.
    suff: (addPol zeroP zeroP = zeroP) by [].
    Abort.

  Hypothesis inj_vm : injective vm.
  Definition eqbPol : Pol -> Pol -> Type := fun P Q => (CPol.eqbP eqbC P Q).
  Definition eqbpol : pol -> pol -> Type := fun p q => (eqtype.eq_op p q).
  Definition eqb_R : forall P p, RelParam P p ->
                            forall Q q, RelParam Q q ->
                                   Hierarchy.Param11.Rel (eqbpol p q) (eqbPol P Q).
  Proof.
  move=> P p /(eqb_R inj_vm CtoR_eqb CtoR_0) H Q q.
  move=> /H; rewrite /eqbpol/eqbPol=> ->.
  exact: id_Param11.
  Defined.

  Trocq Use eqb_R.
  (* problem in Trocq elaboration, this should work *)
  (* to-do: debug why does this fails *)
  Goal (eqbpol zero_pol zero_pol).
    Proof.
      Fail trocq.
      eapply eqb_R.
      - exact: zero_RR.
      - exact: zero_RR.
    Abort.

  Definition eqb_R_sym : forall p P, RelParamSym p P ->
                            forall q Q , RelParamSym q Q ->
                                   Hierarchy.Param11.Rel (eqbPol P Q) (eqbpol p q).
  Proof.
  move=> p P pR q Q qR.
  by apply Param11_sym; apply eqb_R.
  Defined.
  Trocq Use eqb_R_sym.

  (* problem in Trocq elaboration, this should work *)
  (* to-do: debug why does this fails *)
  Goal (eqbPol zeroP zeroP).
      Fail trocq.
      (* it should be as follows *)
      eapply eqb_R_sym.
      - exact: zero_R_sym.
      - exact: zero_R_sym.
      Abort.

End operations.

End Trocq.
