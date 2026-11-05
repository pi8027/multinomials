From Corelib Require Import BinNums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

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
