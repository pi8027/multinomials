Require Import ssreflect.
From Stdlib Require Import BinNat.
From mathcomp Require Import ssrnat ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Monoid.

    Variable S : Type.

    (* Free monoid *)
    Inductive ms (S : Type) := 
    (* embeding every element of S into ms *)
    | Mc : S -> ms S
    (* a constructor for 0 *)
    | Mo : ms S
    (* syntax for the operation *)
    | Madd : ms S -> ms S -> ms S.

    Section Interp.

        (* Given a target type T with monoid symbols we can interpret it as a monoid *)
        Variable (T : Type).
        Variable (zeroT : T) (addT : T -> T -> T).
        Variable (emb : S -> T).

        (* Free monoid generator *)
        Fixpoint interp (m : ms S) : T :=
        match m with 
        | Mc t => emb t 
        | Mo => zeroT 
        | Madd m1 m2 => addT (interp m1) (interp m2)
        end.

    End Interp.
    
    Section Absortion.

        (* Remark: *)
        (* A meta circular interpretation absorbs all the properties from the meta *)
        (* The converse is also true: 
           A property on the interpretation implies the theory on the meta. *)
        Variable (zero : S) (add : S -> S -> S).
        Local Notation interp := (interp zero add (id)).
        Local Notation Mo := (Mo S). 

        (* Assoc Absortion *)
        Lemma addA : (forall t1 t2 t3, add t1 (add t2 t3) = (add (add t1 t2) t3)) <-> 
                    (forall m1 m2 m3, interp (Madd m1 (Madd m2 m3)) = interp (Madd (Madd m1 m2) m3)).
        Proof.
        split=> /= addA t1 t2 t3; first by rewrite addA.
        by rewrite (addA (Mc t1) (Mc t2) (Mc t3)).
        Qed.

        (* neutral identity Absortion *)
        Lemma add1m : (forall t1, add zero t1 = t1) <-> 
                    (forall m1,  interp (Madd Mo m1) = interp m1).
        Proof.
        split=> /= um t1; first by rewrite um.
        by rewrite (um (Mc t1)).
        Qed.

        (* idem for the symmetric case *) 
        Lemma addm1 : (forall t1, add t1 zero = t1) <-> 
                    (forall m1,  interp (Madd m1 Mo) = interp m1).
        Proof.
        split=> /= um t1; first by rewrite um. 
        by rewrite (um (Mc t1)).
        Qed.

    End Absortion.

    Section Param.

        (* Given a target type T and intermediate type M, both with monoid symbols *)
        Variable (M : Type).
        Variable (zeroM : M) (addM : M -> M -> M).

        Variable (T : Type).
        Variable (zeroT : T) (addT : T -> T -> T).

        (* Their interpretation from S into M on the left, 
            and into T and then into M on the right,
            commutes for an additive symbol-preserving morphism *)
        
        (* S *)
        (* | \ *)
        (* |  \*)
        (* |   T*)
        (* |  /*)
        (* | / *)
        (* M *)

        Variable (f : S -> T).
        Variable (phi : T -> M).
        Hypothesis (phi1 : zeroM = phi zeroT).
        Hypothesis (phimorph : forall t1 t2, phi (addT t1 t2) = addM (phi t1) (phi t2)). 

        Variable (g : S -> M).
        Hypothesis (refinement : g =1 phi \o f).

        (* Interpret S into the into the monoid symbols monoid M *)
        Definition eval := interp zeroM addM g.

        (* Embed S into the monoid T *)
        Definition emb := interp zeroT addT f.

        Lemma Param_fl ms : eval ms = phi (emb ms).
        Proof.
        elim: ms=> [s||m1 IHm1 m2 IHm2] /=.
        - exact: refinement.
        - exact: phi1. 
        - by rewrite IHm1 IHm2 phimorph.
        Qed.

    End Param.

End Monoid.

Section sr_pair.

    Variable (S T M : Type).
    (* M and T have monoid symbols *)
    Variable (zeroM : M) (addM : M -> M -> M).
    Variable (zeroT : T) (addT : T -> T -> T).

    (* On the left we eval with g *)
    Variable (g : S -> M).
    
    (* On the right we eval with g post composing with a section retraction pair *) 
    (* (h \o (i \o g)) *)
    Variable (phi : T -> M).
    Variable (i : M -> T).

    Hypothesis phi1 : zeroM = phi zeroT.
    Hypothesis phi_additive : forall t1 t2 : T, phi (addT t1 t2) = addM (phi t1) (phi t2).
    Hypothesis hi_can : cancel i phi.

    Definition LHSs := @interp S M zeroM addM g.
    Definition RHSs := @interp S T zeroT addT (i \o g).

    Lemma param_sr ms : LHSs ms = phi (RHSs ms).
    Proof. 
    apply Param_fl=> [//| // |] s.
    by rewrite /= hi_can.
    Qed.

End sr_pair.

Section Example.

    Variable (S : Type).
    Variable (g : S -> nat).

    Definition inj_Snat := @interp S nat 0 addn g.
    Definition inj_SN := @interp S N N0 N.add (bin_of_nat \o g).
    Definition phis := nat_of_bin.
    
    Lemma nat_of_bin_additive (t1 t2 : N) : phis (t1 + t2)%num = (phis t1) + (phis t2).
    Proof.
    case: t1=> [|p1]; first by rewrite add0n.
    case: t2=> [|p2] /= ; first by rewrite addn0.
    by rewrite nat_of_add_pos. 
    Qed.

    Lemma Nnat ms : inj_Snat ms = phis (inj_SN ms).
    Proof. 
    by apply: (param_sr _ _ nat_of_bin_additive bin_of_natK).
    Qed.

End Example.

