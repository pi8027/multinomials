From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import bigop nmodule rings_modules_and_algebras.
From mathcomp Require Import finmap monalg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory.

(* Monomials and polynomials *)

Section Malg.

Context {I : choiceType}.

Implicit Types (m : cmonom I).

Definition dvdcm m1 m2 : bool := all (fun i => m1 i <= m2 i) (finsupp m1).

Lemma dvdcmPleq {m1 m2} : reflect (forall i, m1 i <= m2 i) (dvdcm m1 m2).
Proof.
apply/(iffP idP) => [dvd i|?]; last exact/allP.
by case: finsuppP (allP dvd i) => // _ ->.
Qed.

Lemma dvdcmE m1 m2 : dvdcm m1 m2 = (mmul (divcm m2 m1) m1 == m2).
Proof.
apply/dvdcmPleq/cmP => [+ i|+ i] => /(_ i); rewrite mulcmE divcmE.
  exact/subnK.
apply/contra_eqT; rewrite -ltnNge => /[dup] /ltnW /eqP ->.
by rewrite add0n ltn_neqAle eq_sym => /andP[].
Qed.

Lemma dvdcmP {m1 m2} : reflect (exists m, mmul m m1 = m2) (dvdcm m1 m2).
Proof.
apply/(iffP idP); first by rewrite dvdcmE => /eqP<-; exists (divcm m2 m1).
by move=> [m <-]; apply/dvdcmPleq => i; rewrite mulcmE leq_addl.
Qed.

Lemma dvdcmm : reflexive dvdcm.
Proof. by move=> m; apply/dvdcmPleq. Qed.

Lemma dvd1cm m : dvdcm mone m.
Proof. by apply/dvdcmP; exists m; rewrite mulm1. Qed.

Lemma dvdcm1 m : (dvdcm m mone) = (m == mone).
Proof.
apply/idP/eqP => [dvd|->]; last exact/dvdcmm.
by apply/eqP/cmP => i; move: (dvdcmPleq dvd i); rewrite cm1 leqn0 => /eqP.
Qed.

Lemma dvdcm_mull d m1 m2 : dvdcm d m2 -> dvdcm d (mmul m1 m2).
Proof.
move=> dvd; apply/dvdcmPleq => i.
by apply/(leq_trans (dvdcmPleq dvd i)); rewrite mulcmE leq_addl.
Qed.

Lemma dvdcm_mulr d m1 m2 : dvdcm d m1 -> dvdcm d (mmul m1 m2).
Proof. by rewrite mulmC; apply/dvdcm_mull. Qed.

Lemma divcmK m1 m2 : dvdcm m1 m2 -> mmul (divcm m2 m1) m1 = m2.
Proof. by move=> /dvdcmP[{}m2 <-]; rewrite mulcmK. Qed.

Section MalgNmod.

Context {G : nmodType} (m : cmonom I).

Implicit Types (g : {malg G[cmonom I]}).

(* Euclidean division of polynomial by monomial *)
Definition divfgm g :=
  \sum_(k <- msupp g | dvdcm m k) << g@_k *g divcm k m >>.

Definition modfgm g := \sum_(k <- msupp g | ~~ dvdcm m k) << g@_k *g k >>.

Lemma divfgmEw g domg : (msupp g `<=` domg)%fset ->
  divfgm g = \sum_(k <- domg | dvdcm m k) << g@_k *g divcm k m >>.
Proof.
move=> le_d; rewrite [LHS]big_mkcond [RHS]big_mkcond (big_fset_incl _ le_d)//.
by move=> k _; case: msuppP => // _ _; rewrite monalgU0 if_same.
Qed.

Lemma modfgmEw g domg : (msupp g `<=` domg)%fset ->
  modfgm g = \sum_(k <- domg | ~~ dvdcm m k) << g@_k *g k >>.
Proof.
move=> le_d; rewrite [LHS]big_mkcond [RHS]big_mkcond (big_fset_incl _ le_d)//.
by move=> k _; case: msuppP => // _ _; rewrite monalgU0 if_same.
Qed.

Fact divfgm_is_nmod_morphism : nmod_morphism divfgm.
Proof.
split=> [|g1 g2]; first by rewrite /divfgm msupp0 big_mkcond big_seq_fset0.
rewrite (divfgmEw (msuppD_le _ _)) (divfgmEw (fsubsetUl _ (msupp g2))).
rewrite (divfgmEw (fsubsetUr (msupp g1) _)) -big_split/=.
by apply/eq_bigr => k; rewrite mcoeffD monalgUD.
Qed.

Fact modfgm_is_nmod_morphism : nmod_morphism modfgm.
Proof.
split=> [|g1 g2]; first by rewrite /modfgm msupp0 big_mkcond big_seq_fset0.
rewrite (modfgmEw (msuppD_le _ _)) (modfgmEw (fsubsetUl _ (msupp g2))).
rewrite (modfgmEw (fsubsetUr (msupp g1) _)) -big_split/=.
by apply/eq_bigr => k; rewrite mcoeffD monalgUD.
Qed.

HB.instance Definition _ :=
  GRing.isNmodMorphism.Build {malg G[cmonom I]} {malg G[cmonom I]} divfgm
    divfgm_is_nmod_morphism.

HB.instance Definition _ :=
  GRing.isNmodMorphism.Build {malg G[cmonom I]} {malg G[cmonom I]} modfgm
    modfgm_is_nmod_morphism.

Lemma divfgmU x k :
  divfgm << x *g k >> = if dvdcm m k then << x *g divcm k m >> else 0.
Proof. by rewrite (divfgmEw msuppU_le) big_mkcond big_seq_fset1 mcoeffUU. Qed.

Lemma modfgmU x k : modfgm << x *g k >> = if dvdcm m k then 0 else << x *g k >>.
Proof.
by rewrite (modfgmEw msuppU_le) big_mkcond big_seq_fset1 mcoeffUU if_neg.
Qed.

End MalgNmod.

Lemma mcoeff_div (G : nmodType) (m1 m2 : cmonom I) (g : {malg G[cmonom I]}) :
  (divfgm m1 g)@_m2 = g@_(mmul m1 m2).
Proof.
rewrite raddf_sum/=; have [m_in_g|m_nin_g] := msuppP g; last first.
  apply/big1_seq => /= _ /andP[/dvdcmP[m <-]] m_in_g; rewrite mcoeffU mulcmK.
  by case: eqP m_in_g m_nin_g => // <-; rewrite mulmC => ->.
rewrite big_mkcond/= (big_fsetD1 _ m_in_g)/= dvdcm_mulr ?dvdcmm// mulKcm.
rewrite mcoeffUU big1_fset ?addr0// => /= m /[!inE] /andP[+ _] _.
case dvdcmP => // -[{}m <-]; rewrite mulcmK mcoeffU.
by have [->|//] := m =P _; rewrite mulmC eqxx.
Qed.

Lemma divfgMm (G : nmodType) (m1 m2 : cmonom I) (g : {malg G[cmonom I]}) :
  divfgm (mmul m1 m2) g = divfgm m2 (divfgm m1 g).
Proof. by apply/malgP => /= m; rewrite !mcoeff_div mulmA. Qed.

Section MalgSemiRing.

Context {R : pzSemiRingType}.

Implicit Types (g : {malg R[cmonom I]}).

Lemma mulfgmK m g : divfgm m (g * << m >>) = g.
Proof.
rewrite [_ * _]fgmulgU raddf_sum/= [RHS]monalgE; apply/eq_bigr => k _.
by rewrite mulr1 divfgmU dvdcm_mull ?dvdcmm// mulcmK.
Qed.

Lemma mulKfgm m g : divfgm m (<< m >> * g) = g.
Proof. by rewrite -commU mulfgmK. Qed.

Lemma modfgmMl m g : modfgm m (g * << m >>) = 0.
Proof.
rewrite [_ * _]fgmulgU raddf_sum/=.
by apply/big1_fset => /= k kg _; rewrite mulr1 modfgmU dvdcm_mull ?dvdcmm.
Qed.

Lemma modfgmMr m g : modfgm m (<< m >> * g) = 0.
Proof. by rewrite -commU modfgmMl. Qed.

Lemma divfgm_eq m g : g = divfgm m g * << m >> + modfgm m g.
Proof.
rewrite /divfgm /modfgm mulr_suml big_mkcond [r in _ + r]big_mkcond.
rewrite -big_split/= [LHS]monalgE; apply/eq_bigr=> k _.
by case: ifP => //=; rewrite (addr0, add0r)// [_ * _]fgmulUU mulr1 => /divcmK->.
Qed.

End MalgSemiRing.

End Malg.
