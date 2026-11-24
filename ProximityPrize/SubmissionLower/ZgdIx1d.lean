import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.AC
set_option Elab.async false
open _root_ renaming AddCommGroup→vi,AdjoinRoot.algebraMap_eq'→zm,AdjoinRoot.mk→pQ,AdjoinRoot.mk_C→zi,AdjoinRoot.of→t7,Algebra→lI,Algebra.IsAlgebraic→v8,Algebra.TensorProduct.includeRight→t5,Algebra.TensorProduct.tensorQuotientEquiv→C9,Algebra.algebraMap→lz,Algebra.trdeg→ oy,CommRing→n5,DFunLike.congr_fun→pU,FaithfulSMul→wA,Field→c9,Finset→pz,Finset.le_sup→y5,Finset.sum_congr→uJ,Finset.sum_le_sum→th,FractionRing→ oD,Function.Injective→ oz,Function.Injective.isDomain→zc,Function.Surjective→Fa,Ideal→cy,Ideal.Quotient.eq_zero_iff_mem→vh,Ideal.Quotient.factor→vk,Ideal.Quotient.factor_mk→xI,Ideal.Quotient.factorₐ→z8,Ideal.Quotient.liftₐ→C5,Ideal.Quotient.mk→lJ,Ideal.Quotient.mk_surjective→u5,Ideal.Quotient.mkₐ→FQ,Ideal.map_map→xu,Ideal.mem_span_singleton_self→z9,Ideal.quotientEquivAlg→EP,Ideal.span→ oj,IntermediateField.adjoin→FR,Irreducible→nI,IsDomain→ oK,IsFractionRing→sI,IsFractionRing.lift_algebraMap→Et,IsFractionRing.map→pL,IsLocalRing.residue→vZ,IsLocalization.map_eq→qM,IsScalarTower→sH,IsScalarTower.algebraMap_apply→uh,IsScalarTower.of_algHom→Cy,IsScalarTower.of_algebraMap_eq→FK
open _root_ renaming LinearMap.finrank_range_of_inj→zR,LinearMap.ker→t8,LinearMap.mulLeft→zE,LinearMap.range→vG,Module.Finite→ ox,Module.Flat→zh,Module.Flat.lTensor_preserves_injective_linearMap→Dz,Module.finrank→ ov,MvPolynomial→aU,MvPolynomial.C→mD,MvPolynomial.X→nq,MvPolynomial.aeval→qy,MvPolynomial.affineDegree→uz,MvPolynomial.affineHilbertPolynomial→ oq,MvPolynomial.algebraTensorAlgEquiv→wB,MvPolynomial.algebraTensorAlgEquiv_tmul→vw,MvPolynomial.eval→qJ,MvPolynomial.eval₂Hom→ oZ,MvPolynomial.eval₂Hom_C→t3,MvPolynomial.eval₂Hom_X'→Fz,MvPolynomial.map→lV,MvPolynomial.mapAlgHom→Dw,MvPolynomial.map_C→wR,MvPolynomial.map_X→x7,MvPolynomial.mk_mem_quotientDegreeLE→zf,MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective→zk,MvPolynomial.quotientBidegreeLE→yJ,MvPolynomial.quotientDegreeLE→ oY,MvPolynomial.rename→Bf,MvPolynomial.restrictBidegree→t4,MvPolynomial.ringHom_ext→yU,MvPolynomial.support_map_subset→Ar,MvPolynomial.totalDegree_C→zg,MvPolynomial.totalDegree_finsetSum_le→Du,MvPolynomial.totalDegree_mul→ze,MvPolynomial.trdeg_of_isDomain→yQ,MvPolynomial.weightedHomogeneousComponent→uW,MvPolynomial.zeroLocus→qG,Nat.card_fin→yB,Option→nX,Option.some_ne_none→Ee,Polynomial→vj,Polynomial.C→pG,Polynomial.C_mul_X_pow_eq_monomial→Eg,Polynomial.X→qx,Polynomial.coe_eval₂RingHom→xW,Polynomial.coe_mapRingHom→sS,Polynomial.coeff_map→zS
open _root_ renaming Polynomial.eval_map_apply→Ea,Polynomial.eval₂_C→yo,Polynomial.induction_on'→Av,Polynomial.mapRingHom→t6,Polynomial.map_C→wY,Polynomial.map_injective→Df,Polynomial.map_map→EK,Polynomial.ringHom_ext→Aa,Polynomial.sylvester→zd,Polynomial.trdeg_of_isDomain→Au,RingHom.comp_apply→p6,RingHom.ext→xm,RingHom.ker→p7,RingHom.ker_isPrime→Ef,Submodule→u8,Subtype.ext→v9,Subtype.val_injective→FU,Sum.inr→p9,TensorProduct.AlgebraTensorModule.lTensor→yl,TensorProduct.inductionOn→z7,add_zero→p5,congrArg→qz,exists_finite_inj_algHom_of_fg→xL,faithfulSMul_iff_algebraMap_injective→vl,inferInstance→vH,injective_iff_map_eq_zero→C4,le_sup_left→yL,map_add→qU,map_mul→pC,smul_eq_mul→u9,trdeg_add_eq→qm,trdeg_eq_zero→t9,trdeg_le_of_injective→Dv
set_option autoImplicit true
section
namespace DQ
noncomputable section
open K1 cu Polynomial
open scoped BigOperators
abbrev DT (n:ℕ) :=aU (Fin n) L
abbrev XO (n:ℕ) :=vj (vj (DT n))
abbrev SourceRing (n:ℕ) :=aU (nX (Fin n)) FX
def specialize {n:ℕ} (f :XO n) (t:Fin n→L) :
    vj (vj L) :=
  f.map (t6 (qJ t))
def aKg {n:ℕ} (f :XO n) (g:ℕ) :Prop :=
 f.natDegree≤g ∧ ∀ i j,((f.coeff i).coeff j).totalDegree≤1
def ZS {n:ℕ} (t:Fin n→L) (S:K[X]) :nX (Fin n)→FX
 | none=>kr S
 | some j=>algebraMap L FX (t j)
def Ag (d:ℕ) :ℕ:=2*d - 1
def Wh (d g:ℕ) :ℕ:=1+Ag d*(g - 1)
abbrev jY (n:ℕ) :=oD (SourceRing n)
abbrev auc (n:ℕ) :=aU (nX (Fin n)) (jY n)
def Qd {n:ℕ} (i:nX (Fin n)) :jY n :=
 lz (SourceRing n) (jY n) (nq i)
def aD8 (n:ℕ) :auc n :=
  (∑ j:Fin n,mD (Qd (some j))*nq (some j)) -
    mD (Qd (n:=n) none)
def aD3 (n:ℕ) :auc n :=
 nq none-MvPolynomial.C (Qd (n:=n) none)
abbrev Gl {n:ℕ} (J:cy (SourceRing n)) (q:auc n) :=
 auc n ⧸
  (J.map (lV (lz FX (jY n))) ⊔ oj {q})
structure bTz {n:ℕ} (J:cy (SourceRing n)) (Dparam Dy :ℕ) :Prop where
 parameter_finite :ox (jY n) (Gl J (aD8 n))
 parameter_length:ov (jY n) (Gl J (aD8 n))≤Dparam
 a6j:ox (jY n) (Gl J (aD3 n))
 ordinate_length:ov (jY n) (Gl J (aD3 n))≤Dy
structure bk0 (U:pz K) (s :K→K[X]) (g H n:ℕ) where
 equation :XO n
 equation_degree :aKg equation g
 parameter :K→Fin n→L
 source :cy (SourceRing n)
 source_prime :source.IsPrime
 source_dim: (oq source).natDegree≤1
 akm:bTz source (g*H) H
 lies_on : ∀ γ∈U,ZS (parameter γ) (s γ)∈qG FX source
 root : ∀ γ∈U,(specialize equation (parameter γ)).eval (j9 (s γ))=0
 simple : ∀ γ∈U,(specialize equation (parameter γ)).derivative.eval (j9 (s γ))≠0
structure bbx (n a b:ℕ) where
 denominator :SourceRing n
 numerator :K→SourceRing n
 ZB:denominator∈t4 (Fin n) FX a b
 Vi : ∀ x,numerator x∈t4 (Fin n) FX a b
def bbx.aay {n a b:ℕ} (C:bbx n a b)
    (t:Fin n→L) (S:K[X]) :Prop :=
  let ev :=qy (ZS t S)
  ev C.denominator≠0 ∧
    ∀ x,ev (C.numerator x)=ev C.denominator*jz (S.eval x)
abbrev baN (n a b:ℕ) :=
 aU (MvPolynomial.bidegreeExponents (Fin n) a b) FX
def br4 {n:ℕ} (a b:ℕ) (J:cy (SourceRing n)) :
    cy (baN n a b) :=
  J.comap (MvPolynomial.bidegreeMap (Fin n) FX a b)
end
end DQ
end
section
namespace Cu
noncomputable section
open K1 cu gT DQ
open scoped Polynomial BigOperators
abbrev sQ:=aU (Fin 2) L
abbrev auG (C₀:sQ) :cy sQ:=oj {C₀}
instance (C₀:sQ) [h:Fact (nI C₀)] : (auG C₀).IsPrime :=
 (Ideal.span_singleton_prime h.out.ne_zero).mpr
   (UniqueFactorizationMonoid.irreducible_iff_prime.mp h.out)
abbrev abz (C₀:sQ) :=sQ ⧸ auG C₀
abbrev oO (C₀:sQ) :=oD (abz C₀)
abbrev y7 (C₀:sQ) :=oD (oO C₀)[X]
def zT (C₀:sQ) :L →+* oO C₀ :=
  (lz (abz C₀) (oO C₀)).comp
    ((lJ (auG C₀)).comp mD)
def Wt (C₀:sQ) (i:Fin 2) :oO C₀ :=
  lz (abz C₀) (oO C₀)
    (lJ (auG C₀) (nq i))
def F5 (C₀:sQ) : (oO C₀)[X] →+* y7 C₀ :=
 lz _ _
def Mu (C₀:sQ) :oO C₀ →+* y7 C₀ :=
 (F5 C₀).comp pG
def Mr (C₀:sQ) [Fact (nI C₀)] :FX →+* y7 C₀ :=
  pL (j:=t6 (zT C₀))
    (Df (zT C₀) (zT C₀).injective)
def BI (C₀:sQ) :cy aZ :=
 oj {lV ((lz L[X] FX).comp (pG:L →+* L[X])) C₀}
def LG (C₀:sQ) [Fact (nI C₀)] :
    kM →+* (y7 C₀)[X] :=
  oZ (Polynomial.C.comp (Mr C₀))
    ![pG (Mu C₀ (Wt C₀ 0)),
      pG (Mu C₀ (Wt C₀ 1)),qx]
structure wJ (C₀:sQ) [Fact (nI C₀)]
  (J:cy kM) (g:ℕ) where
 equation : ((oO C₀)[X])[X]
 primitive :equation.IsPrimitive
 degree :equation.natDegree=g
 irreducible :nI (equation.map (F5 C₀))
 contraction :J=(oj {equation.map (F5 C₀)}).comap (LG C₀)
structure yI {C₀:sQ} [Fact (nI C₀)]
  {J:cy kM} {g:ℕ} (R:wJ C₀ J g) (n:ℕ) where
 coordinate :Fin n→ oO C₀
 scale : (oO C₀)ˣ
 equation :XO n
 degree :aKg equation g
 generic_eq :equation.map
    (t6 (oZ (zT C₀) coordinate)) =
  pG (pG (scale :oO C₀))*R.equation
 coordinates_are_coefficients : ∀ i,∃ j k,
  coordinate i=((pG (pG (scale :oO C₀)) *
    R.equation).coeff j).coeff k
 normalized : ∃ ℓ:Fin n→L,(∑ i,zT C₀ (ℓ i)*coordinate i)=1
abbrev Gc (n:ℕ) :=aU (Fin 2 ⊕ Fin n) FX
abbrev N4 (n:ℕ) :=aU (Fin n) FX
def aa4 (n:ℕ) :N4 n →+* Gc n :=
 (Bf p9).toRingHom
def W8 {C₀:sQ} [Fact (nI C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) :
    Gc n →+* y7 C₀ :=
  oZ (Mr C₀)
    (Sum.elim (Mu C₀ ∘ Wt C₀) (Mu C₀ ∘ A.coordinate))
def EF {C₀:sQ} [Fact (nI C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) :cy (Gc n) :=
  p7 (W8 A)
def adq {C₀:sQ} [Fact (nI C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) :
    SourceRing n →+* (y7 C₀)[X] :=
  oZ (Polynomial.C.comp (Mr C₀))
    (fun i=>i.elim qx (pG ∘ Mu C₀ ∘ A.coordinate))
def SO {C₀:sQ} [Fact (nI C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) :cy (SourceRing n) :=
  (oj {R.equation.map (F5 C₀)}).comap (adq A)
def aCn {n:ℕ} (z :K) (t:Fin n→L) :Fin 2 ⊕ Fin n→FX :=
 Sum.elim ![jz z,(jz z)^p] (fun i=>lz L FX (t i))
def blL (n:ℕ) :aU (Fin 2 ⊕ Fin n) (jY n) :=
  (∑ i:Fin n,mD (Qd (some i))*nq (p9 i)) -
    mD (Qd (n:=n) none)
abbrev aAM {n:ℕ} (B:cy (Gc n)) :=
 aU (Fin 2 ⊕ Fin n) (jY n) ⧸
  (B.map (lV (lz FX (jY n))) ⊔ oj {blL n})
structure a9K {n:ℕ} (B:cy (Gc n)) (H :ℕ) :Prop where
 dimension : (oq B).natDegree≤1
 finite :ox (jY n) (aAM B)
 length:ov (jY n) (aAM B)≤H
end
end Cu
end
section
namespace Cu
noncomputable section
open K1 cu gT DQ
open scoped Polynomial BigOperators
private def KK:FX:=lz L[X] FX qx
private def aTQ (n:ℕ) : (DT n)[X] →+* N4 n :=
 Polynomial.eval₂RingHom (lV (lz L FX)) (mD KK)
def ajx {n:ℕ} (f :XO n) : (N4 n)[X] :=
 f.map (aTQ n)
def a2n {n:ℕ} (f :XO n) (g:ℕ) :N4 n :=
 (ajx f).resultant (ajx f).derivative g (g - 1)
private theorem bnv {n:ℕ} {f :XO n} {g:ℕ}
   (hf :aKg f g) (j:ℕ) : ((ajx f).coeff j).totalDegree≤1 := by
 rw [ajx,zS ,(f.coeff j).as_sum_range_C_mul_X_pow,map_sum]
 apply Du
 intro i _
 rw [pC,map_pow]
 simp only [aTQ,xW,yo ,
   Polynomial.eval₂_X]
 rw [← map_pow mD]
 have hm: (lV (lz L FX) ((f.coeff j).coeff i)).totalDegree ≤
     ((f.coeff j).coeff i).totalDegree := by
   unfold MvPolynomial.totalDegree
   exact Finset.sup_mono (Ar (lz L FX) ((f.coeff j).coeff i))
 exact (ze _ _).trans (by
   rw [zg ,p5]
   exact hm.trans (hf.2 j i))
theorem dIf {n:ℕ} {f :XO n} {g:ℕ}
   (hf :aKg f g) (hg:0<g) : (a2n f g).totalDegree≤Ag g:= by
 classical
 let F:=ajx f
 have hd (i:ℕ) : (F.derivative.coeff i).totalDegree≤1 := by
   have hcast: ((i:N4 n)+1)=mD ((i:FX)+1) := by simp
   rw [Polynomial.coeff_derivative,hcast]
   exact (ze _ _).trans (by
     simpa only [zg ,p5] using bnv hf (i+1))
 let M:=zd F F.derivative g (g - 1)
 have hentry (i j:Fin (g+(g - 1))) : (M i j).totalDegree≤1 := by
   cases j using Fin.addCases with
   | left j =>
     simp only [M,zd ,Matrix.of_apply,Fin.addCases_left]
     split_ifs
     · exact hd _
     · simp
   | right j =>
     simp only [M,zd ,Matrix.of_apply,Fin.addCases_right]
     split_ifs
     · exact bnv hf _
     · simp
 change M.det.totalDegree≤_
 rw [Matrix.det_apply']
 apply Du
 intro σ _
 have hsign: ((Equiv.Perm.sign σ:ℤ) :N4 n) =
     mD ((Equiv.Perm.sign σ:ℤ) :FX) := by simp
 rw [hsign]
 refine (ze _ _).trans ?_
 rw [zg ,zero_add]
 refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
 calc
   _ ≤ ∑ _:Fin (g+(g - 1)),1 :=th (fun i _=>hentry (σ i) i)
   _=Ag g:= by simp [Ag]; omega
private theorem d06 (C₀:sQ) [Fact (nI C₀)] :
  Mr C₀ KK=F5 C₀ Polynomial.X:= by
 unfold Mr KK pL
 rw [qM]
 simp [F5]
private theorem b1t (C₀:sQ) [Fact (nI C₀)] (a :L) :
  Mr C₀ (lz L FX a)=Mu C₀ (zT C₀ a) := by
 rw [uh L L[X] FX]
 unfold Mr pL
 rw [qM]
 simp [Mu,F5]
private theorem cE3 {C₀:sQ} [Fact (nI C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) :
    ((W8 A).comp (aa4 n)).comp (aTQ n) =
      (F5 C₀).comp
        (t6 (oZ (zT C₀) A.coordinate)) := by
  apply Aa
  · have hc: ((W8 A).comp (aa4 n)).comp
        (lV (lz L FX)) =
        (Mu C₀).comp (oZ (zT C₀) A.coordinate) := by
      apply yU
      · intro a
        simp [W8,aa4,b1t]
      · intro i
        simp [W8,aa4]
    intro a
    simpa only [p6,aTQ,xW,
      yo ,sS ,wY ,Mu] using
      pU hc a
  · simpa [aTQ,W8,aa4] using d06 C₀
private def pD {n:ℕ} (t:Fin n→L) :N4 n →+* FX :=
 qJ (lz L FX ∘ t)
private theorem b7z {n:ℕ} (t:Fin n→L) :
    (pD t).comp (aTQ n) =
      (lz L[X] FX).comp (t6 (qJ t)) := by
  apply Aa
  · have hc: (pD t).comp (lV (lz L FX)) =
        (lz L FX).comp (qJ t) := by
      apply yU <;> simp [pD]
    intro a
    simp only [p6,aTQ,xW,
      yo ,sS ,wY]
    calc
      _=lz L FX (qJ t a) :=pU hc a
      _ = _:= by rw [uh L L[X] FX]; rfl
  · simp [pD,aTQ,KK]
theorem fXk {n:ℕ} (f :XO n) (g:ℕ) (z :K) (t:Fin n→L) :
   qy (aCn z t) (aa4 n (a2n f g)) =
     pD t (a2n f g) := by
 change qJ (aCn z t) (Bf p9 (a2n f g))= _
 rw [MvPolynomial.eval_rename]
 rfl
theorem gq7 {n:ℕ} {f :XO n} {g:ℕ}
   (hf :aKg f g) (hg:0<g) {z :K} {t:Fin n→L} {S:K[X]}
   (hr : (specialize f t).eval (j9 S)=0)
   (hres :qy (aCn z t) (aa4 n (a2n f g))≠0) :
   (specialize f t).derivative.eval (j9 S)≠0:= by
 rw [fXk] at hres
 have hmap : (ajx f).map (pD t) =
     (specialize f t).map (lz L[X] FX) := by
   rw [ajx,specialize,EK,EK,b7z]
 have hdeg: (ajx f).natDegree≤g:=Polynomial.natDegree_map_le.trans hf.1
 have hroot : ((ajx f).map (pD t)).eval (kr S)=0:= by
   rw [hmap,kr,Ea ,hr,map_zero]
 have hsimple :=Polynomial.eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero
   (pD t) (ajx f) hdeg hg hres _ hroot
 intro h
 apply hsimple
 rw [hmap,Polynomial.derivative_map,kr,Ea ,h,map_zero]
end
end Cu
end
section
namespace ane
noncomputable section
open cu DQ MvPolynomial
abbrev Gu {n:ℕ} (J:cy (SourceRing n)) :cy (auc n) :=
 J.map (lV (lz FX (jY n)))
abbrev agD {n:ℕ} (J:cy (SourceRing n)) :=
 auc n ⧸ Gu J
abbrev box {n:ℕ} (J:cy (SourceRing n)) (u v :ℕ) :
  u8 (jY n) (agD J) :=
 yJ (Gu J) u v
abbrev aaK {n:ℕ} (J:cy (SourceRing n)) (q:auc n) :
  agD J :=
 lJ (Gu J) q
def bQo {n:ℕ} (J:cy (SourceRing n)) (q:auc n)
    (du dv :ℕ) :Prop :=
  ∃ N :ℕ,∀ u v :ℕ,N≤u→N≤v →
    (∀ x∈box J (u+1) v,aaK J q*x∈box J (u+du) (v+dv)→x∈box J u v) ∧
    (∀ x∈box J u (v+1),aaK J q*x∈box J (u+du) (v+dv)→x∈box J u v)
end
end ane
end
section
namespace ane
noncomputable section
open cu DQ MvPolynomial
open scoped TensorProduct
theorem ea6 {n:ℕ} (J:cy (SourceRing n)) (u v :ℕ) :
    ov FX (yJ J u v) ≤
      ov (jY n) (box J u v) := by
  classical
  let E :=jY n
  let R:=SourceRing n
  let e₀:E ⊗[FX] R ≃ₐ[E] auc n :=
    wB FX E
  let i:R →+* E ⊗[FX] R :=
    (t5 (A:=E) (R:=FX)).toRingHom
  have hmap :e₀.toAlgHom.toRingHom.comp i=lV (lz FX E) := by
    apply xm
    intro p
    change e₀ (1 ⊗ₜ[FX] p)=lV (lz FX E) p
    simpa only [e₀,one_smul] using vw FX E 1 p
  let I:=J.map i
  have hI:Gu J=I.map e₀.toAlgHom.toRingHom:= by
    change Gu J=(J.map i).map e₀.toAlgHom.toRingHom
    rw [xu i e₀.toAlgHom.toRingHom,hmap]
  let e₁: ((E ⊗[FX] R) ⧸ I) ≃ₐ[E] agD J :=
    EP I (Gu J) e₀ hI
  let e :E ⊗[FX] (R ⧸ J) ≃ₐ[E] agD J :=
    (C9 E R E J).trans e₁
  have he₁ (c:E) (p:R) :
      e₁ (lJ I (c ⊗ₜ[FX] p)) =
        c•lJ (Gu J) (lV (lz FX E) p) := by
    change lJ (Gu J) (e₀ (c ⊗ₜ[FX] p))= _
    rw [show e₀ (c ⊗ₜ[FX] p)=c•lV (lz FX E) p from
      vw FX E c p]
    exact (FQ E (Gu J)).toLinearMap.map_smul c _
  let T:=yJ J u v
  let f :E ⊗[FX] T →ₗ[E] agD J :=
    e.toLinearMap.comp (yl E E T.subtype)
  have hf :oz f :=e.injective.comp
    (Dz (M:=E) T.subtype FU)
  have hbox (z :E ⊗[FX] T) :f z∈box J u v := by
    induction z using z7 with
    | tmul c x =>
        obtain ⟨p,hp,hp'⟩:=mem_quotientBidegreeLE.mp x.property
        have hm:lV (lz FX E) p∈t4 (Fin n) E u v :=
          mem_restrictBidegree.mpr fun m hm =>
            mem_restrictBidegree.mp hp m (Ar _ _ hm)
        change e (c ⊗ₜ[FX] (x :R ⧸ J))∈box J u v
        rw [← hp']
        change e₁ (lJ I (c ⊗ₜ[FX] p))∈box J u v
        rw [he₁ c p]
        exact (box J u v).smul_mem c (mem_quotientBidegreeLE.mpr ⟨_,hm,rfl⟩)
    | add x y hx hy =>
        rw [qU]
        exact (box J u v).add_mem hx hy
  rw [← Module.finrank_baseChange (R:=E) (S:=FX) (M' := T)]
  exact LinearMap.finrank_le_finrank_of_injective
    (f :=f.codRestrict (box J u v) hbox) (fun x y h=>hf (qz Subtype.val h))
private theorem bmt {n:ℕ} {J:cy (SourceRing n)} {x :agD J}
  {u v u' v' : ℕ} (hu:u≤u') (hv :v≤v') (hx :x∈box J u v) :
  x∈box J u' v' := by
 obtain ⟨p,hp,rfl⟩:=mem_quotientBidegreeLE.mp hx
 exact mem_quotientBidegreeLE.mpr ⟨p,mem_restrictBidegree_mono hp hu hv,rfl⟩
theorem dfD {n:ℕ} {J:cy (SourceRing n)} {q:auc n}
    {du dv :ℕ} (h:bQo J q du dv) :
    ∃ N :ℕ,∀ u v :ℕ,N≤u→N≤v →
      ∀ x :agD J,aaK J q*x∈box J (u+du) (v+dv)→x∈box J u v := by
  obtain ⟨N,hN⟩:=h
  refine ⟨N,?_⟩
  intro u v hu hv x hqx
  have shrink_u (s r :ℕ) (hx :x∈box J (u+r) (v+s)) :
      x∈box J u (v+s) := by
    induction r with
    | zero=>exact hx
    | succ r ih =>
        apply ih
        apply (hN (u+r) (v+s) (by omega) (by omega)).1 x hx
        exact bmt (by omega) (by omega) hqx
  have shrink_v (s :ℕ) (hx :x∈box J u (v+s)) :x∈box J u v := by
    induction s with
    | zero=>exact hx
    | succ s ih =>
        apply ih
        apply (hN u (v+s) hu (by omega)).2 x hx
        exact bmt le_rfl (by omega) hqx
  obtain ⟨p,hp⟩:=u5 (I:=Gu J) x
  let r :=p.support.sup (fun m=>m none)
  let s :=p.support.sup (fun m=>m.some.degree)
  have hpbox :p∈t4 (Fin n) (jY n) (u+r) (v+s) := by
    refine mem_restrictBidegree.mpr fun m hm=>⟨?_,?_⟩
    · exact (y5 (f := fun m=>m none) hm).trans (Nat.le_add_left _ _)
    · exact (y5 (f := fun m=>m.some.degree) hm).trans (Nat.le_add_left _ _)
  exact shrink_v s (shrink_u s r (mem_quotientBidegreeLE.mpr ⟨p,hpbox,hp⟩))
theorem cSd {n:ℕ} (J:cy (SourceRing n)) (q:auc n)
    (u v u' v' : ℕ) [ox (jY n) (Gl J q)]
    (h : ∀ x :agD J,aaK J q*x∈box J u' v' → x∈box J u v) :
    ov (jY n) (box J u' v') ≤
      ov (jY n) (box J u v) +
        ov (jY n) (Gl J q) := by
  let T:=box J u' v'
  let π:T →ₗ[jY n] Gl J q :=
    (z8 (jY n)
      (yL:Gu J≤Gu J ⊔ oj {q})).toLinearMap.domRestrict T
  let ι:t8 π →ₗ[jY n] agD J :=
    T.subtype.comp (t8 π).subtype
  let μ:box J u v →ₗ[jY n] agD J :=
    (zE (jY n) (aaK J q)).domRestrict _
  have hk :vG ι≤vG μ:= by
    rintro _ ⟨z,rfl⟩
    obtain ⟨p,hp⟩:=u5 (I:=Gu J) z.1.1
    have hz :=LinearMap.mem_ker.mp z.2
    change vk (yL :
      Gu J≤Gu J ⊔ oj {q}) z.1.1=0 at hz
    rw [← hp] at hz
    have hm:p∈Gu J ⊔ oj {q} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨s,hs,t,ht,hst⟩:=Submodule.mem_sup.mp hm
    obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp ht
    have he :aaK J q*aaK J r=z.1.1 := by
      rw [← hp,← hst,qU,Ideal.Quotient.eq_zero_iff_mem.mpr hs,zero_add,pC]
    have hr :aaK J r∈box J u v :=h _ (he.symm ▸ z.1.2)
    exact ⟨⟨aaK J r,hr⟩,he⟩
  have hi:oz ι:=Subtype.val_injective.comp FU
  have hker :ov (jY n) (t8 π) ≤
      ov (jY n) (box J u v) :=
    (zR hi).symm.le.trans
      ((Submodule.finrank_mono hk).trans μ.finrank_range_le)
  have hrange :=Submodule.finrank_le (vG π)
  have hrank :=π.finrank_range_add_finrank_ker
  change _+_=ov (jY n) (box J u' v') at hrank
  omega
end
end ane
end
section
namespace aqe
noncomputable section
open cu DQ MvPolynomial
abbrev aex (n:ℕ) :=nX (Fin n) ⊕ Bool
abbrev Dq (n:ℕ) (k :Type) [n5 k] :=aU (aex n) k
def pad {n:ℕ} (side :Bool) :aex n := .inr side
def group {n:ℕ} : aex n→Bool
 | .inl none=>false
 | .inl (some _)=>true
 | .inr side=>side
def amR (side :Bool) :ℕ×ℕ:=if side then (0,1) else (1,0)
def ahj (n:ℕ) (i:aex n) :ℕ×ℕ:=amR (group i)
def acu (n:ℕ) (i:aex n) :ℕ:=(ahj n i).2
def af6 {n:ℕ} : nX (Fin n)→aex n
 | none=>pad true
 | some j => .inl (some j)
abbrev awV {n:ℕ} {k :Type} [n5 k]
  (p:Dq n k) (d:ℕ×ℕ) :Prop :=
 p.IsWeightedHomogeneous (ahj n) d
def ew {n:ℕ} {k :Type} [n5 k] :
    Dq n k →ₐ[k] aU (nX (Fin n)) k :=
  qy (Sum.elim nq fun _=>1)
def an3 {n:ℕ} {k :Type} [n5 k]
    (I:cy (aU (nX (Fin n)) k)) :
    Dq n k →ₐ[k] (aU (nX (Fin n)) k ⧸ I) :=
  (FQ k I).comp ew
def acf {n:ℕ} {k :Type} [n5 k]
    (I:cy (aU (nX (Fin n)) k)) :
    Dq n k →ₐ[k] aU Bool (aU (nX (Fin n)) k ⧸ I) :=
  qy fun i=>mD (an3 I (nq i))*nq (group i)
def aze {n:ℕ} {k :Type} [n5 k]
    (I:cy (aU (nX (Fin n)) k)) :cy (Dq n k) :=
  p7 (acf I).toRingHom
def lW {n:ℕ} {k :Type} [n5 k]
    (I:cy (aU (nX (Fin n)) k)) (side :Bool) :cy (Dq n k) :=
  aze I ⊔ oj {nq (pad side)}
def aHN {n:ℕ} (I:cy (Dq n FX)) :cy (Dq n (jY n)) :=
 I.map (lV (lz FX (jY n)))
def aog (n:ℕ) :Dq n (jY n) :=
  (∑ j:Fin n,mD (Qd (some j))*nq (af6 (some j))) -
    mD (Qd (n:=n) none)*nq (af6 none)
def bkS {n:ℕ} {k :Type} [n5 k] (I:cy (Dq n k)) :Prop :=
 ∀ p∈I,∀ v :ℕ,uW (acu n) v p∈I
end
end aqe
end
section
namespace aqe
noncomputable section
open cu DQ ane MvPolynomial
open scoped TensorProduct
set_option maxHeartbeats 600000 in
private theorem enf {n:ℕ} {k E :Type} [c9 k] [c9 E]
    [lI k E] [zh k E]
    (J:cy (aU (nX (Fin n)) k)) :
    aze (J.map (lV (lz k E))) =
      (aze J).map (lV (lz k E)) := by
  classical
  let R:=aU (nX (Fin n)) k
  let R' := aU (nX (Fin n)) E
  let h:R →+* R' := lV (lz k E)
  let J' := J.map h
  let A:=R ⧸ J
  let B:=R' ⧸ J'
  let er :E ⊗[k] R ≃ₐ[E] R' := wB k E
  let ir :R →+* E ⊗[k] R :=
    (t5 (A:=E) (R:=k)).toRingHom
  have hir :er.toAlgHom.toRingHom.comp ir=h:= by
    apply xm
    intro p
    change er (1 ⊗ₜ[k] p)=h p
    simpa only [er,h,one_smul] using vw k E 1 p
  have hI:J' = (J.map ir).map er.toAlgHom.toRingHom:= by
    rw [xu,hir]
  let e₁: ((E ⊗[k] R) ⧸ J.map ir) ≃ₐ[E] B :=
    EP (J.map ir) J' er hI
  let ec:E ⊗[k] A ≃ₐ[E] B :=
    (C9 E R E J).trans e₁
  have hec (p:R) :
      ec (1 ⊗ₜ[k] lJ J p)=lJ J' (h p) := by
    change lJ J' (er (1 ⊗ₜ[k] p))= _
    exact qz (lJ J') (pU hir p)
  let j:A →ₐ[k] B :=
    (ec.toAlgHom.restrictScalars k).comp (t5 (A:=E))
  let hₐ:Dq n k →ₐ[k] Dq n E :=
    Dw (Algebra.ofId k E)
  let f :Dq n k →ₐ[k] aU Bool A:=acf J
  let f' : Dq n E →ₐ[E] aU Bool B:=acf J'
  have hj: (Dw (σ:=Bool) j).comp f =
      (f'.restrictScalars k).comp hₐ:= by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i =>
        simp only [AlgHom.comp_apply,f,f',acf,aeval_X,an3,ew,
          Sum.elim_inl,Ideal.Quotient.mkₐ_eq_mk,mapAlgHom_apply,hₐ,Algebra.toRingHom_ofId,
          x7,pC,wR,AlgHom.restrictScalars_apply]
        change mD (ec (1 ⊗ₜ[k] lJ J (nq i)))*_ = _
        have hX:h (nq i)=(nq i:R') :=
          x7 (lz k E) i
        rw [hec,hX]
    | inr side =>
        simp [f,f',acf,an3,ew,hₐ,mapAlgHom_apply]
  let es :E ⊗[k] Dq n k ≃ₐ[E] Dq n E :=
    wB k E
  have hes_tmul (a :E) (p:Dq n k) :
      es (a ⊗ₜ[k] p)=a•hₐ p:= by
    change wB k E (a ⊗ₜ[k] p) =
      a•lV (lz k E) p
    exact vw k E a p
  let et:E ⊗[k] aU Bool A ≃ₐ[E] aU Bool B :=
    MvPolynomial.rTensorAlgEquiv.trans (MvPolynomial.mapAlgEquiv Bool ec)
  have het (a :E) (p:aU Bool A) :
      et (a ⊗ₜ[k] p)=a•lV j.toRingHom p:= by
    ext d
    simp only [et,AlgEquiv.trans_apply,mapAlgEquiv_apply,coeff_map,
      coeff_rTensorAlgEquiv_tmul,coeff_smul]
    change ec (a ⊗ₜ[k] p.coeff d)=a•ec (1 ⊗ₜ[k] p.coeff d)
    rw [TensorProduct.tmul_eq_smul_one_tmul,map_smul]
  let tf :=Algebra.TensorProduct.map (AlgHom.id k E) f
  have hcomp:f'.toRingHom.comp es.toAlgHom.toRingHom =
      et.toAlgHom.toRingHom.comp tf.toRingHom:= by
    apply xm
    intro z
    induction z using z7 with
    | tmul a p =>
        change f' (es (a ⊗ₜ[k] p))=et (a ⊗ₜ[k] f p)
        rw [hes_tmul,map_smul,het]
        exact qz (a • ·) (pU hj p).symm
    | add x y hx hy =>
        rw [qU,qU,hx,hy]
  have hker : (aze J').comap es.toAlgHom.toRingHom =
      (aze J).map (t5 (A:=E) (R:=k)).toRingHom:= by
    rw [aze,RingHom.comap_ker,hcomp]
    change p7 (et.toRingEquiv.toRingHom.comp tf.toRingHom)= _
    rw [RingHom.ker_equiv_comp]
    rw [← Submodule.restrictScalars_inj k]
    change t8 (yl k E f.toLinearMap)= _
    have hk :=Module.Flat.ker_lTensor_eq (R:=k) k E
      (N :=Dq n k) (P:=aU Bool A) f.toLinearMap
    rw [hk]
    exact TensorProduct.AlgebraTensorModule.range_lTensor_idealMap (R:=k) E k
      (p7 f.toRingHom)
  have hes :es.toAlgHom.toRingHom.comp
      (t5 (A:=E) (R:=k)).toRingHom=hₐ.toRingHom:= by
    apply xm
    intro p
    change es (1 ⊗ₜ[k] p)=hₐ p
    simpa only [one_smul] using hes_tmul 1 p
  calc
    aze J' =
        ((aze J').comap es.toAlgHom.toRingHom).map es.toAlgHom.toRingHom :=
      (Ideal.map_comap_of_surjective es.toAlgHom.toRingHom es.surjective _).symm
    _=(aze J).map hₐ.toRingHom:= by
      rw [hker,xu,hes]
theorem ene {n:ℕ} (J:cy (SourceRing n)) :
  aze (Gu J)=aHN (aze J) := by
 have :Module.Free FX (jY n) :=Module.Free.of_divisionRing FX (jY n)
 have :zh FX (jY n) :=Module.Flat.of_free
 exact enf (k :=FX) (E :=jY n) J
end
end aqe
end
section
namespace aqe
noncomputable section
open MvPolynomial
private theorem gMc {n:ℕ} (d:aex n →₀ ℕ) :
  Finsupp.weight (acu n) d = ∑ i:nX (Fin n),d (af6 i) := by
 simp [Finsupp.weight_eq_sum,Fintype.sum_sum_type,Fintype.sum_option,
  acu,ahj,amR,group,af6,pad,Nat.add_comm]
private theorem dzI {n:ℕ} {k :Type} [c9 k]
    (I:cy (Dq n k)) (hI:bkS I) (g:Dq n k)
    (hg : ∀ i:nX (Fin n),∃ e :ℕ,nq (af6 i)^e*g∈I) :
    ∃ B:ℕ,∀ (v :ℕ) (a :Dq n k),B≤v →
      uW (acu n) v (a*g)∈I:= by
  classical
  choose e he using hg
  refine ⟨(∑ i,e i)+weightedTotalDegree (acu n) g+1,?_⟩
  intro v a hv
  induction a using MvPolynomial.induction_on' with
  | monomial d c =>
      by_cases hd : ∃ i,e i≤d (af6 i)
      · obtain ⟨i,hi⟩:=hd
        have hsingle :Finsupp.single (af6 i) (e i)≤d :=
          Finsupp.single_le_iff.mpr hi
        have hfactor :monomial d c =
            monomial (d-Finsupp.single (af6 i) (e i)) c *
              nq (af6 i)^e i:= by
          rw [← monomial_add_single,tsub_add_cancel_of_le hsingle]
        apply hI
        rw [hfactor,mul_assoc]
        exact I.mul_mem_left _ (he i)
      · by_cases hc:c=0
        · simp [hc]
        have hw:Finsupp.weight (acu n) d ≤ ∑ i,e i:= by
          rw [gMc]
          exact th fun i _=>Nat.le_of_lt (Nat.lt_of_not_ge (fun hi=>hd ⟨i,hi⟩))
        have hdeg:weightedTotalDegree (acu n) (monomial d c*g)<v := by
          apply (weightedTotalDegree_mul_le _ _ _).trans_lt
          rw [weightedTotalDegree_monomial _ _ _ hc]
          omega
        rw [weightedHomogeneousComponent_eq_zero v _ hdeg]
        exact I.zero_mem
  | add a b ha hb =>
      rw [add_mul,qU]
      exact I.add_mem ha hb
theorem eul {n:ℕ} {k :Type} [c9 k]
    (I:cy (Dq n k)) (q:Dq n k) (hI:bkS I)
    (hlocal : ∀ p:Dq n k,q*p∈I →
      ∀ i:nX (Fin n),∃ e :ℕ,nq (af6 i)^e*p∈I) :
    ∃ N :ℕ,∀ (v :ℕ) (p:Dq n k),N≤v →
      p.IsWeightedHomogeneous (acu n) v→q*p∈I→p∈I:= by
  classical
  let T:=I.colon (oj {q})
  obtain ⟨s,hs⟩:=T.fg_of_isNoetherianRing
  have hgen (g:s) :
      ∃ B:ℕ,∀ (v :ℕ) (a :Dq n k),B≤v →
        uW (acu n) v (a*(g:Dq n k))∈I:= by
    apply dzI I hI
    apply hlocal
    rw [mul_comm,← Ideal.mem_colon_span_singleton]
    change (g:Dq n k)∈T
    rw [← hs]
    exact Submodule.subset_span g.property
  choose B hB using hgen
  refine ⟨s.attach.sup B,?_⟩
  intro v p hv hhom hqp
  have hp:p∈Submodule.span (Dq n k) (s :Set (Dq n k)) := by
    change p∈oj (s :Set (Dq n k))
    rw [hs]
    apply Ideal.mem_colon_span_singleton.mpr
    simpa only [mul_comm] using hqp
  have H : ∀ a :Dq n k,uW (acu n) v (a*p)∈I:= by
    refine Submodule.span_induction (p:= fun y _ => ∀ a :Dq n k,
      uW (acu n) v (a*y)∈I) ?_ ?_ ?_ ?_ hp
    · intro g hg a
      let i:s :=⟨g,hg⟩
      exact hB i v a ((y5 (f :=B) (s.mem_attach i)).trans hv)
    · intro a
      simp
    · intro x y _ _ hx hy a
      rw [mul_add,qU]
      exact I.add_mem (hx a) (hy a)
    · intro r x _ hx a
      simpa only [u9,mul_assoc] using hx (a*r)
  rw [← weightedHomogeneousComponent_eq_self hhom]
  simpa only [one_mul] using H 1
end
end aqe
end
section
namespace MN
noncomputable section
open K1 cu Polynomial
open scoped BigOperators
def Ag (d:ℕ) :ℕ:=2*d - 1
def Wh (d e :ℕ) :ℕ:=1+Ag d*(e - 1)
def btp (d b:ℕ) :ℕ:=Ag d*b
abbrev Ai:=aU (nX (Fin 2)) FX
def Ul (z :K) (S:K[X]) :nX (Fin 2)→FX
 | none=>kr S
 | some i=>(![jz z,(jz z)^p] :Fin 2→FX) i
structure TaylorChart (d e b:ℕ) where
 denominator :Ai
 numerator :K→Ai
 ZB:denominator ∈
  t4 (Fin 2) FX (Wh d e) (btp d b)
 Vi : ∀ x,numerator x ∈
  t4 (Fin 2) FX (Wh d e) (btp d b)
def TaylorChart.aay {d e b} (C:TaylorChart d e b) (z :K) (S:K[X]) :Prop :=
  let ev :=qJ (Ul z S)
  ev C.denominator≠0 ∧
    ∀ x :K,ev (C.numerator x)=ev C.denominator*jz (S.eval x)
abbrev BK:=AlgebraicClosure FX
structure OF (w:I→K) (T:pz K) (s :K→K[X]) (d:ℕ) :Prop where
 distinct :Set.InjOn s (T:Set K)
 degree : ∀ γ∈T,(s γ).natDegree≤d
 lg : ∀ γ∈T,∃ B:pz I,180265≤B.card ∧ ∀ i∈B,(s γ).eval (node i)=w i
theorem OF.mono {w T s d} (h:OF w T s d) {U:pz K} (hU:U⊆T) :
   OF w U s d :=
 ⟨h.distinct.mono hU,fun γ hγ=>h.degree γ (hU hγ),fun γ hγ=>h.lg γ (hU hγ)⟩
end
end MN
end
section
namespace MN
noncomputable section
open Polynomial Finset K1 ProximityPrize.Benchmark
open scoped BigOperators
private theorem aDW {α ι:Type*} [DecidableEq α] [DecidableEq ι]
    (marks :pz α) (nodes :pz ι) (B:α→pz ι) (x t cap:ℕ)
    (hB : ∀ a∈marks,B a⊆nodes∧(B a).card=x)
    (hpair : ∀ a∈marks,∀ b∈marks,a≠b→(B a∩B b).card≤t)
    (hocc : ∀ i∈nodes,(marks.filter fun a=>i∈B a).card≤ cap) :
    (marks.card*x)^2≤nodes.card*(marks.card*(x+(marks.card - 1)*t)) ∧
      marks.card*x≤nodes.card*cap:= by
  classical
  let occ (i:ι) :=(marks.filter fun a=>i∈B a).card
  have section_eq (V:pz ι) (hV:V⊆nodes) :
      (nodes.filter fun i=>i∈V)=V:= by
    ext i
    exact mem_filter.trans ⟨And.right,fun hi=>⟨hV hi,hi⟩⟩
  have first : ∑ i∈nodes,occ i=marks.card*x := by
    calc
      _ = ∑ a∈marks,(B a).card:= by
        simp only [occ,card_filter]
        rw [sum_comm]
        refine uJ rfl fun a ha => ?_
        rw [sum_boole,Nat.cast_id,section_eq _ (hB a ha).1]
      _ = _:= by rw [uJ rfl (fun a ha=>(hB a ha).2),sum_const,u9]
  have second : ∑ i∈nodes,occ i^2 =
      ∑ a∈marks,∑ b∈marks,(B a∩B b).card:= by
    simp only [occ,sq,card_filter]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    refine uJ rfl fun a ha => ?_
    rw [sum_comm]
    refine uJ rfl fun b _ => ?_
    have identity (i:ι) :
        (if i∈B a then 1 else 0:ℕ)*(if i∈B b then 1 else 0) =
          if i∈B a∩B b then 1 else 0:= by
      by_cases h₁:i∈B a <;> by_cases h₂:i∈B b <;> simp [h₁,h₂]
    simp_rw [identity]
    rw [sum_boole,Nat.cast_id,section_eq _ (inter_subset_left.trans (hB a ha).1)]
  have row (a :α) (ha :a∈marks) :
      ∑ b∈marks,(B a∩B b).card≤x+(marks.card - 1)*t:= by
    rw [← add_sum_erase marks _ ha,inter_self,(hB a ha).2]
    refine Nat.add_le_add_left ?_ _
    calc
      _ ≤ ∑ b∈marks.erase a,t:=th fun b hb =>
        hpair a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm
      _ = _:= by rw [sum_const,card_erase_of_mem ha,u9]
  have second_le : ∑ i∈nodes,occ i^2≤ marks.card*(x+(marks.card - 1)*t) := by
    rw [second]
    exact (th row).trans_eq (by rw [sum_const,u9])
  have cs :=sq_sum_le_card_mul_sum_sq (s :=nodes) (f :=occ)
  rw [first] at cs
  refine ⟨cs.trans (Nat.mul_le_mul_left _ second_le),?_⟩
  rw [← first,← u9,← sum_const]
  exact th hocc
end
end MN
end
section
namespace DQ
noncomputable section
open K1 cu gT Polynomial MvPolynomial Finset
open scoped BigOperators
def c3:Prop :=
  ∀ (n a b Dparam Dy :ℕ),0<a→0<b →
    ∀ J:cy (SourceRing n),J.IsPrime →
      (oq J).natDegree=1→bTz J Dparam Dy →
      uz (br4 a b J)≤((b*Dparam+a*Dy :ℕ) :ℚ)
private theorem cc0 {σ:Type} [Finite σ]
    {P:cy (aU σ FX)} [P.IsPrime]
    (B:pz K) (point :K→σ→FX) (hinj:Set.InjOn point (B:Set K))
    {q:aU σ FX} (hq:q∉P) (hlinear :q.totalDegree≤1)
    (hpoints : ∀ γ∈B,point γ∈qG FX (P ⊔ oj {q}))
    {D:ℕ} (hdim: (oq P).natDegree≤1)
    (hdeg: (oq P).natDegree=1→uz P≤(D:ℚ)) :
    B.card≤D:= by
  classical
  let comps :=(P ⊔ oj {q}).minimalPrimesFinset
  let slice (Q:cy (aU σ FX)) :=B.filter fun γ=>point γ∈qG FX Q
  have cover (γ:K) (hγ:γ∈B) : ∃ Q∈comps,γ∈slice Q:= by
    obtain ⟨Q,hQ,hγQ⟩ :=
      exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ (hpoints γ hγ) (by simp)
    exact ⟨Q,Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ,hγQ⟩⟩
  have dim (Q:cy (aU σ FX)) (hQ:Q∈comps) :
      (oq Q).natDegree+1=(oq P).natDegree :=
    principalCut_natDegree_affineHilbertPolynomial_add_one hq (Ideal.mem_minimalPrimesFinset.mp hQ)
  by_cases hcurve : (oq P).natDegree=1
  · have local_count (Q:cy (aU σ FX)) (hQ:Q∈comps) :
        ((slice Q).card:ℚ)≤uz Q:= by
      obtain ⟨hfinite,hn⟩:=finite_zeroLocus_and_ncard_le_affineDegree (K:=FX) Q
        (by have :=dim Q hQ; omega)
      let im:=(slice Q).image point
      have hsub: (im:Set _)⊆qG FX Q:= by
        intro x hx
        obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hx
        exact (mem_filter.mp hγ).2
      have h:=Set.ncard_le_ncard hsub hfinite
      rw [Set.ncard_coe_finset,card_image_of_injOn (hinj.mono (filter_subset _ _))] at h
      exact (Nat.cast_le.mpr h).trans hn
    have hsum:B.card ≤ ∑ Q∈comps,(slice Q).card :=
      (card_le_card fun γ hγ=>mem_biUnion.mpr (cover γ hγ)).trans card_biUnion_le
    have hsumQ: (B.card:ℚ) ≤ ∑ Q∈comps,((slice Q).card:ℚ) := by exact_mod_cast hsum
    have hbudget: (∑ Q∈comps,uz Q)≤uz P:= by
      simpa only [comps,Nat.cast_one,one_mul] using
        principalCut_sum_affineDegree_minimalPrimes_le hq hlinear
    exact_mod_cast hsumQ.trans ((th local_count).trans (hbudget.trans (hdeg hcurve)))
  · have hB:B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      obtain ⟨Q,hQ,_⟩:=cover γ hγ
      have :=dim Q hQ
      omega
    simp [hB]
end
end DQ
end
section
namespace Cu
noncomputable section
open K1 cu gT DQ
open scoped Polynomial
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (nI C₀)] (J:cy kM) (g:ℕ),
    J.IsPrime→J.comap pZ=BI C₀ →
    ox aQ (abX J) →
    ov aQ (abX J)=C₀.totalDegree*g→0<g →
    Nonempty (wJ C₀ J g)
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (nI C₀)] (J:cy kM) (g:ℕ)
    (R:wJ C₀ J g) (T:pz K) (z :K→K) (s :K→K[X]),
    (∀ γ∈T,aSf J (z γ) (s γ)) →
    ∃ (n:ℕ) (A:yI R n) (t:K→Fin n→L),
      (∀ γ∈T,aCn (z γ) (t γ)∈qG FX (EF A)) ∧
      (∀ γ∈T,ZS (t γ) (s γ)∈qG FX (SO A)) ∧
      (∀ γ∈T,(specialize A.equation (t γ)).eval (j9 (s γ))=0)
def c3:Prop :=
  ∀ (C₀:sQ) [Fact (nI C₀)] (J:cy kM) (g H n:ℕ)
    (R:wJ C₀ J g) (A:yI R n),
    0<g→ ox aQ (SI J) →
    ov aQ (SI J)≤H→a9K (EF A) H
def c4 :Prop :=
  ∀ (C₀:sQ) [Fact (nI C₀)] (J:cy kM) (g H n:ℕ)
    (R:wJ C₀ J g) (A:yI R n),
    a9K (EF A) H→ ox aQ (SI J) →
    ov aQ (SI J)≤H →
    (oq (SO A)).natDegree≤1 ∧
    bTz (SO A) (g*H) H
def c5:Prop :=
  ∀ (n H :ℕ) (B:cy (Gc n)),B.IsPrime→a9K B H →
    ∀ (q:N4 n),aa4 n q∉B →
    ∀ (V:pz K) (pt:K→Fin 2 ⊕ Fin n→FX),Set.InjOn pt (V:Set K) →
      (∀ γ∈V,pt γ∈qG FX B ∧
        qy (pt γ) (aa4 n q)=0) →
      V.card≤q.totalDegree*H
end
end Cu
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace aiO
noncomputable section
open K1 cu gT DQ Cu
open scoped Polynomial
variable {C₀:sQ} [Fact (nI C₀)] {J:cy kM} {g n:ℕ}
abbrev Ot (R:wJ C₀ J g) :=R.equation.map (F5 C₀)
abbrev EC (R:wJ C₀ J g) :=AdjoinRoot (R:=y7 C₀) (Ot R)
instance (R:wJ C₀ J g) :Fact (nI (Ot R)) :=
 ⟨R.irreducible⟩
scoped instance dc7 (C₀:sQ) [Fact (nI C₀)] :
 lI FX (y7 C₀) :=(Mr C₀).toAlgebra
abbrev awU {R:wJ C₀ J g} (A:yI R n) :=
 Gc n ⧸ EF A
def aMf {R:wJ C₀ J g} (A:yI R n) :
    awU A →ₐ[FX] y7 C₀ :=
  Ideal.kerLiftAlg {
    toRingHom:=W8 A
    commutes' a :=t3 _ _ a }
def arQ (R:wJ C₀ J g) :
    (kM ⧸ J) →ₐ[FX] EC R :=
  C5 J
    { toRingHom:=(pQ (R:=y7 C₀) (Ot R)).comp (LG C₀)
      commutes' a := by
        change ((pQ (R:=y7 C₀) (Ot R)).comp (LG C₀)) (mD a) =
          lz FX (EC R) a
        rw [p6,LG,t3 ,
          p6,zi]
        exact pU (zm FX (R:=y7 C₀) (f :=Ot R)).symm a }
    (fun f hf=> by
      rw [R.contraction] at hf
      exact (vh (I:=oj {Ot R})).mpr hf)
def azf {R:wJ C₀ J g} (A:yI R n) :
    (SourceRing n ⧸ SO A) →ₐ[FX] EC R :=
  C5 (SO A)
    { toRingHom:=(pQ (R:=y7 C₀) (Ot R)).comp (adq A)
      commutes' a := by
        change ((pQ (R:=y7 C₀) (Ot R)).comp (adq A)) (mD a) =
          lz FX (EC R) a
        rw [p6,adq,t3 ,
          p6,zi]
        exact pU (zm FX (R:=y7 C₀) (f :=Ot R)).symm a }
    (fun _ hf=>(vh (I:=oj {Ot R})).mpr hf)
open scoped TensorProduct
abbrev E8 {ι:Type} (offset :ι) := {i:ι // i≠offset}
abbrev Jo (k ι:Type) [c9 k] :=oD (aU ι k)
def ahI {k ι:Type} [c9 k] (i:ι) :Jo k ι :=
 lz (aU ι k) (Jo k ι) (nq i)
def No {k ι A:Type} [c9 k] [n5 A] [lI k A]
    (offset :ι) (u:aU (E8 offset) A) :
    aU ι k →+* aU (E8 offset) A:= by
  classical
  exact oZ (MvPolynomial.C.comp (lz k A))
    (fun i=>if hi:i=offset then u else nq ⟨i,hi⟩)
abbrev ami {k ι A:Type} [c9 k] [n5 A] [lI k A]
   (offset :ι) (u:aU (E8 offset) A) :
   lI (aU ι k) (aU (E8 offset) A) :=
 (No (k :=k) offset u).toAlgebra
abbrev Gd (k :Type) [c9 k] {ι A:Type} [n5 A] [lI k A]
  (offset :ι) (u:aU (E8 offset) A) :=
 letI:=ami (k :=k) offset u
 Jo k ι ⊗[aU ι k] aU (E8 offset) A
def anY {k ι σ:Type} [c9 k] (offset :ι)
    (u:aU (E8 offset) (aU σ k)) :
    aU σ (Jo k ι) :=
  oZ (lV (lz k (Jo k ι)))
      (fun i=>mD (ahI i.val)) u -
    mD (ahI offset)
abbrev bbf {k ι σ:Type} [c9 k] (offset :ι)
  (I:cy (aU σ k)) (u:aU (E8 offset) (aU σ k)) :=
 aU σ (Jo k ι) ⧸
  (I.map (lV (lz k (Jo k ι))) ⊔ oj {anY offset u})
def btr {n:ℕ} {A:Type} [n5 A] (x :Fin n→A) :
    aU (E8 (none :nX (Fin n))) A :=
  ∑ i,nq ⟨some i,Ee i⟩*mD (x i)
def JR (F M:Type) [c9 F] [vi M] [Module F M] (d:ℕ) :Prop :=
 ox F M∧ov F M≤d
end
end aiO
end
section
set_option maxHeartbeats 800000
namespace aiO
noncomputable section
open K1 cu gT DQ Cu
open scoped Polynomial
variable {C₀:sQ} [Fact (nI C₀)] {J:cy kM} {g n:ℕ}
theorem bVo {R:wJ C₀ J g} (A:yI R n) :
  oz (aMf A) :=
 Ideal.kerLiftAlg_injective _
theorem c2W (R:wJ C₀ J g) :
  oz (arQ R) := by
 apply (C4 (arQ R)).mpr
 intro a ha
 obtain ⟨f,rfl⟩:=u5 a
 change pQ (R:=y7 C₀) (Ot R) (LG C₀ f)=0 at ha
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 rw [R.contraction]
 exact (vh (I:=oj {Ot R})).mp ha
theorem bHN {R:wJ C₀ J g} (A:yI R n) :
  oz (azf A) := by
 apply (C4 (azf A)).mpr
 intro a ha
 obtain ⟨f,rfl⟩:=u5 a
 change pQ (R:=y7 C₀) (Ot R) (adq A f)=0 at ha
 exact Ideal.Quotient.eq_zero_iff_mem.mpr
  ((vh (I:=oj {Ot R})).mp ha)
scoped instance dyy {R:wJ C₀ J g} (A:yI R n) :
  oK (awU A) :=
 zc _ (bVo A)
theorem a7Y (R:wJ C₀ J g) :
  ov (y7 C₀) (EC R)=g:= by
 change ov (y7 C₀)
  ((y7 C₀)[X] ⧸ oj {Ot R})=g
 rw [finrank_quotient_span_eq_natDegree]
 exact (Polynomial.natDegree_map_eq_of_injective
  (IsFractionRing.injective (oO C₀)[X] (y7 C₀)) R.equation).trans R.degree
scoped instance c8S (R:wJ C₀ J g) :
   ox (y7 C₀) (EC R) :=
 (AdjoinRoot.powerBasis R.irreducible.ne_zero).finite
private theorem cZ6 {D F E :Type} [n5 D] [oK D]
  [c9 F] [c9 E] [lI D F] [sI D F]
  (f :F →+* E) (S:Subfield E) (h : ∀ d,f (lz D F d)∈S) (x :F) :
  f x∈S:= by
 obtain ⟨a,b,_,rfl⟩:=IsFractionRing.div_surjective D x
 rw [map_div₀]
 exact S.div_mem (h a) (h b)
private theorem d5x (C₀:sQ) [Fact (nI C₀)] (a :L) :
  Mr C₀ (lz L FX a)=Mu C₀ (zT C₀ a) := by
 rw [uh L L[X] FX]
 unfold Mr pL
 rw [qM]
 simp [Mu,F5]
private theorem d5y (C₀:sQ) [Fact (nI C₀)] :
  Mr C₀ (lz L[X] FX qx)=F5 C₀ Polynomial.X:= by
 unfold Mr pL
 rw [qM]
 simp [F5]
private theorem c0f {E :Type} [c9 E] (f :y7 C₀ →+* E)
    (S:Subfield E) (hfx : ∀ x,f (Mr C₀ x)∈S)
    (hseed : ∀ i,f (Mu C₀ (Wt C₀ i))∈S)
    (x :y7 C₀) :f x∈S:= by
  refine cZ6 (D:=(oO C₀)[X]) f S (fun q => ?_) x
  change (f.comp (F5 C₀)) q∈S
  have hconst (a :oO C₀) : (f.comp (Mu C₀)) a∈S:= by
    refine cZ6 (D:=abz C₀) (f.comp (Mu C₀)) S (fun b => ?_) a
    obtain ⟨q,rfl⟩:=u5 b
    let e :=(f.comp (Mu C₀)).comp
      ((lz (abz C₀) (oO C₀)).comp
        (lJ (auG C₀)))
    change e q∈S
    induction q using MvPolynomial.induction_on with
    | C a =>
      change f (Mu C₀ (zT C₀ a))∈S
      rw [← d5x]
      exact hfx _
    | add p q hp hq=>exact (map_add e p q).symm ▸ S.add_mem hp hq
    | mul_X p i hp =>
      rw [pC]
      exact S.mul_mem hp (hseed i)
  induction q using Av with
  | add p q hp hq=>exact (map_add (f.comp (F5 C₀)) p q).symm ▸ S.add_mem hp hq
  | monomial i a =>
    rw [← Eg ,pC,map_pow]
    exact S.mul_mem (hconst a) (S.pow_mem (by
      change f (F5 C₀ qx)∈S
      rw [← d5y]
      exact hfx _) _)
private def cSZ {D M:Type} [n5 D] [oK D] [c9 M]
   (f :D →+* M) (hf :oz f) :
   let _:=f.toAlgebra
   oD D →ₐ[D] M:= by
 let _:lI D M:=f.toAlgebra
 exact { toRingHom:=IsFractionRing.lift (g:=f) hf
         commutes' := Et (K:=oD D) (g:=f) hf }
private theorem edN {D M:Type} [n5 D] [oK D] [c9 M]
  (f :D →+* M) (hf :oz f) (x :D) :
  cSZ f hf (lz D (oD D) x)=f x :=
 Et (K:=oD D) (g:=f) hf x
private theorem cS3 {D M:Type} [n5 D] [oK D] [c9 M]
   (f :D →+* M) (hf :oz f)
   (h : ∀ S:Subfield M,(∀ x :D,f x∈S) → ∀ x :M,x∈S) :
   let _:=f.toAlgebra
   IsFractionRing D M:= by
 let _:lI D M:=f.toAlgebra
 let φ:oD D →ₐ[D] M:=cSZ f hf
 have hφ:Fa φ:= by
   intro z
   exact h φ.toRingHom.fieldRange
     (fun x=>⟨lz D (oD D) x,edN f hf x⟩) z
 exact IsFractionRing.of_algEquiv (AlgEquiv.ofBijective φ ⟨φ.injective,hφ⟩)
private theorem gDw {k A B:Type} [c9 k] [n5 A] [n5 B]
  [lI k A] [lI k B] (f :A →ₐ[k] B) :
  @sH k A B vH f.toRingHom.toAlgebra.toSMul inferInstance := by
 let _:lI A B:=f.toRingHom.toAlgebra
 exact FK fun x=>(f.commutes x).symm
abbrev aS4 {R:wJ C₀ J g} (A:yI R n) :
 lI (awU A) (y7 C₀) :=(aMf A).toRingHom.toAlgebra
theorem dyF {R:wJ C₀ J g} (A:yI R n) :
  @sH FX (awU A) (y7 C₀)
    (vH :lI FX (awU A)).toSMul (aS4 A).toSMul
    (dc7 C₀).toSMul :=
 (gDw (k :=FX) (A:=awU A) (B:=y7 C₀) (aMf A) :)
theorem bVp {R:wJ C₀ J g} (A:yI R n)
 (f :Gc n) :
 aMf A (lJ (EF A) f)=W8 A f :=rfl
theorem cCW {R:wJ C₀ J g} (A:yI R n) :
   let _:=aS4 A
   sI (awU A) (y7 C₀) := by
 let m:awU A →+* y7 C₀:=(aMf A).toRingHom
 have hm:oz m:=bVo A
 refine cS3 (D:=awU A) (M:=y7 C₀) m hm ?_
 intro S hS x
 have hmem (b:awU A) :aMf A b∈S:=hS b
 change (RingHom.id (y7 C₀)) x∈S
 apply c0f (C₀:=C₀) (RingHom.id _) S _ _ x
 · intro a
   simpa [bVp,W8] using
     hmem (lJ (EF A) (mD a))
 · intro i
   simpa [bVp,W8] using
     hmem (lJ (EF A) (nq (Sum.inl i)))
theorem c2V (R:wJ C₀ J g) :oK (kM ⧸ J) :=
 zc _ (c2W R)
abbrev eIe (R:wJ C₀ J g) :
 lI (kM ⧸ J) (EC R) :=(arQ R).toRingHom.toAlgebra
theorem eIf (R:wJ C₀ J g) :
    let _:=eIe R
    sI (kM ⧸ J) (EC R) := by
  let B:=kM ⧸ J
  let E :=EC R
  have :oK B:=c2V R
  let m:B →+* E :=(arQ R).toRingHom
  have hm:oz m:=c2W R
  refine cS3 (D:=B) (M:=E) m hm ?_
  intro S hS z
  have hmem (x :B) :arQ R x∈S:=hS x
  have hconstants (x :y7 C₀) :t7 (R:=y7 C₀) (Ot R) x∈S:= by
    apply c0f (t7 (R:=y7 C₀) (Ot R)) S _ _ x
    · intro a
      simpa [arQ,LG] using
        hmem (lJ J (mD a))
    · intro i
      fin_cases i
      · simpa [arQ,LG] using
          hmem (lJ J (nq (0:Fin 3)))
      · simpa [arQ,LG] using
          hmem (lJ J (nq (1 :Fin 3)))
  have hY:pQ (R:=y7 C₀) (Ot R) qx∈S:= by
    simpa [arQ,LG] using
      hmem (lJ J (nq (2 :Fin 3)))
  obtain ⟨q,rfl⟩:=AdjoinRoot.mk_surjective z
  change pQ (R:=y7 C₀) (Ot R) q∈S
  induction q using Av with
  | add p q hp hq=>exact (map_add (AdjoinRoot.mk (R:=y7 C₀) (Ot R)) p q).symm ▸ S.add_mem hp hq
  | monomial i a =>
    rw [← Eg ,pC,map_pow,zi]
    exact S.mul_mem (hconstants a) (S.pow_mem hY i)
private theorem gD8 {k A B:Type} [c9 k] [n5 A]
  [n5 B] [oK A] [oK B] [lI k A] [lI k B]
  (f :A →ₐ[k] B) (hi:oz f) (hf :f.Finite) :
  oy k B=oy k A:= by
 let _:lI A B:=f.toRingHom.toAlgebra
 have :sH k A B:=FK fun x=>(f.commutes x).symm
 have :wA A B:=(vl A B).mpr hi
 have :ox A B:=hf
 have :v8 A B:=Algebra.IsIntegral.isAlgebraic
 rw [← qm k A (A:=B),t9 (R:=A) (A:=B),p5]
private theorem dhY {k σ:Type} [c9 k] [Finite σ]
   (I:cy (aU σ k)) [I.IsPrime] :
   oy k (aU σ k ⧸ I) =
     ((oq I).natDegree :Cardinal) := by
 let B:=aU σ k ⧸ I
 obtain ⟨d,f,hfinj,hf⟩:=xL k B
 rw [gD8 f hfinj hf,
   zk f hf hfinj,
   yB]
 simp [yQ]
theorem enG {R:wJ C₀ J g} (A:yI R n)
   (hd: (oq (EF A)).natDegree≤1) :
   (oq (SO A)).natDegree≤1 := by
 let B:=awU A
 let F:=y7 C₀
 let E :=EC R
 have : (EF A).IsPrime :=Ef (W8 A)
 have : (SO A).IsPrime :=(Ideal.Quotient.isDomain_iff_prime (SO A)).mp
   (zc _ (bHN A))
 let _:lI B F:=aS4 A
 let _:SMul B F:=(aS4 A).toSMul
 let _:SMul FX B:=(vH :lI FX B).toSMul
 let _:SMul FX F:=(dc7 C₀).toSMul
 have :sH FX B F:=dyF A
 have :sI B F:=cCW A
 have :wA B F:=(vl B F).mpr (bVo A)
 have :wA FX F:=(vl FX F).mpr (Mr C₀).injective
 have :v8 B F:=IsLocalization.isAlgebraic F (nonZeroDivisors B)
 have :ox F E :=c8S R
 have :v8 F E :=Algebra.IsAlgebraic.of_finite F E
 have h:oy FX (SourceRing n ⧸ SO A)≤oy FX E :=
   Dv (azf A) (bHN A)
 rw [← qm FX F (A:=E),← qm FX B (A:=F),
   t9 (R:=B) (A:=F),t9 (R:=F) (A:=E),
   p5 ,p5 ,dhY (SO A),
   show oy FX B=oy FX (Gc n ⧸ EF A) from rfl,
   dhY (EF A)] at h
 have h' : (oq (SO A)).natDegree ≤
     (oq (EF A)).natDegree := by exact_mod_cast h
 exact h'.trans hd
end
end aiO
end
section
namespace XW
noncomputable section
open cu gT DQ Cu
open scoped BigOperators Polynomial
def TU {C₀:sQ} [Fact (nI C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) :cy (DT n) :=
  p7 (oZ (zT C₀) A.coordinate)
def gY {C₀:sQ} [Fact (nI C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) :ℕ :=
  letI:lI L (oO C₀) :=(zT C₀).toAlgebra
  let F:=FR L (Set.range A.coordinate)
  ov F (oO C₀)
abbrev Gu {k σ:Type*} [c9 k] (E :Type*) [c9 E] [lI k E]
  (I:cy (aU σ k)) :cy (aU σ E) :=
 I.map (lV (lz k E))
abbrev bcZ {k σ:Type*} [c9 k] (I:cy (aU σ k))
  (f :aU σ k) :=
 aU σ k ⧸ (I ⊔ oj {f})
def a2G (n:ℕ) :aU (Fin n) (jY n) :=
  (∑ i:Fin n,mD (Qd (some i))*nq i) -
    mD (Qd (n:=n) none)
def aIM {n:ℕ} (f :XO n) :aU (Fin n) aQ :=
  (ajx f).eval₂ (lV (lz FX aQ))
    (mD (ek 1))
abbrev aYv {C₀:sQ} [Fact (nI C₀)] {J g n}
  {R:wJ C₀ J g} (A:yI R n) :=
 bcZ (Gu (jY n) (TU A)) (a2G n)
abbrev anh {C₀:sQ} [Fact (nI C₀)] {J g n}
  {R:wJ C₀ J g} (A:yI R n) :=
 bcZ (Gu aQ (TU A)) (aIM A.equation)
structure atV {k σ:Type*} [c9 k] (I:cy (aU σ k))
  (f :aU σ k) :Prop where
 degree :f.totalDegree≤1
 regular :IsLeftRegular (lJ I f)
 boundary : ∃ N :ℕ,∀ d:ℕ,N≤d →
  ∀ x∈oY I (d+1),
    lJ I f*x∈oY I (d+1) →
      x∈oY I d
theorem cGE {C₀:sQ} [Fact (nI C₀)] {J g n}
  {R:wJ C₀ J g} (A:yI R n) (i:Fin n) :
  ∃ j k,(A.equation.coeff j).coeff k-MvPolynomial.X i∈TU A:= by
 obtain ⟨j,k,hi⟩:=A.coordinates_are_coefficients i
 refine ⟨j,k,?_⟩
 have h:=qz (fun F: ((oO C₀)[X])[X]=>(F.coeff j).coeff k)
  A.generic_eq
 simp only [zS ,sS] at h
 change oZ (zT C₀) A.coordinate
  ((A.equation.coeff j).coeff k-MvPolynomial.X i)=0
 rw [map_sub,Fz]
 exact sub_eq_zero.mpr (h.trans hi.symm)
theorem cGD {C₀:sQ} [Fact (nI C₀)] {J g n}
  {R:wJ C₀ J g} (A:yI R n) :
  ∃ ℓ:Fin n→L,
    (∑ i,mD (ℓ i)*nq i) - 1∈TU A:= by
 obtain ⟨ℓ,hℓ⟩:=A.normalized
 refine ⟨ℓ,?_⟩
 change oZ (zT C₀) A.coordinate
  ((∑ i,mD (ℓ i)*nq i) - 1)=0
 simp only [map_sub,map_sum,pC,t3 ,Fz ,
  map_one,sub_eq_zero]
 exact hℓ
end
end XW
end
section
namespace XW
noncomputable section
open Algebra MvPolynomial cu DQ Cu
open scoped Polynomial
private theorem cKL {k σ E :Type} [c9 k] [Finite σ] [c9 E] [lI k E]
  (f :aU σ k →ₐ[k] E) (hE :oy k E≤1) :
  (oq (p7 f.toRingHom)).natDegree≤1 := by
 let I:=p7 f.toRingHom
 let:I.IsPrime :=Ef f.toRingHom
 let ι: (aU σ k ⧸ I) →ₐ[k] E :=
  ⟨RingHom.kerLift f.toRingHom,fun r=>f.commutes r⟩
 have hi:oz ι:=RingHom.kerLift_injective f.toRingHom
 obtain ⟨d,u,hu,hfin⟩:=xL k (aU σ k ⧸ I)
 have h:=(Dv (ι.comp u) (hi.comp hu)).trans hE
 rw [yQ,Cardinal.lift_id,Cardinal.mk_fin] at h
 rw [zk u hfin hu,yB]
 exact_mod_cast h
private theorem aFj (k B:Type) [c9 k] [n5 B] [oK B]
  [lI k B] :oy k (oD B)=oy k B:= by
 let:v8 B (oD B) :=
  (IsFractionRing.comap_isAlgebraic_iff (K:=oD B)).mpr vH
 rw [← qm k B,t9 (R:=B),p5]
private theorem ct7 {k B:Type} [c9 k] [n5 B] [oK B]
  [lI k B] {d:ℕ} (u:aU (Fin d) k →ₐ[k] B)
  (hu:oz u) (hfin:u.Finite) :oy k B=d:= by
 let P:=aU (Fin d) k
 let:lI P B:=u.toRingHom.toAlgebra
 let:sH k P B:=Cy u
 let:wA P B:=(vl P B).mpr hu
 let:ox P B:=hfin
 rw [← qm k P,t9 (R:=P),p5 ,
  yQ,Cardinal.lift_id,Cardinal.mk_fin]
private theorem bNK (C₀:sQ) [hC:Fact (nI C₀)] :
   oy L (oO C₀)≤1 := by
 let B:=abz C₀
 obtain ⟨d,u,hu,hfin⟩:=xL L B
 have hdim: (oq (auG C₀)).natDegree≤1 := by
   simpa using natDegree_affineHilbertPolynomial_le_of_mem (I:=auG C₀)
     hC.out.ne_zero (z9 C₀)
 rw [zk u hfin hu,
   yB] at hdim
 rw [aFj L B,ct7 u hu hfin]
 exact_mod_cast hdim
private theorem bpV (C₀:sQ) [Fact (nI C₀)] (a :L) :
  Mr C₀ (lz L FX a)=lz L (y7 C₀) a := by
 rw [uh L L[X] FX]
 unfold Mr pL
 rw [qM]
 rw [uh L (oO C₀)[X] (y7 C₀)]
 simp only [sS ,Polynomial.algebraMap_apply,wY]
 rfl
private theorem ekr {k F E Q σ:Type} [c9 k] [c9 F] [c9 E] [c9 Q]
  [Finite σ] [lI k F] [lI k E] [lI k Q] [lI E Q]
  [sH k E Q] (i:F →ₐ[k] Q) (f :aU σ F →+* Q)
  (hf : ∀ a,f (mD a)=i a)
  (hF:oy k F=1) (hQ:oy E Q=1) (hE :oy k E≤1) :
  (oq (p7 f)).natDegree≤1 := by
 let:lI F Q:=i.toRingHom.toAlgebra
 let:sH k F Q:=Cy i
 let φ:aU σ F →ₐ[F] Q:=⟨f,hf⟩
 apply cKL φ
 apply (Cardinal.add_le_add_iff_of_lt_aleph0 (γ:=1) (by simp)).mp
 calc
  oy F Q+1=oy k Q:= by rw [add_comm,← hF,qm k F]
  _=oy k E+1 := by rw [← qm k E,hQ]
  _≤1+1 :=add_le_add_left hE 1
theorem aTz {C₀:sQ} [Fact (nI C₀)] {J g n}
   {R:wJ C₀ J g} (A:yI R n) :
   (oq (EF A)).natDegree≤1 ∧
     (oq (TU A)).natDegree≤1 := by
 let E :=oO C₀
 let Q:=y7 C₀
 have hFX:oy L FX=1 :=(aFj L L[X]).trans Au
 have hX:oy E Q=1 :=(aFj E E[X]).trans Au
 let i:FX →ₐ[L] Q:=⟨Mr C₀,bpV C₀⟩
 let u:DT n →ₐ[L] E :=
   ⟨oZ (zT C₀) A.coordinate,t3 _ _⟩
 exact ⟨ekr i (W8 A) (t3 _ _) hFX hX (bNK C₀),
   cKL u (bNK C₀)⟩
end
end XW
end
section
namespace XW
noncomputable section
open MvPolynomial
variable {k σ:Type*} [c9 k]
private theorem guW {I:cy (aU σ k)} {f :aU σ k}
    (h:atV I f) :
    ∃ N :ℕ,∀ d:ℕ,N≤d → ∀ x :aU σ k ⧸ I,
      lJ I f*x∈oY I (d+1) →
        x∈oY I d:= by
  obtain ⟨N,hN⟩:=h.boundary
  refine ⟨N,?_⟩
  intro d hd x hfx
  have shrink : ∀ r,x∈oY I (d+r)→x∈oY I d:= by
    intro r
    induction r with
    | zero=>exact id
    | succ r ih =>
        intro hx
        apply ih
        exact hN (d+r) (by omega) x hx
          (quotientDegreeLE_mono I (by omega) hfx)
  obtain ⟨r,hr⟩:=exists_mem_quotientDegreeLE I x
  exact shrink r (quotientDegreeLE_mono I (by omega) hr)
variable [Finite σ]
private theorem emU {I:cy (aU σ k)} {f :aU σ k}
    (h:atV I f) {d:ℕ}
    (hs : ∀ x :aU σ k ⧸ I,
      lJ I f*x∈oY I (d+1) →
        x∈oY I d) :
    affineHilbertFunction (I ⊔ oj {f}) (d+1)+affineHilbertFunction I d =
      affineHilbertFunction I (d+1) := by
  let J:=I ⊔ oj {f}
  have hIJ:I≤J:=yL
  let U:=oY I d
  let V:=oY I (d+1)
  let W:=oY J (d+1)
  let π:V →ₗ[k] W :=
    ((z8 k hIJ).toLinearMap.domRestrict V).codRestrict W (fun z=> by
      obtain ⟨p,hp,hz⟩:=mem_quotientDegreeLE.mp z.property
      change vk hIJ z.val∈W
      rw [← hz,xI]
      exact zf hp)
  let μ:U →ₗ[k] V :=
    ((zE k (lJ I f)).domRestrict U).codRestrict V (fun x=> by
      change lJ I f*x.val∈V
      have hm:=mul_mem_quotientDegreeLE (zf (I:=I) h.degree) x.property
      simpa only [V,Nat.add_comm 1 d] using hm)
  have hπ:Fa π:= by
    intro z
    obtain ⟨p,hp,hz⟩:=mem_quotientDegreeLE.mp z.property
    exact ⟨⟨lJ I p,zf hp⟩,v9 hz⟩
  have hμ:oz μ:= by
    intro x y hxy
    exact v9 (h.regular (qz (fun z :V=>z.val) hxy))
  have hexact :vG μ=t8 π:= by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      rw [LinearMap.mem_ker]
      apply v9
      change vk hIJ (lJ I f*x.val)=0
      rw [pC,xI,Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (z9 f)),zero_mul]
    · intro hz
      obtain ⟨p,hp,hpz⟩:=mem_quotientDegreeLE.mp z.property
      have hz' := qz (fun w:W=>w.val) (LinearMap.mem_ker.mp hz)
      change vk hIJ z.val=0 at hz'
      rw [← hpz,xI] at hz'
      have hm:p∈oj {f} ⊔ I:=sup_comm I (oj {f}) ▸
        (Ideal.Quotient.eq_zero_iff_mem.mp hz' : p∈J)
      obtain ⟨a,b,hb,he⟩:=Ideal.mem_span_singleton_sup.mp hm
      have he' : lJ I f* lJ I a=z.val := by
        rw [← hpz,← he,qU,pC,Ideal.Quotient.eq_zero_iff_mem.mpr hb,p5 ,
          mul_comm]
      have ha :lJ I a∈U:=hs _ (he'.symm ▸ z.property)
      exact ⟨⟨lJ I a,ha⟩,v9 he'⟩
  have hrank :=π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ,finrank_top,← hexact,
    zR hμ] at hrank
  exact hrank
theorem cXt {I:cy (aU σ k)} {f :aU σ k}
   (hdim: (oq I).natDegree≤1) (h:atV I f) :
   ox k (bcZ I f) ∧
     (ov k (bcZ I f) :ℚ)=(oq I).coeff 1 := by
 let J:=I ⊔ oj {f}
 have hJdim: (oq J).natDegree ≤
     (oq I).natDegree - 1 :=
   (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le h.regular h.degree).1
 have hfinite :ox k (bcZ I f) :=
   (natDegree_affineHilbertPolynomial_eq_zero_iff (I:=J)).mp (by omega)
 let:ox k (aU σ k ⧸ J) :=hfinite
 refine ⟨hfinite,?_⟩
 obtain ⟨N,hN⟩:=guW h
 obtain ⟨N₁,hN₁⟩:=exists_eval_affineHilbertPolynomial I
 obtain ⟨N₂,hN₂⟩:=exists_affineHilbertFunction_eq_finrank J
 let d:=N+N₁+N₂
 have hd:N≤d:= by dsimp [d]; omega
 have hd₁:N₁≤d:= by dsimp [d]; omega
 have hd₂:N₂≤d+1 := by dsimp [d]; omega
 have hsum:=emU h (hN d hd)
 rw [show I ⊔ oj {f} = J from rfl,hN₂ _ hd₂] at hsum
 have hsumQ: (ov k (bcZ I f) :ℚ) +
     (oq I).eval (d:ℚ) =
     (oq I).eval ((d+1 :ℕ) :ℚ) := by
   rw [hN₁ d hd₁,hN₁ (d+1) (by omega)]
   exact_mod_cast hsum
 have he (x :ℚ) : (oq I).eval x =
     (oq I).coeff 1*x+(oq I).coeff 0:= by
   nth_rw 1 [Polynomial.eq_X_add_C_of_natDegree_le_one hdim]
   simp
 simp only [he,Nat.cast_add,Nat.cast_one,mul_add,mul_one] at hsumQ
 linarith
end
end XW
end
section
namespace UI
noncomputable section
open K1 cu gT DQ Cu
open scoped Polynomial
variable {C₀:sQ} [Fact (nI C₀)] {J:cy kM} {g:ℕ}
abbrev K8 (R:wJ C₀ J g) :=R.equation.map (F5 C₀)
instance (R:wJ C₀ J g) :Fact (nI (K8 R)) :=⟨R.irreducible⟩
abbrev EC (R:wJ C₀ J g) :=AdjoinRoot (R:=y7 C₀) (K8 R)
def ek (R:wJ C₀ J g) :kM →+* EC R :=
 (pQ (R:=y7 C₀) (K8 R)).comp (LG C₀)
def LW (R:wJ C₀ J g) :oO C₀ →+* EC R :=
 (t7 (R:=y7 C₀) (K8 R)).comp (Mu C₀)
structure akV (R:wJ C₀ J g) (z :K) (S:K[X]) where
 V:ValuationSubring (EC R)
 Aw:kM →+* V
 generic_eq :V.toSubring.subtype.comp Aw=ek R
 marked_eq : (vZ V).comp Aw =
   ((vZ V).comp (Aw.comp mD)).comp (aEE z S)
def akV.fx {R:wJ C₀ J g} {z :K} {S:K[X]} (M:akV R z S) :
    FX →+* M.V :=
  M.Aw.comp mD
def akV.constant {R:wJ C₀ J g} {z :K} {S:K[X]} (M:akV R z S) :
    L →+* M.V :=
  M.fx.comp (lz L FX)
def akV.by2 {R:wJ C₀ J g} {z :K} {S:K[X]}
    (M:akV R z S) :Prop :=
  ∀ (a :oO C₀) (ha :LW R a∈M.V),
    ∃ c:L,vZ M.V ⟨LW R a,ha⟩ =
      vZ M.V (M.constant c)
end
end UI
end
section
namespace aiO
noncomputable section
open K1 cu gT DQ Cu
open scoped TensorProduct
theorem evz {k U V:Type} [c9 k] [vi U] [Module k U]
  [vi V] [Module k V] (f :U →ₗ[k] V) (hf :oz f) {d:ℕ}
  (h:JR k V d) :JR k U d:= by
 have :=h.1
 exact ⟨FiniteDimensional.of_injective f hf,(f.finrank_le_finrank_of_injective hf).trans h.2⟩
theorem eah {k ι A B:Type} [c9 k] [n5 A] [n5 B]
   [lI k A] [lI k B] (offset :ι) (u:aU (E8 offset) A)
   (f :A →ₐ[k] B) (hf :oz f) {d:ℕ}
   (h:JR (Jo k ι) (Gd k offset (lV f.toRingHom u)) d) :
   JR (Jo k ι) (Gd k offset u) d:= by
 classical
 let T:=aU ι k
 let F:=Jo k ι
 let v :=lV f.toRingHom u
 let _:=ami (k :=k) offset u
 let _:=ami (k :=k) offset v
 have heq : (lV f.toRingHom).comp (No (k :=k) offset u) =
     No (k :=k) offset v := by
   apply yU
   · intro a
     simp [No,p6]
   · intro i
     by_cases hi:i=offset
     · simp [No,hi,v]
     · simp [No,hi]
 let f' : aU (E8 offset) A →ₐ[T] aU (E8 offset) B :=
   { toRingHom:=lV f.toRingHom
     commutes' a :=pU heq a }
 let fL:=yl F F f'.toLinearMap
 have :zh T F:=IsLocalization.flat F (nonZeroDivisors T)
 have hInj:oz fL :=
   Dz f'.toLinearMap (MvPolynomial.map_injective _ hf)
 exact evz fL hInj h
theorem cIU {k σ:Type} [c9 k] {n:ℕ} (x :Fin n→σ) :
    anY (none :nX (Fin n)) (btr fun i=>(nq (x i) :aU σ k)) =
      (∑ i:Fin n,mD (ahI (k :=k) (some i))*nq (x i)) -
        mD (ahI (k :=k) (none :nX (Fin n))) := by
  classical
  simp [anY,btr,map_sum,pC]
theorem cIT {k ι σ:Type} [c9 k] (offset :ι) (x :σ) :
  anY offset (mD (nq x :aU σ k)) =
   nq x-MvPolynomial.C (ahI (k :=k) offset) := by
 simp [anY]
end
end aiO
end
section
namespace aiN
noncomputable section
open cu gT DQ Cu UI
open scoped Polynomial
variable {C₀:sQ} [Fact (nI C₀)] {J:cy kM} {g n:ℕ}
def amB (R:wJ C₀ J g) :FX →+* EC R :=
 (t7 (R:=y7 C₀) (K8 R)).comp (Mr C₀)
def aW2 (R:wJ C₀ J g) :EC R :=
 AdjoinRoot.root (R:=y7 C₀) (K8 R)
def bcC {R:wJ C₀ J g} (A:yI R n) :
    letI:lI FX (EC R) :=(amB R).toAlgebra
    IntermediateField FX (EC R) :=
  letI:lI FX (EC R) :=(amB R).toAlgebra
  FR FX
    (Set.range (fun i=>LW R (A.coordinate i)) ∪ {aW2 R})
abbrev akF {R:wJ C₀ J g} (A:yI R n) :=
 ↥(bcC A)
def auC {R:wJ C₀ J g} (A:yI R n) :
    akF A →+* EC R :=
  letI:lI FX (EC R) :=(amB R).toAlgebra
  (bcC A).val.toRingHom
def aq1 {R:wJ C₀ J g} (A:yI R n) :
    FX →+* akF A :=
  letI:lI FX (EC R) :=(amB R).toAlgebra
  lz FX (akF A)
def bcB {R:wJ C₀ J g} (A:yI R n) :
    akF A:= by
  letI:lI FX (EC R) :=(amB R).toAlgebra
  exact ⟨aW2 R,IntermediateField.subset_adjoin FX _
    (Set.mem_union_right _ (Set.mem_singleton _))⟩
abbrev Jv (E :Type) [c9 E] :=oD E[X]
def IN (E :Type) [c9 E] :E →+* Jv E :=
 (lz E[X] (Jv E)).comp pG
def awC (E :Type) [c9 E] :Jv E :=
 lz E[X] (Jv E) qx
def ZR {E F:Type} [c9 E] [c9 F] (i:E →+* F) :
    Jv E →+* Jv F :=
  pL (j:=t6 i) (Df i i.injective)
@[simp] theorem bsi {E F:Type} [c9 E] [c9 F] (i:E →+* F) (x :E) :
   ZR i (IN E x)=IN F (i x) := by
  unfold ZR IN pL
  simp only [p6,qM,sS ,
   wY]
@[simp] theorem cZf {E F:Type} [c9 E] [c9 F] (i:E →+* F) :
   ZR i (awC E)=awC F:= by
  unfold ZR awC pL
  simp only [qM,sS ,Polynomial.map_X]
def aYW {E :Type} [c9 E] (i:FX →+* E) (y :E)
    (b:aQ →+* Jv E) :Prop :=
  (∀ a,b (lz FX aQ a)=IN E (i a)) ∧
  b (ek 1)=IN E y ∧
  b (ek 0)=awC E
def an8 {E F:Type} [c9 E] [c9 F] (i:E →+* F) :ℕ :=
 letI:lI E F:=i.toAlgebra
 ov E F
end
end aiN
end
section
namespace akS
noncomputable section
open cu Cu MvPolynomial
open scoped TensorProduct
abbrev tu {n:ℕ} (B:cy (Gc n)) :=Gc n ⧸ B
abbrev e7 (n:ℕ) :=oD (N4 n)
abbrev Mb {n:ℕ} (B:cy (Gc n)) :=
 e7 n ⊗[FX] tu B
scoped instance gPV {n:ℕ} (B:cy (Gc n)) :
  n5 (Mb B) :=
 Algebra.TensorProduct.instCommRing (R:=FX) (A:=e7 n) (B:=tu B)
scoped instance gPW {n:ℕ} (B:cy (Gc n)) :
  CommSemiring (Mb B) :=
 Algebra.TensorProduct.instCommSemiring (R:=FX) (A:=e7 n) (B:=tu B)
def ajy {n:ℕ} (B:cy (Gc n)) :tu B →ₐ[FX] Mb B :=
 t5
def pD {n:ℕ} (B:cy (Gc n)) :
    aU (Fin n) (e7 n) →ₐ[e7 n] Mb B :=
  qy (R:=e7 n) (S₁:=Mb B)
    (fun i:Fin n=>ajy B (lJ B (nq (p9 i))))
def aIU {n:ℕ} (B:cy (Gc n)) (d:ℕ) :
    u8 (e7 n) (Mb B) :=
  (restrictTotalDegree (Fin n) (e7 n) d).map (pD B).toLinearMap
def aoe {n:ℕ} (B:cy (Gc n)) :Mb B :=
  ∑ i:Fin n,(lz (N4 n) (e7 n) (nq i)) •
    ajy B (lJ B (nq (p9 i)))
variable {F A:Type} [c9 F] [n5 A] [lI F A]
def abb (a :A) (W:u8 F A) :ℕ→u8 F A
 | 0=>W
 | k+1=>W ⊔ (abb a W k).map (LinearMap.mulLeft F a)
instance (a :A) (W:u8 F A) [ox F W] (k :ℕ) :
   ox F (abb a W k) := by
 induction k with
 | zero=>exact ‹Module.Finite F W›
 | succ k ih =>
   let:=ih
   change ox F ↥(W ⊔ (abb a W k).map (zE F a))
   infer_instance
instance {n:ℕ} (B:cy (Gc n)) (d:ℕ) :
  ox (e7 n) (aIU B d) := by
 unfold aIU
 infer_instance
end
end akS
end
section
set_option maxHeartbeats 2000000
namespace aiO
noncomputable section
open K1 cu gT DQ Cu
def c1 :Prop :=
  ∀ (k ι σ:Type) [c9 k] (offset :ι) (I:cy (aU σ k))
    (u:aU (E8 offset) (aU σ k)) (d:ℕ),
    JR (Jo k ι) (bbf offset I u) d ↔
    JR (Jo k ι)
      (Gd k offset (lV (lJ I) u)) d
def c2 :Prop :=
  ∀ (k ι A B E :Type) [c9 k] [n5 A] [oK A] [c9 B] [c9 E]
    [lI k A] [lI k B] [lI k E] [lI B E] [ox B E]
    (base :A →ₐ[k] B) (cover :B →ₐ[k] E),
    (let _:=base.toRingHom.toAlgebra; sI A B) →
    (∀ x,cover x=lz B E x) →
    ∀ (offset :ι) (u:aU (E8 offset) A) (d:ℕ),
    JR (Jo k ι) (Gd k offset u) d →
    JR (Jo k ι)
      (Gd k offset (lV (cover.toRingHom.comp base.toRingHom) u))
      (ov B E*d)
def c3:Prop :=
  ∀ (k ι ι' A:Type) [c9 k] [n5 A] [lI k A]
    (offset :ι) (offset' : ι') (y :A) (d:ℕ),
    JR (Jo k ι) (Gd k offset (mD y)) d →
    JR (Jo k ι') (Gd k offset' (mD y)) d
private theorem bNv {F σ:Type} [c9 F] (I:cy (aU σ F))
  {u v :aU σ F} {d:ℕ} (e :u=v)
  (h:JR F (aU σ F ⧸ (I ⊔ oj {u})) d) :
  JR F (aU σ F ⧸ (I ⊔ oj {v})) d:= by
 subst v
 exact h
private theorem cRT {k ι A:Type} [c9 k] [n5 A] [lI k A]
  {offset :ι} {u v :aU (E8 offset) A} {d:ℕ} (e :u=v)
  (h:JR (Jo k ι) (Gd k offset u) d) :
  JR (Jo k ι) (Gd k offset v) d:= by
 subst v
 exact h
private theorem cXk {F M:Type} [c9 F] [vi M] [Module F M] {a b:ℕ}
   (h:JR F M a) (hab:a≤b) :JR F M b :=
 ⟨h.1,h.2.trans hab⟩
private theorem cUW (h1 :c1) {k ι σ E :Type} [c9 k] [n5 E]
  [lI k E] (offset :ι) (I:cy (aU σ k))
  (u:aU (E8 offset) (aU σ k))
  (f : (aU σ k ⧸ I) →ₐ[k] E) (hf :oz f)
  {v :aU (E8 offset) E} {d:ℕ}
  (heq :v=lV f.toRingHom (lV (lJ I) u))
  (h:JR (Jo k ι) (Gd k offset v) d) :
  JR (Jo k ι) (bbf offset I u) d:= by
 apply (h1 k ι σ offset I u d).mpr
 exact eah offset _ f hf (cRT heq h)
private theorem eJ1 (h1 :c1) (h2 :c2) {k ι σ B E :Type}
    [c9 k] [c9 B] [c9 E] [lI k B] [lI k E]
    [lI B E] [ox B E] (offset :ι) (I:cy (aU σ k))
    [oK (aU σ k ⧸ I)] (base : (aU σ k ⧸ I) →ₐ[k] B)
    (cover : B →ₐ[k] E) (hfrac : let _ := base.toRingHom.toAlgebra
      sI (aU σ k ⧸ I) B)
    (hcover : ∀ x,cover x=lz B E x)
    (u:aU (E8 offset) (aU σ k)) {d:ℕ}
    (h:JR (Jo k ι) (bbf offset I u) d) :
    JR (Jo k ι)
      (Gd k offset (lV (cover.toRingHom.comp base.toRingHom)
        (lV (lJ I) u))) (ov B E*d) := by
  exact h2 k ι (aU σ k ⧸ I) B E base cover hfrac hcover offset
    (lV (lJ I) u) d ((h1 k ι σ offset I u d).mp h)
private def blN (n:ℕ) :
  aU (E8 (none :nX (Fin n))) (Gc n) :=
 btr fun i=>nq (p9 i)
private theorem dyI {n H :ℕ} (B:cy (Gc n))
  (h:a9K B H) :
  JR (jY n) (bbf (none :nX (Fin n)) B (blN n)) H := by
 have hb:anY (none :nX (Fin n)) (blN n)=blL n :=
  cIU (k :=FX) (n:=n) p9
 have hs :JR (jY n) (aAM B) H :=⟨h.finite,h.length⟩
 exact bNv (F:=jY n) (σ:=Fin 2 ⊕ Fin n)
  (Ideal.map (lV (lz FX (jY n))) B) hb.symm hs
variable {C₀:sQ} [Fact (nI C₀)] {J:cy kM} {g n:ℕ}
variable {R:wJ C₀ J g}
private theorem eJ0 (h1 :c1) (h2 :c2) (A:yI R n) {H :ℕ}
    (h:a9K (EF A) H) :
    JR (jY n) (Gl (SO A) (aD8 n)) (g*H) := by
  classical
  let B:=awU A
  let F:=y7 C₀
  let E :=EC R
  have :oK B:=dyy A
  have :ox F E :=c8S R
  let cover :F →ₐ[FX] E :=
    { toRingHom:=t7 (R:=y7 C₀) (Ot R)
      commutes' a :=(pU (zm FX (R:=y7 C₀) (f :=Ot R)).symm a) }
  have hcover (a :F) :cover a=lz F E a :=rfl
  let offset :nX (Fin n) :=none
  let ui:aU (E8 offset) (SourceRing n) :=
    btr fun i=>nq (some i)
  let ubq:aU (E8 offset) B :=
    lV (R:=Gc n) (S₁:=B)
      (lJ (EF A)) (blN n)
  let uiq:aU (E8 offset) (SourceRing n ⧸ SO A) :=
    lV (R:=SourceRing n) (S₁:=SourceRing n ⧸ SO A)
      (lJ (SO A)) ui
  have hbase :=dyI (EF A) h
  have hE :=eJ1 h1 h2 (k :=FX) (ι:=nX (Fin n))
    (σ:=Fin 2 ⊕ Fin n) (B:=F) (E :=E) offset (EF A) (aMf A) cover
    (cCW A) hcover (blN n) hbase
  have hmap :lV (cover.toRingHom.comp (aMf A).toRingHom) ubq =
      lV (azf A).toRingHom uiq:= by
    simp only [ubq,uiq,blN,ui,btr,map_sum,pC,
      x7,wR]
    apply uJ rfl
    intro i _
    apply qz (fun a :E =>
      (nq ⟨some i,Ee i⟩:aU (E8 offset) E) *
        mD a)
    change lz F E (aMf A (lJ (EF A) (nq (p9 i)))) =
      azf A (lJ (SO A) (nq (some i)))
    simp [azf,bVp,adq,W8]
    exact pU (AdjoinRoot.algebraMap_eq (f :=Ot R))
      (Mu C₀ (A.coordinate i))
  have hi:=cUW h1 offset (SO A) ui (azf A)
    (bHN A) hmap hE
  have hc:anY offset ui=aD8 n:=cIU some
  exact bNv _ hc (cXk hi (Nat.mul_le_mul_right H (a7Y R).le))
private theorem eHU (h1 :c1) (h2 :c2) (h3:c3) (A:yI R n)
   {H :ℕ} (hf :ox aQ (SI J))
   (hd:ov aQ (SI J)≤H) :
   JR (jY n) (Gl (SO A) (aD3 n)) H := by
 let B:=kM ⧸ J
 let E :=EC R
 have :oK B:=c2V R
 let cover :=AlgHom.id FX E
 have hcover (a :E) :cover a=lz E E a :=rfl
 let offset :nX (Fin n) :=none
 let y :B:=lJ J (nq (2 :Fin 3))
 let v :kM:=nq 2
 let w:SourceRing n:=nq none
 let wi:aU (E8 offset) (SourceRing n ⧸ SO A) :=
   lV (R:=SourceRing n) (S₁:=SourceRing n ⧸ SO A)
     (lJ (SO A)) (mD w)
 have hroot :JR aQ (bbf (1 :Fin 2) J (mD v)) H := by
   have hc:anY (1 :Fin 2) (mD v)=Pp (2 :Fin 3) :=
     cIT 1 2
   have hs :JR aQ (SI J) H :=⟨hf,hd⟩
   exact bNv (Ideal.map (lV (lz FX aQ)) J) hc.symm hs
 have hB:JR aQ (Gd FX (1 :Fin 2) (mD y)) H :=
   cRT (wR _ v)
     ((h1 FX (Fin 2) (Fin 3) 1 J (mD v) H).mp hroot)
 have hB' := h3 FX (Fin 2) (nX (Fin n)) B 1 offset y H hB
 have hE :=h2 FX (nX (Fin n)) B E E (arQ R) cover (by exact eIf R)
   hcover offset (mD y) H hB'
 have hy : (cover.toRingHom.comp (arQ R).toRingHom) y =
     (azf A).toRingHom (lJ (SO A) w) := by
   change arQ R y=azf A (lJ (SO A) w)
   simp [azf,arQ,adq,LG,y,w]
 have heq :lV (cover.toRingHom.comp (arQ R).toRingHom) (mD y) =
     lV (azf A).toRingHom wi:= by
   simp only [wi,wR,hy]
 have hi:=cUW h1 offset (SO A) (mD w) (azf A)
   (bHN A) heq hE
 have hc:anY offset (mD w)=aD3 n:=cIT offset none
 exact bNv _ hc (cXk hi (by rw [Module.finrank_self,one_mul]))
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :Cu.c4 := by
 intro C₀ hC₀ J g H n R A hbase hfinite hlength
 have hp:=eJ0 h1 h2 A hbase
 have hy :=eHU h1 h2 h3 A hfinite hlength
 exact ⟨enG A hbase.dimension,⟨hp.1,hp.2,hy.1,hy.2⟩⟩
end
end aiO
end
