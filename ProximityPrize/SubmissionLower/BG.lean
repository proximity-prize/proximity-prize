import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.TrivSqZeroExt.Ideal
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
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.R
import ProximityPrize.SubmissionLower.B1
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2500000
open _root_ renaming AlgEquiv.apply_symm_apply→zIH,AlgHom.pi→Kz,AlgHom.toLinearMap_apply→FV,Algebra→ oD,Algebra.EssFiniteType→Df,Algebra.FormallyEtale→Vq,Algebra.IsAlgebraic→MS,Algebra.IsSeparable→N0,Algebra.algebraMap→cy,Algebra.algebraMap_self_apply→zEi,Algebra.smul_def→TI,Algebra.trdeg→u5,Cardinal.mk→JK,CharP→u9,CharP.cast_eq_zero_iff→S1,CommRing→nq,DFunLike.congr_fun→Nr,ENNReal.ofReal→Au,Equiv.refl→Xu,Equiv.sumCongr→P7,EquivLike.apply_eq_iff_eq→zNr,Field→lV,Fin.castSucc→pU,Fin.castSucc_injective→xI,Fin.castSucc_ne_last→zm4,Fin.last→ II,Fin.lastCases→WK,Fin.snoc→yB,Fin.snoc_castSucc→FQ,Fin.snoc_comp_castSucc→ZK,Fin.snoc_last→Dz,Fin.sum_univ_eq_sum_range→Up,Fin.sum_univ_four→zmL,Fin.sum_univ_three→Kh,Finite→vj,Finset→aU,Finset.card_insert_of_notMem→Xo,Finset.filter_subset→zT0,Finset.induction_on→Cy,Finset.le_sup→zk,Finset.mem_insert→Y4,Finset.mem_univ→vi,Finset.mul_sum→ Iw,Finset.prod_eq_zero→zue,Finset.range→Pc,Finset.smul_sum→UP,Finset.sum_add_distrib→zm,Finset.sum_attach→zKB
open _root_ renaming Finset.sum_congr→sH,Finset.sum_eq_single→G3,Finset.sum_erase_add→zvm,Finset.sum_insert→yo,Finset.sum_ite_eq'→G0,Finset.sum_le_sum→KI,Finset.sum_mul→Nq,Finset.sum_powerset_insert→EK,Finset.univ→th,Finsupp.degree_eq_sum→Qx,Finsupp.induction_linear→Zh,Finsupp.mapDomain→JQ,Finsupp.mapDomain_apply_of_injective→Vz,Finsupp.single→t3,Finsupp.sum_fintype→Z0,Finsupp.weight→t4,Finsupp.weight_single→LP,Fintype.card→G1,FractionRing→vh,Function.Injective→qG,Function.Surjective→t8,Function.iterate_one→zS5,Function.iterate_succ_apply'→Rm,Function.update→GR,Function.update_of_ne→zBg,Ideal→c9,Ideal.Quotient.eq_zero_iff_mem→Ye,Ideal.Quotient.lift→R9,Ideal.Quotient.mk→nI,Ideal.Quotient.mk_eq_mk_iff_sub_mem→Mz,Ideal.Quotient.mk_surjective→vH,Ideal.Quotient.mkₐ→Ee,Ideal.kerLiftAlg→TZ,Ideal.kerLiftAlg_injective→zvo,Ideal.kerLiftAlg_mk→Kv,Ideal.map→zE,Ideal.map_le_iff_le_comap→zo0,Ideal.map_map→Oc,Ideal.map_span→zc,Ideal.mem_map_of_mem→EP,Ideal.mem_span_singleton_self→Pf,Ideal.mem_sup_left→zKg,Ideal.quotientEquivAlg→zpY,Ideal.quotientKerAlgEquivOfSurjective→Qw,Ideal.quotientMap→Yo,Ideal.quotientMap_injective→zmq,Ideal.quotientMapₐ→zwL,Ideal.span→n5
open _root_ renaming Ideal.span_insert→zf9,Ideal.span_mono→Pr,Ideal.span_singleton_le_iff_mem→ In,Ideal.subset_span→sI,Insert.insert→sS,IntermediateField.adjoin→NY,Irreducible→ze,IsAlgClosed→G8,IsDomain→HZ,IsFractionRing.injective→z7,IsLocalRing.ResidueField→G2,IsLocalRing.maximalIdeal→zR,IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing→ztC,IsLocalization→RD,IsLocalization.AtPrime.under_maximalIdeal→znW,IsLocalization.Away.algebraMap_isUnit→Ze,IsLocalization.Away.invSelf→Un,IsLocalization.Away.lift→ztx,IsLocalization.Away.lift_eq→Ts,IsLocalization.algebraMap_mem_map_algebraMap_iff→Te,IsLocalization.exists_mk'_eq→zcf,IsLocalization.isPrime_of_isPrime_disjoint→VH,IsLocalization.minimalPrimes_map→zMt,IsLocalization.mk'→zzm,IsLocalization.mk'_spec→zOg,IsLocalization.ringHom_ext→zuW,IsScalarTower→yl,IsScalarTower.algebraMap_apply→zg,IsScalarTower.algebraMap_eq→S2,IsScalarTower.of_algebraMap_eq→zsL,IsScalarTower.toAlgHom→zE2,IsUnit→qU,LinearIndependent→X8,LinearMap.congr_fun→Zg,LinearMap.finrank_range_of_inj→XJ,LinearMap.mulLeft→XB,Localization.AtPrime→C9,Localization.AtPrime.map_eq_maximalIdeal→zRt,Localization.Away→LQ,MeasurableSet→yJ,Module.Finite→qm,Module.Flat→G6,Module.finrank→pz,Module.length→u8,Module.length_eq_finrank→Yc,MulZeroClass.mul_zero→p9,MvPolynomial→lz,MvPolynomial.C→pQ
open _root_ renaming MvPolynomial.IsPrime.vanishingIdeal_zeroLocus→QL,MvPolynomial.X→lI,MvPolynomial.X_pow_eq_monomial→zp9,MvPolynomial.aeval→ oy,MvPolynomial.aeval_X→wY,MvPolynomial.aeval_eq_eval→x7,MvPolynomial.affineDegree→uJ,MvPolynomial.affineHilbertPolynomial→p7,MvPolynomial.algHom_ext→Dv,MvPolynomial.algebraMap_def→WX,MvPolynomial.algebraMap_eq→F9,MvPolynomial.algebraMvPolynomial→Zf,MvPolynomial.algebraTensorAlgEquiv→Wm,MvPolynomial.basisMonomials→FU,MvPolynomial.coeff_C→zG0,MvPolynomial.coeff_monomial→ IT,MvPolynomial.coeff_mul_X'→X4,MvPolynomial.coeff_sum→NX,MvPolynomial.degreeOf_def→Zi,MvPolynomial.eval→nX,MvPolynomial.eval_C→Fa,MvPolynomial.eval_X→xm,MvPolynomial.eval_map→NI,MvPolynomial.eval₂→SD,MvPolynomial.eventually_eval_affineHilbertPolynomial→zaL,MvPolynomial.ext→Kl,MvPolynomial.hom_eval₂→zUe,MvPolynomial.induction_on→JM,MvPolynomial.isLocalization→zEY,MvPolynomial.isWeightedHomogeneous_monomial→UZ,MvPolynomial.map→ ox,MvPolynomial.map_eval→WW,MvPolynomial.map_injective→RC,MvPolynomial.mem_vanishingIdeal_iff→Ok,MvPolynomial.mem_vanishingIdeal_singleton_iff→v9,MvPolynomial.monomial→ ov,MvPolynomial.monomial_mul_monomial→Kp,MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective→zGE,MvPolynomial.optionEquivLeft→G7,MvPolynomial.pderiv→ oZ,MvPolynomial.pderiv_mul→Qy,MvPolynomial.quotientDegreeLE→zf,MvPolynomial.rename→p6,MvPolynomial.renameEquiv_apply→Ob,MvPolynomial.ringHom_ext→Mw,MvPolynomial.totalDegree_C→UY,MvPolynomial.totalDegree_X→RJ,MvPolynomial.totalDegree_finsetSum_le→SM
open _root_ renaming MvPolynomial.totalDegree_mul→yU,MvPolynomial.totalDegree_sub_C_le→ZJ,MvPolynomial.trdeg_of_isDomain→zUx,MvPolynomial.vanishingIdeal→uh,MvPolynomial.weightedHomogeneousComponent→yQ,MvPolynomial.weightedHomogeneousComponent_eq_self→zfp,MvPolynomial.weightedHomogeneousComponent_mem→zbF,MvPolynomial.weightedHomogeneousComponent_of_mem→Zt,MvPolynomial.zeroLocus→qM,Nat.add_le_add→Aa,Nat.cast_add→Pk,Nat.cast_mul→ IU,Nat.cast_nonneg→NW,Nat.cast_sub→Vl,Nat.choose_one_right→zk4,Nat.le_add_right→JW,Nat.lt_succ_of_le→PD,Nat.mul_le_mul_left→Kc,Nat.mul_le_mul_right→Hw,Nat.sub_add_cancel→z8,Nat.zero_le→v8,Option→zi,Pi.add_apply→Av,Pi.single→vZ,Pi.single_apply→RP,Pi.single_eq_of_ne→C5,Pi.smul_apply→PM,Polynomial→ oz,Polynomial.C→ oY,Polynomial.C_eq_natCast→Np,Polynomial.C_injective→VC,Polynomial.X→pL,Polynomial.X_dvd_iff→zIa,Polynomial.as_sum_range'→Vs,Polynomial.coeff_map→Eg,Polynomial.coeff_zero→KH,Polynomial.coeff_zero_eq_eval_zero→zTt,Polynomial.derivative→mD,Polynomial.derivative_mul→Fz,Polynomial.evalRingHom→y5,Polynomial.eval_C→FR,Polynomial.eval_map→zhI,Polynomial.eval₂RingHom→WD,Polynomial.hasseDeriv→p5,Polynomial.hasseDeriv_map→NZ,Polynomial.mapRingHom→MO,Polynomial.map_monomial→zA0,Polynomial.map_sum→zWf
open _root_ renaming Polynomial.monomial→vl,Polynomial.natDegree_taylor→SC,Polynomial.ringHom_ext→Pv,Polynomial.taylor→xL,Polynomial.taylor_coeff→SW,Polynomial.taylor_taylor→Yi,Polynomial.taylor_zero→z9k,RingHom.comp_apply→Gn,RingHom.congr_fun→Gi,RingHom.ext→Ef,RingHom.injective→Xx,RingHom.ker→ oK,RingHom.ker_isPrime→zgL,RingHom.mem_ker→zS,Set.Subset.antisymm→G5,Set.add_subset_add→zgS,Set.eq_univ_of_forall→zps,Set.image_image→Sv,Set.mem_insert_iff→Sd,Set.mem_preimage→SU,Set.mem_range_self→zWL,Set.mem_singleton_iff→Ww,Set.range→qJ,Set.range_comp'→Xp,Set.univ→z9,Submodule→zd,Submodule.map_mono→zzl,Submodule.mem_top→PA,Submodule.span→Re,Submodule.sum_mem→Wl,Submonoid.powers→LO,Subtype.ext→vG,Subtype.val→XG,Transcendental→VO,TrivSqZeroExt.ext→Gk,aR.Shape→pC,add_comm→LR,add_neg_cancel→OJ,add_nonneg→SL,charP_of_injective_ringHom→vw,congrArg→ oj,congrFun→wR,convexHull→xW,convexHull_min→Mk,convexHull_mono→Ml,convex_convexHull→WY,dN.separant→Bf,div_mul_cancel₀→TH
open _root_ renaming faithfulSMul_iff_algebraMap_injective→zSO,finSuccEquivLast→wA,inferInstance→xu,le_antisymm→yL,le_rfl→t9,map_add→pG,map_mul→lJ,map_natCast→zh,map_ne_zero_iff→Xg,map_neg→ Il,map_ofNat→uW,map_one→vk,map_pow→t7,map_prod→Lf,map_smul→KA,map_sub→qx,map_sum→t5,map_zero→ oq,measurableSet_Icc→MK,measurableSet_le→C4,measurable_const→Gj,measurable_pi_apply→Nj,mul_add→GF,mul_assoc→qy,mul_comm→uz,mul_le_mul_of_nonneg_left→qz,mul_ne_zero→FK,mul_nonneg→Et,mul_one→Dw,nonZeroDivisors→GY,not_le_of_gt→G4,nsmul_eq_mul→Mj,one_mul→t6,pow_ne_zero→Du,pow_succ→GB,smul_eq_mul→G9,sub_eq_zero→Ar,sub_self→Ea,sub_zero→Gr,subset_convexHull→VS,subsingleton_iff_forall_eq→zAZ,succ_nsmul→J4,trdeg_add_eq→Pj,zero_add→wB
set_option autoImplicit true
section
namespace oR
noncomputable section
open K1 aR Polynomial
open scoped BigOperators
def qg {r :ℕ} (top:Fin r) (f :af r) (S:ao[X]) :Prop :=
 cK f S=0∧cK (oZ top f) S≠0
def DU {r :ℕ} (f :af r) :af r :=
 ∑ m∈f.support,ov m (f.coeff m).derivative
def separant (f :af 3) :af 3:=oZ 2 f
def D3 (b:af 3) :af 3 :=
  DU b+MvPolynomial.X 1*oZ 0 b +
    2*lI 2*oZ 1 b
def Ev (f b:af 3) :af 3 :=
 separant f*D3 b - D3 f*oZ 2 b
def AR (f :af 3) :ℕ→af 3
  | 0 => -D3 f
  | j+1 =>
    let b:=AR f j
    separant f*Ev f b-(2*j+1 :ℕ)*b*Ev f (separant f)
def Fb (f :af 3) :Prop :=
 f∣AR f (bf-3)
def ang (w:I→K) (Γ:aU K) (s :K→K[X]) (d:ℕ) :Prop := by
  classical
  exact ∃ persistent:aU I,
    (∀ i∈persistent,∀ γ∈Γ,(s γ).eval (node i)=w i) ∧
    ∀ i,i∉persistent→(Γ.filter fun γ=>(s γ).eval (node i)=w i).card≤d
structure Rr (w:I→K) (Γ:aU K) (s :K→K[X]) where
 n:ℕ
 part:Fin n→aU K
 cap:Fin n→ℕ
 sub : ∀ i,part i⊆Γ
 localCapacity : ∀ i,ang w (part i) s (cap i)
def Rr.CF {w Γ s} (F:Rr w Γ s) :aU K:= by
 classical
 exact Finset.univ.biUnion F.part
def Rr.BJ {w Γ s} (F:Rr w Γ s) :ℕ := ∑ i,F.cap i
abbrev S9:Shape :=⟨120,48,24⟩
def Yr (L:ℕ) :Shape :=
 let j:=2+(L-4)*(S9.j+2)
 ⟨1+(L-4)*S9.b,j,min (1+(L-4)*(S9.t+2)) (j/2)⟩
abbrev tC:Shape :=⟨120,49,24⟩
def amU (p q r :pC) :ℕ:=p.t*(q.j - q.t)*(2*r.b - r.j)
def Wc (p q r :pC) :ℕ :=
  (amU p q r+amU p r q+amU q p r +
    amU q r p+amU r p q+amU r q p)/2
end
end oR
end
section
namespace we
noncomputable section
open K1 aR oR Polynomial
open scoped BigOperators
abbrev aGn:=vh ao[X]
abbrev cH :=AlgebraicClosure aGn
abbrev eT (n:ℕ) :=lz (Fin n) cH
abbrev GD:=Fin bf→cH
abbrev Bk :=c9 (eT bf)
abbrev aap (n:ℕ) :=Fin n× c9 (eT 3)
def qY:ao[X] →+* cH :=
 (cy aGn cH).comp (cy ao[X] aGn)
def fW {n:ℕ} (P:af n) :eT n:=ox qY P
def zq {n:ℕ} (S:ao[X]) :Fin n→cH :=
 fun j=>qY (jet S j)
def afs (S:ao[X]) :GD :=
 fun j=>cy ao cH (S.coeff j)
def JC (a :GD) :cH[X] :=
 ∑ j:Fin bf,vl j.val (a j)
def Dm (f :af 3) :af 3:=AR f (bf-3)
def Vk (f :af 3) :af 3:=AR f (bf - 2)
def BW (f :af 3) :c9 (eT 3) :=
 n5 {fW f,fW (Dm f)}
def D7 (f :af 3) (P:c9 (eT 3)) :Set (Fin 3→cH) :=
  {y | y∈qM cH P ∧
    nX y (fW (separant f))≠0}
def Lx (f :af 3) (P:c9 (eT 3)) :ℕ∞ := by
  classical
  exact if hp:P.IsPrime then
    letI:=hp
    let A:=C9 P
    u8 A (A ⧸ (BW f).map (cy (eT 3) A))
  else 0
def aGt (f :af 3) (P:c9 (eT 3)) :Prop :=
 Lx f P=1∧fW (Vk f)∈P
def avD (f :af 3) (P:c9 (eT 3)) :Set (Fin 3→cH) :=
 {y | y∈D7 f P∧nX y (fW (Vk f))=0}
def vY (P:eT 3) :eT 4 :=p6 pU P
def graph (f :af 3) :eT 4 :=
 vY (fW (D3 f))+3*lI 3*vY (fW (separant f))
def rP (f :af 3) :c9 (eT 4) :=
 n5 {vY (fW f),graph f}
def JZ (f :af 3) (y :Fin 3→cH) :Fin 4→cH :=
  yB y (-MvPolynomial.eval y (fW (D3 f)) /
    (3*nX y (fW (separant f))))
def DO (P:eT 4) (box :pC) (height:ℕ) :Prop :=
  ∀ a∈P.support,a 0+a 1+a 2≤box.b ∧
    a 1+2*a 2≤box.j∧a 2≤box.t∧a 3≤height
def ag9 (f old:af 3) (P:eT 4) :Prop :=
  ∃ (a b:ℕ) (c:cH),c≠0 ∧
    let sep:=vY (fW (separant f))
    sep^a*(sep^b*P-MvPolynomial.C c*vY (fW old))∈rP f
def Uj (f :af 3) (numerator :Fin bf→eT 4)
    (y :Fin 3→cH) :GD :=
  fun i=>nX (JZ f y) (numerator i) /
    nX y (fW (separant f))^(bf-4)
structure Gf (f :af 3) where
 cut:eT 4
 next:eT 4
 numerator :Fin bf→eT 4
 graph_box :DO (graph f) tC 1
 cut_box :DO cut (Yr (bf+1)) (bf - 1)
 next_box :DO next (Yr (bf+2)) bf
 coefficient_box : ∀ i,DO (numerator i) (Yr bf) (bf - 2)
 cut_represents :ag9 f (Dm f) cut
 next_represents :ag9 f (Vk f) next
 btd: (Dm f).totalDegree ≤
   1+(2*(bf+1) - 7)*(f.totalDegree - 1)
 actual : ∀ S:ao[X],S.natDegree≤133671→qg 2 f S →
   cK (Dm f) S=0∧cK (Vk f) S=0 ∧
     Uj f numerator (zq S)=afs S
def Of (P:af 3) (S:cH[X]) :cH[X] :=
  nX (fun j=>p5 j.val S)
    (ox (MO (cy ao cH)) P)
structure acU (f :af 3) (Q:Bk) :Prop where
 prime :Q.IsPrime
 dimension : (p7 Q).natDegree=1
 solves : ∀ a∈qM cH Q,
  Of f (JC a)=0
 regular : ∃ a∈qM cH Q,
  Of (separant f) (JC a)≠0
end
end we
end
section
namespace we
noncomputable section
open K1 aR oR Polynomial
open scoped BigOperators
theorem Yk :qG qY :=
 (cy aGn cH).injective.comp (z7 ao[X] aGn)
theorem a3H {n:ℕ} (P:af n) (S:ao[X]) :
  nX (zq S) (fW P)=qY (cK P S) := by
 unfold fW cK zq
 rw [NI]
 exact (MvPolynomial.eval₂_comp _ _ _).symm
theorem cVV (s :K→K[X]) (Γ:aU K)
  (hs :Set.InjOn s (Γ:Set K)) :
  Set.InjOn (fun γ=>zq (n:=3) (extend (s γ))) (Γ:Set K) := by
 intro γ hγ δ hδ heq
 apply hs hγ hδ
 apply Polynomial.map_injective embed embed.injective
 have h:=Yk (wR heq (0:Fin 3))
 simpa [jet,zq] using h
private theorem bK9 (S:ao[X]) (hS:S.natDegree≤133671) :
  JC (afs S)=S.map (cy ao cH) := by
 unfold JC afs
 rw [Up (fun j =>
  vl j (cy ao cH (S.coeff j)))]
 conv_rhs=>rw [Vs S bf (PD hS)]
 simp only [zWf,zA0]
private def VA (x y :cH) :eT bf :=
 (∑ j:Fin bf,pQ (x^j.val)*lI j)-MvPolynomial.C y
private theorem dhJ (x y :cH) : (VA x y).totalDegree≤1 := by
 unfold VA
 apply (ZJ _ _).trans
 apply SM
 intro j _
 simpa only [UY ,wB,RJ] using
  yU (pQ (x^j.val)) (lI j)
private theorem cNe (a :GD) (x y :cH) :
  nX a (VA x y)=(JC a).eval x - y := by
 simp only [VA,JC,qx ,t5 ,lJ,Fa ,
  xm,Polynomial.eval_finsetSum,Polynomial.eval_monomial,uz]
private def bcP:K →+* cH :=(cy ao cH).comp embed
private def D4 (w:I→K) (i:I) :eT bf :=
 VA (bcP (node i)) (bcP (w i))
end
end we
end
section
namespace yz
noncomputable section
open aR oR we MvPolynomial
open scoped BigOperators Pointwise
abbrev oe :=Fin 4→cH
def yD (f :af 3) :aU (c9 (eT 3)) := by
  classical
  exact if Fb f then ∅ else
    (BW f).retainedMinimalPrimes (fW (separant f))
def S3 (f :af 3) (P:c9 (eT 3)) :Set oe :=
 JZ f '' D7 f P
def F3 (f :af 3) (P:c9 (eT 3)) :c9 (eT 4) :=
 uh cH (S3 f P)
def aCt (s :pC) (h:ℕ) :Set (Fin 4 →₀ ℕ) :=
 {a | a 0+a 1+a 2≤ s.b∧a 1+2*a 2≤ s.j∧a 2≤ s.t∧a 3≤h}
instance gO5 (s :pC) (h:ℕ) :vj (aCt s h) :=
 ((Finsupp.finite_of_degree_le (s.b+h)).subset (by
   intro a ha
   change a.degree≤ s.b+h
   rw [Qx ,zmL]
   exact (Aa ha.1 ha.2.2.2))).to_subtype
abbrev RY:=Yr (bf+2)
def ay3 (F G E L:eT 4) :c9 (eT 4) :=
 n5 {F,G,E,L}
abbrev oF (y :oe) :c9 (eT 4) :=
 uh cH {y}
def Ny (J:c9 (eT 4)) (y :oe) :ℕ∞ :=
 let A:=C9 (oF y)
 u8 A (A ⧸ J.map (cy (eT 4) A))
abbrev iz :=Fin 4→ℝ
def nD (s :pC) (h:ℕ) :Set iz :=
  {x | (∀ j,0≤x j)∧x 0 + x 1 + x 2≤ s.b ∧
    x 1+2*x 2≤ s.j∧x 2≤ s.t∧x 3≤h}
def alT (F:eT 4) :Set iz :=
 xW ℝ {x | ∃ a∈F.support,∀ j,0≤x j∧x j≤a j}
def aa1 (B:Fin 4→Set iz) :ℝ :=
  ∑ S∈(th :aU (Fin 4)).powerset,
    (-1 :ℝ)^(4 - S.card)*(MeasureTheory.volume (∑ i∈S,B i)).toReal
end
end yz
end
section
namespace yz
noncomputable section
open aR oR we MvPolynomial
open scoped BigOperators
theorem bsa {R:Type} [nq R] [IsNoetherianRing R]
    {P J:c9 R} [P.IsPrime] (hP:P∈J.minimalPrimes) :
    let A:=C9 P
    u8 A (A ⧸ J.map (cy R A)) < ⊤ := by
  let A:=C9 P
  let L:=J.map (cy R A)
  change u8 A (A ⧸ L) < ⊤
  have hmin:zR A∈L.minimalPrimes := by
    rw [show L=J.map (cy R A) from rfl,
      zMt P.primeCompl A,SU,
      znW A P]
    exact hP
  have :IsArtinianRing (A ⧸ L) :=
    ztC L hmin
  exact lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L,
        isArtinian_of_surjective_algebraMap (vH (I:=L))⟩))
private theorem cUa (f :af 3) :qG (JZ f) := by
 intro y z h
 funext i
 simpa only [JZ,FQ] using wR h i.castSucc
@[simp] theorem ahz (f :af 3) (x :Fin 3→cH) (P:eT 3) :
   eval (JZ f x) (vY P)=eval x P:= by
  rw [vY,eval_rename]
  have h:JZ f x ∘ pU=x :=ZK
  rw [h]
private theorem three_ne_zero : (3:cH)≠0:= by
 let:u9 ao K1.p:=vw aR.embed.injective K1.p
 let:u9 (oz ao) K1.p :=
  vw VC K1.p
 let:u9 cH K1.p :=
  vw Yk K1.p
 exact fun h=>(by decide : ¬ K1.p∣3)
  ((S1  cH K1.p 3).mp h)
theorem bpz {f :af 3} {x :Fin 3→cH}
   (hx :eval x (fW (separant f))≠0) :
   eval (JZ f x) (graph f)=0:= by
 have hs : (3:cH)*eval x (fW (separant f))≠0 :=
   FK three_ne_zero hx
 have hz :JZ f x 3 = -eval x (fW (D3 f)) /
     (3*eval x (fW (separant f))) := by
   exact Dz _ _
 rw [graph,pG,lJ,lJ,uW,xm,
   ahz,ahz,hz]
 let u:=eval x (fW (D3 f))
 let s :=eval x (fW (separant f))
 change u+3*(-u/(3*s))*s=0
 calc
   _=u+(-u/(3*s))*(3*s) := by ring
   _=0:= by rw [TH _ hs,OJ]
theorem bpH {f old:af 3} {B:eT 4}
   (hB:ag9 f old B) {x :Fin 3→cH}
   (hf :eval x (fW f)=0) (hx :eval x (fW (separant f))≠0) :
   eval (JZ f x) B=0↔eval x (fW old)=0:= by
 have ht:rP f≤oK (eval (JZ f x)) := by
   apply Ideal.span_le.mpr
   intro q hq
   change q∈oK (eval (JZ f x))
   rw [zS]
   simp only [Sd ,Ww] at hq
   rcases hq with rfl | rfl
   · simpa only [ahz] using hf
   · exact bpz hx
 obtain ⟨a,b,c,hc,hm⟩:=hB
 have he :=RingHom.mem_ker.mp (ht hm)
 simp only [lJ,t7,qx ,Fa ,ahz] at he
 have heq :=sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (Du a hx))
 constructor
 · intro h
   rw [h,p9] at heq
   exact (mul_eq_zero.mp heq.symm).resolve_left hc
 · intro h
   rw [h,p9] at heq
   exact (mul_eq_zero.mp heq).resolve_left (Du b hx)
end
end yz
end
section
namespace zP
noncomputable section
open aR oR we yz MvPolynomial
open scoped Pointwise
abbrev Exponent:=Fin 4 →₀ ℕ
def a9X (A:aU Exponent) :Prop :=
 ∀ ⦃a b:Exponent⦄,a∈A→b≤a→b∈A
def an7:Exponent →+ iz where
 toFun a i:=(a i:ℝ)
 map_zero' := by ext i; simp
 map_add' a b:= by ext i; simp [Finsupp.add_apply]
def LK (A:Set Exponent) :Set iz :=
 xW ℝ (an7 '' A)
def a3z (F:eT 4) :aU Exponent :=
 F.support.biUnion fun a=>Finset.Icc 0 a
def auv (s :pC) (h:ℕ) :aU Exponent :=
 (Set.toFinite (aCt s h)).toFinset
def ke (f :Fin 4→eT 4) :c9 (eT 4) :=
 n5 (qJ f)
abbrev xB (A:Fin 4→aU Exponent) :=
 lz (Σ i:Fin 4,↥(A i)) cH
abbrev fZ (A:Fin 4→aU Exponent) :=
 vh (xB A)
def ve (A:Fin 4→aU Exponent) (i:Fin 4) :
    lz (Fin 4) (fZ A) :=
  ∑ a : ↥(A i),ov a.1
    (cy (xB A) (fZ A) (lI ⟨i,a⟩))
abbrev HG (A:Fin 4→aU Exponent) :=
 lz (Fin 4) (fZ A) ⧸ n5 (qJ (ve A))
def TX (A:Fin 4→aU Exponent) (d:Fin 4→ℕ) :ℕ :=
 (∑ i:Fin 4,d i•(↑(A i) :Set Exponent)).ncard
def corner (q n:ℕ) (S:aU (Fin 4)) :Fin 4→ℕ :=
 fun i=>q+if i∈S then n else 0
end
end zP
end
section
namespace zP
noncomputable section
open aR we yz MvPolynomial
theorem a5J {F:eT 4} {a :Exponent} :
  a∈a3z F ↔ ∃ b∈F.support,a≤b:= by
 classical
 simp [a3z,Finset.mem_Icc,show (0:Exponent)≤a from fun _=>v8 _]
theorem aIA {s :pC} {h:ℕ} {a :Exponent} :
  a∈auv s h↔a∈aCt s h :=
 Set.Finite.mem_toFinset _
theorem cWU (F:eT 4) :
   LK (a3z F)=alT F:= by
 unfold LK alT
 apply G5
 · apply Ml
   rintro x ⟨e,he,rfl⟩
   obtain ⟨a,ha,hea⟩:=a5J.mp he
   exact ⟨a,ha,fun i=>⟨NW _,Nat.cast_le.mpr (hea i)⟩⟩
 · refine Mk ?_ (WY _ _)
   rintro x ⟨a,ha,hx⟩
   let KN :Set iz :=
    Set.univ.pi fun i=>({0,(a i:ℝ)} : Set ℝ)
   have hxc:x∈xW ℝ KN := by
    apply mem_convexHull_pi
    intro i _
    rw [convexHull_pair,segment_eq_Icc (NW (a i))]
    exact hx i
   apply Ml (t:=an7 '' (↑(a3z F) :Set Exponent)) ?_ hxc
   intro y hy
   change ∀ i∈(z9 :Set (Fin 4)),y i∈({0,(a i:ℝ)} : Set ℝ) at hy
   have hv (i:Fin 4) : ∃ b:ℕ,(b:ℝ)=y i∧b≤a i:= by
    have hi:=hy i (Set.mem_univ i)
    simp only [Sd ,Ww] at hi
    rcases hi with hi | hi
    · exact ⟨0,by simpa using hi.symm,v8 _⟩
    · exact ⟨a i,hi.symm,t9⟩
   choose v hv using hv
   let e :Exponent:=Finsupp.equivFunOnFinite.symm v
   have hev : ∀ i,e i=v i:= fun i =>
    wR (Finsupp.equivFunOnFinite.apply_symm_apply v) i
   refine ⟨e,a5J.mpr ⟨a,ha,fun i=>(hev i).trans_le (hv i).2⟩,?_⟩
   funext i
   change (e i:ℝ)=y i
   rw [hev i,(hv i).1]
private def aMB (s :pC) (h:ℕ) (u:Fin 4→ℝ) :iz :=
 let z :=u 2*s.t
 let y :=u 1*((s.j:ℝ) - 2*z)
 ![u 0*((s.b:ℝ) - y - z),y,z,u 3*h]
private theorem dEI (s :pC) (h:ℕ) (u:Fin 4→ℝ) (i:Fin 4) :
  aMB s h u=(1 - u i)•aMB s h (GR u i 0) +
   u i•aMB s h (GR u i 1) := by
 funext j
 fin_cases i <;> fin_cases j <;>
  simp [aMB,Av,G9,GR] <;> ring
private theorem dES (s :pC) (h:ℕ) (hs :s.j≤ s.b)
   (ht:2*s.t≤ s.j) (u:Fin 4→ℝ) (hu : ∀ i,u i=0∨u i=1) :
   aMB s h u∈LK (auv s h) := by
 have hbinary (i:Fin 4) : ∃ v :ℕ,(v :ℝ)=u i∧v≤1 := by
   rcases hu i with hi | hi
   · exact ⟨0,by simpa using hi.symm,v8 1⟩
   · exact ⟨1,by simpa using hi.symm,t9⟩
 choose v hv using hbinary
 let z :=v 2*s.t
 let y :=v 1*(s.j - 2*z)
 have hz :z≤ s.t:= by
   simpa [z] using Hw s.t (hv 2).2
 have hzs :2*z≤ s.j:=(Kc 2 hz).trans ht
 have hy :y≤ s.j - 2*z := by
   simpa [y] using Hw (s.j - 2*z) (hv 1).2
 have hyz :y+2*z≤ s.j:= by omega
 have hys :y≤ s.b:= by omega
 have hzys :z≤ s.b - y := by omega
 let rU:Fin 4→ℕ := ![v 0*(s.b - y - z),y,z,v 3*h]
 let e :Exponent:=Finsupp.equivFunOnFinite.symm rU
 have he (i:Fin 4) :e i=rU i :=
   wR (Finsupp.equivFunOnFinite.apply_symm_apply rU) i
 have hsupp:e∈auv s h:= by
   apply aIA.mpr
   have hc₀:v 0*(s.b - y - z)≤ s.b - y - z := by
     simpa using Hw (s.b - y - z) (hv 0).2
   have hc₃:v 3*h≤h:= by simpa using Hw h (hv 3).2
   change e 0+e 1+e 2≤ s.b∧e 1+2*e 2≤ s.j∧e 2≤ s.t∧e 3≤h
   rw [he 0,he 1,he 2,he 3]
   change v 0*(s.b - y - z)+y+z≤ s.b∧y+2*z≤ s.j∧z≤ s.t∧v 3*h≤h
   exact ⟨by omega,hyz,hz,hc₃⟩
 apply VS ℝ _
 refine ⟨e,hsupp,?_⟩
 have hz' : (z :ℝ)=u 2*s.t:= by
   simp only [z,IU,(hv 2).1]
 have hy' : (y :ℝ)=u 1*((s.j:ℝ) - 2*(u 2*s.t)) := by
   simp only [y,IU,Vl hzs,Nat.cast_ofNat,(hv 1).1]
   rw [hz']
 funext i
 change (e i:ℝ)=aMB s h u i
 rw [he]
 fin_cases i
 · change (↑(v 0*(s.b - y - z)) :ℝ) =
     u 0*((s.b:ℝ) - u 1*((s.j:ℝ) - 2*(u 2*s.t)) - u 2*s.t)
   rw [IU,Vl hzys,Vl hys,(hv 0).1,hy',hz']
 · exact hy'
 · exact hz'
 · change (↑(v 3*h) :ℝ)=u 3*h
   rw [IU,(hv 3).1]
private theorem dEU (s :pC) (h:ℕ) (hs :s.j≤ s.b)
    (ht:2*s.t≤ s.j) (S:aU (Fin 4)) (u:Fin 4→ℝ)
    (hside : ∀ i∈S,0≤u i∧u i≤1)
    (hcorner : ∀ i∉S,u i=0∨u i=1) :
    aMB s h u∈LK (auv s h) := by
  classical
  induction S using Cy generalizing u with
  | empty =>
      exact dES s h hs ht u (fun i=>hcorner i (by simp))
  | insert i S hi ih =>
      have updated (b:ℝ) (hb:b=0∨b=1) :
          aMB s h (GR u i b)∈LK (auv s h) := by
        apply ih
        · intro j hj
          have hji:j≠i:= fun e=>hi (e ▸ hj)
          simpa [zBg hji] using hside j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hji:j=i
          · subst j
            simpa using hb
          · rw [zBg hji]
            exact hcorner j (by simp [hji,hj])
      have hui:=hside i (Finset.mem_insert_self i S)
      rw [dEI s h u i]
      exact WY ℝ _ (updated 0 (Or.inl rfl)) (updated 1 (Or.inr rfl))
        (sub_nonneg.mpr hui.2) hui.1 (sub_add_cancel 1 (u i))
private theorem aND {x d:ℝ} (hx :0≤x) (hxd:x≤d) :
   ∃ u:ℝ,0≤u∧u≤1∧u*d=x := by
 by_cases hd:d=0
 · exact ⟨0,t9,zero_le_one,by linarith⟩
 · have hd' : 0<d:=lt_of_le_of_ne (hx.trans hxd) (Ne.symm hd)
   exact ⟨x/d,div_nonneg hx hd'.le,(div_le_one hd').mpr hxd,TH x hd⟩
private theorem dPE (s :pC) (h:ℕ) :Convex ℝ (nD s h) := by
 intro x hx y hy a b ha hb hab
 obtain ⟨hx,hx₁,hx₂,hx₃,hx₄⟩:=hx
 obtain ⟨hy,hy₁,hy₂,hy₃,hy₄⟩:=hy
 refine ⟨fun i=>SL (Et ha (hx i)) (Et hb (hy i)),?_,?_,?_,?_⟩
 · change a*x 0+b*y 0+(a*x 1+b*y 1)+(a*x 2+b*y 2)≤ s.b
   nlinarith [qz hx₁ ha,qz hy₁ hb,
    oj (fun t:ℝ=>t*s.b) hab]
 · change a*x 1+b*y 1+2*(a*x 2+b*y 2)≤ s.j
   nlinarith [qz hx₂ ha,qz hy₂ hb,
    oj (fun t:ℝ=>t*s.j) hab]
 · change a*x 2+b*y 2≤ s.t
   nlinarith [qz hx₃ ha,qz hy₃ hb,
    oj (fun t:ℝ=>t*s.t) hab]
 · change a*x 3+b*y 3≤h
   nlinarith [qz hx₄ ha,qz hy₄ hb,
    oj (fun t:ℝ=>t*h) hab]
theorem bIk (s :pC) (h:ℕ) (hs :s.j≤ s.b)
    (ht:2*s.t≤ s.j) :LK (auv s h)=nD s h:= by
  apply G5
  · refine Mk ?_ (dPE s h)
    rintro x ⟨e,he,rfl⟩
    obtain ⟨he₁,he₂,he₃,he₄⟩:=aIA.mp he
    refine ⟨fun i=>NW _,?_,?_,Nat.cast_le.mpr he₃,Nat.cast_le.mpr he₄⟩
    · change (e 0:ℝ)+e 1+e 2≤ s.b
      exact_mod_cast he₁
    · change (e 1 :ℝ)+2*e 2≤ s.j
      exact_mod_cast he₂
  · intro x hx
    obtain ⟨hx,hx₁,hx₂,hx₃,hx₄⟩:=hx
    obtain ⟨u₀,hu₀,hv₀,h₀⟩:=aND (hx 0) (show x 0≤ s.b - x 1 - x 2 by linarith)
    obtain ⟨u₁,hu₁,hv₁,h₁⟩:=aND (hx 1) (show x 1≤ s.j - 2*x 2 by linarith)
    obtain ⟨u₂,hu₂,hv₂,h₂⟩:=aND (hx 2) hx₃
    obtain ⟨u₃,hu₃,hv₃,h₃⟩:=aND (hx 3) hx₄
    let u:Fin 4→ℝ := ![u₀,u₁,u₂,u₃]
    have hu:aMB s h u=x := by
      funext i
      fin_cases i
      · change u₀*((s.b:ℝ) - u₁*((s.j:ℝ) - 2*(u₂*s.t)) - u₂*s.t)=x 0
        rw [h₂,h₁,h₀]
      · change u₁*((s.j:ℝ) - 2*(u₂*s.t))=x 1
        rw [h₂,h₁]
      · exact h₂
      · exact h₃
    rw [← hu]
    apply dEU s h hs ht th
    · intro i _
      fin_cases i
      · exact ⟨hu₀,hv₀⟩
      · exact ⟨hu₁,hv₁⟩
      · exact ⟨hu₂,hv₂⟩
      · exact ⟨hu₃,hv₃⟩
    · simp
end
end zP
end
section
namespace yz
noncomputable section
open aR oR we MvPolynomial
open scoped BigOperators Pointwise
private theorem dsq {k σ:Type} [lV k] [vj σ] (x :σ→k) :
  uJ (uh k {x})=1 := by
 have hker :uh k {x} = oK (oy x :lz σ k →ₐ[k] k) := by
  ext p
  rw [zS ,v9]
 rw [hker]
 have hs :t8 (oy x :lz σ k →ₐ[k] k) :=
  fun b=>⟨C b,by simp⟩
 let e := Qw hs
 let:=Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
 rw [affineDegree_eq_finrank,e.toLinearEquiv.finrank_eq,Module.finrank_self,Nat.cast_one]
private theorem bK6 {k σ τ:Type} [lV k] [vj σ] [vj τ]
    (A:Set (σ→k)) (I:c9 (lz σ k)) (hI:I=uh k A)
    (hprime :I.IsPrime) (hdim: (p7 I).natDegree=1)
    (hone :1≤uJ I) (D:lz σ k) (N :τ→lz σ k)
    (hD:D.totalDegree≤1) (hN : ∀ i,(N i).totalDegree≤1)
    (hnonzero : ∀ x∈A,eval x D ≠0) :
    ∃ Q:c9 (lz τ k),Q.IsPrime∧(p7 Q).natDegree≤1 ∧
      uJ Q≤uJ I ∧
      ∀ x∈A,(fun i=>eval x (N i)/eval x D)∈qM k Q:= by
  have hA:A.Nonempty := by
    by_contra! h
    exact hprime.ne_top (by rw [hI,h,vanishingIdeal_empty])
  obtain ⟨x₀,hx₀⟩:=hA
  let e :lz σ k →ₐ[k] (A→k) :=Kz fun x=>oy x.val
  have he :I=oK e := by
    ext p
    rw [hI,Ok,zS ,_root_.funext_iff]
    exact ⟨fun h x=>h x.val x.property,fun h x hx=>h ⟨x,hx⟩⟩
  clear hI
  subst I
  let I:=oK e
  let:I.IsPrime :=hprime
  change (p7 I).natDegree=1 at hdim
  change 1≤uJ I at hone
  let R:=lz σ k ⧸ I
  let j:R →ₐ[k] (A→k) :=TZ e
  have hj:qG j:=zvo e
  let dr :R:=nI I D
  let d:A→k :=e D
  have hjd:j dr=d:=rfl
  have hd:qU d:=Pi.isUnit_iff.mpr fun x=>isUnit_iff_ne_zero.mpr (hnonzero _ x.property)
  let y (i:τ) (x :A) :k :=eval x.val (N i)/eval x.val D
  let φ:lz τ k →ₐ[k] (A→k) :=oy y
  let Q:=oK φ
  have hφ (p:lz τ k) (x :A) :
      φ p x=oy (fun i=>y i x) p:= by
    let π:=Pi.evalAlgHom k (fun _:A=>k) x
    have h:π.comp φ=oy (fun i=>y i x) := by
      apply Dv
      intro i
      simp [φ,π]
    exact Nr h p
  have hy (i:τ) :d*y i=e (N i) := by
    ext x
    change eval x.val D *(eval x.val (N i)/eval x.val D)=eval x.val (N i)
    rw [uz ,TH _ (hnonzero _ x.property)]
  let V (m:ℕ) :zd k (A→k) :=(zf I m).map j.toLinearMap
  let W (m:ℕ) :zd k (A→k) :=(V m).comap (XB k (d^m))
  have hW (m:ℕ) (z :A→k) :
      z∈W m ↔ ∃ r∈zf I m,j r=d^m*z := by
    simp only [W,V,Submodule.mem_comap,Submodule.mem_map,LinearMap.mulLeft_apply,
      FV]
    rfl
  have hdr_pow (n:ℕ) :dr^n∈zf I n:= by
    dsimp only [dr]
    rw [← t7]
    exact mk_mem_quotientDegreeLE ((totalDegree_pow _ _).trans (by simpa using Kc n hD))
  have hmono:Monotone W:= by
    intro m n hmn z hz
    obtain ⟨r,hr,heq⟩:=(hW _ _).mp hz
    refine (hW _ _).mpr ⟨dr^(n - m)*r,?_,?_⟩
    · simpa only [z8 hmn] using
        mul_mem_quotientDegreeLE (hdr_pow (n - m)) hr
    · rw [lJ,t7,hjd,heq,← qy ,← pow_add,z8 hmn]
  have hmul (i:τ) (m:ℕ) (z :A→k) (hz :z∈W m) :
      y i*z∈W (m+1) := by
    obtain ⟨r,hr,heq⟩:=(hW _ _).mp hz
    refine (hW _ _).mpr ⟨r* nI I (N i),
      mul_mem_quotientDegreeLE hr (mk_mem_quotientDegreeLE (hN i)),?_⟩
    rw [lJ,heq,Kv,GB,← hy]
    ring
  have hclear (p:lz τ k) (m:ℕ) (hp:p.totalDegree≤ m) :
      ∃ r∈zf I m,j r=d^m*φ p:= by
    have hz : (1 :A→k)∈W 0 :=
      (hW _ _).mpr ⟨1,one_mem_quotientDegreeLE I _,by simp⟩
    have h:=aeval_mem_of_forall_mul_mem y hmono hz hmul hp
    rw [t6] at h
    exact (hW _ _).mp h
  have hQ:Q.IsPrime := by
    apply Ideal.isPrime_iff.mpr
    constructor
    · intro htop
      have hz :φ 1=0:=RingHom.mem_ker.mp (show 1∈Q from htop ▸ PA)
      rw [vk] at hz
      exact one_ne_zero (wR hz ⟨x₀,hx₀⟩)
    · intro p q hpq
      have hz :=RingHom.mem_ker.mp hpq
      change φ (p*q)=0 at hz
      rw [lJ] at hz
      obtain ⟨r,_,hr⟩:=hclear p _ t9
      obtain ⟨s,_,hs⟩:=hclear q _ t9
      have hrs :r*s=0:=hj (by
        rw [lJ,hr,hs,oq]
        calc
          _=(d^p.totalDegree*d^q.totalDegree)*(φ p*φ q) := by ring
          _=0:= by rw [hz,p9])
      rcases mul_eq_zero.mp hrs with hr₀ | hs₀
      · left
        apply RingHom.mem_ker.mpr
        exact (hd.pow _).mul_left_cancel (by rw [← hr,hr₀,oq,p9])
      · right
        apply RingHom.mem_ker.mpr
        exact (hd.pow _).mul_left_cancel (by rw [← hs,hs₀,oq,p9])
  have hgrowth (m:ℕ) :affineHilbertFunction Q m≤affineHilbertFunction I m:= by
    let ι:=TZ φ
    have hm (a :zf Q m) :d^m*ι a.1∈V m:= by
      obtain ⟨p,hp,hp'⟩:=mem_quotientDegreeLE.mp a.2
      obtain ⟨r,hr,heq⟩:=hclear p m hp
      refine Submodule.mem_map.mpr ⟨r,hr,?_⟩
      rw [FV,← hp',Kv,heq]
    let l:zf Q m →ₗ[k] V m :=
      (((XB k (d^m)).comp ι.toLinearMap).domRestrict
        (zf Q m)).codRestrict (V m) hm
    have hl:qG l:= by
      intro a b hab
      have h:d^m*ι a.1=d^m*ι b.1 :=oj XG hab
      exact vG (zvo φ ((hd.pow _).mul_left_cancel h))
    exact (LinearMap.finrank_le_finrank_of_injective hl).trans (Submodule.finrank_map_le _ _)
  have hle : ∀ᶠ m:ℕ in Filter.atTop,
      (p7 Q).eval (m:ℚ)≤(p7 I).eval (m:ℚ) := by
    filter_upwards [zaL Q,
      zaL I] with m hq hi
    rw [hq,hi]
    exact_mod_cast hgrowth m
  obtain ⟨hdegree,hcoeff⟩:=Polynomial.natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg Q) hle
  have hcover (x :A) : (fun i=>y i x)∈qM k Q:= by
    intro p hp
    rw [← hφ p x,RingHom.mem_ker.mp hp]
    rfl
  refine ⟨Q,hQ,hdegree.trans_eq hdim,?_,fun x hx=>hcover ⟨x,hx⟩⟩
  by_cases heq : (p7 Q).natDegree=(p7 I).natDegree
  · rw [uJ,uJ,heq]
    exact qz (hcoeff heq) (NW _)
  · have hzero : (affineHilbertPolynomial Q).natDegree=0:= by omega
    let:=hQ
    let:=natDegree_affineHilbertPolynomial_eq_zero_iff.mp hzero
    have hmax :=Ideal.Quotient.maximal_of_isField Q (IsField.of_isDomain_of_finite k _)
    have hpoint :Q≤uh  k {(fun i=>y i ⟨x₀,hx₀⟩)} := by
      intro p hp
      exact (v9  _ _).mpr (hcover ⟨x₀,hx₀⟩ p hp)
    have hprime' : (uh  k {(fun i=>y i ⟨x₀,hx₀⟩)}).IsPrime :=xu
    rw [hmax.eq_of_le hprime'.ne_top hpoint,dsq]
    exact hone
private theorem bmt {B:eT 4} {s t:pC} {h k :ℕ}
  (hb:s.b≤t.b) (hj:s.j≤t.j) (ht:s.t≤t.t) (hh:h≤k)
  (hB:DO B s h) :DO B t k := by
 intro a ha
 obtain ⟨hb',hj',ht',hh'⟩:=hB a ha
 exact ⟨hb'.trans hb,hj'.trans hj,ht'.trans ht,hh'.trans hh⟩
end
end yz
end
section
namespace yz
noncomputable section
open aR oR we MvPolynomial
open scoped BigOperators
private theorem cXL {f :af 3} (hf :f≠0) :
  vY (fW f)≠0:= by
 have hg:fW f≠0:= by
  simpa only [fW,oq] using (RC _ Yk).ne hf
 simpa only [vY,oq] using
  (rename_injective pU (xI 3)).ne hg
end
end yz
end
section
namespace zP
noncomputable section
open aR oR we yz MvPolynomial Filter MeasureTheory
open scoped BigOperators Pointwise Topology
def c1 :Prop :=
  ∀ (A:Fin 4→aU Exponent),
    (∀ i,0∈A i)→qm (fZ A) (HG A) →
    ∀ (f :Fin 4→eT 4),(∀ i,(f i).support⊆A i) →
    ∀ points :aU oe,
      (∀ y∈points,oF y∈(ke f).minimalPrimes) →
      (∑ y∈points,(Ny (ke f) y).toNat) ≤
        pz (fZ A) (HG A)
def c2 :Prop :=
  ∀ (A:Fin 4→aU Exponent),(∀ i,0∈A i) →
    (∀ j:Fin 4,∃ i,t3 j 1∈A i) →
    qm (fZ A) (HG A) ∧
      ∃ q:ℕ,∀ n:ℕ,
        (pz (fZ A) (HG A) :ℝ)*(n:ℝ)^4 =
          ∑ S∈(th :aU (Fin 4)).powerset,
            (-1 :ℝ)^(4 - S.card)*(TX A (corner q n S) :ℝ)
def c3:Prop :=
  ∀ (A:Fin 4→aU Exponent),(∀ i,0∈A i)→(∀ i,a9X (A i)) →
    ∀ (q:ℕ) (S:aU (Fin 4)),
      Tendsto (fun n:ℕ=>(TX A (corner q n S) :ℝ)/(n:ℝ)^4)
        atTop (𝓝 (volume (∑ i∈S,LK (A i))).toReal)
private theorem c0v (h2 :c2) (h3:c3)
    (A:Fin 4→aU Exponent) (hzero : ∀ i,0∈A i)
    (hdown : ∀ i,a9X (A i))
    (hcoords : ∀ j:Fin 4,∃ i,t3 j 1∈A i) :
    qm (fZ A) (HG A) ∧
      (pz (fZ A) (HG A) :ℝ) =
        aa1 (fun i=>LK (A i)) := by
  obtain ⟨hfinite,q,hq⟩:=h2 A hzero hcoords
  refine ⟨hfinite,?_⟩
  unfold aa1
  apply tendsto_nhds_unique (l:=(atTop:Filter ℕ))
    (f := fun n:ℕ => ∑ S∈(th :aU (Fin 4)).powerset,
      (-1 :ℝ)^(4 - S.card)*((TX A (corner q n S) :ℝ)/(n:ℝ)^4))
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 :ℕ)] with n hn
    have hn' : (n:ℝ)^4≠0:=Du _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
    symm
    calc
      _=(∑ S∈(th :aU (Fin 4)).powerset,
          (-1 :ℝ)^(4 - S.card)*(TX A (corner q n S) :ℝ))/(n:ℝ)^4 := by
        simp only [Finset.sum_div,mul_div_assoc]
      _ = _:= by rw [← hq n,mul_div_cancel_right₀ _ hn']
  · exact tendsto_finsetSum _ fun S _=>(h3 A hzero hdown q S).const_mul _
private theorem cK8 (F:eT 4) :a9X (a3z F) := by
 intro a b ha hab
 obtain ⟨e,he,hae⟩:=a5J.mp ha
 exact a5J.mpr ⟨e,he,hab.trans hae⟩
private theorem bCe (s :pC) (h:ℕ) :a9X (auv s h) := by
 intro a b ha hb
 have ha' := aIA.mp ha
 obtain ⟨hb₁,hb₂,hb₃,hb₄⟩:=ha'
 apply aIA.mpr
 exact ⟨(Aa (Aa (hb 0) (hb 1)) (hb 2)).trans hb₁,
  (Aa (hb 1) (Kc 2 (hb 2))).trans hb₂,
  (hb 2).trans hb₃,(hb 3).trans hb₄⟩
private theorem bQd (s :pC) (h:ℕ) : (0:Exponent)∈auv s h :=
 aIA.mpr (by simp [aCt])
end
end zP
end
section
namespace aaq
noncomputable section
open zP MvPolynomial
open scoped Pointwise
abbrev Degree :=Fin 4→ℕ
abbrev af (A:Fin 4→aU Exponent) :=lz (Fin 4) (fZ A)
def Bc (A:Fin 4→aU Exponent) (d:Degree) :Set Exponent :=
 ∑ i:Fin 4,d i•(↑(A i) :Set Exponent)
def dO (A:Fin 4→aU Exponent) (d:Degree) :zd (fZ A) (af A) :=
  Re (fZ A)
    (qJ fun a : ↥(Bc A d)=>ov a.1 (1 :fZ A))
def shift (d:Degree) (i:Fin 4) (n:ℕ) :Degree :=d+Pi.single i n
def mo (A:Fin 4→aU Exponent) (k :ℕ) :c9 (af A) :=
 n5 (ve A '' {i:Fin 4 | (i:ℕ)<k})
end
end aaq
end
section
namespace aaq
noncomputable section
open zP MvPolynomial
open scoped Pointwise
variable {A:Fin 4→aU Exponent}
private theorem bqc (s :Set Exponent) (hs :s.Finite) (n:ℕ) : (n•s).Finite := by
 induction n with
 | zero=>simpa only [zero_nsmul] using (Set.finite_zero : (0:Set Exponent).Finite)
 | succ n ih=>rw [succ_nsmul]; exact ih.add hs
private theorem cNL (A:Fin 4→aU Exponent) (d:Degree) :
  (Bc A d).Finite := by
 classical
 unfold Bc
 have h (s :aU (Fin 4)) : (∑ i∈s,d i•(↑(A i) :Set Exponent)).Finite := by
  induction s using Cy with
  | empty=>simp
  | @insert i s nhi ih =>
    rw [yo nhi]
    exact (bqc _ (A i).finite_toSet _).add ih
 exact h _
instance (d:Degree) :qm (fZ A) (dO A d) := by
 classical
 let _:=(cNL A d).fintype
 exact Module.Finite.span_of_finite _ (Set.finite_range _)
private theorem b9q {d:Degree} {a :Exponent} (ha :a∈Bc A d)
  (c:fZ A) :ov a c∈dO A d:= by
 have h:ov a (1 :fZ A)∈dO A d :=
  Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩
 simpa only [smul_monomial,G9,Dw] using (dO A d).smul_mem c h
private theorem aC6 (A:Fin 4→aU Exponent) (d e :Degree) :
  Bc A (d+e)=Bc A d+Bc A e := by
 simp only [Bc,Av,add_nsmul,zm]
private theorem aUt (A:Fin 4→aU Exponent) (i:Fin 4) :
   Bc A (vZ i 1)=A i:= by
 classical
 unfold Bc
 rw [G3 i]
 · simp
 · intro j _ hj
   rw [C5 hj,zero_nsmul]
 · simp
theorem bFi (i:Fin 4) {d:Degree} {p:af A}
   (hp:p∈dO A d) :ve A i*p∈dO A (shift d i 1) := by
 change p∈Re _ _ at hp
 induction hp using Submodule.span_induction with
 | mem p hp =>
   obtain ⟨a,rfl⟩:=hp
   rw [ve,Nq]
   refine Wl _ fun b _ => ?_
   rw [Kp]
   apply b9q
   rw [shift,aC6,aUt]
   exact Set.mem_add.mpr ⟨a,a.2,b,b.2,LR _ _⟩
 | zero=>simp
 | add p r _ _ hp hr=>simpa only [mul_add] using (dO A _).add_mem hp hr
 | smul c p _ hp=>simpa only [mul_smul_comm] using (dO A _).smul_mem c hp
private theorem cw5 (hz : ∀ i,0∈A i) (d:Degree) :
  (0:Exponent)∈Bc A d:= by
 classical
 have hn (i:Fin 4) (n:ℕ) : (0:Exponent)∈n•(↑(A i) :Set Exponent) := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [succ_nsmul]; exact Set.mem_add.mpr ⟨0,ih,0,hz i,zero_add _⟩
 have h (s :aU (Fin 4)) : (0:Exponent) ∈ ∑ i∈s,d i•(↑(A i) :Set Exponent) := by
  induction s using Cy with
  | empty=>simp
  | @insert i s nhi ih =>
    rw [yo nhi]
    exact Set.mem_add.mpr ⟨0,hn i _,0,ih,wB _⟩
 exact h _
private theorem b2s (hz : ∀ i,0∈A i) {d e :Degree} (h:d≤e) :
  Bc A d⊆Bc A e := by
 have he :e=d+(e - d) := by
  funext i
  exact (Nat.add_sub_of_le (h i)).symm
 intro a ha
 rw [he,aC6]
 exact Set.mem_add.mpr ⟨a,ha,0,cw5 hz _,add_zero _⟩
theorem a6w (hz : ∀ i,0∈A i) {d e :Degree} (h:d≤e) :dO A d≤dO A e := by
 apply Submodule.span_le.mpr
 rintro _ ⟨a,rfl⟩
 exact b9q (b2s hz h a.2) _
private theorem eDV
  (hz : ∀ i,0∈A i) (hv : ∀ j:Fin 4,∃ i,t3 j 1∈A i)
  (a :Exponent) : ∃ n:ℕ,a∈Bc A (fun _=>n) := by
 classical
 have hadd {a b:Exponent} {m n:ℕ} (ha :a∈Bc A (fun _=>m))
    (hb:b∈Bc A (fun _=>n)) :a+b∈Bc A (fun _=>m+n) := by
  change _∈Bc A ((fun _=>m)+(fun _=>n))
  rw [aC6]
  exact Set.mem_add.mpr ⟨a,ha,b,hb,rfl⟩
 have hvar (j:Fin 4) :t3 j 1∈Bc A (fun _=>1) := by
  obtain ⟨i,hi⟩:=hv j
  exact b2s hz (show vZ i 1≤fun _=>1 by
    intro l; by_cases h:l=i <;> simp [h,C5])
    (by rw [aUt]; exact Finset.mem_coe.mpr hi)
 have hsingle (j:Fin 4) (m:ℕ) :t3 j m∈Bc A (fun _=>m) := by
  induction m with
  | zero=>simpa using cw5 hz (fun _=>0)
  | succ m ih =>
    rw [Finsupp.single_add]
    exact hadd ih (hvar j)
 have hsum (s :aU (Fin 4)) :
    (∑ j∈s,t3 j (a j))∈Bc A (fun _ => ∑ j∈s,a j) := by
  induction s using Cy with
  | empty=>simpa only [Finset.sum_empty] using cw5 hz (fun _=>0)
  | @insert j s hj ih =>
    rw [yo hj,yo hj]
    exact hadd (hsingle j _) ih
 refine ⟨∑ j:Fin 4,a j,?_⟩
 have ha : (∑ j:Fin 4,t3 j (a j))=a := by
  ext j
  simp
 simpa only [ha] using hsum th
theorem btB (hz : ∀ i,0∈A i)
   (hv : ∀ j:Fin 4,∃ i,t3 j 1∈A i) (p:af A) :
   ∃ n:ℕ,p∈dO A (fun _=>n) := by
 classical
 choose n hn using eDV hz hv
 refine ⟨p.support.sup n,?_⟩
 have hsum: (∑ a∈p.support,ov a (p.coeff a))∈dO A (fun _=>p.support.sup n) := by
   refine Wl _ fun a ha=>b9q ?_ _
   exact b2s hz (show (fun _=>n a)≤(fun _=>p.support.sup n:Degree) from
     fun _=>zk ha) (hn a)
 rwa [← p.as_sum] at hsum
theorem b3c (A:Fin 4→aU Exponent) (d:Degree) :
   pz (fZ A) (dO A d)=TX A d:= by
 classical
 let _:=(cNL A d).fintype
 let m : ↥(Bc A d)→af A:= fun a=>ov a.1 1
 have h:X8 (fZ A) m :=
   (FU (Fin 4) (fZ A)).linearIndependent.comp
     (fun a : ↥(Bc A d)=>a.1) Subtype.val_injective
 change pz (fZ A) (Re _ (qJ m))=(Bc A d).ncard
 exact (finrank_span_eq_card h).trans (Set.fintypeCard_eq_ncard _)
end
end aaq
end
section
namespace aaq
noncomputable section
private def apt (d:Degree) (n:ℕ) (S:aU (Fin 4)) :Degree :=
 fun i=>d i+if i∈S then n else 0
private def aGQ (F:Degree→ℝ) (J:aU (Fin 4)) (d:Degree) (n:ℕ) :ℝ :=
 ∑ S∈J.powerset,(-1 :ℝ)^(J.card - S.card)*F (apt d n S)
private theorem cpp (d:Degree) (i:Fin 4) (t:ℕ) :d≤ shift d i t :=
 fun _=>JW _ _
private theorem gqa (d:Degree) (n:ℕ) (S:aU (Fin 4)) :d≤apt d n S :=
 fun _=>JW _ _
private theorem aQg (d:Degree) (i:Fin 4) (t:ℕ) :
  shift d i (t+1)=shift (shift d i t) i 1 := by
 funext j
 by_cases h:j=i <;> simp [shift,h,C5 ,add_assoc]
private theorem gp9 {i:Fin 4} {S:aU (Fin 4)} (hi:i∉S)
  (d:Degree) (n:ℕ) :apt d n (sS i S)=shift (apt d n S) i n:= by
 funext j
 by_cases h:j=i <;> simp [shift,apt,hi,h,C5]
private theorem ddS (d:Degree) (i:Fin 4) (t n:ℕ) (S:aU (Fin 4)) :
  shift (apt d n S) i t=apt (shift d i t) n S:= by
 funext j
 simp only [shift,apt,Av]
 ac_rfl
private theorem b7R {F G:Degree→ℝ} {q:ℕ} {i:Fin 4}
   (h : ∀ d:Degree,(∀ j,q≤d j)→F (shift d i 1)-F d=G d)
   (d:Degree) (hd : ∀ j,q≤d j) (n:ℕ) :
   F (shift d i n)-F d = ∑ t∈Pc n,G (shift d i t) := by
 induction n with
 | zero=>simp [shift]
 | succ n ih =>
   rw [Finset.sum_range_succ,← ih,aQg,
     ← h (shift d i n) (fun j=>(hd j).trans (cpp d i n j))]
   ring
private theorem dAf {F G:Degree→ℝ} {q:ℕ} {i:Fin 4} {J:aU (Fin 4)}
    (hi:i∉J) (h : ∀ d:Degree,(∀ j,q≤d j)→F (shift d i 1)-F d=G d)
    (d:Degree) (hd : ∀ j,q≤d j) (n:ℕ) :
    aGQ F (sS i J) d n = ∑ t∈Pc n,aGQ G J (shift d i t) n:= by
  unfold aGQ
  rw [EK hi,← zm,Finset.sum_comm]
  apply sH rfl
  intro S hS
  have hsub:=Finset.mem_powerset.mp hS
  have hiS:i∉S:= fun hh=>hi (hsub hh)
  have hcard:=Finset.card_le_card hsub
  rw [ Xo hi,Xo hiS,
    Nat.add_sub_add_right,show J.card+1 - S.card=(J.card - S.card)+1 by omega,
    GB,gp9 hiS]
  have hs : (-1 :ℝ)^(J.card - S.card)*(-1)*F (apt d n S) +
      (-1 :ℝ)^(J.card - S.card)*F (shift (apt d n S) i n) =
      (-1 :ℝ)^(J.card - S.card) *
        (F (shift (apt d n S) i n)-F (apt d n S)) := by ring
  rw [hs,b7R h _ (fun j=>(hd j).trans (gqa d n S j)),Iw]
  simp only [ddS]
theorem b3Q (H :ℕ→Degree→ℝ) (C:ℝ) (q:ℕ)
    (hstep : ∀ (i:Fin 4) (d:Degree),(∀ j,q≤d j) →
      H i.val (shift d i 1) - H i.val d=H (i.val+1) (shift d i 1))
    (htop : ∀ d:Degree,(∀ j,q≤d j)→H 4 d=C) (n:ℕ) :
    (∑ S∈(th :aU (Fin 4)).powerset,
      (-1 :ℝ)^(4 - S.card)*H 0 (zP.corner q n S))=C*(n:ℝ)^4 := by
  let tail (k :ℕ) :aU (Fin 4) :=Finset.univ.filter fun i=>k≤ i.val
  have htail (i:Fin 4) :tail i.val=sS i (tail (i.val+1)) := by
    ext j
    simp only [tail,Finset.mem_filter,vi ,true_and,Y4]
    constructor
    · intro h
      by_cases he :j=i
      · exact Or.inl he
      · exact Or.inr (by have hne :=Fin.val_ne_of_ne he; omega)
    · rintro (rfl | h)
      · exact t9
      · omega
  have hnot (i:Fin 4) :i∉tail (i.val+1) := by simp [tail]
  have ht4 :tail 4 = ∅ := by ext i; simp [tail,not_le.mpr i.isLt]
  have ht0:tail 0=Finset.univ := by simp [tail]
  have hbox (k :ℕ) (hk :k≤4) : ∀ d:Degree,(∀ j,q≤d j) →
      aGQ (H k) (tail k) d n=C*(n:ℝ)^(4 - k) := by
    refine Nat.decreasingInduction' (m:=k) (n:=4)
      (P:= fun l => ∀ d:Degree,(∀ j,q≤d j) →
        aGQ (H l) (tail l) d n=C*(n:ℝ)^(4-l)) ?_ hk ?_
    · intro l hl _ ih d hd
      let i:Fin 4 :=⟨l,hl⟩
      have hi:tail l=sS i (tail (l+1)) :=htail i
      rw [hi,dAf (hnot i) (hstep i) d hd]
      have he (t:ℕ) :aGQ (fun e=>H (l+1) (shift e i 1))
          (tail (l+1)) (shift d i t) n=C*(n:ℝ)^(4-(l+1)) := by
        unfold aGQ
        simpa only [aGQ,ddS] using
          ih (shift (shift d i t) i 1) (fun j =>
            ((hd j).trans (cpp d i t j)).trans (cpp (shift d i t) i 1 j))
      calc
        _ = ∑ _t∈Pc n,C*(n:ℝ)^(4-(l+1)) :=
          sH rfl fun t _=>he t
        _ = _:= by
          simp only [Finset.sum_const,Finset.card_range,Mj]
          rw [show 4-l=(4-(l+1))+1 by omega,GB]
          ring
    · intro d hd
      have he :apt d n ∅ = d:= by funext j; simp [apt]
      simpa [aGQ,ht4,he] using htop d hd
  have h:=hbox 0 (by decide) (fun _=>q) (fun _=>t9)
  have hc (S:aU (Fin 4)) :apt (fun _=>q) n S=zP.corner q n S:=rfl
  simpa [aGQ,ht0,hc] using h
end
end aaq
end
section
namespace aeC
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
def aqG (f :af 3) (P:c9 (eT 3)) :Prop :=
 ∀ b:af 3,fW b∈P→fW (Ev f b)∈P
def Bt (y :Fin 3→cH) :af 3 →+* cH :=
 (nX y).comp (ox qY)
def centre {F:Type*} [lV F] (e :af 3 →+* F) :F :=
 e (pQ pL)
def afk {F:Type*} [lV F] (f :af 3) (e :af 3 →+* F) :ℕ→F
 | 0=>e (MvPolynomial.X 0)
 | 1=>e (MvPolynomial.X 1)
 | 2=>e (MvPolynomial.X 2)
 | k+3=>2*e (AR f k) /
     (((k+3).factorial:F)*e (separant f)^(2*k+1))
def aac {F:Type*} [lV F] (f :af 3) (e :af 3 →+* F) :F[X] :=
  xL (-centre e)
    (∑ j:Fin bf,vl j.val (afk f e j.val))
def aWP (f :af 3) (y :Fin 3→cH) :GD :=
 fun j=>(aac f (Bt y)).coeff j.val
def bX0 (f :af 3) (P:c9 (eT 3)) :Set GD :=
 aWP f '' D7 f P
def aHk (f :af 3) (P:c9 (eT 3)) :Bk :=
 uh cH (bX0 f P)
def jW {A:Type*} [nq A] (k :ao →+* A) (f :af 3) (U:A[X]) :
    A[X] :=
  SD (MO k) (fun i=>p5 i.val U) f
end
end aeC
end
section
namespace aeC
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
theorem bCY (f :af 3) (y :Fin 3→cH) :
  JC (aWP f y)=aac f (Bt y) := by
 let U:=aac f (Bt y)
 have hdeg:U.natDegree≤bf - 1 := by
  dsimp [U,aac]
  rw [SC]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt i.isLt)
 change (∑ j:Fin bf,vl j.val (U.coeff j.val))=U
 rw [Up (fun j=>vl j (U.coeff j))]
 exact (Vs U bf (PD hdeg)).symm
private theorem gAP {A:Type*} [nq A] {L:ℕ}
   (x :A) (a :ℕ→A) (j:Fin L) :
   (p5 j.val (xL (-x)
     (∑ l:Fin L,vl l.val (a l.val)))).eval x=a j.val := by
 rw [← SW,Yi ,OJ,
   z9k,Polynomial.finsetSum_coeff]
 simp only [Polynomial.coeff_monomial,Fin.val_inj,G0 ,vi ,
   ite_true]
private theorem dGG (f :af 3) (e :af 3 →+* cH) (i:Fin 3) :
  afk f e i.val=e (lI i) := by
 fin_cases i <;> rfl
private theorem gBq:3<bf := by
 change 3<133672
 omega
theorem c7C (f :af 3) (y :Fin 3→cH) (i:Fin 3) :
   (p5 i.val (aac f (Bt y))).eval (qY pL) =
     y i:= by
 have hx :centre (Bt y)=qY Polynomial.X:= by
   simp [centre,Bt]
 let j:Fin bf :=⟨i.val,i.isLt.trans gBq⟩
 calc
   _=(p5 j.val (aac f (Bt y))).eval (centre (Bt y)) :=
     oj (fun x=>(p5 i.val (aac f (Bt y))).eval x) hx.symm
   _=afk f (Bt y) j.val :=
     gAP (centre (Bt y)) (afk f (Bt y)) j
   _=Bt y (lI i) :=dGG f (Bt y) i
   _=y i:= by simp [Bt]
theorem cML :
   (y5 (qY pL)).comp
     (MO (cy ao cH))=qY:= by
 apply Pv
 · intro a
   change ((oY a).map (cy ao cH)).eval
     (qY pL)=qY (oY a)
   rw [Polynomial.map_C,FR,← Polynomial.algebraMap_eq]
   rfl
 · simp
theorem cNc (f b:af 3) (y :Fin 3→cH) :
   (Of b (aac f (Bt y))).eval (qY pL) =
     nX y (fW b) := by
 unfold Of fW
 rw [NI,NI]
 change (y5 (qY pL)) (SD _ _ _)= _
 rw [zUe,cML]
 simp only [Polynomial.coe_evalRingHom,c7C]
theorem cb0 (f :af 3) (P:c9 (eT 3)) {y :Fin 3→cH}
  (hy :y∈D7 f P) :
  aWP f y∈qM cH (aHk f P) :=
 MvPolynomial.zeroLocus_vanishingIdeal_le (bX0 f P) ⟨y,hy,rfl⟩
theorem c7O (f :af 3) (P:c9 (eT 3)) (hp:P.IsPrime)
  (hsep:fW (separant f)∉P) : (D7 f P).Nonempty := by
 classical
 let _:=hp
 by_contra hn
 apply hsep
 rw [← QL (K:=cH) P]
 intro y hy
 change nX y (fW (separant f))=0
 by_contra he
 exact hn ⟨y,hy,he⟩
private def aQ2 (f :af 3) : (eT bf)[X] :=
 jW ((pQ:cH →+* eT bf).comp
  (cy ao cH)) f
  (∑ j:Fin bf,vl j.val (lI j))
private theorem aVM {A B:Type*} [nq A] [nq B]
  (h:A →+* B) (k :ao →+* A) (f :af 3) (U:A[X]) :
  (jW k f U).map h=jW (h.comp k) f (U.map h) := by
 unfold jW
 change (MO h) (SD _ _ _)= _
 rw [zUe]
 simp only [Polynomial.coe_mapRingHom,NZ,Polynomial.mapRingHom_comp]
private theorem cNd (f :af 3) (a :GD) :
   (aQ2 f).map (nX a) =
     Of f (JC a) := by
 unfold aQ2
 rw [aVM]
 have hk : (nX a).comp ((pQ :
     cH →+* eT bf).comp (cy ao cH)) =
     algebraMap ao cH :=Ef fun z=> by simp
 rw [hk]
 simp only [zWf,zA0,xm]
 unfold jW Of JC
 rw [NI]
theorem deO (f :af 3) (P:c9 (eT 3))
  (h : ∀ y∈D7 f P,Of f (aac f (Bt y))=0)
  (a :GD) (ha :a∈qM cH (aHk f P)) :
  Of f (JC a)=0:= by
 rw [← cNd]
 ext m
 rw [Eg ,KH]
 apply ha
 intro z hz
 obtain ⟨y,hy,rfl⟩:=hz
 change nX (aWP f y) ((aQ2 f).coeff m)=0
 rw [← Eg ,cNd,bCY,
  h y hy,KH]
end
end aeC
end
section
namespace aaq
noncomputable section
open zP
def c1 :Prop :=
  ∀ (A:Fin 4→aU Exponent),(∀ i,0∈A i) →
    qm (fZ A) (HG A)
def c2 :Prop :=
  ∀ (A:Fin 4→aU Exponent),(∀ i,0∈A i) →
    ∀ (i:Fin 4) (p:af A),
      ve A i*p∈mo A i.val→p∈mo A i.val
def c3:Prop :=
  ∀ (A:Fin 4→aU Exponent),(∀ i,0∈A i) →
    (∀ j:Fin 4,∃ i,t3 j 1∈A i) →
    ∃ q:ℕ,∀ (i:Fin 4) (d:Degree),(∀ j,q≤d j) →
      ∀ p∈dO A (shift d i 1),p∈mo A (i.val+1) →
        ∃ r∈dO A d,p - ve A i*r∈mo A i.val
private def Jw (A:Fin 4→aU Exponent) (k :ℕ) :
  af A →ₐ[fZ A] af A ⧸ mo A k :=
 Ee (fZ A) (mo A k)
private def ZY (A:Fin 4→aU Exponent) (k :ℕ) (d:Degree) :
   zd (fZ A) (af A ⧸ mo A k) :=
 (dO A d).map (Jw A k).toLinearMap
private instance (A:Fin 4→aU Exponent) (k :ℕ) (d:Degree) :
  qm (fZ A) (ZY A k d) := by
 unfold ZY
 infer_instance
private def lO (A:Fin 4→aU Exponent) (k :ℕ) (d:Degree) :ℕ :=
 pz (fZ A) (ZY A k d)
variable {A:Fin 4→aU Exponent}
private theorem aCc (k :ℕ) (p:af A) :
 Jw A k p=0↔p∈mo A k :=Ye
private theorem bll (k :ℕ) (p r :af A) :
  Jw A k p=Jw A k r↔p - r∈mo A k := by
 rw [← aCc,qx ,Ar]
private theorem a6N {k l:ℕ} (h:k≤l) :mo A k≤ mo A l :=
 Pr (Set.image_mono fun _ hi=>lt_of_lt_of_le hi h)
private theorem b1K (i:Fin 4) :ve A i∈mo A (i.val+1) :=
 sI ⟨i,Nat.lt_succ_self _,rfl⟩
private theorem b50 (A:Fin 4→aU Exponent) (d:Degree) :
  lO A 0 d=TX A d:= by
 have hbot:mo A 0 = ⊥ := by simp [mo]
 let f :=((Jw A 0).toLinearMap.comp (dO A d).subtype)
 have hrange :LinearMap.range f=ZY A 0 d:= by
  simp [f,ZY,LinearMap.range_comp]
 have hinj:qG f := by
  intro p r hpr
  apply vG
  change Jw A 0 (p:af A)=Jw A 0 (r :af A) at hpr
  have hm:=(bll 0 (p:af A) (r :af A)).mp hpr
  rw [hbot,Ideal.mem_bot] at hm
  exact sub_eq_zero.mp hm
 unfold lO
 rw [← hrange,XJ hinj,b3c]
private theorem bt1 (A:Fin 4→aU Exponent) :
  mo A 4=n5 (qJ (ve A)) := by
 have h : {i:Fin 4 | (i:ℕ)<4} = Set.univ :=zps fun i=>i.isLt
 rw [mo,h,Set.image_univ]
private theorem b5Y (hz : ∀ i,0∈A i)
   (hv : ∀ j:Fin 4,∃ i,t3 j 1∈A i)
   (hf :qm (fZ A) (HG A)) :
   ∃ q:ℕ,∀ d:Degree,(∀ j,q≤d j) →
     lO A 4 d=pz (fZ A) (HG A) := by
 let hfin:qm (fZ A) (af A ⧸ mo A 4) := by
   rw [bt1]; exact hf
 let N :ℕ →o zd (fZ A) (af A ⧸ mo A 4) :=
   ⟨fun n=>ZY A 4 (fun _=>n),
     fun _ _ h=>zzl (a6w hz fun _=>h)⟩
 have hsup: (⨆ n,N n) = ⊤ := by
   apply top_unique
   intro x _
   obtain ⟨p,rfl⟩:=Ideal.Quotient.mkₐ_surjective (fZ A) (mo A 4) x
   obtain ⟨n,hn⟩:=btB hz hv p
   exact le_iSup N n (Submodule.mem_map_of_mem hn)
 obtain ⟨q,hq⟩:=hfin.fg_top.stabilizes_of_iSup_eq N hsup
 refine ⟨q,fun d hd => ?_⟩
 have hqd:ZY A 4 d = ⊤ := top_unique (by
   rw [hq]
   exact zzl (a6w hz hd))
 unfold lO
 rw [hqd,finrank_top,bt1]
private theorem cev (i:Fin 4) (d:Degree)
   (hinj : ∀ p:af A,ve A i*p∈mo A i.val→p∈mo A i.val)
   (hlift : ∀ p∈dO A (shift d i 1),p∈mo A (i.val+1) →
     ∃ r∈dO A d,p - ve A i*r∈mo A i.val) :
   lO A (i.val+1) (shift d i 1)+lO A i.val d=lO A i.val (shift d i 1) := by
 let f :=Ideal.Quotient.factorₐ (fZ A)
   (a6N (A:=A) (Nat.le_succ i.val))
 have hf (p:af A) :f (Jw A i.val p)=Jw A (i.val+1) p:=rfl
 let cut:ZY A i.val (shift d i 1) →ₗ[fZ A]
     ZY A (i.val+1) (shift d i 1) :=
   f.toLinearMap.restrict (by
     rintro _ ⟨p,hp,rfl⟩
     exact ⟨p,hp,(hf p).symm⟩)
 let mul :ZY A i.val d →ₗ[fZ A] ZY A i.val (shift d i 1) :=
   (XB (fZ A) (Jw A i.val (ve A i))).restrict (by
     rintro _ ⟨p,hp,rfl⟩
     exact ⟨_,bFi i hp,lJ (Jw A i.val) _ _⟩)
 have hsurj:t8 cut:= by
   intro y
   obtain ⟨p,hp,he⟩:=y.property
   exact ⟨⟨Jw A i.val p,⟨p,hp,rfl⟩⟩,vG ((hf p).trans he)⟩
 have hmul :qG mul := by
   apply (LinearMap.ker_eq_bot (f :=mul)).mp
   apply LinearMap.ker_eq_bot'.mpr
   intro x hx
   obtain ⟨p,_,hp⟩:=x.property
   change Jw A i.val p=(x :af A ⧸ mo A i.val) at hp
   have hz :Jw A i.val (ve A i*p)=0:= by
     rw [lJ]
     have h:=oj XG hx
     change Jw A i.val (ve A i)*(x :af A ⧸ mo A i.val)=0 at h
     rwa [hp]
   have hpI:=hinj p ((aCc _ _).mp hz)
   exact vG (hp.symm.trans ((aCc _ _).mpr hpI))
 have hk :LinearMap.range mul=LinearMap.ker cut:= by
   ext y
   constructor
   · rintro ⟨x,rfl⟩
     apply LinearMap.mem_ker.mpr
     apply vG
     change f (Jw A i.val (ve A i)*(x :af A ⧸ mo A i.val))=0
     rw [lJ,hf,(aCc _ _).mpr (b1K i),zero_mul]
   · intro hy
     obtain ⟨p,hp,he⟩:=y.property
     change Jw A i.val p=(y :af A ⧸ mo A i.val) at he
     have hz :=oj XG (LinearMap.mem_ker.mp hy)
     change f (y :af A ⧸ mo A i.val)=0 at hz
     rw [← he,hf] at hz
     obtain ⟨r,hr,hrel⟩:=hlift p hp ((aCc _ _).mp hz)
     refine ⟨⟨Jw A i.val r,⟨r,hr,rfl⟩⟩,vG ?_⟩
     change Jw A i.val (ve A i)*Jw A i.val r=(y :af A ⧸ mo A i.val)
     rw [← he,← lJ]
     exact ((bll _ _ _).mpr hrel).symm
 have hdim:=LinearMap.finrank_range_add_finrank_ker cut
 rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,← hk,
   XJ hmul] at hdim
 exact hdim
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :zP.c2 := by
 intro A hz hv
 have hfinite :=h1 A hz
 obtain ⟨q1,hq1⟩:=h3 A hz hv
 obtain ⟨q2,hq2⟩:=b5Y hz hv hfinite
 refine ⟨hfinite,max q1 q2,fun n => ?_⟩
 let H (k :ℕ) (d:Degree) :ℝ:=lO A k d
 have hstep (i:Fin 4) (d:Degree) (hd : ∀ j,max q1 q2≤d j) :
     H i.val (shift d i 1) - H i.val d=H (i.val+1) (shift d i 1) := by
   have hnat :=cev i d (h2 A hz i) (hq1 i d fun j=>(le_max_left _ _).trans (hd j))
   dsimp only [H]
   rw [sub_eq_iff_eq_add]
   exact_mod_cast hnat.symm
 have htop (d:Degree) (hd : ∀ j,max q1 q2≤d j) :
     H 4 d=(pz (fZ A) (HG A) :ℝ) := by
   dsimp only [H]
   rw [hq2 d fun j=>(le_max_right _ _).trans (hd j)]
 simpa only [H,b50] using (b3Q H _ _ hstep htop n).symm
end
end aaq
end
section
namespace aA2
noncomputable section
open aR oR we
abbrev TC {R:Type*} [nq R] (I:c9 R) (s :R) :=
 LQ (nI I s)
def ad2 {R:Type*} [nq R] (I:c9 R) (s :R) :R →+* TC I s :=
 (cy (R ⧸ I) (TC I s)).comp (nI I)
abbrev sep (f :af 3) :eT 3:=fW (separant f)
abbrev S7 (f :af 3) :eT 4 :=vY (sep f)
def Wy (f :af 3) (T:Gf f) :c9 (eT 4) :=
 rP f ⊔ n5 {T.cut}
abbrev aeI (f :af 3) :=TC (BW f) (sep f)
abbrev aYQ (f :af 3) (T:Gf f) :=TC (Wy f T) (S7 f)
abbrev Nt (f :af 3) :=ad2 (BW f) (sep f)
abbrev zp (f :af 3) (T:Gf f) :=ad2 (Wy f T) (S7 f)
end
end aA2
end
section
namespace aeC
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
@[simp] private theorem alJ (P:af 3) (m:Fin 3 →₀ ℕ) :
    (DU P).coeff m=mD (P.coeff m) := by
  classical
  rw [DU,NX]
  simp only [IT,G0]
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,oq]
private theorem a2C (p:ao[X]) :
  DU (pQ p:af 3)=pQ (mD p) := by
 classical
 apply Kl
 intro m
 rw [alJ]
 by_cases hm:0=m <;> simp [zG0,hm]
private theorem a2D (P Q:af 3) :
  DU (P+Q)=DU P+DU Q:= by
 ext m
 simp
private theorem bnc (P:af 3) (j:Fin 3) :
  DU (P*lI j)=DU P*lI j:= by
 classical
 ext m
 rw [alJ,X4 ,X4]
 split_ifs <;> simp
private theorem aNu (P:af 3) (a :Fin 3→ao[X]) :
    mD (nX a P)=nX a (DU P) +
      ∑ i,mD (a i)*nX a (oZ i P) := by
  classical
  induction P using JM with
  | C c=>simp [a2C]
  | add P Q hP hQ =>
    simp only [pG,a2D,hP,hQ,GF,zm]
    ring
  | mul_X P j ih =>
    rw [lJ,xm,Fz ,ih,bnc,
      lJ,xm]
    simp only [Qy ,pG,lJ,xm,
      GF,zm]
    have left: (∑ i,mD (a i) *
          (nX a (oZ i P)*a j)) =
        (∑ i,mD (a i)*nX a (oZ i P))*a j:= by
      simp only [Nq,qy]
    have right: (∑ i,mD (a i) *
          (nX a P*nX a (oZ i (lI j)))) =
        mD (a j)*nX a P:= by
      simp [MvPolynomial.pderiv_X,RP ,mul_ite]
    rw [left,right]
    ring
private theorem bo0 (S:ao[X]) :
  mD (p5 1 S)=2*p5 2 S:= by
 have h:=Zg (hasseDeriv_comp (R:=ao) 1 1) S
 simpa [hasseDeriv_one',zk4,Mj] using h
private theorem a3I (P:af 3) (S:ao[X]) :
   mD (cK P S)=cK (D3 P) S +
     mD (jet S (2 :Fin 3))*cK (separant P) S:= by
 unfold cK D3 separant
 rw [aNu,Kh]
 simp only [pG,lJ,uW,xm]
 have h0:mD (jet S (0:Fin 3))=jet S (1 :Fin 3) := by
   simp [jet]
 have h1 :mD (jet S (1 :Fin 3))=2*jet S (2 :Fin 3) :=
   bo0 S
 rw [h0,h1]
 ring
private theorem a3K (f P:af 3) (S:ao[X]) (hf :cK f S=0) :
   cK (Ev f P) S=cK (separant f) S*mD (cK P S) := by
 have hz :cK (D3 f) S +
     mD (jet S (2 :Fin 3))*cK (separant f) S=0:= by
   rw [← a3I,hf,oq]
 unfold Ev
 rw [a3I]
 change (nX (jet S)) (_-_)= _
 rw [qx ,lJ,lJ]
 change cK (separant f) S*cK (D3 P) S -
     cK (D3 f) S*cK (separant P) S= _
 linear_combination -cK (separant P) S*hz
private theorem anS (a :ℕ) (U V:ao[X]) :
   U*(U*mD (U^a*V))-(a :ao[X])*(U*mD U)*(U^a*V) =
     U^(a+2)*mD V:= by
 cases a with
 | zero=>simp [pow_two,mul_assoc]
 | succ a =>
   rw [Fz ,derivative_pow,Nat.succ_sub_one,
     pow_add U (a+1) 2,pow_succ' U a]
   simp only [Np]
   push_cast
   ring
theorem bFn (f :af 3) (S:ao[X]) (hf :cK f S=0) (k :ℕ) :
    cK (AR f k) S =
      cK (separant f) S^(2*k+1) *
        ((mD (R:=ao))^[k + 1]) (jet S (2 :Fin 3)) := by
  induction k with
  | zero =>
    have hz :cK (D3 f) S +
        mD (jet S (2 :Fin 3))*cK (separant f) S=0:= by
      rw [← a3I,hf,oq]
    change nX (jet S) (-D3 f) =
      cK (separant f) S^(2*0+1) *
        ((mD (R:=ao))^[0 + 1]) (jet S (2 :Fin 3))
    rw [Il]
    simp only [Nat.mul_zero,Nat.zero_add,pow_one,zS5]
    change -cK (D3 f) S= _
    linear_combination -hz
  | succ k ih =>
    let e :=nX (jet S:Fin 3→ao[X])
    change e (_-_)= _
    rw [qx ,lJ,lJ,lJ,zh]
    change cK (separant f) S*cK (Ev f (AR f k)) S -
      (↑(2*k+1) :ao[X])*cK (AR f k) S *
        cK (Ev f (separant f)) S= _
    rw [a3K _ _ _ hf,a3K _ _ _ hf,ih]
    rw [show 2*(k+1)+1=(2*k+1)+2 by omega,
      Rm  (mD  (R:=ao)) (k+1) (jet S (2 :Fin 3))]
    calc
      _=cK (separant f) S*(cK (separant f) S *
          mD (cK (separant f) S^(2*k+1) *
            ((mD (R:=ao))^[k + 1]) (jet S (2 :Fin 3)))) -
          (↑(2*k+1) :ao[X])*(cK (separant f) S*mD (cK (separant f) S)) *
            (cK (separant f) S^(2*k+1) *
              ((mD (R:=ao))^[k + 1]) (jet S (2 :Fin 3))) := by ring
      _ = _:=anS (2*k+1) (cK (separant f) S)
        (((mD (R:=ao))^[k + 1]) (jet S (2 :Fin 3)))
private theorem bPp (k :ℕ) (S:ao[X]) :
   2*((mD (R:=ao))^[k + 1]) (jet S (2 :Fin 3)) =
     ((mD (R:=ao))^[k+3]) S:= by
 have hsecond: ((mD (R:=ao))^[2]) S=2*jet S (2 :Fin 3) := by
   rw [Rm (mD (R:=ao)) 1 S,zS5]
   change mD (mD S)=2*p5 2 S
   simpa only [hasseDeriv_one'] using bo0 S
 rw [show k+3=(k+1)+2 by omega,
   Function.iterate_add_apply (mD  (R:=ao)) (k+1) 2 S,hsecond]
 simpa only [Nat.cast_ofNat] using
   (Polynomial.iterate_derivative_natCast_mul (n:=2) (k :=k+1)
     (f :=jet S (2 :Fin 3))).symm
private theorem factorial_ne_zero (j:ℕ) (hj:j<K1.p) :
  (j.factorial:cH)≠0:= by
 let g:K1.K →+* cH :=qY.comp (Polynomial.C.comp embed)
 intro hz
 have hK: (j.factorial:K1.K)=0 :=
  g.injective (by simpa only [zh,oq] using hz)
 have hp:=CharP.char_is_prime_of_two_le K1.K K1.p (by decide)
 exact (G4 hj) (hp.dvd_factorial.mp ((S1 K1.K K1.p _).mp hK))
private theorem dGH (f :af 3) (S:ao[X]) (hr :qg 2 f S)
   (j:ℕ) (hj:j<bf) :
   afk f (Bt (zq S)) j=qY (p5 j S) := by
 rcases j with _ | _ | _ | k
 · simp [afk,Bt,zq,jet]
 · simp [afk,Bt,zq,jet]
 · simp [afk,Bt,zq,jet]
 have he (b:af 3) :Bt (zq S) b=qY (cK b S) :=
   a3H b S
 have hsep:qY (cK (separant f) S)≠0 :=
   fun h=>hr.2 (Yk (h.trans qY.map_zero.symm))
 have hchar :bf<K1.p:= by
   change 133672<2130706433
   omega
 have hfact : ((k+3).factorial:cH)≠0 :=
   factorial_ne_zero _ (hj.trans hchar)
 change afk f (Bt (zq S)) (k+3)=qY (p5 (k+3) S)
 rw [afk,he,he,bFn _ _ hr.1,lJ,t7]
 apply (div_eq_iff (FK hfact (Du _ hsep))).mpr
 rw [show 2*(qY (cK (separant f) S)^(2*k+1) *
     qY (((mD (R:=ao))^[k + 1]) (jet S (2 :Fin 3)))) =
     qY (cK (separant f) S)^(2*k+1) *
     qY (2*((mD (R:=ao))^[k + 1]) (jet S (2 :Fin 3))) by
   rw [lJ,uW]
   ring]
 have hscale : ((mD (R:=ao))^[k+3]) S =
     ((k+3).factorial:ao[X])*p5 (k+3) S:= by
   rw [← Polynomial.factorial_smul_hasseDeriv,LinearMap.smul_apply,Mj]
 rw [bPp,hscale,lJ,zh]
 ring
theorem c7y (f :af 3) (S:ao[X]) (hS:S.natDegree≤133671)
   (hr :qg 2 f S) :
   aWP f (zq S)=afs S:= by
 let U:=S.map (cy ao cH)
 let x :=qY pL
 have hx :centre (Bt (zq S))=x := by
   simp [centre,Bt,x]
 have hdegree : (xL x U).natDegree<bf := by
   rw [SC,show U.natDegree=S.natDegree from
     Polynomial.natDegree_map_eq_of_injective (cy ao cH).injective S]
   exact PD hS
 have htaylor : (∑ j:Fin bf,
     vl j.val (afk f (Bt (zq S)) j.val)) =
     Polynomial.taylor x U:= by
   rw [Up (fun j =>
     vl j (afk f (Bt (zq S)) j))]
   conv_rhs=>rw [Vs _ bf hdegree]
   refine sH rfl fun j hj => ?_
   rw [dGH f S hr j (Finset.mem_range.mp hj),SW]
   congr 1
   dsimp [U,x]
   rw [NZ]
   exact (Gi cML (p5 j S)).symm
 have hU:aac f (Bt (zq S))=U:= by
   rw [aac,hx,htaylor,Yi ,neg_add_cancel,z9k]
 funext j
 change (aac f (Bt (zq S))).coeff j.val =
   cy ao cH (S.coeff j.val)
 rw [hU,Eg]
end
end aeC
end
section
namespace aA2
noncomputable section
open aR oR we yz MvPolynomial
theorem avJ {R:Type*} [nq R] {I:c9 R} {s a :R} (ha :a∈I) :
  ad2 I s a=0:= by
 rw [ad2,Gn,Ideal.Quotient.eq_zero_iff_mem.mpr ha,oq]
theorem ajV {R:Type*} [nq R] (I:c9 R) (s :R) :
  qU (ad2 I s s) :=
 Ze (nI I s)
theorem bs6 {R A:Type*} [nq R] [nq A] {I:c9 R} {s :R}
  {g h:TC I s →+* A} (he :g.comp (ad2 I s)=h.comp (ad2 I s)) :g=h:= by
 apply zuW (LO (nI I s))
 apply Ef
 intro a
 obtain ⟨b,rfl⟩:=vH a
 exact Nr he b
def aO6 {R A:Type*} [nq R] [nq A] (I:c9 R) (s :R)
    (b:R →+* A) (hI:I≤oK b) (hs :qU (b s)) :TC I s →+* A :=
  let g:=R9 I b fun _ hx=>RingHom.mem_ker.mp (hI hx)
  ztx (g:=g) (nI I s) hs
@[simp] theorem aWc {R A:Type*} [nq R] [nq A] (I:c9 R) (s :R)
   (b:R →+* A) (hI:I≤oK b) (hs :qU (b s)) (a :R) :
   aO6 I s b hI hs (ad2 I s a)=b a :=
  Ts (g:=R9 I b
   fun _ hx=>RingHom.mem_ker.mp (hI hx)) (nI I s) hs (nI I a)
private theorem three_ne_zero : (3:cH)≠0:= by
 let:u9 ao K1.p:=vw aR.embed.injective K1.p
 let:u9 (oz ao) K1.p :=
  vw VC K1.p
 let:u9 cH K1.p :=
  vw Yk K1.p
 exact fun h=>(by decide : ¬ K1.p∣3)
  ((S1  cH K1.p 3).mp h)
private theorem bhV {A:Type*} [nq A] (c:cH →+* A) :
  qU (3:A) := by
 simpa only [uW] using (isUnit_iff_ne_zero.mpr three_ne_zero).map c
private theorem b5E {A:Type*} [nq A] (f :af 3)
  (w:eT 4 →+* A) (hu:qU (w (S7 f))) (hG:w (graph f)=0)
  {z :A} (hz :w (vY (fW (D3 f)))+3*z*w (S7 f)=0) :
  w (lI 3)=z := by
 have hh:=hG
 rw [graph,pG,lJ,lJ,uW] at hh
 have he :=add_left_cancel (hh.trans hz.symm)
 have hc (x :A) :3*x*w (S7 f)=(3*w (S7 f))*x := by ring
 rw [hc,hc] at he
 exact ((bhV (w.comp C)).mul hu).mul_left_cancel he
private theorem bu1 {A:Type*} [nq A] {f old:af 3} {F:eT 4}
   (hF:ag9 f old F) (w:eT 4 →+* A)
   (hG:rP f≤oK w) (hs :qU (w (S7 f))) :
   w F=0↔w (vY (fW old))=0:= by
 obtain ⟨a,b,c,hc,hm⟩:=hF
 have he :=RingHom.mem_ker.mp (hG hm)
 simp only [lJ,qx ,t7] at he
 have hz :w (S7 f)^b*w F=w (C c)*w (vY (fW old)) := by
   apply sub_eq_zero.mp
   apply (hs.pow a).mul_left_cancel
   simpa only [p9] using he
 constructor
 · intro h
   have hu:qU (w (C c)) :=(isUnit_iff_ne_zero.mpr hc).map (w.comp C)
   apply hu.mul_left_cancel
   rw [p9,← hz,h,p9]
 · intro h
   apply (hs.pow b).mul_left_cancel
   rw [p9,hz,h,p9]
private def a5Y (f :af 3) :aeI f :=
 -Nt f (fW (D3 f)) *
   ↑(((bhV ((Nt f).comp C)).mul (ajV (BW f) (sep f))).unit⁻¹)
private theorem bsV (f :af 3) :
  Nt f (fW (D3 f))+3*a5Y f*Nt f (sep f)=0:= by
 let a :=Nt f (fW (D3 f))
 let s :=Nt f (sep f)
 let u:=((bhV ((Nt f).comp C)).mul (ajV (BW f) (sep f))).unit
 have hu: (u:aeI f)=3*s :=IsUnit.unit_spec _
 change a+3*(-a*(↑u⁻¹:aeI f))*s=0
 calc
  _=a + -a*((↑u⁻¹:aeI f)*(u:aeI f)) := by rw [hu]; ring
  _=0:= by simp
private def substitute (f :af 3) :eT 4 →+* aeI f :=
 eval₂Hom ((Nt f).comp C) (yB (fun i=>Nt f (lI i)) (a5Y f))
@[simp] private theorem awF (f :af 3) (p:eT 3) :
    substitute f (vY p)=Nt f p:= by
  rw [substitute,vY,eval₂Hom_rename,ZK]
  have h:eval₂Hom ((Nt f).comp C) (fun i:Fin 3=>Nt f (lI i))=Nt f := by
    apply Mw
    · intro c
      simp
    · intro i
      simp
  rw [h]
private theorem bw2 (f :af 3) :
  substitute f (lI (II 3))=a5Y f := by
 rw [substitute,eval₂Hom_X']
 exact Dz _ _
private theorem cqL (f :af 3) :substitute f (graph f)=0:= by
 rw [graph,pG,lJ,lJ,uW,awF,awF,
  show (3:Fin 4)=II 3 from rfl,bw2]
 exact bsV f
private theorem cqM (f :af 3) (T:Gf f) :
   Wy f T≤oK (substitute f) := by
 have hG:rP f≤oK (substitute f) := by
   rw [rP,zf9,sup_le_iff,In,
     In,zS ,zS]
   refine ⟨?_,cqL f⟩
   rw [awF]
   exact avJ (sI (by simp))
 have hs :qU (substitute f (S7 f)) := by
   rw [awF]
   exact ajV _ _
 refine sup_le hG ((In _).mpr (RingHom.mem_ker.mpr ?_))
 apply (bu1 T.cut_represents _ hG hs).mpr
 rw [awF]
 exact avJ (sI (by simp))
private def aN4 (f :af 3) (T:Gf f) :aYQ f T →+* aeI f :=
 aO6 _ _ (substitute f) (cqM f T)
  (by rw [awF]; exact ajV _ _)
private theorem bqL (f :af 3) (T:Gf f) (b:eT 4) :
  aN4 f T (zp f T b)=substitute f b:= by
 rw [aN4,aWc]
private theorem bs5 (f :af 3) (T:Gf f) :
   BW f≤oK ((zp f T).comp (p6 pU).toRingHom) := by
 let b:=(zp f T).comp (p6 pU).toRingHom
 have hG:rP f≤oK (zp f T) := fun u hu =>
   RingHom.mem_ker.mpr (avJ (show u∈Wy f T from zKg hu))
 change BW f≤oK b
 rw [BW,zf9,sup_le_iff]
 rw [In,In]
 refine ⟨hG (show vY (fW f)∈rP f from
   sI (by simp)),RingHom.mem_ker.mpr ?_⟩
 exact (bu1 T.cut_represents _ hG (ajV _ _)).mp
   (avJ (show T.cut∈Wy f T from
     Ideal.mem_sup_right (Pf _)))
private def a6e (f :af 3) (T:Gf f) :aeI f →+* aYQ f T :=
 aO6 _ _ ((zp f T).comp (p6 pU).toRingHom)
  (bs5 f T) (ajV (Wy f T) (S7 f))
@[simp] private theorem a6f (f :af 3) (T:Gf f) (a :eT 3) :
   a6e f T (Nt f a)=zp f T (vY a) :=
  aWc _ _ ((zp f T).comp (p6 pU).toRingHom)
   (bs5 f T) (ajV (Wy f T) (S7 f)) a
def aH6 (f :af 3) (T:Gf f) :aeI f ≃+* aYQ f T:= by
  refine RingEquiv.ofRingHom (a6e f T) (aN4 f T) ?_ ?_
  · apply bs6
    have hcomp: (aN4 f T).comp (zp f T)=substitute f :=
      Ef (bqL f T)
    rw [RingHom.comp_assoc,RingHom.id_comp,hcomp]
    apply Mw
    · intro c
      simp [substitute,vY]
    · intro i
      refine WK ?_ (fun j => ?_) i
      · have hG:zp f T (graph f)=0 :=
          avJ (zKg (sI (by simp)))
        have he :=DFunLike.congr_arg (a6e f T) (bsV f)
        rw [pG,lJ,lJ,uW,oq,a6f,a6f] at he
        have h:=b5E f (zp f T) (ajV _ _) hG he
        rw [Gn,bw2]
        exact h.symm
      · simp [substitute,vY]
  · apply bs6
    apply Ef
    intro a
    simp [bqL]
@[simp] theorem bHy (f :af 3) (T:Gf f) (a :eT 3) :
   aH6 f T (Nt f a)=zp f T (vY a) :=
  a6f f T a
end
end aA2
end
section
namespace as3
noncomputable section
open zP aaq MvPolynomial
abbrev Slot (A:Fin 4→aU Exponent) :=(i:Fin 4) × ↥(A i)
abbrev vJ (A:Fin 4→aU Exponent) :=
 lz (Slot A) (fZ A)
def jT (A:Fin 4→aU Exponent) (v :Slot A) :Degree :=
 vZ v.1 1
abbrev Kx (A:Fin 4→aU Exponent) (d:Degree) :=
 weightedHomogeneousSubmodule (fZ A) (jT A) d
def ew (A:Fin 4→aU Exponent) :vJ A →ₐ[fZ A] af A :=
 oy fun v=>ov v.2.val 1
def aEy (A:Fin 4→aU Exponent) (k :ℕ) :Set (vJ A) :=
 {f | (∃ d,f∈Kx A d)∧ew A f∈mo A k}
def Se (A:Fin 4→aU Exponent) (k :ℕ) :c9 (vJ A) :=
 n5 (aEy A k)
def T2 (A:Fin 4→aU Exponent) (i:Fin 4) :vJ A :=
  ∑ a : ↥(A i),C (cy (xB A) (fZ A) (lI ⟨i,a⟩)) *
    lI ⟨i,a⟩
def ke (A:Fin 4→aU Exponent) (k :ℕ) :c9 (vJ A) :=
 Se A 0 ⊔ n5 (T2 A '' {i:Fin 4 | (i:ℕ)<k})
def GW (A:Fin 4→aU Exponent) (b: (i:Fin 4) → ↥(A i)) :
    vJ A :=
  ∏ i:Fin 4,lI (⟨i,b i⟩:Slot A)
def ab5 (A:Fin 4→aU Exponent) (hz : ∀ i,0∈A i) :vJ A :=
 GW A fun i=>⟨0,hz i⟩
open scoped Pointwise
private def alq (A:Fin 4→aU Exponent) (v :Slot A) :Exponent :=
 v.2.val
private def afB (A:Fin 4→aU Exponent) (d:Degree) :Set Exponent :=
 {a | ∃ e :Slot A →₀ ℕ,
   t4 (jT A) e=d∧t4 (alq A) e=a}
private theorem aC6 (A:Fin 4→aU Exponent) (d e :Degree) :
  Bc A (d+e)=Bc A d+Bc A e := by
 simp only [Bc,Av,add_nsmul,zm]
private theorem aUt (A:Fin 4→aU Exponent) (i:Fin 4) :
   Bc A (vZ i 1)=A i:= by
 classical
 unfold Bc
 rw [G3 i]
 · simp
 · intro j _ hj
   rw [C5 hj,zero_nsmul]
 · simp
private theorem bOD (A:Fin 4→aU Exponent) (d:Degree) :
    Bc A d=afB A d:= by
  classical
  have hadd (d e :Degree) :
      afB A d+afB A e⊆afB A (d+e) := by
    intro m hm
    obtain ⟨a,⟨u,hu,rfl⟩,b,⟨v,hv,rfl⟩,rfl⟩:=Set.mem_add.mp hm
    exact ⟨u+v,by rw [pG,hu,hv],pG _ _ _⟩
  have hzero : (0:Exponent)∈afB A 0 :=
    ⟨0,oq _,oq _⟩
  have hsingle (i:Fin 4) : (↑(A i) :Set Exponent)⊆afB A (vZ i 1) := by
    intro a ha
    let v :Slot A:=⟨i,⟨a,ha⟩⟩
    exact ⟨Finsupp.single v 1,by rw [Finsupp.weight_single,one_smul]; rfl,
      by rw [LP ,one_smul]; rfl⟩
  have hscale (i:Fin 4) (n:ℕ) :
      n•(↑(A i) :Set Exponent)⊆afB A (n•vZ i 1) := by
    induction n with
    | zero=>simpa using hzero
    | succ n ih =>
      rw [J4 ,J4]
      exact (zgS ih (hsingle i)).trans (hadd _ _)
  have hsum (s :aU (Fin 4)) :
      (∑ i∈s,d i•(↑(A i) :Set Exponent)) ⊆
        afB A (∑ i∈s,d i•vZ i 1) := by
    induction s using Cy with
    | empty=>simpa using hzero
    | @insert i s hi ih =>
      rw [yo hi,yo hi]
      exact (zgS (hscale i _) ih).trans (hadd _ _)
  apply G5
  · have hdeg: (∑ i:Fin 4,d i•vZ i (1 :ℕ))=d:= by
      funext j
      simp [Finset.sum_apply,RP]
    simpa only [Bc,hdeg] using hsum th
  · clear hsum
    rintro _ ⟨e,rfl,rfl⟩
    induction e using Zh with
    | zero=>simp [Bc]
    | add e f he hf =>
      rw [pG,pG,aC6]
      exact Set.mem_add.mpr ⟨_,he,_,hf,rfl⟩
    | single v n =>
      rw [LP ,LP]
      have hv :alq A v∈Bc A (jT A v) := by
        rw [jT,aUt]
        exact v.2.property
      induction n with
      | zero=>simp [Bc]
      | succ n ih =>
        rw [J4 ,J4 ,aC6]
        exact Set.mem_add.mpr ⟨_,ih,_,hv,rfl⟩
private theorem aT6 (A:Fin 4→aU Exponent) (e :Slot A →₀ ℕ) :
   ew A (ov e 1)=ov (t4 (alq A) e) 1 := by
 induction e using Zh with
 | zero=>simp [monomial_zero']
 | add e f he hf =>
   rw [← t6 (1 :fZ A),← Kp,lJ,he,hf,
    Kp,t6,pG]
 | single v n =>
   rw [← zp9,t7,ew,wY]
   change (ov (alq A v) (1 :fZ A))^n= _
   rw [monomial_pow,one_pow,LP]
theorem aOJ (A:Fin 4→aU Exponent) (d:Degree) :
   (Kx A d).map (ew A).toLinearMap=dO A d:= by
 have hS:Kx A d=restrictSupport (fZ A)
     {e | t4 (jT A) e=d} :=
   weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
 rw [hS,restrictSupport_eq_span,Submodule.map_span,dO]
 congr 1
 ext p
 constructor
 · rintro ⟨_,⟨e,he,rfl⟩,rfl⟩
   rw [FV,aT6]
   refine ⟨⟨_,?_⟩,rfl⟩
   rw [bOD]
   exact ⟨e,he,rfl⟩
 · rintro ⟨a,rfl⟩
   have ha :a.val∈afB A d:= by
     rw [← bOD]
     exact a.property
   obtain ⟨e,he,hea⟩:=ha
   exact ⟨_,⟨e,he,rfl⟩,by rw [FV,aT6,hea]⟩
variable {A:Fin 4→aU Exponent}
theorem aN7 (i:Fin 4) :
  T2 A i∈Kx A (vZ i 1) := by
 classical
 apply Wl
 intro a _
 have hC:=isWeightedHomogeneous_C (jT A)
  (cy (xB A) (fZ A) (lI ⟨i,a⟩))
 have hX:=isWeightedHomogeneous_X (fZ A) (jT A) (⟨i,a⟩:Slot A)
 simpa only [mem_weightedHomogeneousSubmodule,wB,jT] using hC.mul hX
theorem aNd (i:Fin 4) :
  ew A (T2 A i)=ve A i:= by
 classical
 simp only [T2,ve,t5 ,lJ,ew,aeval_C,
  F9,wY ,C_mul_monomial,Dw]
end
end as3
end
section
namespace dm9
noncomputable section
open aR oR we yz MvPolynomial
open RingTheory.Sequence
open scoped Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem bHC (f :af 3) (P:c9 (eT 3)) [P.IsPrime]
    (hs :fW (separant f)∉P) :
    (F3 f P).IsPrime ∧
      (p7 (F3 f P)).natDegree =
        (p7 P).natDegree := by
  let s :=fW (separant f)
  let v :eT 3 := -fW (D3 f)*C ((3:cH)⁻¹)
  let L:=LQ (nI P s)
  let J:=awayPresentationIdeal P s
  have hsA:nI P s≠0:=mt Ideal.Quotient.eq_zero_iff_mem.mp hs
  have hsreg:IsLeftRegular (nI P s) := fun _ _ h=>mul_left_cancel₀ hsA h
  have :HZ L:=IsLocalization.Away.isDomain L hsA
  have hJ:J.IsPrime :=zgL (awayPresentation P s)
  let coords :Fin 4→lz (zi (Fin 3)) cH :=
    yB (fun i=>lI (some i)) (p6 some v*lI none)
  let φ:eT 4 →ₐ[cH] lz (zi (Fin 3)) cH :=oy coords
  have hpoint (w:zi (Fin 3)→cH) (hw:w∈qM cH J) :
      (fun i=>oy w (coords i))=JZ f (w ∘ some) := by
    have hrel :=hw _ (X_none_mul_rename_some_sub_one_mem_awayPresentationIdeal P s)
    rw [qx ,lJ,wY ,aeval_rename,vk,Ar] at hrel
    have hinv :w none=(oy (w ∘ some) s)⁻¹:=eq_inv_of_mul_eq_one_left hrel
    funext i
    refine WK ?_ (fun j => ?_) i
    · simp only [coords,JZ,Dz ,lJ,aeval_rename,wY ,hinv,v,
        Il,aeval_C,zEi,x7,div_eq_mul_inv,mul_inv_rev]
      ac_rfl
    · simp [coords,JZ,Function.comp_def]
  have himage : (fun w:zi (Fin 3)→cH=>JZ f (w ∘ some)) ''
        qM cH J=S3 f P:= by
    change (JZ f ∘ (fun w:zi (Fin 3)→cH=>w ∘ some)) ''
      qM cH J=JZ f '' D7 f P
    rw [Set.image_comp]
    have hopen:=image_comp_some_zeroLocus_awayPresentationIdeal (K:=cH) P s
    simpa only [D7,x7] using oj (Set.image (JZ f)) hopen
  have hcomap :F3 f P=J.comap φ:= by
    ext p
    change p∈uh cH (S3 f P)↔φ p∈J
    have hjp:φ p∈J↔φ p∈uh cH (qM cH J) := by
      rw [QL J]
    rw [← himage,hjp]
    simp only [Ok,Set.forall_mem_image]
    refine forall₂_congr fun w hw => ?_
    change oy (JZ f (w ∘ some)) p=0↔oy w (oy coords p)=0
    rw [comp_aeval_apply,hpoint w hw]
  have hrename :φ.comp (p6 pU)=p6 some := by
    apply Dv
    intro i
    simp [φ,coords]
  have hback : (F3 f P).comap (p6 pU)=P:= by
    rw [hcomap]
    change J.comap (φ.comp (p6 pU))=P
    rw [hrename]
    ext p
    change p6 some p∈awayPresentationIdeal P s↔p∈P
    rw [mem_awayPresentationIdeal,awayPresentation_rename_some,
      map_eq_zero_iff _ (IsLocalization.Away.algebraMap_injective_of_isLeftRegular hsreg),
      Ye]
  have hupper : (p7 (J.comap φ)).natDegree ≤
      (p7 J).natDegree :=
    zGE (zwL J φ t9)
      zmq
  have hlower : (p7 ((F3 f P).comap (p6 pU))).natDegree ≤
      (p7 (F3 f P)).natDegree :=
    zGE
      (zwL (F3 f P) (p6 pU) t9)
      zmq
  rw [hback] at hlower
  rw [natDegree_affineHilbertPolynomial_awayPresentationIdeal hsreg,← hcomap] at hupper
  refine ⟨?_,yL hupper hlower⟩
  rw [hcomap]
  exact hJ.comap φ
end
end dm9
end
section
namespace Qp
open aR yz
structure OE (P:Set iz) :Prop where
 polytope : ∃ v :Set iz,v.Finite∧P=xW ℝ v
 zero_mem:0∈P
 zero_height : ∀ x∈P,x 3=0
def bF (s :pC) :Prop :=s.j≤ s.b∧2*s.t≤ s.j
end Qp
end
section
namespace Qp
noncomputable section
open aR yz MeasureTheory Set
private theorem a9x {α β:Type} [MeasureSpace α] [MeasureSpace β]
   [SigmaFinite (volume :Measure α)]
   (e :β ≃ᵐ ℝ×α) (he :MeasurePreserving e) {C:Set β} (hC:yJ C)
   {d:ℝ} (hd : ∀ v∈C,(e v).1∈Icc 0 d) :
   volume C = ∫⁻ t in Icc 0 d,volume ((fun v=>e.symm (t,v)) ⁻¹' C) := by
 have hpre :yJ (e.symm ⁻¹' C) :=hC.preimage e.symm.measurable
 rw [← (MeasurePreserving.symm e he).measure_preimage_equiv C,Measure.volume_eq_prod,
   Measure.prod_apply hpre,← lintegral_indicator MK]
 apply lintegral_congr
 intro t
 by_cases ht:t∈Icc 0 d
 · rw [indicator_of_mem ht]
   rfl
 · rw [indicator_of_notMem ht]
   have h:Prod.mk t ⁻¹' (e.symm ⁻¹' C) = ∅ := by
     apply eq_empty_iff_forall_notMem.mpr
     intro v hv
     have hv' := hd _ hv
     rw [e.apply_symm_apply] at hv'
     exact ht hv'
   rw [h,measure_empty]
private theorem fs1 {a b d:ℝ} (hd:0≤d)
   (hn : ∀ x∈Icc 0 d,0≤a+b*x) :
   (∫⁻ x in Icc 0 d,Au (a+b*x))=Au (d*a+b*d^2/2) := by
 have hi:IntegrableOn (fun x :ℝ=>a+b*x) (Icc 0 d) :=
   (show Continuous (fun x :ℝ=>a+b*x) by fun_prop).integrableOn_Icc
 have hnn : ∀ᵐ x ∂(volume :Measure ℝ).restrict (Icc 0 d),0≤a+b*x :=
   (ae_restrict_mem MK).mono hn
 rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
 congr 1
 rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hd,
   intervalIntegral.integral_add
     (show IntervalIntegrable (fun _:ℝ=>a) volume 0 d from intervalIntegrable_const)
     ((show Continuous (fun x :ℝ=>b*x) by fun_prop).intervalIntegrable 0 d),
   intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
 simp only [Gr,G9,zero_pow (by decide : (2 :ℕ)≠0)]
 ring
private abbrev fbW {n:ℕ} : (Fin (n+1)→ℝ) ≃ᵐ ℝ×(Fin n→ℝ) :=
 MeasurableEquiv.piFinSuccAbove (fun _=>ℝ) (II n)
private theorem fr7 {n:ℕ} (t:ℝ) (v :Fin n→ℝ) :
  fbW.symm (t,v)=yB v t:= by
 change @Fin.insertNth n (fun _=>ℝ) (II n) t v = @yB n (fun _=>ℝ) v t
 exact Fin.insertNth_last' t v
private def triangle (d e :ℝ) :Set (Fin 2→ℝ) :=
 {x | x 1∈Icc 0 e∧x 0∈Icc 0 (d - x 1)}
private theorem fvT {d e :ℝ} (he :0≤e) (hed:e≤d) :
    volume (triangle d e)=Au (e*d-e^2/2) := by
  let equiv : (Fin 2→ℝ) ≃ᵐ (ℝ×ℝ) :=
    (MeasurableEquiv.finTwoArrow (α:=ℝ)).trans MeasurableEquiv.prodComm
  have hpres :MeasurePreserving equiv :=
    (Measure.measurePreserving_swap (μ:=(volume :Measure ℝ)) (ν:=(volume :Measure ℝ))).comp
      (volume_preserving_finTwoArrow ℝ)
  have hm:yJ (triangle d e) := by
    have h0:Measurable (fun x :Fin 2→ℝ=>x 0) :=Nj 0
    have h1 :Measurable (fun x :Fin 2→ℝ=>x 1) :=Nj 1
    exact (measurableSet_Icc.preimage h1).inter
      ((C4 Gj h0).inter (C4 h0 (by fun_prop)))
  rw [a9x equiv hpres hm (fun v hv=>hv.1)]
  calc
    _ = ∫⁻ x in Icc 0 e,Au (d+(-1)*x) := by
      apply setLIntegral_congr_fun MK
      intro x hx
      have hsec: (fun v :ℝ=>equiv.symm (x,v)) ⁻¹' triangle d e=Icc 0 (d - x) := by
        ext y
        change (x∈Icc 0 e∧y∈Icc 0 (d - x))↔_
        simp [hx]
      dsimp only
      rw [hsec,Real.volume_Icc]
      congr 1
      ring
    _ = _:= by
      rw [fs1 he (fun x hx=> by linarith [hx.2])]
      congr 1
      ring
private def bkw (b j c:ℝ) :Set (Fin 3→ℝ) :=
 {x | (∀ i,0≤x i)∧x 0 + x 1 + x 2≤b∧x 1+2*x 2≤j∧x 2≤ c}
private theorem frB (b j c:ℝ) :yJ (bkw b j c) := by
 have horth:yJ {x :Fin 3→ℝ | ∀ i,0≤x i} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter (fun i=>C4 Gj (Nj i))
 have hb:yJ {x :Fin 3→ℝ | x 0 + x 1 + x 2≤b} :=
  C4 (by fun_prop) Gj
 have hj:yJ {x :Fin 3→ℝ | x 1+2*x 2≤j} :=
  C4 (by fun_prop) Gj
 have ht:yJ {x :Fin 3→ℝ | x 2≤ c} :=
  C4 (Nj 2) Gj
 exact horth.inter (hb.inter (hj.inter ht))
private theorem fsM {b j c:ℝ} (hc:0≤ c) (hbj:j≤b) (hjc:2*c≤j) :
    volume (bkw b j c)=Au (c*(j - c)*(b - j/2)) := by
  have hbound (v :Fin 3→ℝ) (hv :v∈bkw b j c) : (fbW v).1∈Icc 0 c :=
    ⟨hv.1 2,hv.2.2.2⟩
  rw [a9x fbW (volume_preserving_piFinSuccAbove _ _) (frB b j c) hbound]
  calc
    _ = ∫⁻ z in Icc 0 c,Au (j*(b - j/2)+(-2*(b - j/2))*z) := by
      apply setLIntegral_congr_fun MK
      intro z hz
      have hsec: (fun v :Fin 2→ℝ=>fbW.symm (z,v)) ⁻¹' bkw b j c =
          triangle (b - z) (j - 2*z) := by
        ext v
        have h0: (@yB 2 (fun _=>ℝ) v z) 0=v 0 :=
          @FQ 2 (fun _=>ℝ) z v 0
        have h1 : (@yB 2 (fun _=>ℝ) v z) 1=v 1 :=
          @FQ 2 (fun _=>ℝ) z v 1
        have h2 : (@yB 2 (fun _=>ℝ) v z) 2=z :=
          @Dz 2 (fun _=>ℝ) z v
        simp only [SU,fr7,bkw,triangle,mem_ofPred_eq,mem_Icc,
          Fin.forall_iff_castSucc (n:=2),Dz ,FQ,Fin.forall_fin_two,
          h0,h1,h2]
        change ((0≤z∧0≤v 0∧0≤v 1)∧v 0+v 1+z≤b ∧
          v 1+2*z≤j∧z≤ c)↔((0≤v 1∧v 1≤j - 2*z) ∧
          0≤v 0∧v 0≤b - z - v 1)
        constructor
        · rintro ⟨⟨_,hv0,hv1⟩,hb',hj',_⟩
          exact ⟨⟨hv1,by linarith⟩,hv0,by linarith⟩
        · rintro ⟨⟨hv1,hj'⟩,hv0,hb'⟩
          exact ⟨⟨hz.1,hv0,hv1⟩,by linarith,by linarith,hz.2⟩
      dsimp only
      rw [hsec,fvT (by linarith [hz.2]) (by linarith [hz.1])]
      congr 1
      ring
    _ = _:= by
      rw [fs1 hc (fun z hz=> by
        have h1 :0≤j - 2*z := by linarith [hz.2]
        have h2 :0≤b - j/2 := by linarith
        nlinarith [Et h1 h2])]
      congr 1
      ring
end
end Qp
end
section
namespace as3
noncomputable section
open zP aaq MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 :Prop :=
  ∀ (A:Fin 4→aU Exponent) (hz : ∀ i,0∈A i),
    (∀ j:Fin 4,∃ i,t3 j 1∈A i) →
    ∀ (i:Fin 4) (f :vJ A),f∈aEy A (i.val+1) →
      ∃ n:ℕ,ab5 A hz^n*f∈ke A (i.val+1)
def c2 :Prop :=
  ∀ (A:Fin 4→aU Exponent) (hz : ∀ i,0∈A i) (i:Fin 4)
    (b: (j:Fin 4) → ↥(A j)) (f :vJ A) (n:ℕ),
    ab5 A hz^n*f∈ke A (i.val+1) →
      ∃ m:ℕ,GW A b^m*f∈ke A (i.val+1)
private theorem weight_apply (A:Fin 4→aU Exponent) (e :Slot A →₀ ℕ) (i:Fin 4) :
   t4 (jT A) e i = ∑ a : ↥(A i),e ⟨i,a⟩:= by
 classical
 rw [Finsupp.weight_eq_sum,Finset.sum_apply,Fintype.sum_sigma]
 rw [G3 i]
 · simp [jT,PM]
 · intro j _ hj
   simp [jT,PM,C5 (Ne.symm hj)]
 · simp
private theorem b9r (A:Fin 4→aU Exponent)
    (J:c9 (vJ A)) (g:vJ A) (N :ℕ)
    (hkill : ∀ b: (i:Fin 4) → ↥(A i),GW A b^N*g∈J)
    (e :Slot A →₀ ℕ) (c:fZ A)
    (he : ∀ i,G1 ↥(A i)*N<t4 (jT A) e i) :
    ov e c*g∈J:= by
  classical
  have hpick (i:Fin 4) : ∃ a : ↥(A i),N≤e ⟨i,a⟩:= by
    by_contra! h
    have hsum: (∑ a : ↥(A i),e ⟨i,a⟩)≤G1 ↥(A i)*N := by
      calc
        _ ≤ ∑ _a : ↥(A i),N :=KI fun a _=>(h a).le
        _ = _:= by simp
    exact (G4 (he i)) ((weight_apply A e i).trans_le hsum)
  choose b hb using hpick
  let v :Slot A →₀ ℕ := ∑ i:Fin 4,t3 ⟨i,b i⟩ N
  have hv :v≤e := by
    rintro ⟨i,a⟩
    rw [show v ⟨i,a⟩=t3 (⟨i,b i⟩:Slot A) N ⟨i,a⟩ by
      simp only [v,Finsupp.finsetSum_apply]
      apply G3 i
      · intro j _ hj
        apply Finsupp.single_eq_of_ne
        intro h
        exact hj (oj Sigma.fst h).symm
      · simp]
    by_cases ha :b i=a
    · subst a
      simpa using hb i
    · simp [Ne.symm ha]
  have hchart:GW A b^N=ov v (1 :fZ A) := by
    unfold GW
    rw [← Finset.prod_pow]
    simp only [zp9,v,monomial_sum_one]
  have hfac:ov e c*g=ov (e - v) c*(GW A b^N*g) := by
    rw [hchart,← qy ,Kp,Dw ,LR (e - v),
      add_tsub_cancel_of_le hv]
  rw [hfac]
  exact J.mul_mem_left _ (hkill b)
private theorem b53 (A:Fin 4→aU Exponent)
  (J:c9 (vJ A)) (g:vJ A) (N :ℕ)
  (hkill : ∀ b: (i:Fin 4) → ↥(A i),GW A b^N*g∈J)
  {f :vJ A} {d:Degree} (hf :f∈Kx A d)
  (hd : ∀ i,G1 ↥(A i)*N<d i) :
  f * g∈J:= by
 classical
 rw [f.as_sum,Nq]
 exact J.sum_mem fun e he=>b9r A J g N hkill e _ (by
  have hdeg:=hf (mem_support_iff.mp he)
  intro i
  simpa only [hdeg] using hd i)
private theorem Zy (A:Fin 4→aU Exponent) {g:vJ A} {e :Degree}
   (hg:g∈Kx A e) (f :vJ A) (d:Degree) :
   yQ (jT A) (d+e) (f * g) =
     yQ (jT A) d f * g:= by
 classical
 induction f using MvPolynomial.induction_on' with
 | monomial a c =>
   have ha :=UZ (jT A) a c rfl
   have hg' : g.IsWeightedHomogeneous (jT A) e :=hg
   simp only [Zt (ha.mul hg'),
     Zt ha,add_right_cancel_iff]
   split <;> simp_all
 | add p r hp hr=>simp [add_mul,hp,hr]
private theorem emL (A:Fin 4→aU Exponent) (k :ℕ) (J:c9 (vJ A))
    (hlocal : ∀ g∈aEy A k,∀ b: (i:Fin 4) → ↥(A i),
      ∃ n:ℕ,GW A b^n*g∈J) :
    ∃ q:ℕ,∀ (d:Degree),(∀ i,q≤d i) →
      ∀ f∈Kx A d,f∈Se A k→f∈J:= by
  classical
  obtain ⟨G,hG,hspan⟩:=(Submodule.fg_span_iff_fg_span_finset_subset
    (R:=vJ A) (aEy A k)).mp (IsNoetherian.noetherian _)
  have hspan' : Se A k=n5 (↑G:Set (vJ A)) :=hspan
  choose D hD using fun g:G=>(hG g.property).1
  choose n hn using fun g:G=>hlocal g (hG g.property)
  let N (g:G) :=Finset.univ.sup (n g)
  have hN (g:G) (b: (i:Fin 4) → ↥(A i)) :GW A b^N g*(g:vJ A)∈J:= by
    have hle :n g b≤N g:=zk (f :=n g) (vi b)
    have hpow:GW A b^N g*(g:vJ A) =
        GW A b^(N g - n g b)*(GW A b^n g b*(g:vJ A)) := by
      rw [← qy ,← pow_add,z8 hle]
    rw [hpow]
    exact J.mul_mem_left _ (hn g b)
  let bound (g:G) (i:Fin 4) :=D g i+Fintype.card ↥(A i)*N g+1
  let q:=Finset.univ.sup fun g:G=>Finset.univ.sup (bound g)
  refine ⟨q,?_⟩
  intro d hd f hf hrel
  rw [hspan'] at hrel
  obtain ⟨c,hc⟩:=Submodule.mem_span_finset'.mp hrel
  have hsum:=oj (yQ (jT A) d) hc
  rw [t5 ,zfp (show f.IsWeightedHomogeneous _ d from hf)]
    at hsum
  rw [← hsum]
  refine J.sum_mem fun g _ => ?_
  have hgd (i:Fin 4) :bound g i≤d i:= by
    exact (zk (f :=bound g) (vi i)).trans
      ((zk (f := fun x :G=>Finset.univ.sup (bound x)) (vi g)).trans (hd i))
  have hdiff : ∀ i,G1 ↥(A i)*N g<(d - D g) i:= by
    intro i
    have hh:=hgd i
    change D g i+Fintype.card ↥(A i)*N g+1≤d i at hh
    change _<d i - D g i
    omega
  have heq :d - D g+D g=d:= by
    funext i
    exact z8 (by have hh:=hgd i; dsimp [bound] at hh; omega)
  change yQ (jT A) d (c g*(g:vJ A))∈J
  rw [← heq,Zy A (hD g)]
  exact b53 A J g (N g) (hN g)
    (zbF _ _ _) hdiff
variable {A:Fin 4→aU Exponent}
private theorem ce4 (k :ℕ) :
  Se A k≤(mo A k).comap (ew A).toRingHom :=
 Ideal.span_le.mpr fun _ h=>h.2
private theorem ce3 (k :ℕ) :
  (Se A k).IsHomogeneous (Kx A) :=
 Ideal.homogeneous_span _ _ fun _ h=>h.1
private theorem a6N {k l:ℕ} (h:k≤l) :mo A k≤ mo A l :=
 Pr (Set.image_mono fun _ hi=>lt_of_lt_of_le hi h)
private theorem fVU {k l:ℕ} (h:k≤l) :Se A k≤Se A l :=
 Pr fun _ hf=>⟨hf.1,a6N h hf.2⟩
private def b9L (A:Fin 4→aU Exponent) (i:Fin 4) :c9 (vJ A) :=
 Se A i.val ⊔ n5 {T2 A i}
private theorem bZm (i:Fin 4) :ke A (i.val+1)≤b9L A i:= by
 apply sup_le ((fVU (v8 i.val)).trans le_sup_left)
 apply Ideal.span_le.mpr
 rintro _ ⟨j,hj,rfl⟩
 change j.val< i.val+1 at hj
 by_cases hji:j=i
 · subst j
   exact Submodule.mem_sup_right (Pf _)
 · have hlt:j.val< i.val := by
    have hn:j.val≠i.val := fun he=>hji (Fin.ext he)
    omega
   apply Submodule.mem_sup_left
   apply sI
   exact ⟨⟨_,aN7 j⟩,by
    rw [aNd]
    exact sI ⟨j,hlt,rfl⟩⟩
theorem of_children (h1 :c1) (h2 :c2) :aaq.c3:= by
 classical
 intro A hz hv
 have hlocal (i:Fin 4) (f :vJ A) (hf :f∈aEy A (i.val+1))
     (b: (j:Fin 4) → ↥(A j)) : ∃ n:ℕ,GW A b^n*f∈b9L A i:= by
   obtain ⟨n,hn⟩:=h1 A hz hv i f hf
   obtain ⟨m,hm⟩:=h2 A hz i b f n hn
   exact ⟨m,bZm i hm⟩
 choose q hq using fun i:Fin 4=>emL A (i.val+1) (b9L A i) (hlocal i)
 refine ⟨Finset.univ.sup q,?_⟩
 intro i d hd p hp hpI
 have hp' : p∈(Kx A (shift d i 1)).map (ew A).toLinearMap:= by
   rwa [aOJ]
 obtain ⟨f,hf,hfp⟩:=hp'
 change ew A f=p at hfp
 have hfI:f∈Se A (i.val+1) :=
   sI ⟨⟨_,hf⟩,hfp ▸ hpI⟩
 have hqd (j:Fin 4) :q i≤ shift d i 1 j :=
   (zk (f :=q) (vi i)).trans
     ((hd j).trans (JW _ _))
 have hJ:=hq i _ hqd f hf hfI
 change f∈Se A i.val ⊔ n5 {T2 A i} at hJ
 rw [sup_comm] at hJ
 obtain ⟨m,g,hg,hsum⟩:=Ideal.mem_span_singleton_sup.mp hJ
 let r :=yQ (jT A) d m
 let s :=yQ (jT A) (shift d i 1) g
 have hs :s∈Se A i.val :=
   weightedHomogeneousComponent_mem_of_mem _ _ (ce3 i.val) hg _
 have hfg:r*T2 A i+s=f := by
   have he :=oj (yQ (jT A) (shift d i 1)) hsum
   rw [pG,zfp (show f.IsWeightedHomogeneous _ _ from hf)]
     at he
   change yQ (jT A) (d+Pi.single i 1)
     (m*T2 A i)+s=f at he
   rwa [Zy A (aN7 i)] at he
 have hsI:ew A s∈mo A i.val :=ce4 i.val hs
 refine ⟨ew A r,?_,?_⟩
 · rw [← aOJ]
   exact ⟨r,zbF _ _ _,rfl⟩
 · have he :=oj (ew A) hfg
   rw [pG,lJ,aNd,hfp] at he
   rw [← he,uz (ve A i),add_sub_cancel_left]
   exact hsI
end
end as3
end
section
namespace abG
noncomputable section
open we yz zP MvPolynomial
abbrev Affine (L:Type) [nq L] :=lz (Fin 4) L
def H8 {L:Type} [nq L] (f :Fin 4→Affine L) :
    c9 (Affine L) :=
  n5 (qJ f)
abbrev Total (L:Type) [lV L] :=Affine (oz L)
abbrev sU (L:Type) [lV L] :=vh (oz L)
def reduce {L:Type} [lV L] :Total L →+* Affine L :=
 ox (y5 0)
def bC {L:Type} [lV L] :Total L →+* Affine (sU L) :=
 ox (cy (oz L) (sU L))
abbrev aw3 {L:Type} [lV L] (g:Fin 4→Total L) :=
 Affine (sU L) ⧸ (H8 g).map bC
def aNY {L:Type} [lV L] (g:Fin 4→Total L) :
    Total L →+* aw3 g :=
  (nI _).comp bC
abbrev wN {L:Type} [lV L] (y :Fin 4→L) :c9 (Affine L) :=
 uh L {y}
abbrev MZ {L:Type} [lV L] (y :Fin 4→L) :=
 C9 (wN y)
abbrev abV {L:Type} [lV L] (I:c9 (Affine L)) (y :Fin 4→L) :=
 MZ y ⧸ I.map (cy (Affine L) (MZ y))
def aoK {L:Type} [lV L] (I:c9 (Affine L)) (y :Fin 4→L) :
    Affine L →ₐ[L] abV I y :=
  (Ee L _).comp (zE2 L (Affine L) (MZ y))
abbrev aJS {L:Type} [lV L] (y :Fin 4→L) :c9 (Total L) :=
 (wN y).comap reduce
instance gRY {L:Type} [lV L] (y :Fin 4→L) :
  (aJS y).IsPrime :=
 Ideal.IsPrime.comap reduce
abbrev aud {L:Type} [lV L] (y :Fin 4→L) :=
 C9 (aJS y)
abbrev bi0 {L:Type} [lV L] (g:Fin 4→Total L) (y :Fin 4→L) :=
 aud y ⧸ (H8 g).map (cy (Total L) (aud y))
def aGS {L:Type} [lV L] (g:Fin 4→Total L) (y :Fin 4→L) :
    Total L →+* bi0 g y :=
  (nI _).comp (cy (Total L) (aud y))
def bBT {L:Type} [lV L] (g:Fin 4→Total L) (y :Fin 4→L) :
    bi0 g y :=
  aGS g y (pQ pL)
def aUu (L:Type) [lV L] [oD cH L] (y :oe) :Fin 4→L :=
 fun i=>cy cH L (y i)
def gN (L:Type) [lV L] [oD cH L]
    (I:c9 (eT 4)) :c9 (Affine L) :=
  I.map (ox (cy cH L))
end
end abG
end
section
namespace aA1
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
def KX:af 3 →ₐ[ao[X]] af 4 :=p6 pU
abbrev KY (f :af 3) :af 4 :=KX (oR.separant f)
def Xj (f :af 3) :af 4 :=
 KX (D3 f)+3*lI 3*KY f
def apE (f :af 3) :af 4 :=
 pQ (oY (-(3:ao)⁻¹))*dN.pK (Xj f)
def a5p (f :af 3) (a :ℕ) (b:af 4) :af 4 :=
  KY f*dN.pK b+apE f*oZ 3 b -
    (a :af 4)*dN.pK (KY f)*b
def YL (f :af 3) :ℕ→af 4
 | 0=>MvPolynomial.X 3
 | k+1=>a5p f k (YL f k)
def bhU:ℕ→ao
 | 0=>1
 | k+1=>bhU k*((k+4 :ℕ) :ao)⁻¹
def su (f :af 3) (j:ℕ) :af 4 :=
  if h:j<3 then
    lI ⟨j,h.trans (by decide :3<4)⟩
  else
    pQ (oY (bhU (j-3))) *
      YL f (j-3)
def bf4 (f :af 3) (d j:ℕ) :af 4 :=
 KY f^(d-(j-3))*su f j
def centre :cH :=qY pL
end
end aA1
end
section
namespace aeC
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
def c3:Prop :=
  ∀ (f :af 3) (P:c9 (eT 3)),
    ze f→0<f.degreeOf 2 → ¬ Fb f →
    P∈(BW f).retainedMinimalPrimes (fW (separant f)) →
    (p7 P).natDegree=1
def c4 :Prop :=
  ∀ (f :af 3) (P:c9 (eT 3)),
    P.IsPrime→fW (separant f)∉P →
    (p7 P).natDegree=1 →
    (aHk f P).IsPrime∧(p7 (aHk f P)).natDegree=1
end
end aeC
end
section
namespace Qp
noncomputable section
open aR oR we yz MvPolynomial
open scoped BigOperators Pointwise
theorem cDT (s :pC) (h:ℕ) :Convex ℝ (nD s h) := by
 intro x hx y hy a b ha hb hab
 obtain ⟨hx,hxb,hxj,hxt,hxh⟩:=hx
 obtain ⟨hy,hyb,hyj,hyt,hyh⟩:=hy
 simp only [nD,Set.mem_ofPred_eq,Av,PM,G9]
 refine ⟨fun i=>SL (Et ha (hx i)) (Et hb (hy i)),?_,?_,?_,?_⟩
 · nlinarith [qz hxb ha,qz hyb hb,
    oj (fun r :ℝ=>r*(s.b:ℝ)) hab]
 · nlinarith [qz hxj ha,qz hyj hb,
    oj (fun r :ℝ=>r*(s.j:ℝ)) hab]
 · nlinarith [qz hxt ha,qz hyt hb,
    oj (fun r :ℝ=>r*(s.t:ℝ)) hab]
 · nlinarith [qz hxh ha,qz hyh hb,
    oj (fun r :ℝ=>r*(h:ℝ)) hab]
private theorem dYz (F:eT 4) :
    ∃ v :Set iz,v.Finite∧alT F=xW ℝ v := by
  let KN (a : ↥F.support) :Set iz :=
    Set.univ.pi (fun j=>({0,(a.val j:ℝ)} : Set ℝ))
  let v := ⋃ a,KN a
  refine ⟨v,Set.finite_iUnion (fun a=>Set.Finite.pi (fun j=> by simp)),?_⟩
  have hc (a : ↥F.support) :xW ℝ (KN a) =
      {x :iz | ∀ j,0≤x j∧x j≤(a.val j:ℝ)} := by
    dsimp only [KN]
    rw [convexHull_pi]
    have hseg (j:Fin 4) :xW ℝ ({0,(a.val j:ℝ)} : Set ℝ) =
        Set.Icc 0 (a.val j:ℝ) := by
      rw [convexHull_pair,segment_eq_Icc (by positivity)]
    simp only [hseg,Set.pi_univ_Icc]
    ext x
    exact forall_and.symm
  unfold alT
  apply G5
  · apply Mk _ (WY _ _)
    rintro x ⟨a,ha,hx⟩
    have hx' : x∈xW ℝ (KN ⟨a,ha⟩) := by rwa [hc]
    exact Ml (Set.subset_iUnion KN ⟨a,ha⟩) hx'
  · apply Ml
    intro x hx
    obtain ⟨a,ha⟩:=Set.mem_iUnion.mp hx
    have hx' : x∈xW ℝ (KN a) :=VS ℝ _ ha
    rw [hc] at hx'
    exact ⟨a.val,a.property,hx'⟩
private def bLF (f :af 3) :Shape :=⟨f.totalDegree,qE f,f.degreeOf 2⟩
private theorem bvn (f :af 3) :
  DO (vY (fW f)) (bLF f) 0:= by
 classical
 intro a ha
 rw [vY,support_rename_of_injective (xI 3)] at ha
 obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ha
 have hb' : b∈f.support :=support_map_subset _ _ hb
 have htotal:b.degree≤f.totalDegree :=le_totalDegree hb'
 have hindex :b.sum (fun j a=>j.val*a)≤qE f :=
  zk (f := fun m=>m.sum (fun j a=>j.val*a)) hb'
 have htop:=monomial_le_degreeOf 2 hb'
 rw [Qx ,Kh] at htotal
 rw [Z0 _ _ (fun j=>p9 j.val),Kh] at hindex
 have h0:JQ pU b 0=b 0 :=
  Vz (xI 3) b 0
 have h1 :JQ pU b 1=b 1 :=
  Vz (xI 3) b 1
 have h2 :JQ pU b 2=b 2 :=
  Vz (xI 3) b 2
 have h3:JQ pU b 3=0 :=
  Finsupp.mapDomain_of_notMem_range b _ (fun ⟨j,hj⟩=>zm4 j hj)
 simp only [h0,h1,h2,h3,bLF,le_refl,and_true]
 exact ⟨htotal,by simpa using hindex,htop⟩
private theorem b1b {F:eT 4} {s :pC} {h:ℕ}
  (hs :DO F s h) :alT F⊆nD s h:= by
 apply Mk _ (cDT s h)
 rintro x ⟨a,ha,hx⟩
 obtain ⟨hb,hj,ht,hh⟩:=hs a ha
 have hb' : (a 0:ℝ)+a 1+a 2≤ s.b:= by exact_mod_cast hb
 have hj' : (a 1 :ℝ)+2*a 2≤ s.j:= by exact_mod_cast hj
 exact ⟨fun j=>(hx j).1,by linarith [(hx 0).2,(hx 1).2,(hx 2).2],
  by linarith [(hx 1).2,(hx 2).2],(hx 2).2.trans (by exact_mod_cast ht),
  (hx 3).2.trans (by exact_mod_cast hh)⟩
theorem b3f {f :af 3} (hf :f≠0) :OE (alT (vY (fW f))) := by
 have hg:fW f≠0:= by
  simpa only [fW,oq] using (RC _ Yk).ne hf
 have hF:vY (fW f)≠0:= by
  simpa only [vY,oq] using
   (rename_injective pU (xI 3)).ne hg
 obtain ⟨a,ha⟩:=support_nonempty.mpr hF
 refine ⟨dYz _,VS ℝ _ ⟨a,ha,fun _=>⟨t9,by positivity⟩⟩,?_⟩
 intro x hx
 have hc:=b1b (bvn f) hx
 exact yL (by simpa using hc.2.2.2.2) (hc.1 3)
end
end Qp
end
section
namespace Qp
noncomputable section
open aR oR yz MeasureTheory
open scoped BigOperators Pointwise
private theorem aXT {x A B:ℝ} (hx :0≤x) (hA:0≤A) (hB:0≤B)
   (h:x≤A+B) : ∃ y,0≤y∧y≤A∧0≤x - y∧x - y≤B:= by
 refine ⟨min x A,le_min hx hA,min_le_right _ _,sub_nonneg.mpr (min_le_left _ _),?_⟩
 rcases le_total x A with hle | hle
 · simpa only [min_eq_left hle,Ea] using hB
 · rw [min_eq_right hle]
   linarith
private theorem aTp:nD ⟨0,0,0⟩ 0=0:= by
 ext x
 rw [Set.mem_zero]
 constructor
 · intro hx
   obtain ⟨hx,hb,_,_,hh⟩:=hx
   have h0:=hx 0
   have h1 :=hx 1
   have h2 :=hx 2
   have h3:=hx 3
   norm_num at hb hh
   funext i
   change x i=0
   fin_cases i
   · change x 0=0
     linarith
   · change x 1=0
     linarith
   · change x 2=0
     linarith
   · change x 3=0
     linarith
 · rintro rfl
   simp [nD]
private theorem dEu {p q:pC} (hp:bF p) (hq:bF q)
   {h k :ℕ} {x :iz} (hx :x∈nD (p.plus q) (h+k)) :
   x∈nD p h+nD q k := by
 obtain ⟨hx,hb,hj,ht,hh⟩:=hx
 simp only [Shape.plus,Pk] at hb hj ht hh
 have hpj: (p.j:ℝ)≤p.b:= by exact_mod_cast hp.1
 have hqj: (q.j:ℝ)≤q.b:= by exact_mod_cast hq.1
 have hpt:2*(p.t:ℝ)≤p.j:= by exact_mod_cast hp.2
 have hqt:2*(q.t:ℝ)≤q.j:= by exact_mod_cast hq.2
 obtain ⟨z,hz,hzp,hz',hzq⟩:=aXT (hx 2) (by positivity) (by positivity) ht
 obtain ⟨v,hv,hvp,hv',hvq⟩:=aXT (hx 1)
   (show 0≤(p.j:ℝ) - 2*z by linarith)
   (show 0≤(q.j:ℝ) - 2*(x 2 - z) by linarith) (by linarith)
 obtain ⟨u,hu,hup,hu',huq⟩:=aXT (hx 0)
   (show 0≤(p.b:ℝ) - v - z by linarith)
   (show 0≤(q.b:ℝ)-(x 1 - v)-(x 2 - z) by linarith) (by linarith)
 obtain ⟨w,hw,hwp,hw',hwq⟩:=aXT (hx 3) (by positivity) (by positivity) hh
 let y :iz := ![u,v,z,w]
 have hy :y∈nD p h:= by
   refine ⟨?_,?_,?_,hzp,hwp⟩
   · intro i
     fin_cases i <;> assumption
   · change u+v+z≤(p.b:ℝ)
     linarith
   · change v+2*z≤(p.j:ℝ)
     linarith
 have hy' : x - y∈nD q k := by
   refine ⟨?_,?_,?_,hzq,hwq⟩
   · intro i
     fin_cases i <;> assumption
   · change (x 0 - u)+(x 1 - v)+(x 2 - z)≤(q.b:ℝ)
     linarith
   · change (x 1 - v)+2*(x 2 - z)≤(q.j:ℝ)
     linarith
 exact Set.mem_add.mpr ⟨y,hy,x - y,hy',by abel⟩
theorem dEt {p q:pC} (hp:bF p) (hq:bF q) (h k :ℕ) :
  nD (p.plus q) (h+k)=nD p h+nD q k := by
 apply G5 (fun _ hx=>dEu hp hq hx)
 intro x hx
 obtain ⟨y,⟨hy,hyb,hyj,hyt,hyh⟩,z,⟨hz,hzb,hzj,hzt,hzh⟩,rfl⟩:=Set.mem_add.mp hx
 refine ⟨fun i=>SL (hy i) (hz i),?_,?_,?_,?_⟩ <;>
  simp only [Av,Shape.plus,Pk] <;> linarith
private def xl {ι:Type} (S:aU ι) (p:ι→pC) :Shape :=
 ⟨∑ i∈S,(p i).b,∑ i∈S,(p i).j,∑ i∈S,(p i).t⟩
private theorem crv {ι:Type} (S:aU ι) (p:ι→pC)
   (hp : ∀ i,bF (p i)) :bF (xl S p) := by
 constructor
 · exact KI (fun i _=>(hp i).1)
 · change 2*(∑ i∈S,(p i).t) ≤ ∑ i∈S,(p i).j
   rw [Iw]
   exact KI (fun i _=>(hp i).2)
private theorem bOy {ι:Type} (S:aU ι) (p:ι→pC)
   (h:ι→ℕ) (hp : ∀ i,bF (p i)) :
   (∑ i∈S,nD (p i) (h i))=nD (xl S p) (∑ i∈S,h i) := by
 classical
 induction S using Cy with
 | empty=>simp only [xl,Finset.sum_empty,aTp]
 | @insert i S hi ih =>
   rw [yo hi,ih,← dEt (hp i) (crv S p hp)]
   simp only [xl,Shape.plus,yo hi]
end
end Qp
end
section
namespace aA1
noncomputable section
open aR oR Polynomial MvPolynomial
open dN (lX pK u6 aNw)
private theorem alJ {r :ℕ} (P:af r) (m:Fin r →₀ ℕ) :
   (DU P).coeff m=(P.coeff m).derivative := by
 classical
 rw [DU,NX]
 simp only [IT,G0]
 split_ifs with h
 · rfl
 · rw [MvPolynomial.notMem_support_iff.mp h,oq]
private theorem dMH (P:af 3) :
   lX (KX P)=KX (DU P) := by
 apply Kl
 intro m
 change (DU (KX P)).coeff m= _
 rw [alJ]
 change ((p6 pU P).coeff m).derivative =
   (p6 pU (DU P)).coeff m
 by_cases h : ∃ u:Fin 3 →₀ ℕ,u.mapDomain pU=m
 · obtain ⟨u,rfl⟩:=h
   rw [coeff_rename_mapDomain _ (xI 3),coeff_rename_mapDomain _ (xI 3),
     alJ]
 · rw [coeff_rename_eq_zero _ _ _ (fun u hu=>(h ⟨u,hu⟩).elim),
     coeff_rename_eq_zero _ _ _ (fun u hu=>(h ⟨u,hu⟩).elim),oq]
theorem aWm (P:af 3) :oZ 3 (KX P)=0:= by
 induction P using JM with
 | C a=>simp [KX]
 | add P Q hP hQ=>simp only [map_add,hP,hQ,add_zero]
 | mul_X P i h =>
   have hi:i.castSucc≠(3:Fin 4) :=zm4 i
   rw [lJ,show KX (lI i)=lI i.castSucc from rename_X _ _,
     Qy ,h,pderiv_X_of_ne hi,zero_mul,p9,wB]
theorem btu (P:af 3) :pK (KX P)=Xj P:= by
 unfold pK Xj D3
 rw [dMH,Kh]
 have hs (i:Fin 3) :oZ i.castSucc (KX P)=KX (oZ i P) :=
   pderiv_rename (xI 3) i P
 have hx (i:Fin 3) :KX (lI i)=lI i.castSucc:=rename_X _ _
 have hc (a :ℕ) :pQ (oY (a :ao))=(a :af 4) := by
   rw [Np,zh]
 simp only [hs,hx,hc,pG,lJ,uW]
 change _=KX (DU P)+MvPolynomial.X 1*KX (oZ 0 P) +
     2*lI 2*KX (oZ 1 P)+3*lI 3*KX (oZ 2 P)
 norm_num [Fin.val_succ,Fin.val_zero]
 ring
theorem b5I (f :af 3) :Bf (Xj f)=3*KY f := by
 have h3:oZ 3 (3:af 4)=0:=(oZ (R:=ao[X]) (3:Fin 4)).map_natCast 3
 simp [Bf ,Xj,aWm,h3,uz]
theorem bqC {a :ℕ} (ha :0<a) (hp:a<K1.p) : (a :ao)≠0:= by
 let _:u9 ao K1.p:=vw embed.injective K1.p
 intro hz
 exact (G4 hp) (Nat.le_of_dvd ha ((S1 ao K1.p a).mp hz))
private theorem three_ne_zero : (3:ao[X])≠0:= by
 have h:=bqC (a :=3) (by decide) (by decide)
 exact Polynomial.C_ne_zero.mpr h
@[simp] theorem bbM (P:af 3) (S:ao[X]) :cK (KX P) S=cK P S :=
  eval_rename _ _ _
theorem cKv (P:af 3) (S:ao[X]) :
  mD (cK P S)=cK (Xj P) S:= by
 let g:af 4 :=lI 3-MvPolynomial.C (jet S (3:Fin 4))
 have hg:cK g S=0:= by simp [cK,g]
 have hsep:Bf g=1 := by
  simp [Bf ,g]
 have h:=aNw g (KX P) S hg
 unfold u6 at h
 rw [hsep,show Bf (KX P)=0 from aWm P,
  p9,Gr,t6,btu,bbM,
  show cK (1 :af 4) S=1 by exact vk _,t6] at h
 exact h.symm
theorem b5D {f :af 3} {S:ao[X]} (h:cK f S=0) :
  cK (Xj f) S=0:= by
 rw [← cKv,h,oq]
private theorem gBr (f :af 3) :
  3*apE f = -pK (Xj f) := by
 let c:ao →+* af 4 :=(pQ:ao[X] →+* af 4).comp oY
 have h: (3:ao) * -(3:ao)⁻¹ = -1 := by
  have hn: (3:ao)≠0:=bqC (a :=3) (by decide) (by decide)
  rw [mul_neg,mul_inv_cancel₀ hn]
 change c 3*(c (-(3:ao)⁻¹)*_)= _
 rw [← qy ,← lJ,h,Il,vk]
 ring
private theorem duC (f :af 3) (b:af 4) (S:ao[X])
   (hf :cK f S=0) :
   cK (KY f*pK b+apE f*oZ 3 b) S =
     cK (KY f) S*mD (cK b S) := by
 have hpoly :u6 (Xj f) b =
     3*(KY f*pK b+apE f*oZ 3 b) := by
   rw [u6,b5I,Bf ,GF,← qy ,← qy ,
     gBr]
   ring
 have h:=aNw (Xj f) b S (b5D hf)
 rw [hpoly,b5I] at h
 let e :=nX (jet S:Fin 4→ao[X])
 change e (3*_)=e (3*_)*_ at h
 rw [lJ,lJ,uW,qy] at h
 exact mul_left_cancel₀ three_ne_zero h
private theorem duD (f :af 3) (S:ao[X]) :
  cK (pK (KY f)) S=mD (cK (KY f) S) := by
 rw [btu,← cKv,bbM]
private theorem dLx (a :ℕ) (u v :ao[X]) :
   u*mD (u^a*v)-(a :ao[X])*mD u*(u^a*v) =
     u^(a+1)*mD v := by
 cases a with
 | zero=>simp
 | succ a =>
   rw [Fz ,derivative_pow,Nat.succ_sub_one,GB u (a+1)]
   simp only [Np]
   push_cast
   rw [GB u a]
   ring
theorem cBt (f :af 3) (S:ao[X]) (hf :cK f S=0) (k :ℕ) :
    cK (YL f k) S=cK (KY f) S^k *
      ((mD (R:=ao))^[k]) (jet S (3:Fin 4)) := by
  induction k with
  | zero=>simp [YL,cK]
  | succ k ih =>
    let e :=nX (jet S:Fin 4→ao[X])
    change e (a5p f k (YL f k))= _
    unfold a5p
    rw [qx ,lJ,lJ,zh]
    change cK (KY f*pK (YL f k) +
        apE f*oZ 3 (YL f k)) S -
        (k :ao[X])*cK (pK (KY f)) S*cK (YL f k) S= _
    rw [duC _ _ _ hf,duD,ih,dLx,
      Rm]
theorem aNh (S:ao[X]) (k :ℕ) :
  mD (p5 k S)=oY ((k+1 :ℕ) :ao)*p5 (k+1) S:= by
 have h:=Zg (hasseDeriv_comp (R:=ao) 1 k) S
 simpa [hasseDeriv_one',zk4,Mj,Np,Nat.add_comm,add_mul] using h
end
end aA1
end
section
namespace abG
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
section Branch
variable {L:Type} [lV L]
private def bIC (y :Fin 4→L) :aud y →+* MZ y :=
 Localization.localRingHom (aJS y) (wN y) reduce rfl
private def cDE (g:Fin 4→Total L) (y :Fin 4→L) :
  bi0 g y →+* abV (H8 fun i=>reduce (g i)) y := by
 refine Yo _ (bIC y) ?_
 rw [zo0,H8,Ideal.span_le]
 rintro _ ⟨i,rfl⟩
 change bIC y (cy (Total L) (aud y) (g i)) ∈
  (H8 fun i=>reduce (g i)).map (cy (Affine L) (MZ y))
 rw [bIC,Localization.localRingHom_to_map]
 exact EP _ (sI (zWL i))
private theorem dAr (g:Fin 4→Total L) (y :Fin 4→L) (p:Total L) :
  cDE g y (aGS g y p) =
   aoK (H8 fun i=>reduce (g i)) y (reduce p) := by
 simp [cDE,aGS,aoK,bIC]
private theorem bXh (g:Fin 4→Total L) (p:Total L)
   (h:aNY g p=0) :
   ∃ d:oz L,d≠0∧C d*p∈H8 g:= by
 let:oD (Total L) (Affine (sU L)) :=Zf
 let S:=(oz L)⁰.map (C (σ:=Fin 4))
 have :RD S (Affine (sU L)) :=
   zEY (oz L)⁰ (sU L)
 have hmem:cy (Total L) (Affine (sU L)) p ∈
     (H8 g).map (cy (Total L) (Affine (sU L))) :=
   Ideal.Quotient.eq_zero_iff_mem.mp h
 obtain ⟨_,⟨d,hd,rfl⟩,hp⟩ :=
   (Te S _ (H8 g) p).mp hmem
 exact ⟨d,mem_nonZeroDivisors_iff_ne_zero.mp hd,hp⟩
theorem fV1 (g:Fin 4→Total L) (y :Fin 4→L)
   (hreg:IsSMulRegular (bi0 g y) (bBT g y))
   (p:Total L) (hp:aNY g p=0) :
   aoK (H8 fun i=>reduce (g i)) y (reduce p)=0:= by
 obtain ⟨d,hd0,hd⟩:=bXh g p hp
 obtain ⟨q,hfactor,hq⟩:=d.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hd0 (0:L)
 rw [Polynomial.C_0,Gr] at hfactor hq
 have hu:C q∉aJS y := by
   change reduce (C q)∉wN y
   rw [v9]
   rw [zIa,zTt] at hq
   simpa [reduce] using hq
 have hunit :qU (aGS g y (C q)) :=
   (IsLocalization.map_units (aud y) (⟨C q,hu⟩: (aJS y).primeCompl)).map
     (nI _)
 have hz :aGS g y (C d*p)=0 :=
   Ideal.Quotient.eq_zero_iff_mem.mpr (EP _ hd)
 have hz' : bBT g y ^d.rootMultiplicity 0 *
     (aGS g y (C q)*aGS g y p)=0:= by
   rw [hfactor] at hz
   simpa only [lJ,t7,qy ,bBT] using hz
 have hz'' : aGS g y (C q)*aGS g y p=0 :=
   (hreg.pow (d.rootMultiplicity 0)) (by simpa only [G9,p9] using hz')
 have hp' : aGS g y p=0 :=
   hunit.mul_left_cancel (by simpa only [p9] using hz'')
 rw [← dAr,hp',oq]
end Branch
section Rank
variable {L:Type} [lV L]
private theorem ar6:t8 (reduce (L:=L)) := by
 apply MvPolynomial.map_surjective
 intro a
 exact ⟨oY a,FR⟩
private theorem dLp (g:Fin 4→Total L) (a :oz L) :
    aNY g (C a) =
      cy (sU L) (aw3 g)
        (cy (oz L) (sU L) a) := by
  change nI _
    (ox (cy (oz L) (sU L)) (C a))= _
  rw [map_C]
  rfl
theorem de2 (g:Fin 4→Total L)
    {D:Type} [AddCommGroup D] [Module L D]
    (s :Affine L →ₗ[L] D) (hs :t8 s)
    (hrel : ∀ p,aNY g p=0→s (reduce p)=0)
    [qm (sU L) (aw3 g)] :
    pz L D ≤pz (sU L) (aw3 g) := by
  classical
  let n:=pz L D
  obtain ⟨b,hb⟩:=exists_linearIndependent_of_le_finrank (R:=L) (M:=D)
    (show n≤pz L D from t9)
  choose p hp using fun i=>(hs.comp ar6) (b i)
  let v (i:Fin n) :=aNY g (p i)
  let inc:=cy (oz L) (sU L)
  have hsum (a :Fin n→ oz L) :
      aNY g (∑ i,C (a i)*p i) = ∑ i,inc (a i)•v i:= by
    simp only [t5 ,lJ,dLp]
    apply sH rfl
    intro i _
    exact (TI (inc (a i)) (v i)).symm
  have hconstant (a :Fin n→ oz L) (ha : (∑ i,inc (a i)•v i)=0) (i:Fin n) :
      (a i).eval 0=0:= by
    have hz :=hrel _ ((hsum a).trans ha)
    have hrow (j:Fin n) :
        s (reduce (C (a j)*p j))=(a j).eval 0•b j:= by
      rw [lJ]
      change s (ox (y5 0) (C (a j))*reduce (p j))= _
      rw [map_C,MvPolynomial.C_mul',KA]
      rw [show s (reduce (p j))=b j from hp j]
      rfl
    simp only [t5 ,hrow] at hz
    exact Fintype.linearIndependent_iff.mp hb _ hz i
  suffices hv :X8 (sU L) v by
    simpa [n] using hv.fintype_card_le_finrank
  refine Fintype.linearIndependent_iff.mpr fun a ha j => ?_
  by_contra hj
  obtain ⟨den,hden⟩:=IsLocalization.exist_integer_multiples_of_finite (oz L)⁰ a
  choose c hc using hden
  have hden0:inc den≠0:= by
    simpa only [inc,oq] using
      (z7 (oz L) (sU L)).ne
        (mem_nonZeroDivisors_iff_ne_zero.mp den.prop)
  have hc' (i:Fin n) :inc (c i)=inc den*a i :=
    (hc i).trans (TI (den:oz L) (a i))
  have hcj:c j≠0:= by
    intro hz
    exact (FK hden0 hj) (by rw [← hc',hz,oq])
  have hc0: (∑ i,inc (c i)•v i)=0:= by
    simp only [hc',mul_smul,← UP ,ha,smul_zero]
  let P (d:ℕ) := ∃ a :Fin n→ oz L,
    a j≠0∧(a j).natDegree=d∧(∑ i,inc (a i)•v i)=0
  have hP : ∃ d,P d:=⟨(c j).natDegree,c,hcj,rfl,hc0⟩
  obtain ⟨a,haj,hdeg,ha0⟩:=Nat.find_spec hP
  have hdiv (i:Fin n) :pL∣a i:= by
    rw [zIa,zTt]
    exact hconstant a ha0 i
  choose a' ha' using hdiv
  have ha'j:a' j≠0:= by
    intro hz
    exact haj (by rw [ha' j,hz,p9])
  have hX:inc pL≠0:= by
    simpa only [inc,oq] using
      (z7 (oz L) (sU L)).ne Polynomial.X_ne_zero
  have ha'0: (∑ i,inc (a' i)•v i)=0:= by
    have h:inc pL•(∑ i,inc (a' i)•v i)=0:= by
      simp only [UP ,← mul_smul,← inc.map_mul,← ha',ha0]
    exact (smul_eq_zero.mp h).resolve_left hX
  have hmin:=Nat.find_min' hP (show P (a' j).natDegree from ⟨a',ha'j,rfl,ha'0⟩)
  rw [ha' j,Polynomial.natDegree_X_mul ha'j] at hdeg
  omega
end Rank
section IsolatedPoints
open scoped Function
variable {L:Type} [lV L]
private theorem a6D:qG (wN (L:=L)) := by
 intro x y h
 funext j
 have hx :lI j - C (x j)∈wN x := by
  rw [v9]
  simp
 rw [h,v9] at hx
 simpa [Ar,eq_comm] using hx
theorem eMc (I:c9 (Affine L)) (y :Fin 4→L)
   (hy :wN y∈I.minimalPrimes) :
   ∃ n:ℕ,wN y ^n≤oK (aoK I y).toRingHom:= by
 let T:=MZ y
 let J:=I.map (cy (Affine L) T)
 have hm:zR T∈J.minimalPrimes := by
   rw [show J=I.map (cy (Affine L) T) from rfl,
     zMt (wN y).primeCompl T,SU,
     znW T (wN y)]
   exact hy
 have :IsArtinianRing (T ⧸ J) :=
   ztC J hm
 obtain ⟨n,hn⟩:=IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
 refine ⟨n,fun p hp=>Ideal.Quotient.eq_zero_iff_mem.mpr (hn ?_)⟩
 rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (wN y) T,← Ideal.map_pow]
 exact EP _ hp
theorem eMd (I:c9 (Affine L)) (y :Fin 4→L)
    (n:ℕ) (hn:wN y ^n≤oK (aoK I y).toRingHom) :
    t8 (aoK I y) := by
  intro z
  obtain ⟨z,rfl⟩:=vH z
  obtain ⟨r,s,rfl⟩:=zcf (wN y).primeCompl z
  have hcop:IsCoprime (wN y) (n5 {(s :Affine L)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have he :=(xu : (wN y).IsMaximal).eq_of_le h le_sup_left
    have hle :n5 {(s :Affine L)} ≤
        wN y ⊔ n5 {(s :Affine L)} := le_sup_right
    have hm:=hle (Pf (s :Affine L))
    rw [← he] at hm
    exact s.prop hm
  obtain ⟨a,ha,b,hb,hab⟩:=(hcop.pow_left (m:=n)).exists
  obtain ⟨w,rfl⟩:=Ideal.mem_span_singleton.mp hb
  have hs :aoK I y (s :Affine L)*aoK I y w=1 := by
    have hz :aoK I y a=0:=hn ha
    simpa only [pG,lJ,hz,wB,vk] using oj (aoK I y) hab
  have hr :aoK I y r =
      nI _ (zzm (MZ y) r s) *
        aoK I y (s :Affine L) := by
    let mk :=nI (I.map (cy (Affine L) (MZ y)))
    change mk (cy (Affine L) (MZ y) r) =
      mk (zzm (MZ y) r s) *
        mk (cy (Affine L) (MZ y) s)
    rw [← lJ,zOg]
  refine ⟨r*w,?_⟩
  rw [lJ,hr,qy ,hs,Dw]
theorem eMy (I:c9 (Affine L)) {ι:Type} [Fintype ι]
   (y :ι→Fin 4→L) (hy :qG y)
   (hmin : ∀ i,wN (y i)∈I.minimalPrimes) :
   t8 (Kz fun i=>aoK I (y i)) := by
 classical
 choose n hn using fun i=>eMc I (y i) (hmin i)
 intro z
 choose r hr using fun i=>eMd I (y i) (n i) (hn i) (z i)
 have hcop:Pairwise (IsCoprime on fun i=>wN (y i)^n i) := by
   intro i j hij
   have hne :wN (y i)≠wN (y j) :=
     fun he=>hij (hy (a6D he))
   exact (Ideal.isCoprime_of_isMaximal hne).pow_left.pow_right
 obtain ⟨p,hp⟩:=Ideal.exists_forall_sub_mem_ideal hcop r
 refine ⟨p,funext fun i => ?_⟩
 change aoK I (y i) p=z i
 rw [← hr i,← Ar,← qx]
 exact hn i (hp i)
end IsolatedPoints
end
end abG
end
section
namespace bjy
noncomputable section
open aR oR we aeC Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem cSH :G6 (af 3) (eT 3) := by
 have :G6 ao[X] aGn :=
  IsLocalization.flat aGn (GY ao[X])
 have :G6 ao[X] cH :=
  Module.Flat.trans ao[X] aGn cH
 have h:Algebra.IsPushout ao[X] (af 3) cH (eT 3) :=xu
 exact Module.Flat.isBaseChange ao[X] (af 3) cH (eT 3) h.out
private theorem bLG (b:af 3) :
  cy (af 3) (eT 3) b=fW b:= by
 exact oj (fun g=>ox g b)
  (S2 ao[X] aGn cH)
@[simp] private theorem alJ (b:af 3) (m:Fin 3 →₀ ℕ) :
    (DU b).coeff m=mD (b.coeff m) := by
  classical
  rw [DU,NX]
  simp only [IT,G0]
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,oq]
private theorem a2D (a b:af 3) :
  DU (a+b)=DU a+DU b:= by
 ext m
 simp
private theorem dL8 (a b:af 3) :
  DU (a*b)=DU a*b+a*DU b:= by
 classical
 apply Kl
 intro m
 rw [alJ]
 change mD ((a*b).coeff m) =
  (DU a*b).coeff m+(a*DU b).coeff m
 simp only [alJ,MvPolynomial.coeff_mul,t5 ,Fz ,
  zm]
theorem bOL (f a b:af 3) :
  Ev f (a+b)=Ev f a+Ev f b:= by
 simp only [Ev,D3,a2D,pG]
 ring
theorem bhP (f a b:af 3) :
  Ev f (a*b)=Ev f a*b+a*Ev f b:= by
 simp only [Ev,D3,dL8,Qy]
 ring
private theorem dgI (f :af 3) :Ev f f=0:= by
 unfold Ev separant
 exact sub_eq_zero.mpr (uz _ _)
end
end bjy
end
section
namespace aY0
noncomputable section
open aaq as3 MvPolynomial
abbrev nU:=we.cH
abbrev N9:=Fin 4→aU zP.Exponent
private abbrev a3r :Degree ≃+ (Fin 4 →₀ ℕ) :=
 Finsupp.addEquivFunOnFinite.symm
private def aaB (A:N9) : (Slot A →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
 t4 fun v=>v.2.val
private def XE (A:N9) : (Slot A →₀ ℕ) →+ ((Fin 4 ⊕ Fin 4) →₀ ℕ) :=
 Finsupp.sumFinsuppAddEquivProdFinsupp.symm.toAddMonoidHom.comp
  ((a3r.toAddMonoidHom.comp (t4 (jT A))).prod (aaB A))
private theorem bxp {A:N9} {e f :Slot A →₀ ℕ} :
    XE A e=XE A f ↔
      t4 (jT A) e=t4 (jT A) f ∧
        aaB A e=aaB A f := by
  change Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_,_) =
    Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_,_)↔_
  rw [zNr,Prod.ext_iff]
  change (a3r (t4 (jT A) e) =
    a3r (t4 (jT A) f)∧_)↔_
  rw [zNr]
private def avB {R σ τ:Type*} [nq R] (w: (σ →₀ ℕ) →+ (τ →₀ ℕ)) :
  lz σ R →ₐ[R] lz τ R :=
 AddMonoidAlgebra.mapDomainAlgHom R R w
private theorem ajT {R σ τ:Type*} [nq R]
  (w: (σ →₀ ℕ) →+ (τ →₀ ℕ)) (e :σ →₀ ℕ) (c:R) :
  avB w (ov e c)=ov (w e) c:= by
 change AddMonoidAlgebra.mapDomain w (AddMonoidAlgebra.single e c)= _
 rw [AddMonoidAlgebra.mapDomain_single]
 rfl
def Nb (A:N9) (R:Type*) [nq R] :c9 (lz (Slot A) R) :=
  n5 {p | ∃ e f :Slot A →₀ ℕ,XE A e=XE A f ∧
    p=ov e 1 - ov f 1}
theorem bsj {R S:Type*} [nq R] [nq S]
   (A:N9) (g:R →+* S) :
   (Nb A R).map (ox g)=Nb A S:= by
 rw [Nb,zc,Nb]
 congr 1
 ext p
 constructor
 · rintro ⟨_,⟨e,f,h,rfl⟩,rfl⟩
   exact ⟨e,f,h,by simp⟩
 · rintro ⟨e,f,h,rfl⟩
   exact ⟨_,⟨e,f,h,rfl⟩,by simp⟩
private theorem brR {A:N9} {R τ:Type*} [nq R]
   (s :Set (Slot A →₀ ℕ)) (w: (Slot A →₀ ℕ)→(τ →₀ ℕ))
   (h : ∀ e∈s,∀ f∈s,w e=w f→XE A e=XE A f) :
   ∃ l:lz τ R →ₗ[R] (lz (Slot A) R ⧸ Nb A R),
     ∀ e∈s,l (ov (w e) 1)=nI _ (ov e 1) := by
 classical
 let J:=Nb A R
 let g (a :τ →₀ ℕ) :lz (Slot A) R ⧸ J :=
   if ha : ∃ e∈s,w e=a then nI J (ov ha.choose 1) else 0
 refine ⟨(FU τ R).constr R g,fun e he => ?_⟩
 change (FU τ R).constr R g ((FU τ R) (w e))= _
 rw [Module.Basis.constr_basis]
 let he' : ∃ f∈s,w f=w e :=⟨e,he,rfl⟩
 dsimp only [g]
 rw [dite_eq_left he',Mz]
 exact sI ⟨_,_,h _ he'.choose_spec.1 e he he'.choose_spec.2,rfl⟩
private theorem bxs (A:N9) (R:Type*) [nq R] :
   oK (avB (R:=R) (XE A)).toRingHom=Nb A R:= by
 let J:=Nb A R
 let φ:=avB (R:=R) (XE A)
 obtain ⟨l,hl⟩:=brR (R:=R) z9 (XE A)
   (fun _ _ _ _ h=>h)
 have hfac:l.comp φ.toLinearMap=(Ee R J).toLinearMap:= by
   apply (FU (Slot A) R).ext
   intro e
   simp only [coe_basisMonomials,LinearMap.comp_apply,FV]
   rw [show φ (ov e 1)=ov (XE A e) 1 from ajT _ _ _]
   exact hl e (Set.mem_univ _)
 apply yL
 · intro p hp
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   have h:=Nr hfac p
   change l (φ p)=nI J p at h
   change φ p=0 at hp
   simpa [hp] using h.symm
 · apply Ideal.span_le.mpr
   rintro _ ⟨e,f,h,rfl⟩
   change avB (R:=R) (XE A) (ov e 1 - ov f 1)=0
   rw [qx ,ajT,ajT,h,Ea]
private theorem boT (A:N9) :
  ew A=avB (aaB A) := by
 apply Dv
 intro v
 rw [ew,wY ,lI,ajT,aaB,LP ,one_smul]
theorem ce5 (A:N9) :
    Se A 0=Nb A (zP.fZ A) := by
  classical
  have hprefix :mo A 0 = ⊥ := by simp [mo]
  apply yL
  · apply Ideal.span_le.mpr
    rintro p ⟨⟨d,hd⟩,hp⟩
    have hz :ew A p=0:= by simpa [hprefix] using hp
    let J:=Nb A (zP.fZ A)
    obtain ⟨l,hl⟩:=brR (R:=zP.fZ A)
      {e | t4 (jT A) e=d} (aaB A)
      (fun e he f hf h=>bxp.mpr ⟨he.trans hf.symm,h⟩)
    let q:=Ee (zP.fZ A) J
    have hfac:l (ew A p)=q p:= by
      calc
        l (ew A p)=l (ew A (∑ e∈p.support,ov e (p.coeff e))) :=
          oj (fun r=>l (ew A r)) p.as_sum
        _=q (∑ e∈p.support,ov e (p.coeff e)) := by
          simp only [t5]
          apply sH rfl
          intro e he
          rw [show ov e (p.coeff e)=p.coeff e•ov e 1 by
            simp [smul_monomial]]
          simp only [KA,boT,ajT,
            hl e (hd (mem_support_iff.mp he))]
          rfl
        _=q p:=(oj q p.as_sum).symm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p=0
    rw [← hfac,hz,oq]
  · apply Ideal.span_le.mpr
    rintro _ ⟨e,f,h,rfl⟩
    obtain ⟨hd,ha⟩:=bxp.mp h
    apply sI
    refine ⟨⟨_,Submodule.sub_mem (Kx A (t4 (jT A) e)) ?_ ?_⟩,?_⟩
    · exact UZ _ _ _ rfl
    · exact UZ _ _ _ hd.symm
    · rw [hprefix,Ideal.mem_bot,qx ,boT,
        ajT,ajT,ha,Ea]
abbrev aqn (A:N9) :=lz (Slot A) nU ⧸ Nb A nU
instance (A:N9) :HZ (aqn A) := by
 have : (Nb A nU).IsPrime := by
  rw [← bxs]
  exact zgL _
 infer_instance
theorem b9p {A:N9} (v :Slot A) :
  nI (Nb A nU) (lI v)≠0:= by
 intro h
 have hm:=Ideal.Quotient.eq_zero_iff_mem.mp h
 rw [← bxs] at hm
 change avB (R:=nU) (XE A) (lI v)=0 at hm
 rw [lI,ajT,monomial_eq_zero] at hm
 exact one_ne_zero hm
end
end aY0
end
section
namespace ac0
noncomputable section
open MvPolynomial
open scoped BigOperators
variable {k σ:Type} [lV k] [vj σ]
def P5 (a :σ→k) :lz σ k := by
 classical
 letI:=Fintype.ofFinite σ
 exact ∑ i,pQ (a i)*lI i
def auW (I:c9 (lz σ k)) (a :σ→k) (t:k) :
    c9 (lz σ k) :=
  I ⊔ n5 {P5 a-MvPolynomial.C t}
def projection (I:c9 (lz σ k)) (a :σ→k) :
    oz k →ₐ[k] (lz σ k ⧸ I) :=
  Polynomial.aeval (nI I (P5 a))
def cxE (I:c9 (lz σ k)) (hI:I.IsPrime) (a :σ→k) :Prop :=
  letI:I.IsPrime :=hI
  let u:vh (lz σ k ⧸ I) :=
    cy (lz σ k ⧸ I) _ (nI I (P5 a))
  VO k u ∧
    N0 (NY k ({u} : Set _))
      (vh (lz σ k ⧸ I))
end
end ac0
end
section
namespace abG
noncomputable section
open we zP MvPolynomial
open scoped TensorProduct
private abbrev rS (A:Fin 4→aU Exponent) :=Σ i:Fin 4,↥(A i)
private def center {A:Fin 4→aU Exponent} (f :Fin 4→eT 4)
   (a :rS A) :cH :=
 (f a.1).coeff a.2.1
private def aCF (A:Fin 4→aU Exponent) (f :Fin 4→eT 4)
  (a :rS A) :oz (fZ A) :=
 oY (cy cH (fZ A) (center f a)) +
  pL*oY (cy (xB A) (fZ A) (lI a))
def ahx (A:Fin 4→aU Exponent) (f :Fin 4→eT 4)
    (i:Fin 4) :Total (fZ A) :=
  ∑ a : ↥(A i),ov a.1 (aCF A f ⟨i,a⟩)
private def ajl (A:Fin 4→aU Exponent) (f :Fin 4→eT 4) :
  xB A →+* oz (fZ A) :=
 eval₂Hom (Polynomial.C.comp (cy cH (fZ A))) (aCF A f)
private theorem bXC (A:Fin 4→aU Exponent)
    (f :Fin 4→eT 4) :qG (ajl A f) := by
  let shift:xB A →ₐ[cH] xB A :=
    oy fun a=>C (center f a)+MvPolynomial.X a
  let unshift:xB A →ₐ[cH] xB A :=
    oy fun a=>lI a - C (center f a)
  have hshift:unshift.comp shift=AlgHom.id cH _:= by
    apply Dv
    intro a
    simp [shift,unshift,F9]
  have hleft:Function.LeftInverse unshift shift:= fun p=>AlgHom.congr_fun hshift p
  have heval : (y5 1).comp (ajl A f) =
      (cy (xB A) (fZ A)).comp shift.toRingHom:= by
    apply Mw
    · intro c
      change Polynomial.eval 1 (ajl A f (C c)) =
        cy (xB A) (fZ A) (shift (C c))
      rw [ajl,eval₂Hom_C,Gn,FR,algHom_C]
      exact zg cH (xB A) (fZ A) c
    · intro a
      change Polynomial.eval 1 (ajl A f (lI a)) =
        cy (xB A) (fZ A)
          (oy (fun b=>C (center f b)+MvPolynomial.X b) (lI a))
      rw [ajl,MvPolynomial.eval₂Hom_X',wY]
      simp only [aCF,Polynomial.eval_add,Polynomial.eval_mul,FR,
        Polynomial.eval_X,t6,pG]
      rw [zg cH (xB A) (fZ A)]
      rfl
  intro p q hpq
  apply hleft.injective
  apply z7 (xB A) (fZ A)
  exact (Gi heval p).symm.trans
    ((oj (y5 1) hpq).trans (Gi heval q))
private def aNZ (A:Fin 4→aU Exponent) (f :Fin 4→eT 4) :
  fZ A →+* sU (fZ A) :=
 IsFractionRing.lift (g:=(cy (oz (fZ A))
    (sU (fZ A))).comp (ajl A f))
  ((z7 (oz (fZ A)) (sU (fZ A))).comp
    (bXC A f))
private theorem b4z (A:Fin 4→aU Exponent)
    (f :Fin 4→eT 4) (a :rS A) :
    aNZ A f (cy (xB A) (fZ A) (lI a)) =
      cy (oz (fZ A)) (sU (fZ A))
        (aCF A f a) := by
  rw [aNZ,IsFractionRing.lift_algebraMap]
  simp [ajl]
theorem bZ0 (A:Fin 4→aU Exponent) (f :Fin 4→eT 4)
  (hs : ∀ i,(f i).support⊆A i) :
  H8 (fun i=>reduce (ahx A f i))=gN (fZ A)
    (ke f) := by
 classical
 have hrow (i:Fin 4) :reduce (ahx A f i) =
    ox (cy cH (fZ A)) (f i) := by
  have hsum: (∑ a∈A i,ov a ((f i).coeff a))=f i:= by
    rw [← Finset.sum_subset (hs i),← MvPolynomial.as_sum]
    intro a _ ha
    rw [notMem_support_iff.mp ha,monomial_zero]
  conv_rhs=>rw [← hsum]
  simp [reduce,ahx,aCF,center]
  exact zKB (A i)
    (fun a=>ov a (cy cH (fZ A) ((f i).coeff a)))
 simp only [H8,gN,ke,zc,← Xp,hrow]
def cC2 {k L:Type} [lV k] [lV L] [oD k L]
    (I:c9 (Affine k)) :
    L ⊗[k] (Affine k ⧸ I) ≃ₐ[L]
      Affine L ⧸ I.map (ox (cy k L)) := by
  let e :=Wm (σ:=Fin 4) k L
  refine (Algebra.TensorProduct.tensorQuotientEquiv L (Affine k) L I).trans
    (zpY _ _ e ?_)
  change I.map (ox (cy k L)) =
    (I.map (Algebra.TensorProduct.includeRight (A:=L)).toRingHom).map
      e.toRingEquiv.toRingHom
  rw [Oc]
  congr 1
  apply Ef
  intro p
  change ox (cy k L) p=e (1 ⊗ₜ[k] p)
  simp [e]
private theorem bGF {k L:Type} [lV k] [lV L] [oD k L]
   (I:c9 (Affine k)) [qm k (Affine k ⧸ I)] :
   qm L (Affine L ⧸ I.map (ox (cy k L))) ∧
   pz L (Affine L ⧸ I.map (ox (cy k L))) =
     pz k (Affine k ⧸ I) := by
 let e :=(cC2 (L:=L) I).toLinearEquiv
 exact ⟨Module.Finite.equiv e,e.finrank_eq.symm.trans Module.finrank_baseChange⟩
theorem bZZ (A:Fin 4→aU Exponent) (f :Fin 4→eT 4)
    (hf :qm (fZ A) (HG A)) :
    qm (sU (fZ A)) (aw3 (ahx A f)) ∧
    pz (sU (fZ A)) (aw3 (ahx A f)) =
      pz (fZ A) (HG A) := by
  let:oD (fZ A) (sU (fZ A)) :=
    (aNZ A f).toAlgebra
  have hrow (i:Fin 4) :
      ox (cy (fZ A) (sU (fZ A)))
          (ve A i)=bC (ahx A f i) := by
    change ox (aNZ A f) (ve A i)= _
    simp [ve,bC,ahx,b4z]
  have hid :
      (n5 (qJ (ve A))).map
          (ox (cy (fZ A) (sU (fZ A)))) =
        (H8 (ahx A f)).map bC:= by
    simp only [H8,zc,← Xp,hrow]
  have :=hf
  have hbase :=bGF (L:=sU (fZ A))
    (n5 (qJ (ve A)))
  rw [hid] at hbase
  exact hbase
end
end abG
end
section
namespace aA1
noncomputable section
open aR oR we Polynomial
open scoped BigOperators
theorem Yk :qG qY :=
 (cy aGn cH).injective.comp (z7 _ _)
@[simp] theorem aNx {r :ℕ} (S:ao[X]) (P:af r) :
    nX (zq S) (fW P)=qY (cK P S) :=
  (WW qY (jet S) P).symm
theorem beh (P:af 3) :fW (KX P)=vY (fW P) :=
 MvPolynomial.map_rename qY pU P
theorem bHp (f :af 3) :fW (Xj f)=graph f := by
 unfold Xj graph
 change ox qY (_+_)= _
 rw [pG,lJ,lJ,MvPolynomial.map_X,uW]
 exact congrArg₂ (· + 3*lI 3 * ·) (beh _) (beh _)
private theorem bHj {a :ao[X]} (h:a≠0) :qY a≠0:= by
 intro ha
 exact h (Yk (ha.trans qY.map_zero.symm))
private theorem egh: (3:cH)≠0:= by
 have h:=bqC (a :=3) (by decide) (by decide)
 intro hz
 apply h
 apply (cy ao cH).injective
 rw [zh,oq]
 exact hz
theorem b5C {f :af 3} {S:ao[X]} (hS:qg 2 f S) :
    JZ f (zq S)=zq (n:=4) S:= by
  funext i
  refine WK ?_ (fun j => ?_) i
  · have hs :qY (cK (separant f) S)≠0:=bHj hS.2
    have h:=oj qY (b5D hS.1)
    change qY (nX (jet S:Fin 4→ao[X]) (_+_))= _ at h
    simp only [pG,lJ,uW,oq,xm,
      show ∀ p:af 3,nX (jet S) (KX p)=cK p S from
        fun p=>bbM p S] at h
    unfold JZ
    rw [Dz ,aNx,aNx,
      div_eq_iff (FK egh hs)]
    change -qY (cK (D3 f) S) =
      qY (jet S (3:Fin 4))*(3*qY (cK (separant f) S))
    linear_combination -h
  · exact FQ _ _ _
private theorem ekn {f :af 3} {S:ao[X]} (hS:qg 2 f S)
  {P:eT 4} (hP:P∈rP f) :
  nX (zq S) P=0:= by
 let e :=nX (zq (n:=4) S)
 have hJ:rP f≤oK e := by
  rw [rP,Ideal.span_le]
  intro p hp
  change e p=0
  simp only [Sd ,Ww] at hp
  rcases hp with rfl | rfl
  · simp [e,← beh,bbM,hS.1]
  · simp [e,← bHp,b5D hS.1]
 exact hJ hP
private theorem gmv (S:ao[X]) (k :ℕ) (hk :k+3<K1.p) :
   oY (bhU k)*((mD (R:=ao))^[k]) (jet S (3:Fin 4)) =
    p5 (k+3) S:= by
 induction k with
 | zero=>simp [bhU,jet]
 | succ k ih =>
   have he :=oj mD (ih (by omega))
   rw [Fz ,derivative_C,zero_mul,wB,aNh] at he
   rw [bhU,lJ,uz (oY (bhU k)),qy ,
    Rm,he,← qy ,← lJ,
    inv_mul_cancel₀ (bqC (a :=k+4) (by omega) (by omega)),vk,t6]
private theorem duB (f :af 3) (S:ao[X]) (hf :cK f S=0)
   (j:ℕ) (hj:j<K1.p) :
   cK (su f j) S=cK (KY f) S^(j-3)*p5 j S:= by
 have hVar (i:Fin 4) :cK (lI i) S=p5 i.val S :=
   xm i
 unfold su
 split_ifs with h
 · rw [hVar,show j-3=0 by omega,pow_zero,t6]
 · let e :=nX (jet S:Fin 4→ao[X])
   change e (pQ _ *_)= _
   rw [lJ,Fa]
   change oY _ *cK (YL f (j-3)) S= _
   rw [cBt _ _ hf,mul_left_comm,gmv S (j-3) (by omega),
     z8  (by omega :3≤j)]
private theorem cBr (f :af 3) (S:ao[X]) (hf :cK f S=0)
  (d j:ℕ) (hd:j-3≤d) (hj:j<K1.p) :
  cK (bf4 f d j) S=cK (separant f) S^d*p5 j S:= by
 let e :=nX (jet S:Fin 4→ao[X])
 change e (_^_ *su f j)= _
 rw [lJ,t7]
 change cK (KY f) S^_ *cK (su f j) S= _
 rw [duB f S hf j hj,← qy ,← pow_add,z8 hd,bbM]
private theorem gAO (S:ao[X]) (j:ℕ) :
   (xL centre (S.map (cy ao cH))).coeff j =
     qY (p5 j S) := by
 rw [SW,NZ,zhI]
 have he :WD (cy ao cH) centre=qY:= by
   apply Pv
   · intro a
     change (oY a).eval₂ (cy ao cH) centre=qY (oY a)
     rw [eval₂_C]
     exact zg ao ao[X] cH a
   · exact eval₂_X _ _
 exact Gi he _
private theorem dgY (S:ao[X]) (m:ℕ) (hS:S.natDegree< m)
    (i:ℕ) :
    (∑ j:Fin m,((pL-Polynomial.C centre)^j.val).coeff i *
      qY (p5 j.val S))=cy ao cH (S.coeff i) := by
  let P:=S.map (cy ao cH)
  have hn: (xL centre P).natDegree< m:= by
    rw [SC]
    exact Polynomial.natDegree_map_le.trans_lt hS
  have Hd: (xL centre P).degree<(m:WithBot ℕ) :=
    Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hn)
  have hsum: (∑ j:Fin m,oY ((xL centre P).coeff j.val) *
      (pL-Polynomial.C centre)^j.val)=P:= by
    exact (Polynomial.sum_fin
      (fun j (a :cH)=>oY a*(pL-Polynomial.C centre)^j)
      (fun _=> by rw [Polynomial.C_0,zero_mul]) Hd).trans (Polynomial.sum_taylor_eq P centre)
  calc
    _ = ∑ j:Fin m,(oY ((xL centre P).coeff j.val) *
        (pL-Polynomial.C centre)^j.val).coeff i:= by
      apply sH rfl
      intro j _
      rw [coeff_C_mul,gAO,uz]
    _=P.coeff i:= by rw [← finsetSum_coeff,hsum]
    _ = _:=Eg (cy ao cH) i
private theorem cte {f :af 3} {S:ao[X]} (hf :cK f S=0)
  (k :ℕ) (hk :S.natDegree-3<k) :
  cK (YL f k) S=0:= by
 rw [cBt f S hf,iterate_derivative_eq_zero,p9]
 exact (natDegree_hasseDeriv_le S 3).trans_lt hk
private theorem bTV {f old:af 3} {P:eT 4} {S:ao[X]}
  (hS:qg 2 f S) (hP:ag9 f old P)
  (hzero :nX (zq S) P=0) :cK old S=0:= by
 obtain ⟨a,b,c,hc,h⟩:=hP
 have he :=ekn hS h
 simp only [lJ,t7,qx ,hzero,p9,Fa ,
  ← beh,aNx,bbM,zero_sub] at he
 have hs :qY (cK (separant f) S)≠0 :=
  bHj hS.2
 have hq:qY (cK old S)=0:= by
  simpa [mul_eq_zero,Du _ hs,hc] using he
 exact Yk (by simpa only [oq] using hq)
end
end aA1
end
section
namespace ac0
noncomputable section
open MvPolynomial
open scoped BigOperators Function
variable {k σ:Type} [lV k] [vj σ]
theorem bxW (a :σ→k) (t:k) :
  (P5 a-MvPolynomial.C t).totalDegree≤1 := by
 classical
 apply (ZJ _ _).trans
 unfold P5
 apply SM
 intro i _
 exact (yU _ _).trans (by rw [UY ,RJ,wB])
theorem aYo {I:c9 (lz σ k)} {a z :σ→k} {t:k} :
  z∈qM k (auW I a t)↔z∈qM k I∧oy z (P5 a)=t:= by
 rw [auW,mem_zeroLocus_sup_span_singleton_iff,qx ,aeval_C]
 exact and_congr_right fun _=>Ar
theorem bJD [G8 k] (J:c9 (lz σ k))
    (hJ: (p7 J).natDegree=0) (hrad:J.IsRadical) :
    ((qM k J).ncard:ℚ)=uJ J:= by
  classical
  let:qm k (lz σ k ⧸ J) :=
    natDegree_affineHilbertPolynomial_eq_zero_iff.mp hJ
  let Ju:=qM k J
  have hZ:Ju.Finite :=finite_zeroLocus_of_finite_quotient J
  let:Fintype Ju:=hZ.fintype
  let e (x :Ju) :lz σ k →ₐ[k] k :=oy x.val
  let M (x :Ju) :=oK (e x)
  have hpair :Pairwise (IsCoprime on M) := by
    intro x y hxy
    obtain ⟨i,hi⟩ : ∃ i,y.val i≠x.val i:= by
      by_contra! he
      exact hxy (vG (funext he).symm)
    let u:lz σ k :=
      pQ ((y.val i - x.val i)⁻¹)*(lI i-MvPolynomial.C (x.val i))
    have hx :e x u=0:= by simp [e,u]
    have hy :e y u=1 := by
      simp [e,u,inv_mul_cancel₀ (sub_ne_zero.mpr hi)]
    refine Ideal.isCoprime_iff_exists.mpr ⟨u,RingHom.mem_ker.mpr hx,1 - u,?_,by ring⟩
    exact RingHom.mem_ker.mpr (by rw [qx ,vk,hy,Ea])
  let φ:=Kz e
  have hker :oK φ=J:= by
    calc
      _=uh k Ju:= by
        ext p
        rw [zS ,Ok]
        exact ⟨fun h x hx=>wR h (⟨x,hx⟩:Ju),fun h=>funext fun x=>h x.val x.property⟩
      _=J:=(vanishingIdeal_zeroLocus_eq_radical J).trans (Ideal.radical_eq_iff.mpr hrad)
  have hsurj:t8 φ:= by
    intro d
    obtain ⟨q,hq⟩:=Ideal.quotientInfToPiQuotient_surj hpair
      (fun x=>nI (M x) (pQ (d x)))
    obtain ⟨p,rfl⟩:=vH q
    refine ⟨p,funext fun x => ?_⟩
    have hx :=oj (TZ (e x)) (wR hq x)
    rw [Ideal.quotientInfToPiQuotient_mk',Kv,Kv] at hx
    simpa [φ,e] using hx
  let E :=(Ideal.quotientEquivAlgOfEq k hker.symm).trans (Qw hsurj)
  rw [affineDegree_eq_finrank,E.toLinearEquiv.finrank_eq,Module.finrank_fintype_fun_eq_card]
  exact_mod_cast (Nat.card_eq_fintype_card (α:=Ju))
end
end ac0
end
section
namespace ana
noncomputable section
open K1 aR oR Polynomial PolynomialDifferential
open scoped BigOperators nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev Tv :=vh ao[X]
abbrev asx :ao[X] →+* Tv :=cy ao[X] Tv
abbrev constants :ao →+* Tv :=asx.comp oY
abbrev center :Tv :=asx pL
def flatten (f :af 2) :DifferentialPolynomial ao 1 :=
 (MvPolynomial.optionEquivRight ao (Fin 2)).symm f
def bY (f :af 2) :DifferentialPolynomial Tv 1 :=
 ox constants (flatten f)
def u7 (f :af 2) :lz (Fin 2) Tv :=ox asx f
def Ia (S:ao[X]) :Fin 2→Tv :=
 polynomialJet center (S.map constants)
theorem bhW:qG asx :=z7 _ _
private theorem auQ (S:ao[X]) : (S.map constants).eval center=asx S:= by
 rw [zhI]
 change WD constants center S=asx S
 congr 1
 apply Pv
 · intro a
   simp [constants]
 · simp [center]
theorem cZT (S:ao[X]) (i:Fin 2) :
  Ia S i=asx (jet S i) := by
 change (p5 i.val (S.map constants)).eval center= _
 rw [NZ,auQ]
 rfl
theorem b8P:qG Ia := by
 intro S T heq
 have h:=wR heq (0:Fin 2)
 simpa only [cZT,jet,Fin.val_zero,Polynomial.hasseDeriv_zero',
  bhW.eq_iff] using h
theorem bT0 (f :af 2) (S:ao[X]) :
  oy (Ia S) (u7 f)=asx (cK f S) := by
 have hm:Ia S=asx ∘ jet S:=funext (cZT S)
 rw [u7,x7,hm,cK,← WW]
theorem cbT {f :af 2} (hf :f≠0) :u7 f≠0 :=
 fun h=>hf ((RC _ bhW) (h.trans (oq _).symm))
theorem cbW {f :af 2} (hf :ze f) (hp:0<f.degreeOf 1) :
   (n5 {u7 f}).IsPrime := by
 let M:=(ao[X]⁰).map (pQ (σ:=Fin 2))
 have hI: (n5 {f}).IsPrime :=
   (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
 have hdis :Disjoint (M:Set (af 2)) (n5 {f} : c9 (af 2)) := by
   rw [Set.disjoint_left]
   rintro _ ⟨a,ha,rfl⟩ hd
   obtain ⟨q,hq⟩:=Ideal.mem_span_singleton.mp hd
   have ha' : a≠0:=nonZeroDivisors.ne_zero ha
   have hq' : q≠0:= by
     intro h
     exact ha' (by simpa [h] using hq)
   have hh:=oj (MvPolynomial.degreeOf (1 :Fin 2)) hq
   rw [MvPolynomial.degreeOf_C,MvPolynomial.degreeOf_mul_eq hf.ne_zero hq'] at hh
   omega
 have h:=VH M
   (lz (Fin 2) Tv) (n5 {f}) hI hdis
 simpa only [u7,WX ,zc,Set.image_singleton] using h
private theorem aQw (f :af 2) (S:ao[X]) :
  differentialSpecialization (flatten f) S=cK f S:= by
 let x :zi (Fin 2)→ao[X] := fun
  | none=>Polynomial.X
  | some i=>jet S i
 have h:=MvPolynomial.aeval_optionEquivRight_symm (R:=ao) x f
 have hx :x none=Polynomial.X:=rfl
 have hj: (fun j=>x (some j))=jet S:=rfl
 rw [hx,hj,Polynomial.aeval_X_left] at h
 rw [show (AlgHom.id ao ao[X]).toRingHom=RingHom.id (ao[X]) from rfl,
  MvPolynomial.map_id,x7] at h
 unfold flatten at *
 unfold cK differentialSpecialization
 refine (AlgHom.congr_fun ?_ _).trans h
 apply Dv
 intro v
 rw [differentialSpecializationHom,wY ,wY]
 cases v <;> rfl
theorem adr (f :af 2) :jetTotalDegree (bY f)≤f.totalDegree := by
 apply (jetTotalDegree_map_le constants _).trans
 have hw: (jetDegreeWeight:zi (Fin 2)→ℕ) =
     fun v=>v.elim 0 (fun _=>1) := by
   funext v
   cases v <;> rfl
 rw [jetTotalDegree,hw,← MvPolynomial.totalDegree_optionEquivRight]
 simp only [flatten,zIH,le_refl]
theorem aCA (f :af 2) : (bY f).degreeOf (some 1)≤f.degreeOf 1 := by
 have h: (flatten f).degreeOf (some 1)=f.degreeOf 1 := by
  rw [← MvPolynomial.degreeOf_optionEquivRight]
  simp only [flatten,zIH]
 rw [← h,Zi ,Zi]
 exact Multiset.count_le_of_le _ MvPolynomial.degrees_map_le
theorem bZ3 (f :af 2) :f.degreeOf 1≤qE f := by
 rw [MvPolynomial.degreeOf_eq_sup,qE]
 exact Finset.sup_le fun m hm=> by
   apply (zk (f := fun m:Fin 2 →₀ ℕ =>
     m.sum fun i a=>i.val*a) hm).trans'
   rw [Z0 _ _ (by simp),Fin.sum_univ_two]
   simp
end
end ana
end
section
namespace aA2
noncomputable section
open aR oR we yz MvPolynomial
private theorem bHx {f :af 3} {P:c9 (eT 3)} [P.IsPrime]
    (hsep:sep f∉P) : (F3 f P).comap (p6 pU).toRingHom=P:= by
  apply SetLike.ext
  intro a
  change vY a∈F3 f P↔a∈P
  constructor
  · intro ha
    have hh:sep f*a∈uh cH (qM cH P) := by
      intro x hx
      change eval x (sep f*a)=0
      rw [lJ]
      by_cases hs :eval x (sep f)=0
      · rw [hs,zero_mul]
      · have he :eval (JZ f x) (vY a)=0:=ha _ ⟨x,⟨hx,hs⟩,rfl⟩
        rw [ahz] at he
        rw [he,p9]
    rw [QL] at hh
    exact (‹P.IsPrime›.mem_or_mem hh).resolve_left hsep
  · intro ha y hy
    obtain ⟨x,hx,rfl⟩:=hy
    simpa only [x7,ahz] using hx.1 a ha
end
end aA2
end
section
namespace aeB
noncomputable section
open aR oR yz MeasureTheory
open scoped BigOperators Pointwise
def gsP:Fin 4→Shape :=
 ![S9,tC,Yr (bf+1),RY]
def gsO:Fin 4→ℕ :=
 ![0,1,bf - 1,bf]
def slots (P:Set iz) :Fin 4→Set iz :=
 GR (fun i=>nD (gsP i) (gsO i)) 0 P
def UB (P:Set iz) :ℝ :=
 sSup ((fun x :iz=>x 0 + x 1 + x 2) '' P)
def V9 (P:Set iz) :ℝ :=
 sSup ((fun x :iz=>x 1+2*x 2) '' P)
def WA (P:Set iz) :ℝ :=
 sSup ((fun x :iz=>x 2) '' P)
def apK (P C:Set iz) (t:ℝ) :ℝ :=
 ((volume (t•P+C)).toReal-(volume C).toReal)/t
def ajg (s :pC) (h:ℕ) (B J T:ℝ) :ℝ :=
  (h:ℝ)*((s.t:ℝ)*((s.j:ℝ) - s.t)*B +
    (s.t:ℝ)*((s.b:ℝ) - s.j+(s.t:ℝ)/2)*J +
    ((s.j:ℝ) - 2*s.t)*((s.b:ℝ)-(s.j:ℝ)/2)*T)
end
end aeB
end
section
namespace ac0
noncomputable section
open aR oR we yz MvPolynomial
open scoped BigOperators Pointwise
def c1 :Prop :=
  ∀ (k σ:Type) [lV k] [G8 k] [vj σ]
    (I:c9 (lz σ k)),I.IsPrime →
    (p7 I).natDegree=1 →
    ∃ bad:aU (zd k (σ→k)),
      (∀ B∈bad,B ≠ ⊤) ∧
      ∀ (a :σ→k),(∀ B∈bad,a∉B) →
        (projection I a).Finite ∧
        ∀ t:k,(p7 (auW I a t)).natDegree=0 ∧
          uJ (auW I a t)=uJ I
def c2 :Prop :=
  ∀ (k σ:Type) [lV k] [G8 k] [vj σ]
    (I:c9 (lz σ k)) (hI:I.IsPrime),
    (p7 I).natDegree=1 →
    ∃ B:zd k (σ→k),B ≠ ⊤ ∧
      ∀ (a :σ→k),a∉B→cxE I hI a
def c3:Prop :=
  ∀ (k σ:Type) [lV k] [G8 k] [vj σ]
    (I:c9 (lz σ k)) (hI:I.IsPrime)
    (a :σ→k),(projection I a).Finite→cxE I hI a →
    ∃ bad:aU k,∀ t∉bad,(auW I a t).IsRadical
end
end ac0
end
section
namespace aeB
noncomputable section
open yz MeasureTheory MvPolynomial
open scoped BigOperators Pointwise
def rest:aU (Fin 4) :=sS 1 (sS 2 (sS 3 ∅))
theorem bPu: (th :aU (Fin 4))=sS 0 rest:= by decide
theorem biT: (0:Fin 4)∉rest:= by decide
private theorem ds2 (u v :Fin 4→ℝ) :
   (∑ S∈(th :aU (Fin 4)).powerset,
     (-1 :ℝ)^(4 - S.card) * ∏ i,(if i∈S then u i else v i)) =
     ∏ i,(u i - v i) := by
 rw [bPu]
 unfold rest
 simp only [
   EK (a :=(0:Fin 4)) (s :=sS 1 (sS 2 (sS 3 ∅))) (by decide),
   EK (a :=(1 :Fin 4)) (s :=sS 2 (sS 3 ∅)) (by decide),
   EK (a :=(2 :Fin 4)) (s :=sS 3 ∅) (by decide),
   EK (a :=(3:Fin 4)) (s := ∅) (by decide),
   Finset.powerset_empty,Finset.sum_singleton]
 norm_num [Finset.card_insert_of_notMem, Finset.mem_insert]
 ring
private def weights (t:ℝ) (S:aU (Fin 4)) (i:Fin 4) :ℝ :=
 if i∈S then (![t,1,1,1] :Fin 4→ℝ) i else 0
private theorem d1Q (p:lz (Fin 4) ℝ) (w:Fin 4→ℝ) :
  p.eval w = ∑ d∈p.support,p.coeff d * ∏ i,(w i)^d i:= by
 conv_lhs=>rw [p.as_sum]
 rw [MvPolynomial.eval_sum]
 apply sH rfl
 intro d _
 rw [eval_monomial,Finsupp.prod_of_support_subset d (Finset.subset_univ _) _ (by simp)]
private theorem c4s (p:lz (Fin 4) ℝ) (t:ℝ) :
    (∑ S∈(th :aU (Fin 4)).powerset,
      (-1 :ℝ)^(4 - S.card)*p.eval (weights t S)) =
      ∑ d∈p.support,p.coeff d * ∏ i,((![t,1,1,1] :Fin 4→ℝ) i^d i - 0^d i) := by
  simp_rw [d1Q,Iw]
  rw [Finset.sum_comm]
  apply sH rfl
  intro d _
  calc
    _ = ∑ S∈(th :aU (Fin 4)).powerset,
        p.coeff d*((-1 :ℝ)^(4 - S.card) *
          ∏ i,(if i∈S then (![t,1,1,1] :Fin 4→ℝ) i^d i else 0^d i)) := by
      apply sH rfl
      intro S _
      have heq : (∏ i,weights t S i^d i) =
          ∏ i,(if i∈S then (![t,1,1,1] :Fin 4→ℝ) i^d i else 0^d i) := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi:i∈S <;> simp [weights,hi]
      rw [heq]
      ring
    _ = _:= by
      rw [← Iw ,ds2]
private theorem eO2 (d:Fin 4 →₀ ℕ) (hd:d.degree=4) (t:ℝ) :
    (∏ i,((![t,1,1,1] :Fin 4→ℝ) i^d i - 0^d i)) =
      t * ∏ i,((![1,1,1,1] :Fin 4→ℝ) i^d i - 0^d i) := by
  by_cases hz : ∃ i,d i=0
  · obtain ⟨i,hi⟩:=hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]),
      zue (vi  i) (by simp [hi]),p9 ]
  · have hn (i:Fin 4) :0<d i:=Nat.pos_of_ne_zero (fun hi=>hz ⟨i,hi⟩)
    rw [Qx ,zmL] at hd
    have hones (i:Fin 4) :d i=1 := by
      have h0:=hn 0
      have h1 :=hn 1
      have h2 :=hn 2
      have h3:=hn 3
      fin_cases i
      · change d 0=1
        omega
      · change d 1=1
        omega
      · change d 2=1
        omega
      · change d 3=1
        omega
    simp [hones,Fin.prod_univ_four]
private theorem c4t (p:lz (Fin 4) ℝ)
    (hp:p.IsHomogeneous 4) (t:ℝ) :
    (∑ S∈(th :aU (Fin 4)).powerset,
      (-1 :ℝ)^(4 - S.card)*p.eval (weights t S)) =
      t * ∑ S∈(th :aU (Fin 4)).powerset,
        (-1 :ℝ)^(4 - S.card)*p.eval (weights 1 S) := by
  rw [c4s,c4s,Iw]
  apply sH rfl
  intro d hd
  have hd' : d.degree=4 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hd)
  rw [eO2 d hd' t]
  ring
end
end aeB
end
section
namespace aY0
noncomputable section
open as3 MvPolynomial
abbrev adl (A:N9) :=lz (Slot A) (aqn A)
def coordinate {A:N9} (v :Slot A) :aqn A :=
 nI (Nb A nU) (lI v)
def avA (A:N9) (b: (j:Fin 4) → ↥(A j)) :aqn A :=
 ∏ j:Fin 4,coordinate ⟨j,b j⟩
theorem bsI (A:N9) (b: (j:Fin 4) → ↥(A j)) :
  avA A b≠0 :=
 Finset.prod_ne_zero_iff.mpr fun j _=>b9p ⟨j,b j⟩
def a5P (A:N9) (i:Fin 4) :adl A :=
 ∑ a : ↥(A i),C (coordinate ⟨i,a⟩)*lI ⟨i,a⟩
def Wd (A:N9) (k :ℕ) :c9 (adl A) :=
 n5 (a5P A '' {i:Fin 4 | i.val<k})
private theorem cqN {L:Type*} [nq L] (A:N9) (k :ℕ)
    (b: (j:Fin 4) → ↥(A j)) (z :Slot A→L) (w:Fin 4→L)
    (hw : ∀ j,w j*z ⟨j,b j⟩=1) :
    ∃ E :lz (Slot A) L →ₐ[L] lz (Slot A) L,
      oK E.toRingHom =
        n5 ((fun j:Fin 4 => ∑ a : ↥(A j),C (z ⟨j,a⟩)*lI ⟨j,a⟩) ''
          {j:Fin 4 | j.val<k}) := by
  classical
  let terms (j:Fin 4) (a : ↥(A j)) :lz (Slot A) L :=
    C (z ⟨j,a⟩)*lI ⟨j,a⟩
  let equation (j:Fin 4) := ∑ a,terms j a
  let rest (j:Fin 4) := ∑ a∈Finset.univ.erase (b j),terms j a
  let value (v :Slot A) :lz (Slot A) L :=
    if v.1.val<k∧v.2=b v.1 then-(C (w v.1)*rest v.1) else lI v
  let E :lz (Slot A) L →ₐ[L] lz (Slot A) L:=oy value
  let J:=n5 (equation '' {j:Fin 4 | j.val<k})
  have hsum (j:Fin 4) :equation j=rest j+terms j (b j) :=
    (zvm _ _ (vi (b j))).symm
  have hrest (j:Fin 4) :E (rest j)=rest j:= by
    simp only [rest,t5]
    apply sH rfl
    intro a ha
    have hne :=(Finset.mem_erase.mp ha).1
    simp [terms,E,value,hne]
  have hpivot (j:Fin 4) (hj:j.val<k) :
      E (lI ⟨j,b j⟩) = - (C (w j)*rest j) := by
    simp [E,value,hj]
  have hunit (j:Fin 4) :C (w j)*C (z ⟨j,b j⟩)=(1 :lz (Slot A) L) := by
    rw [← lJ,hw,vk]
  refine ⟨E,show oK E.toRingHom=J from yL ?_ ?_⟩
  · let q:=Ee L J
    have hq:q.comp E=q:= by
      apply Dv
      rintro ⟨j,a⟩
      change q (E (lI ⟨j,a⟩))=q (lI ⟨j,a⟩)
      by_cases h:j.val<k∧a=b j
      · obtain ⟨hj,rfl⟩:=h
        rw [hpivot j hj,Ideal.Quotient.mkₐ_eq_mk,Mz]
        rw [show-(C (w j)*rest j)-MvPolynomial.X ⟨j,b j⟩ =
          -(C (w j)*rest j+MvPolynomial.X ⟨j,b j⟩) by abel]
        apply J.neg_mem
        have he :equation j∈J:=sI ⟨j,hj,rfl⟩
        have hm:=J.mul_mem_left (C (w j)) he
        simpa only [hsum j,terms,GF,← qy ,hunit j,t6] using hm
      · simp [E,value,h]
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p=0
    have hh:=Nr hq p
    change q (E p)=q p at hh
    change E p=0 at hp
    simpa only [hp,oq] using hh.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    change E (equation j)=0
    rw [hsum,pG,hrest]
    simp only [terms,lJ,hpivot j hj,mul_neg]
    rw [show E (C (z ⟨j,b j⟩))=C (z ⟨j,b j⟩) by simp [E]]
    rw [← qy ,uz (C (z ⟨j,b j⟩)),hunit,t6,OJ]
theorem b9l (A:N9) (k :ℕ) (b: (j:Fin 4) → ↥(A j))
   {a :aqn A} (ha :a≠0) (u:adl A) (n:ℕ)
   (hu:C a^n*u∈Wd A k) :
   ∃ m:ℕ,C (avA A b)^m*u∈Wd A k := by
 classical
 let x :=avA A b
 let L:=LQ x
 have hx :x≠0:=bsI A b
 let:HZ L:=Localization.Away.isDomain hx
 let g:=cy (aqn A) L
 let z (v :Slot A) :=g (coordinate v)
 have hux :qU (∏ j:Fin 4,z ⟨j,b j⟩) := by
   simp only [z,← Lf]
   change qU (cy (aqn A) L x)
   exact Ze (S:=L) x
 have hz (j:Fin 4) :qU (z ⟨j,b j⟩) :=
   isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i=>z ⟨i,b i⟩) (vi j)) hux
 choose w hw using fun j=>isUnit_iff_exists_inv.mp (hz j)
 obtain ⟨E,hE⟩:=cqN A k b z w (fun j=>(uz _ _).trans (hw j))
 let:oD (adl A) (lz (Slot A) L) :=Zf
 let incl:=cy (adl A) (lz (Slot A) L)
 let M:=(LO x).map (C (σ:=Slot A))
 have :RD M (lz (Slot A) L) :=
   zEY (LO x) L
 have hincl:incl=ox g:=rfl
 have hJ: (Wd A k).map incl=oK E.toRingHom:= by
   rw [hE,Wd,zc,Sv]
   congr 1
   apply Set.image_congr
   intro i _
   simp [hincl,a5P,z]
 have hmem:=EP incl hu
 rw [hJ] at hmem
 change E (incl (C a^n*u))=0 at hmem
 have hga :g a≠0:= by
   have hinj:qG g:=IsLocalization.injective (S:=L)
     (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
   exact fun h=>ha (hinj (h.trans (oq g).symm))
 have hEa :E (incl (C a))=C (g a) := by simp [hincl]
 have heu:E (incl u)=0:= by
   rw [lJ,t7,lJ,t7,hEa] at hmem
   exact (mul_eq_zero.mp hmem).resolve_left (Du _ (C_ne_zero.mpr hga))
 have hu' : incl u∈(Wd A k).map incl:= by rw [hJ]; exact heu
 obtain ⟨_,⟨_,⟨m,rfl⟩,rfl⟩,hm⟩ :=
   (Te M _ (Wd A k) u).mp hu'
 exact ⟨m,by simpa only [t7] using hm⟩
end
end aY0
end
section
namespace aA1
noncomputable section
open aR oR MvPolynomial
open scoped Polynomial
private theorem bKm (P:af 3) (i:Fin 3) :
  (oZ i P).totalDegree≤P.totalDegree - 1 := by
 simpa only [weightedTotalDegree_one,Pi.one_apply] using
  weightedTotalDegree_pderiv_le_sub (1 :Fin 3→ℕ) i P
private theorem dL7 (P:af 3) :
  (DU P).totalDegree≤P.totalDegree := by
 unfold DU
 exact SM fun m hm =>
  (totalDegree_monomial_le _ _).trans (le_totalDegree hm)
private theorem c1g (a :ℕ) (P:af 3) :
  ((a :af 3)*P).totalDegree≤P.totalDegree := by
 rw [← zh (C:ao[X] →+* af 3) a]
 exact (yU _ _).trans (by rw [UY ,wB])
private theorem asl (P:af 3) (i j:Fin 3) :
   (lI j*oZ i P).totalDegree≤P.totalDegree := by
 by_cases h:P.totalDegree=0
 · rw [totalDegree_eq_zero_iff_eq_C.mp h,pderiv_C,p9,totalDegree_zero]
   exact v8 _
 · have hp:=bKm P i
   apply (yU _ _).trans
   rw [RJ]
   omega
private theorem b8u (P:af 3) :
  (D3 P).totalDegree≤P.totalDegree := by
 unfold D3
 exact (totalDegree_add _ _).trans (max_le
  ((totalDegree_add _ _).trans (max_le (dL7 P) (asl P 0 1)))
  (by rw [qy]; exact (c1g 2 _).trans (asl P 1 2)))
private theorem dgE (f P:af 3) :
   (Ev f P).totalDegree≤P.totalDegree+(f.totalDegree - 1) := by
 unfold Ev
 apply (totalDegree_sub _ _).trans
 refine max_le ?_ ?_
 · have hs :=bKm f 2
   have hl:=b8u P
   apply (yU _ _).trans
   unfold separant
   omega
 · by_cases h:P.totalDegree=0
   · rw [totalDegree_eq_zero_iff_eq_C.mp h,pderiv_C,p9,totalDegree_zero]
     exact v8 _
   · have hl:=b8u f
     have hp:=bKm P 2
     apply (yU _ _).trans
     omega
private theorem cHq (f :af 3) (j:ℕ) :
    (AR f j).totalDegree≤1+(2*j+1)*(f.totalDegree - 1) := by
  have hs : (separant f).totalDegree≤f.totalDegree - 1 :=bKm f 2
  induction j with
  | zero =>
    rw [AR,totalDegree_neg]
    have h:=b8u f
    simp only [Nat.mul_zero,wB,t6]
    omega
  | succ j ih =>
    rw [AR]
    let b:=AR f j
    change (separant f*Ev f b -
      ((2*j+1 :ℕ) :af 3)*b*Ev f (separant f)).totalDegree≤_
    have h₁:=(yU (separant f) (Ev f b)).trans
      (Aa hs (dgE f b))
    have h₂:=(yU (((2*j+1 :ℕ) :af 3)*b)
      (Ev f (separant f))).trans
      (Aa (c1g (2*j+1) b)
        ((dgE f (separant f)).trans (Nat.add_le_add_right hs _)))
    have hstep:=(totalDegree_sub _ _).trans (max_le h₁ (h₂.trans_eq (by omega)))
    change b.totalDegree≤_ at ih
    calc
      _≤b.totalDegree+2*(f.totalDegree - 1) := by
        apply hstep.trans
        omega
      _≤_:= by
        rw [show 2*(j+1)+1=(2*j+1)+2 by omega,Nat.add_mul]
        omega
end
end aA1
end
section
set_option backward.isDefEq.respectTransparency false
namespace aA9
noncomputable section
open zP MvPolynomial
abbrev Ground :=we.cH
abbrev Coeff (A:Fin 4→aU Exponent) :=Σ i:Fin 4,↥(A i)
abbrev aGw (A:Fin 4→aU Exponent) :=lz (Fin 4) (xB A)
def abu (A:Fin 4→aU Exponent) (i:Fin 4) :aGw A :=
 ∑ a : ↥(A i),ov a.1 (lI ⟨i,a⟩)
def ajt {R:Type*} [nq R] (f :Fin 4→R) (k :ℕ) :c9 R :=
 n5 (f '' {i:Fin 4 | (i:ℕ)<k})
private def aAW {A:Fin 4→aU Exponent} (k :ℕ) (v :Coeff A) :Prop :=
 v.1.val<k∧v.2.val=0
private abbrev Pivot (A:Fin 4→aU Exponent) (k :ℕ) := {v :Coeff A // aAW k v}
private abbrev E8 (A:Fin 4→aU Exponent) (k :ℕ) := {v :Coeff A // ¬aAW k v}
private abbrev X5 (A:Fin 4→aU Exponent) (k :ℕ) :=
 lz (Fin 4 ⊕ E8 A k) Ground
private def a7F (A:Fin 4→aU Exponent) (k :ℕ) :
  Fin 4 ⊕ Coeff A ≃ Pivot A k ⊕ (Fin 4 ⊕ E8 A k) := by
 classical
 exact (P7 (Xu _) (Equiv.sumCompl (aAW k)).symm).trans
  ((Equiv.sumAssoc _ _ _).symm.trans
    ((P7 (Equiv.sumComm _ _) (Xu _)).trans (Equiv.sumAssoc _ _ _)))
private theorem fVq (A:Fin 4→aU Exponent) (k :ℕ) (j:Fin 4) :
  a7F A k (.inl j) = .inr (.inl j) := by
 simp [a7F]
private theorem fVp {A:Fin 4→aU Exponent} {k :ℕ} {v :Coeff A}
  (hv :aAW k v) :a7F A k (.inr v) = .inl ⟨v,hv⟩:= by
 classical
 simp [a7F,Equiv.sumCompl_symm_apply_of_pos hv]
private theorem fVo {A:Fin 4→aU Exponent} {k :ℕ} {v :Coeff A}
  (hv : ¬aAW k v) :a7F A k (.inr v) = .inr (.inr ⟨v,hv⟩) := by
 classical
 simp [a7F,Equiv.sumCompl_symm_apply_of_neg hv]
private def Wn (A:Fin 4→aU Exponent) (k :ℕ) :
   aGw A ≃ₐ[Ground] lz (Pivot A k) (X5 A k) :=
 (sumAlgEquiv Ground (Fin 4) (Coeff A)).symm.trans
   ((renameEquiv Ground (a7F A k)).trans (sumAlgEquiv Ground _ _))
private theorem fVu (A:Fin 4→aU Exponent) (k :ℕ) (j:Fin 4) :
  Wn A k (lI j)=C (lI (.inl j)) := by
 simp [Wn,Ob ,fVq]
private theorem fVt {A:Fin 4→aU Exponent} {k :ℕ} {v :Coeff A}
  (hv :aAW k v) :Wn A k (C (lI v))=lI ⟨v,hv⟩:= by
 simp [Wn,Ob ,fVp hv]
private theorem fVs {A:Fin 4→aU Exponent} {k :ℕ} {v :Coeff A}
  (hv : ¬aAW k v) :Wn A k (C (lI v))=C (lI (.inr ⟨v,hv⟩)) := by
 simp [Wn,Ob ,fVo hv]
private def Nx {A:Fin 4→aU Exponent} {k :ℕ}
   (hz : ∀ i,0∈A i) (i:Fin 4) (hi:i.val<k) :Pivot A k :=
 ⟨⟨i,⟨0,hz i⟩⟩,hi,rfl⟩
private theorem c38 {A:Fin 4→aU Exponent} {k :ℕ}
  (hz : ∀ i,0∈A i) :
  t8 (fun i : {i:Fin 4 // i.val<k} => Nx hz i.val i.property) := by
 rintro ⟨⟨i,⟨a,ha⟩⟩,hi,hzero⟩
 change a=0 at hzero
 subst a
 exact ⟨⟨i,hi⟩,rfl⟩
private def c8d {A:Fin 4→aU Exponent} (k :ℕ) (v :Coeff A) :X5 A k := by
 classical
 exact if h:aAW k v then 0 else lI (.inr ⟨v,h⟩)
private def tail {A:Fin 4→aU Exponent} (k :ℕ)
   (hz : ∀ i,0∈A i) (i:Fin 4) :X5 A k :=
 ∑ a∈Finset.univ.erase (⟨0,hz i⟩ : ↥(A i)),
   c8d k ⟨i,a⟩*a.val.prod (fun j e=>(lI (.inl j) :X5 A k)^e)
private theorem c7N {A:Fin 4→aU Exponent} {k :ℕ}
  (hz : ∀ i,0∈A i) (i:Fin 4) (hi:i.val<k) :
  Wn A k (abu A i)=lI (Nx hz i hi)+C (tail k hz i) := by
 classical
 unfold abu tail
 rw [← zvm _ _ (vi (⟨0,hz i⟩ : ↥(A i))),pG,
  monomial_zero',fVt (show aAW k (⟨i,⟨0,hz i⟩⟩:Coeff A) from ⟨hi,rfl⟩),
  LR,t5 ,t5]
 congr 1
 apply sH rfl
 intro a ha
 have hn : ¬aAW k (⟨i,a⟩:Coeff A) := by
  intro h
  exact (Finset.ne_of_mem_erase ha) (vG h.2)
 simp only [monomial_eq,lJ,fVs hn,c8d,dite_eq_right hn]
 congr 1
 rw [Finsupp.prod,Lf ,Finsupp.prod,Lf]
 simp [fVu]
private theorem d1L {B ι:Type*} [nq B] (s :ι→B) :
    oK (oy s :lz ι B →ₐ[B] B).toRingHom =
      n5 (qJ fun i=>lI i - C (s i)) := by
  let I:c9 (lz ι B) :=n5 (qJ fun i=>lI i - C (s i))
  change oK (oy s :lz ι B →ₐ[B] B).toRingHom=I
  apply yL
  · intro f hf
    have h (p:lz ι B) :p - C (oy s p)∈I:= by
      induction p using JM with
      | C b=>simp
      | add p q hp hq =>
        simpa only [pG,add_sub_add_comm] using I.add_mem hp hq
      | mul_X p i hp =>
        simp only [lJ,wY]
        have hi:lI i - C (s i)∈I:=sI ⟨i,rfl⟩
        have he :p*lI i - C (oy s p*s i) =
            (p - C (oy s p))*lI i+C (oy s p)*(lI i - C (s i)) := by
          rw [lJ]
          ring
        rw [← lJ,he]
        exact I.add_mem (I.mul_mem_right (lI i) hp) (I.mul_mem_left _ hi)
    have hf' : oy s f=0:=hf
    simpa only [hf',oq,Gr] using h f
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simp [zS]
private def cU1 {A:Fin 4→aU Exponent} (hz : ∀ i,0∈A i) (k :ℕ) :
    (aGw A ⧸ ajt (abu A) k) ≃ₐ[Ground] X5 A k := by
  let e :=Wn A k
  let s :Pivot A k→X5 A k := fun v => -tail k hz v.val.1
  have hker :=d1L s
  have hmap :zE e.toRingHom (ajt (abu A) k) =
      oK (oy s :lz (Pivot A k) (X5 A k) →ₐ[ X5 A k] X5 A k).toRingHom:= by
    rw [hker,ajt,zc,Sv]
    apply oj n5
    ext f
    constructor
    · rintro ⟨i,hi,rfl⟩
      refine ⟨Nx hz i hi,?_⟩
      change lI (Nx hz i hi) - C (s (Nx hz i hi)) =
        Wn A k (abu A i)
      simpa only [s,Nx,Il,sub_neg_eq_add] using (c7N hz i hi).symm
    · rintro ⟨v,rfl⟩
      obtain ⟨⟨i,hi⟩,rfl⟩:=c38 hz v
      refine ⟨i,hi,?_⟩
      change Wn A k (abu A i) =
        lI (Nx hz i hi) - C (s (Nx hz i hi))
      simpa only [s,Nx,Il,sub_neg_eq_add] using c7N hz i hi
  let f :lz (Pivot A k) (X5 A k) →ₐ[Ground] X5 A k :=
    (oy s :lz (Pivot A k) (X5 A k) →ₐ[ X5 A k] X5 A k).restrictScalars Ground
  have hsurj:t8 f := fun b=>⟨C b,aeval_C s b⟩
  let q:=zpY (ajt (abu A) k) (oK f.toRingHom) e hmap.symm
  exact q.trans (Qw hsurj)
private theorem diG {A:Fin 4→aU Exponent}
  (hz : ∀ i,0∈A i) (k :ℕ) : (ajt (abu A) k).IsPrime := by
 apply (Ideal.Quotient.isDomain_iff_prime _).mp
 let e :=(cU1 hz k).toRingEquiv
 exact e.toMulEquiv.isDomain
private theorem gG3 {A:Fin 4→aU Exponent}
   (hz : ∀ i,0∈A i) (i:Fin 4) :
   abu A i∉ajt (abu A) i.val := by
 classical
 let v :Coeff A→Ground := fun j=>if j.1=i then 1 else 0
 let ev :=(eval v).comp (constantCoeff :aGw A →+* xB A)
 have h (j:Fin 4) :ev (abu A j)=v ⟨j,⟨0,hz j⟩⟩:= by
   unfold abu
   rw [t5 ,G3 (⟨0,hz j⟩ : ↥(A j))]
   · simp [ev,monomial_zero']
   · intro a _ ha
     have ha' : a.val≠0:= fun ha' => ha (vG ha')
     simp [ev,constantCoeff_monomial,ha']
   · simp
 have hle :ajt (abu A) i.val≤oK ev := by
   apply Ideal.span_le.mpr
   rintro _ ⟨j,hj,rfl⟩
   change j.val< i.val at hj
   have hji:j≠i:= fun he=>(ne_of_lt hj) (oj Fin.val he)
   change ev (abu A j)=0
   rw [h]
   simp [v,hji]
 intro hi
 have h0:ev (abu A i)=0:=hle hi
 simp [h,v] at h0
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Affine (A:Fin 4→aU Exponent) :=lz (Fin 4) (fZ A)
private abbrev aYB (A:Fin 4→aU Exponent) :=
 (GY (xB A)).map (C (σ:=Fin 4))
private theorem cZG (A:Fin 4→aU Exponent) (i:Fin 4) :
  cy (aGw A) (Affine A) (abu A i)=ve A i:= by
 rw [WX ,abu,ve,t5]
 apply sH rfl
 intro a _
 exact MvPolynomial.map_monomial _ _ _
private theorem cZp (A:Fin 4→aU Exponent) (k :ℕ) :
  zE (cy (aGw A) (Affine A)) (ajt (abu A) k) =
   ajt (ve A) k := by
 simp only [ajt,zc,Sv,cZG]
theorem efX {A:Fin 4→aU Exponent} (hz : ∀ i,0∈A i)
   (i:Fin 4) (p:Affine A) :
   ve A i*p∈ajt (ve A) i.val →
     p∈ajt (ve A) i.val := by
 intro hp
 let J:=ajt (abu A) i.val
 obtain ⟨q,s,rfl⟩:=zcf (aYB A) p
 rw [← cZp] at hp ⊢
 change _∈zE _ J at hp ⊢
 have hq:cy (aGw A) (Affine A) (abu A i*q) ∈
     zE (cy (aGw A) (Affine A)) J:= by
   rw [lJ,cZG,← zOg (Affine A) q s,← qy]
   exact Ideal.mul_mem_right _ _ hp
 obtain ⟨d,hd,hmem⟩ :=
   (Te (aYB A) _ J _).mp hq
 rw [mul_left_comm] at hmem
 have hprime :=diG hz i.val
 exact (IsLocalization.mk'_mem_map_algebraMap_iff (aYB A) _ J q s).mpr
   ⟨d,hd,(hprime.mem_or_mem hmem).resolve_left (gG3 hz i)⟩
private theorem dSx {R:Type*} [nq R] (f :Fin 4→R) :
  ajt f 4=n5 (qJ f) := by
 rw [ajt,show {i:Fin 4 | i.val<4} = z9 from zps Fin.isLt,
  Set.image_univ]
private def Tg {A:Fin 4→aU Exponent} (hz : ∀ i,0∈A i) :
  Fin 4 ≃ Pivot A 4 :=
 Equiv.ofBijective (fun i=>Nx hz i i.isLt) ⟨fun _ _ h=>oj (fun x=>x.val.1) h,
  fun v=> by
   obtain ⟨⟨i,_⟩,rfl⟩:=c38 hz v
   exact ⟨i,rfl⟩⟩
private theorem bq2 {A:Fin 4→aU Exponent} (hz : ∀ i,0∈A i) :
  u5 Ground (aGw A ⧸ ajt (abu A) 4)=JK (Coeff A) := by
 classical
 rw [(cU1 hz 4).trdeg_eq,zUx,Cardinal.lift_id]
 exact Cardinal.mk_congr ((P7 (Tg hz) (Xu _)).trans
  (Equiv.sumCompl (aAW 4)))
private theorem edW (A:Fin 4→aU Exponent) :
  u5 Ground (fZ A)=JK (Coeff A) := by
 let:MS (xB A) (fZ A) :=
  IsLocalization.isAlgebraic _ (GY (xB A))
 rw [← Pj Ground (xB A),trdeg_eq_zero (R:=xB A),add_zero,
  zUx,Cardinal.lift_id]
private theorem gEb {F U S:Type} [lV F] [nq U] [nq S]
    [oD F U] [oD U S] [oD F S] [yl F U S]
    (M:Submonoid U) [RD M S] (J:c9 U) (hprime :J.IsPrime)
    (hdis :Disjoint (M:Set U) (J:Set U)) :
    u5 F (S ⧸ zE (cy U S) J)=u5 F (U ⧸ J) := by
  let B:=U ⧸ J
  let I:=zE (cy U S) J
  let G:=S ⧸ I
  let:I.IsPrime :=VH M S J hprime hdis
  let:J.IsPrime :=hprime
  let f :B →+* G:=Yo I (cy U S) Ideal.le_comap_map
  have hf (u:U) :f (nI J u)=nI I (cy U S u) :=rfl
  have hfinj:qG f := by
    intro a b hab
    obtain ⟨a,rfl⟩:=vH a
    obtain ⟨b,rfl⟩:=vH b
    rw [hf,hf,Mz ,← qx ,← Ideal.mem_comap] at hab
    change a - b∈I.under U at hab
    rw [show I.under U=J from IsLocalization.under_map_of_isPrime_disjoint M S hprime hdis] at hab
    exact (Mz a b).mpr hab
  let:oD B G:=RingHom.toAlgebra (R:=B) (S:=G) f
  let:yl F B G:=zsL fun a=> by
    change nI I (cy F S a)=f (nI J (cy F U a))
    rw [hf,zg F U S]
  let:FaithfulSMul B G:=(zSO B G).mpr hfinj
  let:MS B G:=⟨fun x=> by
    obtain ⟨p,rfl⟩:=vH x
    obtain ⟨⟨q,s⟩,hs⟩:=IsLocalization.surj M p
    let a :=nI J q
    let b:=nI J s.val
    have hb:b≠0:= fun hb=>Set.disjoint_left.mp hdis s.property
      (Ideal.Quotient.eq_zero_iff_mem.mp hb)
    have hq:nI I p*f b=f a := by
      simp only [a,b,hf,← lJ,hs]
    refine ⟨oY b*pL-Polynomial.C a,?_,?_⟩
    · intro h0
      have h:=oj (fun P:oz B=>P.coeff 1) h0
      have hb1 : (oY b*(pL:oz B)).coeff 1=b:= by
        rw [Polynomial.coeff_C_mul_X,ite_eq_left rfl]
      have ha1 : (oY a).coeff 1=0:= by
        rw [Polynomial.coeff_C,ite_eq_right Nat.one_ne_zero]
      change (oY b*pL-Polynomial.C a).coeff 1=(0:oz B).coeff 1 at h
      rw [Polynomial.coeff_sub,hb1,ha1,Gr,KH] at h
      exact hb h
    · let ev :oz B →ₐ[B] G:=Polynomial.aeval (nI I p)
      change ev (oY b*pL-Polynomial.C a)=0
      have hC (c:B) :ev (oY c)=f c:=ev.commutes c
      have hX:ev pL=nI I p:=Polynomial.aeval_X _
      rw [qx ,lJ,hC,hC,hX,uz ,hq,Ea]⟩
  change u5 F G=u5 F B
  rw [← Pj F B,trdeg_eq_zero (R:=B),add_zero]
theorem b4E {A:Fin 4→aU Exponent} (hz : ∀ i,0∈A i) :
   qm (fZ A) (HG A) := by
 classical
 let J:=ajt (abu A) 4
 let S:=Affine A
 let U:=aGw A
 let M:=aYB A
 let I:=n5 (qJ (ve A))
 let G:=S ⧸ I
 have hI:zE (cy U S) J=I:=(cZp A 4).trans (dSx _)
 by_cases htop:I = ⊤
 · let:Subsingleton G:=Ideal.Quotient.subsingleton_iff.mpr htop
   exact Module.Finite.of_finite (R:=fZ A) (M:=G)
 have hprime :J.IsPrime :=diG hz 4
 have hdis :Disjoint (M:Set U) (J:Set U) := by
   apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint M S J).mp
   rwa [hI]
 let:I.IsPrime :=hI ▸ VH M S J hprime hdis
 let:yl Ground U S:=zsL fun a=> by
   change C (cy Ground (fZ A) a)=cy U S (C (C a))
   rw [WX ,map_C]
   rfl
 have htrG:u5 Ground G=JK (Coeff A) := by
   have h:=gEb (F:=Ground) (S:=S) M J hprime hdis
   rw [hI] at h
   exact h.trans (bq2 hz)
 have htr :=Pj Ground (fZ A) (A:=G)
 rw [edW,htrG,Cardinal.add_eq_left_iff] at htr
 have hztr :u5 (fZ A) G=0:= by
   refine htr.resolve_left ?_
   intro h
   exact (Cardinal.mk_lt_aleph0 (α:=Coeff A)).not_ge ((le_max_left _ _).trans h)
 let:Algebra.IsIntegral (fZ A) G:=⟨fun x=>isAlgebraic_iff_isIntegral.mp
   ((trdeg_eq_zero_iff.mp hztr).isAlgebraic x)⟩
 exact Algebra.IsIntegral.finite (R:=fZ A) (A:=G)
end
end aA9
end
section
namespace bRg
noncomputable section
open Algebra KaehlerDifferential MvPolynomial
open scoped BigOperators IntermediateField.algebraAdjoinAdjoin
private theorem gD9 {k P A:Type} [lV k]
  [nq P] [HZ P] [nq A] [HZ A]
  [oD k P] [oD k A] {ι:Type} {v :ι→P}
  (hv :IsTranscendenceBasis k v) (g:P →ₐ[k] A)
  (hg:qG g) (hgfin:g.Finite) :
  u5 k (vh A)=JK ι:= by
 let K:=vh A
 let _:oD P A:=g.toRingHom.toAlgebra
 have :yl k P A := .of_algebraMap_eq fun a=>(g.commutes a).symm
 have :yl k P K:=IsScalarTower.to₁₂₄ k P A K
 have :FaithfulSMul P A:=(zSO P A).mpr hg
 have :qm P A:=hgfin
 have :MS P K:=(IsFractionRing.isAlgebraic_iff' P A K).mp xu
 exact (hv.algebraMap_comp (A:=K)).cardinalMk_eq_trdeg.symm
private theorem bZj {k σ:Type} [lV k] [vj σ]
  (I:c9 (lz σ k)) [I.IsPrime]
  (hd: (p7 I).natDegree=1) :
  u5 k (vh (lz σ k ⧸ I))=1 := by
 obtain ⟨d,g,hg,hgfin⟩:=exists_finite_inj_algHom_of_fg k (lz σ k ⧸ I)
 have hd' : d = 1 := by
  simpa using (natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective
    g hgfin hg).symm.trans hd
 simpa [hd'] using gD9
  (IsTranscendenceBasis.mvPolynomial (Fin d) k) g hg hgfin
private theorem dW1 {k K:Type} [lV k] [lV K] [oD k K]
   [PerfectField k] [Df k K] (ht:u5 k K=1) :
   pz K Ω[K⁄k]=1 := by
 obtain ⟨s,hs,hsep⟩:=exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
 have hcard:G1 s=1 := by
   have h:=hs.cardinalMk_eq_trdeg.trans ht
   rw [Cardinal.mk_fintype] at h
   exact_mod_cast h
 let v :s→K:=(↑)
 have hv :qJ v=(s :Set K) := by
   ext x
   exact ⟨fun ⟨y,hy⟩=>hy ▸ y.property,fun hx=>⟨⟨x,hx⟩,rfl⟩⟩
 rw [← hv] at hsep
 let P:=lz s k
 let A:=Algebra.adjoin k (qJ v)
 let E :=NY k (qJ v)
 let e :P ≃ₐ[k] A:=hs.1.aevalEquiv
 let _:oD P E :=((cy A E).comp e.toRingHom).toAlgebra
 let _:oD P K:=((cy E K).comp (cy P E)).toAlgebra
 have :yl P E K := .of_algebraMap_eq fun _=>rfl
 have :yl k P K := .of_algebraMap_eq fun a=> by
   change cy k K a=cy E K (cy A E (e (cy k P a)))
   rw [e.commutes,← zg k A E,
     ← zg k E K]
 have :IsFractionRing P E :=IsFractionRing.of_ringEquiv_left e.toRingEquiv fun _=>rfl
 have :Vq P E :=Algebra.FormallyEtale.of_isLocalization
   (GY P)
 have :N0 E K:=hsep
 have :Vq E K:=Algebra.FormallyEtale.of_isSeparable E K
 have :Vq P K:=Algebra.FormallyEtale.comp P E K
 let b:=((mvPolynomialBasis k s).baseChange K).map
   (tensorKaehlerEquivOfFormallyEtale k P K)
 exact (Module.finrank_eq_card_basis b).trans hcard
private theorem gpJ {k E K:Type} [lV k] [lV E] [lV K]
  [oD k E] [oD k K] [oD E K] [yl k E K] [Df E K]
  (z :E) (hd:pz K Ω[K⁄k]=1)
  (hu:D k K (cy E K z)≠0) :N0 E K:= by
 apply (Algebra.FormallyUnramified.iff_isSeparable (K:=E) K).mp
 constructor
 let m:=KaehlerDifferential.map k E K K
 have hm:m (D k K (cy E K z))=0:= by
  simpa only [m,map_D,zEi] using (D E K).map_algebraMap z
 apply (zAZ 0).mpr
 intro y
 obtain ⟨x,rfl⟩:=KaehlerDifferential.map_surjective k E K y
 obtain ⟨t,rfl⟩:=exists_smul_eq_of_finrank_eq_one hd hu x
 change m (t•D k K (cy E K z))=0
 rw [KA,hm,smul_zero]
private theorem gpI {k K:Type} [lV k] [lV K]
   [G8 k] [oD k K] [Df k K] (u:K)
   (hd:pz K Ω[K⁄k]=1) (hu:D k K u≠0) :
   VO k u∧N0 (NY k {u}) K:= by
 let E :=NY k ({u} : Set K)
 have humem:u∈E :=IntermediateField.mem_adjoin_simple_self k u
 have htrans :VO k u:= by
   intro ha
   have :MS k E :=
     IntermediateField.isAlgebraic_adjoin_simple (isAlgebraic_iff_isIntegral.mp ha)
   have hbot:E = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic E
   rw [hbot] at humem
   obtain ⟨t,ht⟩:=(IntermediateField.mem_bot.mp humem)
   exact hu (ht ▸ (D k K).map_algebraMap t)
 refine ⟨htrans,?_⟩
 have :Df E K:=EssFiniteType.of_comp k E K
 exact gpJ (⟨u,humem⟩:E) hd hu
theorem proof :ac0.c2 := by
  classical
  intro k σ _ _ _ I hI hd
  have :I.IsPrime :=hI
  let A:=lz σ k ⧸ I
  let K:=vh A
  let f :lz σ k →ₐ[k] K :=
    (zE2 k A K).comp (Ee k I)
  have :Df A K:=EssFiniteType.of_isLocalization K (GY A)
  have :Df k K:=EssFiniteType.comp k A K
  have hr :pz K Ω[K⁄k]=1 :=dW1 (bZj I hd)
  let _:Fintype σ:=Fintype.ofFinite σ
  let L: (σ→k) →ₗ[k] Ω[K⁄k] := {
    toFun:= fun a => ∑ i,a i•D k K (f (lI i))
    map_add' := by
      intro a b
      simp [add_smul,zm]
    map_smul' := by
      intro t a
      simp [smul_smul,UP] }
  refine ⟨L.ker,?_,?_⟩
  · intro htop
    have hX (i:σ) :D k K (f (lI i))=0:= by
      have h:L (vZ i 1)=0:=LinearMap.mem_ker.mp (htop.symm ▸ PA)
      simpa [L,RP] using h
    have hp (p:lz σ k) :D k K (f p)=0:= by
      induction p using JM with
      | C t =>
        rw [← F9,f.commutes]
        exact (D k K).map_algebraMap t
      | add p q hp hq=>simp only [map_add,hp,hq,add_zero]
      | mul_X p i hp=>simp only [map_mul,Derivation.leibniz,hp,hX,smul_zero,add_zero]
    have hA (x :A) :D k K (cy A K x)=0:= by
      obtain ⟨p,rfl⟩:=vH x
      exact hp p
    have hK (x :K) :D k K x=0:= by
      obtain ⟨p,q,_,rfl⟩:=IsFractionRing.div_surjective A x
      simp [Derivation.leibniz_div,hA]
    have hle : (⊤ : zd K Ω[K⁄k]) ≤ ⊥ := by
      rw [← span_range_derivation k K,Submodule.span_le]
      rintro _ ⟨x,rfl⟩
      simpa using hK x
    have :Subsingleton Ω[K⁄k] :=(zAZ 0).mpr fun x =>
      (Submodule.mem_bot K).mp (hle (PA:x ∈ ⊤))
    exact Nat.zero_ne_one ((Module.finrank_zero_of_subsingleton (R:=K) (M:=Ω[K⁄k])).symm.trans hr)
  · intro a ha
    have hL:L a=D k K (f (ac0.P5 a)) := by
      change (∑ i,a i•D k K (f (lI i))) =
        D k K (f (∑ i,pQ (a i)*lI i))
      simp only [t5]
      apply sH rfl
      intro i _
      rw [← F9,← TI,KA,(D k K).map_smul]
    have hn:D k K (f (ac0.P5 a))≠0:= by
      rw [← hL]
      exact fun hz=>ha (LinearMap.mem_ker.mpr hz)
    exact gpI _ hr hn
end
end bRg
end
section
namespace aeB
noncomputable section
open aR oR yz Qp MeasureTheory Filter
open scoped BigOperators Pointwise Topology
def c2 :Prop :=
  ∀ P:Set iz,OE P→P⊆nD S9 0 →
    ∀ (s :pC) (h:ℕ),bF s→s.j<s.b→0<s.t→0<h →
      Tendsto (apK P (nD s h)) (𝓝[Set.Ioi 0] (0:ℝ))
        (𝓝 (ajg s h (UB P) (V9 P) (WA P)))
private theorem bPM {A:Set iz} (hA : ∀ x∈A,x 3=0) :
  volume A=0:= by
 let arq (i:Fin 4) :Set ℝ:=if i=3 then {0} else z9
 have hsub:A⊆Set.pi z9 arq:= by
  intro x hx
  refine Set.mem_pi.mpr (fun i _ => ?_)
  by_cases hi:i=3
  · simpa [arq,hi] using hA x hx
  · simp [arq,hi]
 have hz :volume (Set.pi z9 arq)=0:= by
  rw [volume_pi_pi]
  exact zue (vi (3:Fin 4)) (by simp [arq])
 exact yL ((measure_mono hsub).trans_eq hz) bot_le
end
end aeB
end
section
namespace bz3
noncomputable section
open aR oR MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
def Mt (R:Type*) [CommSemiring R] :
    lz (Fin 2) R ≃ₐ[R] (lz (Fin 1) R)[X] :=
  (renameEquiv R wA).trans (G7 R (Fin 1))
private abbrev Ka :af 1 ≃ₐ[ao[X]] ao[X][X] :=
 uniqueAlgEquiv ao[X] (Fin 1)
private theorem aUW (f :af 2) : (Mt ao[X] f).natDegree=f.degreeOf 1 := by
 change (G7 _ _ (p6 wA f)).natDegree=f.degreeOf 1
 rw [natDegree_optionEquivLeft]
 exact degreeOf_rename_of_injective finSuccEquivLast.injective (II 1)
private theorem bqd (f :af 2) :
  Mt ao[X] (oZ 1 f)=(Mt ao[X] f).derivative := by
 change G7 _ _ (p6 wA (oZ 1 f)) =
  (G7 _ _ (p6 wA f)).derivative
 rw [← pderiv_rename finSuccEquivLast.injective,
  show wA (1 :Fin 2)=none from finSuccEquivLast_last,
  optionEquivLeft_pderiv_none]
private theorem aYc (g:af 1) (S:ao[X]) :
  (Ka g).eval S=nX (jet S) g:= by
 have h:=eval₂_uniqueAlgEquiv (f :=g) (φ:=RingHom.id ao[X]) (a :=jet S)
 have hzero :jet S (default :Fin 1)=S:= by
  change p5 0 S=S
  simp
 simpa only [Polynomial.eval₂_id,MvPolynomial.eval₂_id,hzero] using h
private theorem aDh (f :af 2) (S:ao[X]) :
   ((Mt ao[X] f).map (nX (jet S))).eval (jet S (1 :Fin 2)) =
     cK f S:= by
 rw [Mt,AlgEquiv.trans_apply,Ob ,← optionEquivLeft_elim_eval,
   eval_rename,cK]
 apply oj (fun x :Fin 2→ao[X]=>nX x f)
 funext i
 fin_cases i <;> rfl
private theorem cu8 (g:af 1) : (Ka g).natDegree≤g.totalDegree := by
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro k hk
 rw [Ka,coeff_uniqueAlgEquiv]
 by_contra hn
 have h:=le_totalDegree (mem_support_iff.mpr hn)
 change (t3 (default :Fin 1) k).degree≤g.totalDegree at h
 rw [Finsupp.degree_single] at h
 exact (G4 hk) h
private theorem aUV (f :af 2) (k :ℕ) (hk :k≤f.totalDegree) :
  k+(Ka ((Mt ao[X] f).coeff k)).natDegree≤f.totalDegree := by
 change k+(Ka ((G7 _ _ (p6 wA f)).coeff k)).natDegree≤_
 have hdeg: (p6 wA f).totalDegree=f.totalDegree :=
  totalDegree_renameEquiv wA f
 have hh:=totalDegree_coeff_optionEquivLeft_add_le ao[X] (Fin 1)
  (p6 wA f) k
  (by rw [hdeg]; exact hk)
 rw [hdeg] at hh
 exact (Nat.add_le_add_left (cu8 _) _).trans (by simpa [LR] using hh)
private def QI (f :af 2) :ao[X][X] :=
 let A:=Mt ao[X] f
 if 0<A.natDegree then
  Ka (A.resultant A.derivative A.natDegree (A.natDegree - 1))
 else Ka (A.coeff 0)
private theorem bpk (f :af 2) (hf :ze f) {B:ℕ} (hB:2≤B)
    (hchar :B<K1.p) (hb:f.totalDegree≤B) :
    QI f≠0∧(QI f).natDegree≤f.totalDegree*(B - 1) ∧
      ∀ S:ao[X],cK f S=0→(QI f).eval S=0 ∨
        (0<f.degreeOf 1∧qg 1 f S) := by
  let A:=Mt ao[X] f
  let c:=A.natDegree
  let b:=f.totalDegree
  have hcb:c≤b:= by
    change (Mt ao[X] f).natDegree≤f.totalDegree
    exact (aUW f).le.trans (f.degreeOf_le_totalDegree 1)
  have hAb:A≠0:=(Xg _ (Mt ao[X]).injective).mpr hf.ne_zero
  by_cases hc:0<c
  · let R:=A.resultant A.derivative c (c - 1)
    have hform :QI f=Ka R:=ite_eq_left hc
    have hcast: (c:af 1)≠0:= by
      have :u9 ao K1.p:=vw embed.injective K1.p
      have :u9 ao[X] K1.p :=
        vw (VC (R:=ao)) K1.p
      have :u9 (af 1) K1.p :=
        vw (MvPolynomial.C_injective (σ:=Fin 1) (R:=ao[X])) K1.p
      intro h
      have hp:K1.p∣c:=(S1 (af 1) K1.p c).mp h
      exact (G4 (hcb.trans_lt (hb.trans_lt hchar)))
        (Nat.le_of_dvd hc hp)
    have hder :A.derivative≠0:= by
      intro h
      have hz :=oj (fun P: (af 1)[X]=>P.coeff (c - 1)) h
      rw [Polynomial.coeff_derivative,z8 hc,KH] at hz
      have hnat : (((c - 1 :ℕ) :af 1)+1)=(c:af 1) := calc
        _=((c - 1+1 :ℕ) :af 1) := by rw [Pk,Nat.cast_one]
        _ = _:=oj (fun k :ℕ=>(k :af 1)) (z8 hc)
      rw [hnat] at hz
      change A.leadingCoeff*(c:af 1)=0 at hz
      exact (FK (Polynomial.leadingCoeff_ne_zero.mpr hAb) hcast) hz
    have hR:R≠0 :=
      Polynomial.resultant_derivative_ne_zero_of_irreducible A (hf.map (Mt ao[X])) hder
    have hdeg: (Ka R).natDegree+c^2≤(2*c - 1)*b:= by
      let B:=A.map Ka.toRingHom
      have h:=Polynomial.natDegree_resultant_derivative_padded_add_sq_le B c b (by
        intro k hk
        rw [Eg]
        exact aUV f k (hk.trans hcb))
      dsimp only [B] at h
      rw [Polynomial.derivative_map,Polynomial.resultant_map_map] at h
      exact h
    have hbudget: (Ka R).natDegree≤b*(b - 1) := by
      have hbpos :1≤b:=hc.trans_le hcb
      have hcpos :1≤2*c:= by omega
      zify [hbpos,hcpos] at hdeg ⊢
      nlinarith [sq_nonneg ((b:ℤ)-(c:ℤ))]
    refine ⟨by rw [hform]; exact (Xg _ Ka.injective).mpr hR,?_,?_⟩
    · rw [hform]
      exact hbudget.trans (Kc b (Nat.sub_le_sub_right hb 1))
    · intro S hS
      by_cases hS' : cK (oZ 1 f) S=0
      · left
        rw [hform,aYc]
        exact Polynomial.map_resultant_eq_zero_of_common_root (nX (jet S))
          A A.derivative t9 (Polynomial.natDegree_derivative_le A) (Or.inl hc.ne')
          (jet S (1 :Fin 2)) ((aDh f S).trans hS) (by
            rw [show A.derivative=Mt ao[X] (oZ 1 f) from (bqd f).symm]
            exact (aDh _ S).trans hS')
      · exact Or.inr ⟨(aUW f) ▸ hc,hS,hS'⟩
  · have hform :QI f=Ka (A.coeff 0) :=ite_eq_right hc
    have hAc:A=oY (A.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero (Nat.eq_zero_of_not_pos hc).le
    have hA0:A.coeff 0≠0:= fun h=>hAb (by simpa [h] using hAc)
    refine ⟨by rw [hform]; exact (Xg _ Ka.injective).mpr hA0,?_,?_⟩
    · rw [hform]
      have h:=aUV f 0 (v8 _)
      exact (by simpa using h: (Ka (A.coeff 0)).natDegree≤b).trans
        (by simpa using Kc  b (by omega :1≤B - 1))
    · intro S hS
      left
      have h:=(aDh f S).trans hS
      change (A.map _).eval _=0 at h
      conv at h=>lhs; rw [hAc]
      rw [hform,aYc]
      simpa only [Polynomial.map_C,FR] using h
theorem bFR (q:af 2) {B J:ℕ} (hq:q≠0) (hB:2≤B)
   (hchar :B<K1.p) (hb:q.totalDegree≤B) (hj:q.degreeOf 1≤J) :
   ∃ (A:aU (af 2)) (u:ao[X][X]),
     (∀ g∈A,ze g∧0<g.degreeOf 1) ∧
     (∑ g∈A,g.totalDegree)≤B∧(∑ g∈A,g.degreeOf 1)≤J ∧
     u≠0∧u.natDegree≤B*(B - 1) ∧
     ∀ S:ao[X],cK q S=0→u.eval S=0 ∨ ∃ g∈A,qg 1 g S:= by
 classical
 let _:StrongNormalizationMonoid (af 2) :=
   UniqueFactorizationMonoid.strongNormalizationMonoid
 let M:=normalizedFactors q
 let A:=M.toFinset
 let T:=A.filter fun g=>0<g.degreeOf 1
 have hA : ∀ g∈A,Irreducible g:= fun g hg =>
   irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
 have hdiv : (∏ g∈A,g)∣q :=
   (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq).dvd
 have hcap: (∑ g∈A,g.totalDegree)≤B:= by
   have h:=sum_weightedTotalDegree_le_of_prod_dvd (1 :Fin 2→ℕ) A id hq hdiv
   simp only [id_eq,weightedTotalDegree_one] at h
   exact h.trans hb
 have hT : ∀ g∈T,ze g∧0<g.degreeOf 1 := fun g hg =>
   ⟨hA g (Finset.mem_filter.mp hg).1,(Finset.mem_filter.mp hg).2⟩
 have hJ: (∑ g∈T,g.degreeOf 1)≤J:= by
   obtain ⟨r,hr⟩:=(Finset.prod_dvd_prod_of_subset T A id
     (zT0 _ _)).trans hdiv
   have hprod:=Finset.prod_ne_zero_iff.mpr fun g hg=>(hT g hg).1.ne_zero
   have hr0:r≠0:= fun hh=>hq (by simp [hr,hh])
   simp only [id_eq] at hr
   have hb' := hj
   rw [hr,degreeOf_mul_eq hprod hr0,degreeOf_prod_eq T (fun g=>g)
     (fun g hg=>(hT g hg).1.ne_zero)] at hb'
   exact (JW _ _).trans hb'
 have hspec (g:af 2) (hg:g∈A) :=
   bpk g (hA g hg) hB hchar
     ((Finset.single_le_sum (fun x _=>v8 x.totalDegree) hg).trans hcap)
 let u := ∏ g∈A,QI g
 refine ⟨T,u,hT,?_,hJ,Finset.prod_ne_zero_iff.mpr (fun g hg=>(hspec g hg).1),?_,?_⟩
 · exact (Finset.sum_le_sum_of_subset_of_nonneg (zT0 _ _)
     (fun g _ _=>v8 g.totalDegree)).trans hcap
 · calc
     u.natDegree ≤ ∑ g∈A,(QI g).natDegree :=Polynomial.natDegree_prod_le _ _
     _ ≤ ∑ g∈A,g.totalDegree*(B - 1) :=KI fun g hg=>(hspec g hg).2.1
     _≤B*(B - 1) := by rw [← Nq]; exact Hw _ hcap
 · intro S hS
   have hroot :nX (jet S) M.prod=0:= by
     have hd:=map_dvd (nX (jet S)) (prod_normalizedFactors hq).symm.dvd
     change cK q S∣ _ at hd
     rwa [hS,zero_dvd_iff] at hd
   rw [map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hroot
   obtain ⟨g,hgM,hgS⟩:=hroot
   have hgA:g∈A:=Multiset.mem_toFinset.mpr hgM
   rcases (hspec g hgA).2.2 S hgS with hzero | ⟨hpos,hreg⟩
   · left
     change y5 S u=0
     rw [show u = ∏ g∈A,QI g from rfl,Lf]
     exact Finset.prod_eq_zero_iff.mpr ⟨g,hgA,hzero⟩
   · exact Or.inr ⟨g,Finset.mem_filter.mpr ⟨hgA,hpos⟩,hreg⟩
end
end bz3
end
section
namespace abG
noncomputable section
open we yz zP MvPolynomial
def c1 :Prop :=
  ∀ (L:Type) [lV L] [oD cH L]
    (I:c9 (eT 4)) (y :oe),oF y∈I.minimalPrimes →
    wN (aUu L y)∈(gN L I).minimalPrimes ∧
      qm L (abV (gN L I) (aUu L y)) ∧
      pz L (abV (gN L I) (aUu L y)) =
        (Ny I y).toNat
def c2 :Prop :=
  ∀ (L:Type) [lV L] [Infinite L] (g:Fin 4→Total L) (y :Fin 4→L),
    wN y∈(H8 fun i=>reduce (g i)).minimalPrimes →
    IsSMulRegular (bi0 g y) (bBT g y)
private theorem dAs {L:Type} [lV L] [Infinite L] (h:c2)
   (g:Fin 4→Total L) {ι:Type} [Fintype ι] (y :ι→Fin 4→L)
   (hy :qG y)
   (hmin : ∀ i,wN (y i)∈(H8 fun j=>reduce (g j)).minimalPrimes)
   (hlocal : ∀ i,qm L (abV (H8 fun j=>reduce (g j)) (y i)))
   [qm (sU L) (aw3 g)] :
   (∑ i,pz L (abV (H8 fun j=>reduce (g j)) (y i))) ≤
     pz (sU L) (aw3 g) := by
 let I:=H8 (fun j=>reduce (g j))
 let s :=Kz fun i=>aoK I (y i)
 have hs :t8 s :=eMy I y hy hmin
 have hrel (p:Total L) (hp:aNY g p=0) :s (reduce p)=0:= by
   funext i
   exact fV1 g (y i) (h L g (y i) (hmin i)) p hp
 let pointModules : ∀ i:ι,Module L (abV I (y i)) :=
   fun i=>xu
 let:Module L ((i:ι)→abV I (y i)) :=Pi.module ι _ L
 let : ∀ i:ι,Module.Free L (abV I (y i)) := fun i=>xu
 let : ∀ i:ι,qm L (abV I (y i)) :=hlocal
 let s' : Affine L →ₗ[L] ((i:ι)→abV I (y i)) :=s.toLinearMap
 have hr :pz L ((i:ι)→abV I (y i)) ≤
     pz (sU L) (aw3 g) := by
   refine de2 (L:=L) (D:=(i:ι)→abV I (y i)) g s' ?_ ?_
   · exact hs
   · exact hrel
 rw [Module.finrank_pi_fintype] at hr
 exact hr
theorem of_children (h1 :c1) (h2 :c2) :zP.c1 := by
  classical
  intro A _ hfinite f hsupport points hpoints
  let L:=fZ A
  have :Infinite L:=Infinite.of_injective (cy cH L) (Xx _)
  let g:=ahx A f
  let I:=H8 (fun i=>reduce (g i))
  let y : ↥points→Fin 4→L:= fun i=>aUu L i.1
  have hI:I=gN L (ke f) :=bZ0 A f hsupport
  have hlocal (i : ↥points) :
      wN (y i)∈I.minimalPrimes ∧
        qm L (abV I (y i)) ∧
        pz L (abV I (y i)) =
          (Ny (ke f) i.1).toNat := by
    rw [hI]
    exact h1 L (ke f) i.1 (hpoints i.1 i.2)
  have hy :qG y := by
    intro i j hij
    apply vG
    funext a
    exact (Xx (cy cH L)) (wR hij a)
  obtain ⟨hfin,hrank⟩:=bZZ A f hfinite
  have :=hfin
  have h:=dAs h2 g y hy (fun i=>(hlocal i).1) (fun i=>(hlocal i).2.1)
  rw [hrank] at h
  calc
    (∑ z∈points,(Ny (ke f) z).toNat) =
        ∑ i : ↥points,pz L (abV I (y i)) := by
      rw [← zKB points (fun z=>(Ny (ke f) z).toNat)]
      exact sH rfl fun i _=>(hlocal i).2.2.symm
    _≤_:=h
end
end abG
end
section
namespace aFQ
noncomputable section
open aR oR we aeC Polynomial
def bDm (P:c9 (eT 3)) :c9 (af 3) :=
 P.comap (ox qY)
abbrev aql (f :af 3) :=LQ (separant f)
def adZ (f :af 3) :af 3 →+* aql f :=cy _ _
def Cm (f :af 3) (P:c9 (eT 3)) :c9 (aql f) :=
 (bDm P).map (adZ f)
def Chart (f :af 3) (P:c9 (eT 3)) :=aql f ⧸ Cm f P
instance gPg (f :af 3) (P:c9 (eT 3)) :nq (Chart f P) :=
 inferInstanceAs (nq (aql f ⧸ Cm f P))
def KM (f :af 3) (P:c9 (eT 3)) :af 3 →+* Chart f P :=
  show af 3 →+* (aql f ⧸ Cm f P) from
    (nI (Cm f P)).comp (adZ f)
def azj (f :af 3) (P:c9 (eT 3)) :Chart f P :=
 nI (Cm f P) (Un (separant f))
theorem aXF (f :af 3) (P:c9 (eT 3)) :
  KM f P (separant f)*azj f P=1 := by
 change nI (Cm f P) (adZ f (separant f)) *
  nI (Cm f P) (Un (separant f))=1
 rw [← lJ,show adZ f (separant f)* Un (separant f)=1
  from IsLocalization.Away.mul_invSelf (separant f),vk]
theorem bm2 (f :af 3) (P:c9 (eT 3)) {b:af 3}
  (hb:fW b∈P) :KM f P b=0 :=
 Ideal.Quotient.eq_zero_iff_mem.mpr (EP _ hb)
private def b7C {R:Type*} [nq R] {f :af 3} (g:af 3 →+* R)
  (hs :qU (g (separant f))) :aql f →+* R :=
 ztx (separant f) hs
def aGX {R:Type*} [nq R] {f :af 3} {P:c9 (eT 3)}
    (g:af 3 →+* R) (hg : ∀ b∈bDm P,g b=0)
    (hs :qU (g (separant f))) :Chart f P →+* R :=
  show (aql f ⧸ Cm f P) →+* R from
    R9 (Cm f P) (b7C g hs) (by
      change (bDm P).map (adZ f)≤oK (b7C g hs)
      rw [zo0]
      intro b hb
      change b7C g hs (adZ f b)=0
      exact (Ts (separant f) hs b).trans (hg b hb))
theorem cE7 {R:Type*} [nq R] {f :af 3} {P:c9 (eT 3)}
  (g:af 3 →+* R) (hg : ∀ b∈bDm P,g b=0)
  (hs :qU (g (separant f))) (b:af 3) :
  aGX g hg hs (KM f P b)=g b :=
 Ts (separant f) hs b
def constants {A:Type*} [nq A] (e :af 3 →+* A) :ao →+* A :=
 e.comp (MvPolynomial.C.comp oY)
def Ub (f :af 3) (P:c9 (eT 3)) :ℕ→Chart f P
 | 0=>KM f P (MvPolynomial.X 0)
 | 1=>KM f P (MvPolynomial.X 1)
 | 2=>KM f P (MvPolynomial.X 2)
 | k+3=>2*KM f P (AR f k) *
     constants (KM f P) (((k+3).factorial:ao)⁻¹) *
     azj f P^(2*k+1)
def aon {A:Type*} [Semiring A] (len:ℕ) (a :ℕ→A) :A[X] :=
 ∑ j:Fin len,vl j.val (a j.val)
def aMK (f :af 3) (P:c9 (eT 3)) : (Chart f P)[X] :=
 aon bf (Ub f P)
def aot (f :af 3) (P:c9 (eT 3)) : (Chart f P)[X] :=
 xL (-KM f P (pQ pL)) (aMK f P)
end
end aFQ
end
section
namespace aF0
noncomputable section
open K1 aR cu qQ Polynomial
open ana
abbrev total:=Bivariate.totalDegree (F:=FX)
def cBx (S:K[X]) :IW →+* FX :=
 WD (y5 (kr S)) (kr S.derivative)
def power (d:ℕ) :ℕ:=2*d-3
def BJ (d b:ℕ) :ℕ:=1+power d*(b - 1)
def YM (d b j:ℕ) :ℕ:=min (BJ d b) (power d*(j - 1)+d)
structure dmu (f :af 2) (d b j:ℕ) where
 cut:K→K→lz (Fin 2) Tv
 ags : ∀ x y,(cut x y).totalDegree≤BJ d b
 top_bound : ∀ x y,(cut x y).degreeOf 1≤YM d b j
 agrees : ∀ S:K[X],S.natDegree≤d→ oR.qg 1 f (extend S) → ∀ x y,
  oy (Ia (extend S)) (cut x y)=0↔S.eval x=y
end
end aF0
end
section
namespace cxS
noncomputable section
open we yz abG MvPolynomial IsLocalRing
open scoped TensorProduct
private theorem fTE {k :Type} [lV k] (y :Fin 4→k) :
    wN y=n5 (qJ fun i=>lI i - C (y i)) := by
  let J:c9 (Affine k) :=n5 (qJ fun i=>lI i - C (y i))
  let q:=nI J
  refine yL ?_ (Ideal.span_le.mpr ?_)
  · have hcomp:q=q.comp (C.comp (eval y)) := by
      apply Mw
      · intro a
        simp
      · intro i
        have h:q (lI i - C (y i))=0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (sI (zWL i))
        simpa [q,qx ,Ar] using h
    intro p hp
    rw [v9,x7] at hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p=0
    rw [hcomp,Gn,Gn,hp,oq,oq]
  · rintro _ ⟨i,rfl⟩
    change lI i - C (y i)∈uh k {y}
    rw [v9]
    simp
private theorem b8F {k L:Type} [lV k] [lV L] [oD k L]
  (y :Fin 4→k) :
  (wN y).map (ox (cy k L)) =
    wN (cy k L ∘ y) := by
 simp only [fTE,zc,← Xp,Function.comp_apply,
  qx ,map_X,map_C]
private theorem dNS {k L:Type} [lV k] [lV L] [oD k L]
   (y :Fin 4→k) :
   (wN (cy k L ∘ y)).comap (ox (cy k L)) =
     wN y := by
 ext p
 rw [Ideal.mem_comap,v9,v9,
   x7,x7,← WW,map_eq_zero_iff _ (Xx _)]
private theorem ey6 {R S:Type} [nq R] [nq S]
  (f :R →+* S) {I p:c9 R} {q:c9 S}
  (hp:I.IsMinimalPrime p) (hq:q.IsPrime) (hm:p.map f=q) (hc:q.comap f=p) :
  (I.map f).IsMinimalPrime q:= by
 refine ⟨⟨hq,hm ▸ Ideal.map_mono hp.le⟩,?_⟩
 intro T hT hTq
 have :=hT.1
 have hTp:T.comap f≤p:=hc ▸ Ideal.comap_mono hTq
 have hpT:p≤T.comap f :=
  hp.2 ⟨Ideal.comap_isPrime _ _,Ideal.map_le_iff_le_comap.mp hT.2⟩ hTp
 exact hm ▸ Ideal.map_le_iff_le_comap.mpr hpT
private theorem dsB {k L:Type} [lV k] [lV L] [oD k L] :
    let:oD (Affine k) (Affine L) :=(ox (cy k L)).toAlgebra
    G6 (Affine k) (Affine L) := by
  let:oD (Affine k) (Affine L) :=(ox (cy k L)).toAlgebra
  let e :=(Algebra.TensorProduct.comm k (Affine k) L).toRingEquiv.trans
    (Wm (σ:=Fin 4) k L).toRingEquiv
  let e' : Affine k ⊗[k] L ≃ₐ[Affine k] Affine L :=
    { e with
      commutes' := fun p=> by
        change Wm k L (1 ⊗ₜ[k] p) =
          ox (cy k L) p
        simp }
  exact Module.Flat.of_linearEquiv e'.symm.toLinearEquiv
private theorem fWR {L:Type} [lV L] (y :Fin 4→L) :
   t8 (cy L (G2 (MZ y))) := by
 let B:=MZ y
 let p:=wN y
 let e :=IsLocalization.AtPrime.equivQuotMaximalIdeal p B
 intro x
 change ∃ a :L,nI (zR B) (cy L B a)=x
 obtain ⟨z,rfl⟩:=e.surjective x
 obtain ⟨P,rfl⟩:=vH z
 have he :nI p (C (eval y P))=nI p P:= by
   rw [Ideal.Quotient.eq,v9,x7,
     qx ,Fa ,Ea]
 refine ⟨eval y P,?_⟩
 rw [zg L (Affine L) B,F9]
 simpa only [e,IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk] using oj e he
private theorem evP {L:Type} [lV L]
  (I:c9 (Affine L)) (y :Fin 4→L) :
  u8 L (abV I y)=u8 (MZ y) (abV I y) := by
 let B:=MZ y
 have :IsLocalHom (cy L B) :=⟨fun a ha =>
  isUnit_iff_ne_zero.mpr (by intro h; subst a; simp at ha)⟩
 have hres :t8 (cy (G2 L) (G2 B)) := by
  intro x
  obtain ⟨a,ha⟩:=fWR y x
  exact ⟨residue L a,ha⟩
 have hlen:u8 (G2 L) (G2 B)=1 := by
  rw [Module.length_eq_of_surjective hres,Yc]
  simp
 rw [IsLocalRing.length_restrictScalars L B (abV I y),hlen,Dw]
theorem proof :abG.c1 := by
  intro L _ _ I y hy
  let:oD (eT 4) (Affine L) :=(ox (cy cH L)).toAlgebra
  let p:=oF y
  let q:=wN (aUu L y)
  have hm:p.map (cy (eT 4) (Affine L))=q:=b8F y
  have hc:q.comap (cy (eT 4) (Affine L))=p:=dNS y
  have hmin:q∈(gN L I).minimalPrimes :=
    ey6 (cy (eT 4) (Affine L)) hy xu hm hc
  have :q.LiesOver p:=⟨hc.symm⟩
  have :G6 (eT 4) (Affine L) :=dsB
  let A:=MZ y
  let B:=MZ (aUu L y)
  let:oD A B:=Localization.AtPrime.algebraOfLiesOver p q
  have :yl (eT 4) A B:=xu
  have :IsLocalHom (cy A B) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  have hmap (J:c9 (eT 4)) :
      (J.map (cy (eT 4) A)).map (cy A B) =
        (gN L J).map (cy (Affine L) B) := by
    change _=(J.map (cy (eT 4) (Affine L))).map (cy (Affine L) B)
    rw [Oc,Oc,← S2 ,
      ← S2]
  have hmax : (zR A).map (cy A B)=zR B:= by
    rw [← zRt (I:=p),hmap]
    change (p.map (cy (eT 4) (Affine L))).map (cy (Affine L) B)= _
    rw [hm,zRt]
  let J:=I.map (cy (eT 4) A)
  have :IsSimpleModule B (B ⧸ zR B) :=
    isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal B).1
  have hlen:=IsLocalRing.length_baseChange A B (A ⧸ J)
  rw [hmax,Module.length_eq_one B (B ⧸ zR B),Dw] at hlen
  have hdim:u8 L (abV (gN L I) (aUu L y)) =
      Ny I y := by
    rw [evP]
    change u8 B (B ⧸ (gN L I).map (cy (Affine L) B)) =
      u8 A (A ⧸ J)
    rw [← hmap I]
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toLinearEquiv.length_eq.trans hlen
  have hfinite :Ny I y < ⊤ := bsa hy
  have :IsNoetherian L (abV (gN L I) (aUu L y)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (Module.length_ne_top_iff.mp (hdim.trans_lt hfinite).ne)).1
  refine ⟨hmin,xu,?_⟩
  simpa only [Yc,ENat.toNat_natCast] using oj ENat.toNat hdim
end
end cxS
end
section
namespace aFQ
noncomputable section
open aR oR we aeC Polynomial
open scoped BigOperators
@[simp] private theorem alJ (b:af 3) (m:Fin 3 →₀ ℕ) :
    (DU b).coeff m=mD (b.coeff m) := by
  classical
  rw [DU,NX]
  simp only [IT,G0]
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,oq]
private theorem a2C (g:ao[X]) :
  DU (pQ g:af 3)=pQ (mD g) := by
 classical
 apply Kl
 intro m
 rw [alJ]
 by_cases hm:0=m <;> simp [zG0,hm]
@[simp] theorem cFY (i:Fin 3) :
   DU (lI i:af 3)=0:= by
  classical
  ext m
  simp only [alJ,MvPolynomial.coeff_X,AddMonoidAlgebra.coeff_zero,
   Finsupp.zero_apply]
  split_ifs <;> simp
private theorem csW (f :af 3) (g:ao[X]) :
  Ev f (pQ g)=separant f*pQ g.derivative := by
 simp [Ev,D3,a2C]
variable {f :af 3} {P:c9 (eT 3)}
private abbrev Dual (f :af 3) (P:c9 (eT 3)) :=
 TrivSqZeroExt (Chart f P) (Chart f P)
private def rowJet (f :af 3) (P:c9 (eT 3)) :af 3 →+* Dual f P where
  toFun b:=(KM f P b,azj f P*KM f P (Ev f b))
  map_zero' := by
    apply Gk
    · exact oq _
    · rw [show (0:af 3)=MvPolynomial.C 0 by rw [map_zero],csW]
      simp
  map_one' := by
    apply Gk
    · exact vk _
    · rw [show (1 :af 3)=MvPolynomial.C 1 by rw [map_one],csW]
      simp
  map_add' b c:= by
    apply Gk
    · exact pG _ _ _
    · change _ *KM f P _ = _ *KM f P _+_ *KM f P _
      rw [bjy.bOL,pG,GF]
  map_mul' b c:= by
    apply Gk
    · exact lJ _ _ _
    · change _ *KM f P _ =
        KM f P b*(_ *KM f P _)+(_ *KM f P _)*KM f P c
      rw [bjy.bhP,pG,lJ,lJ]
      ring
private def U5 (h:aqG f P) :Chart f P →+* Dual f P :=
 aGX (rowJet f P) (fun b hb=> by
  apply Gk
  · exact bm2 f P hb
  · change azj f P*KM f P (Ev f b)=0
    rw [bm2 f P (h b hb),p9])
  (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsUnit.of_mul_eq_one _ (aXF f P)))
private theorem cE5 (h:aqG f P) (b:af 3) :
  U5 h (KM f P b)=rowJet f P b :=
 cE7 _ _ _ b
private theorem cE6 (h:aqG f P) (a :Chart f P) :
   (U5 h a).fst=a := by
 let q:=nI (Cm f P)
 have he : (TrivSqZeroExt.fstHom (Chart f P) (Chart f P) (Chart f P)).toRingHom.comp
     ((U5 h).comp q)=q:= by
   apply zuW (LO (separant f))
   apply Ef
   intro b
   change (U5 h (KM f P b)).fst=KM f P b
   rw [cE5]
   rfl
 obtain ⟨b,rfl⟩:=vH a
 exact Gi he b
def delta (h:aqG f P) :Chart f P →+ Chart f P :=
  (TrivSqZeroExt.sndHom (R:=Chart f P) (M:=Chart f P)).toAddMonoidHom.comp
    (U5 h).toAddMonoidHom
theorem aT8 (h:aqG f P) (a b:Chart f P) :
  delta h (a*b)=a*delta h b+delta h a*b:= by
 change (U5 h (a*b)).snd= _
 rw [lJ]
 change (U5 h a).fst*delta h b+delta h a*(U5 h b).fst= _
 rw [cE6,cE6]
theorem aT7 (h:aqG f P) (b:af 3) :
  delta h (KM f P b)=azj f P*KM f P (Ev f b) := by
 change (U5 h (KM f P b)).snd= _
 rw [cE5]
 rfl
theorem cKh (h:aqG f P) (b:ao[X]) :
   delta h (KM f P (pQ b)) =
     KM f P (pQ b.derivative) := by
 rw [aT7,csW,lJ,← qy ,uz (azj f P),
   aXF,t6]
end
end aFQ
end
section
namespace Mc
noncomputable section
open Polynomial Matrix
def Sm {A:Type} [nq A] (P:Fin 2→ A[X]) (L s :ℕ) :
    Matrix (Fin 2×Fin L) (Fin s) A :=
  fun i j=>(P i.1*pL ^j.val).coeff i.2.val
def a6n {F:Type} [lV F] (P:Fin 2→F[X][X]) (h:ℕ) :
    Fin 2×Fin (h+1)→F[X] :=
  fun i=>(P i.1).coeff i.2.val
def acq {A row:Type} [nq A] {s :ℕ}
    (W:Matrix row (Fin s) A) (rows :Fin s→ row) :A :=
  (W.submatrix rows id).det
end
end Mc
end
