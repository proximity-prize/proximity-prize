import ProximityPrize.SubmissionLower.Q4

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactProperMultiplicitySymbolic6735Research
open ContactProperDelayedTailCertificate6735Research
open ContactGenericInitialPoint
open ContactFlagBezout6543Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactOriginalFactorLocalDVR6731Research
open ContactLocalHypersurfaceBridge6731Research
open ContactSymbolicPowerTransport6732Research
open ContactTaylorNumerators
open ContactFirstTailCertificate6731Research
open ContactNumeratorFactorScaling6731Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
theorem exists_original_multiplier_for_localMultiplicity
    (S:Stage K I Gamma x p flag)
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6735Research.w+1))
    (C:FirstTailComponent S):
    let d:=originalData S C
    let mu:=localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C
    ∃ s:MvPolynomial (Fin 4) K,
      s∉componentPrime S C∧
      s*numerator K d.factor
        (ContactTwoTailParameters6735Research.w+1)∈
          factorIdeal d.factor ⊔ componentPrime S C^mu:=by
  let d:=originalData S C
  let family:=canonicalLocalDVRFamily S hfirstProper
  let mu:=localMultiplicity S family C
  let N:=numerator K d.factor
    (ContactTwoTailParameters6735Research.w+1)
  let p0:=componentPrime S C
  let I0:=factorIdeal d.factor
  let q0:=quotientPrime I0 p0
  let R:=LocalRing S C
  letI:IsDomain R:=family.domain C
  letI:IsDiscreteValuationRing R:=family.dvr C
  have hmuPos:1 ≤ mu:=one_le_localMultiplicity S hfirstProper C
  have horder:IsDiscreteValuationRing.addVal R (localImage S C N)=mu:=by
    change IsDiscreteValuationRing.addVal R (localImage S C N)=
      (IsDiscreteValuationRing.addVal R (localImage S C N)).toNat
    apply (ENat.coe_toNat ?_).symm
    intro htop
    change 1 ≤ (IsDiscreteValuationRing.addVal R (localImage S C N)).toNat at hmuPos
    rw [htop] at hmuPos
    simp at hmuPos
  obtain ⟨uniformizer,hUniformizer⟩:=
    IsDiscreteValuationRing.exists_irreducible R
  have hdvd:uniformizer^mu∣localImage S C N:=by
    apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
    rw [hUniformizer.addVal_pow,horder]
  have hxMax:localImage S C N∈IsLocalRing.maximalIdeal R^mu:=by
    rw [hUniformizer.maximalIdeal_eq,Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact hdvd
  haveI:I0.IsPrime:=factorIdeal_isPrime d.factor d.irreducible
  haveI:q0.IsPrime:=quotientPrime_isPrime I0 p0 (factorLe S C)
  exact exists_multiplier_mem_sup_pow_of_localized_mem
    I0 p0 (factorLe S C) q0 rfl N mu hxMax
theorem proper_global_tail_mem_projected_primary
    {B:Type*} [CommRing B]
    (S:Stage K I Gamma x p flag)
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6735Research.w+1))
    (C:FirstTailComponent S)
    (f:MvPolynomial (Fin 4) K →+*B)
    (surface tail scalar:B) (J:Ideal B) [J.IsMaximal]
    (hfactor:f (originalData S C).factor∈Ideal.span {surface})
    (hsurface:surface∈J)
    (hcontract:Ideal.comap f J=componentPrime S C)
    (htail:tail=f (numerator K S.F
      (ContactTwoTailParameters6735Research.w+1))*scalar):
    tail∈Ideal.span {surface} ⊔
      J^localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C:=by
  let d:=originalData S C
  let mu:=localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C
  let b:=ContactTwoTailParameters6735Research.w+1
  let Nfactor:=numerator K d.factor b
  let Q:=Ideal.span {surface} ⊔ J^mu
  obtain ⟨s,hsnot,hsN⟩:=
    exists_original_multiplier_for_localMultiplicity S hfirstProper C
  have hmapI:Ideal.map f (factorIdeal d.factor) ≤ Ideal.span {surface}:=by
    rw [factorIdeal,Ideal.map_span,Set.image_singleton,Ideal.span_le]
    exact Set.singleton_subset_iff.mpr hfactor
  have hmapP:Ideal.map f (componentPrime S C) ≤ J:=by
    rw [Ideal.map_le_iff_le_comap,hcontract]
  have hmapPow:Ideal.map f (componentPrime S C^mu) ≤ J^mu:=by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmapP mu
  have htarget:Ideal.map f
      (factorIdeal d.factor ⊔ componentPrime S C^mu) ≤ Q:=by
    rw [Ideal.map_sup]
    exact sup_le (hmapI.trans le_sup_left) (hmapPow.trans le_sup_right)
  have hmul:f s*f Nfactor∈Q:=by
    rw [←map_mul]
    exact htarget (Ideal.mem_map_of_mem f hsN)
  have hfs:f s∉J:=by
    intro hsJ
    apply hsnot
    rw [←hcontract]
    exact hsJ
  have hmuPos:1 ≤ mu:=one_le_localMultiplicity S hfirstProper C
  have hNfactor:f Nfactor∈Q:=
    mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
      surface (f Nfactor) (f s) J hsurface mu hmuPos hfs hmul
  have hdiff:d.factor∣numerator K S.F b-
      d.cofactor^(2*b)*Nfactor:=
    factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
      d.product b
  have hdiffMap:f (numerator K S.F b-
      d.cofactor^(2*b)*Nfactor)∈Ideal.span {surface}:=
    (Ideal.span {surface}).mem_of_dvd (map_dvd f hdiff) hfactor
  have hproduct:f (d.cofactor^(2*b)*Nfactor)∈Q:=by
    rw [map_mul]
    exact Q.mul_mem_left _ hNfactor
  have hwhole:f (numerator K S.F b)∈Q:=by
    have hdiffQ:f (numerator K S.F b-
        d.cofactor^(2*b)*Nfactor)∈Q:=
      (show Ideal.span {surface} ≤ Q from le_sup_left) hdiffMap
    have hadd:=Q.add_mem hdiffQ hproduct
    simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using hadd
  rw [htail]
  exact Q.mul_mem_right scalar hwhole
end
end ProximityPrize.SubmissionLower.ContactProperMultiplicitySymbolic6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperFlagFiberData6733Research
open ContactProperDelayedTailCertificate6735Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFlagBezout6543Research
open ContactFlagPlaneFiberPrimary6733Research
open ContactFlagPlaneSurfaceLocalAdapter6732Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactFirstTailCertificate6731Research
open ContactTaylorNumerators
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open ContactFlagTriangularProjectionResearch
noncomputable section
set_option autoImplicit false
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
abbrev StageComponent (S:Stage K I Gamma x p flag):=FirstTailComponent S
def stageSurfacePlane (S:Stage K I Gamma x p flag)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
    PlaneRing (GenericField K):=
  flagPlaneMap (GenericField K) lam mu nu order S.G
def stageTailPlane (S:Stage K I Gamma x p flag)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
    PlaneRing (GenericField K):=
  flagPlaneMap (GenericField K) lam mu nu order
    (globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6735Research.w+1))
def stageFiberTargetMap (_S:Stage K I Gamma x p flag)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
    MvPolynomial (Fin 4) K →+*Polynomial (FiberCoefficient q hq):=
  ((fiberLocalizePlane q hq).comp
    (flagPlaneMap (GenericField K) lam mu nu order)).comp
      (surfaceMap (polynomialEmbedding K))
def stageFiberScalar (_S:Stage K I Gamma x p flag)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
    Polynomial (FiberCoefficient q hq):=
  fiberLocalizePlane q hq
    (flagPlaneMap (GenericField K) lam mu nu order
      (MvPolynomial.C ((-polynomialEmbedding K Polynomial.X)^
        (ContactTwoTailParameters6735Research.w+1))))
end
end ProximityPrize.SubmissionLower.ContactProperFlagFiberData6733Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperFlagIndexedFiberData6735Research
open ContactProperDelayedTailCertificate6735Research ContactProperMultiplicitySymbolic6735Research
open ContactGenericInitialPoint ContactGenericSurface ContactFlagBezout6543Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedFiberCertificate6733Research
open ContactFlagPlaneFiberPrimary6733Research
open ContactProperFlagFiberData6733Research
open ContactFlagPlaneSurfaceLocalAdapter6732Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactFirstTailCertificate6731Research ContactRegularComponentCover
open ContactOriginalFactorLocalDVR6731Research ContactTaylorNumerators
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open ArbitraryPlaneEvaluationFamilyResearch ContactFlagTriangularProjectionResearch
open ContactFlagAffineFamilyDegree6543Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {A:Type} [Fintype A]
theorem indexedStageSurface_mem_relation
    (S:Stage K I Gamma x p flag)
    (component:A → StageComponent S)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (ht:∀ a:A,Transcendental (GenericField K)
      (flagEvaluation (GenericField K) (component a).1 lam mu nu
        (MvPolynomial.X (order 0)))) (a:A):
    stageSurfacePlane S lam mu nu order∈
      relationKernel (GenericField K)
        (CoordinateField (GenericField K) (component a).1) order
        (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
  change planeEvaluation (GenericField K)
    (CoordinateField (GenericField K) (component a).1) order
      (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
        (planeMap (GenericField K) order (flagAlgHom lam mu nu S.G))=0
  rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
  change flagEvaluation (GenericField K) (component a).1 lam mu nu
    (flagAlgHom lam mu nu S.G)=0
  rw [flagEvaluation_flag]
  change S.G∈RingHom.ker
    (coordinateEvaluation (GenericField K) (component a).1).toRingHom
  rw [coordinateEvaluation_ker]
  exact regularComponent_G_mem (GenericField K) S.G _ _ (component a)
theorem indexedStageTail_mem_relation
    (S:Stage K I Gamma x p flag)
    (component:A → StageComponent S)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (ht:∀ a:A,Transcendental (GenericField K)
      (flagEvaluation (GenericField K) (component a).1 lam mu nu
        (MvPolynomial.X (order 0)))) (a:A):
    stageTailPlane S lam mu nu order∈
      relationKernel (GenericField K)
        (CoordinateField (GenericField K) (component a).1) order
        (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
  let tail:=globalTailCut (polynomialEmbedding K) S.F
    (ContactTwoTailParameters6735Research.w+1)
  change planeEvaluation (GenericField K)
    (CoordinateField (GenericField K) (component a).1) order
      (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
        (planeMap (GenericField K) order (flagAlgHom lam mu nu tail))=0
  rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
  change flagEvaluation (GenericField K) (component a).1 lam mu nu
    (flagAlgHom lam mu nu tail)=0
  rw [flagEvaluation_flag]
  change tail∈RingHom.ker
    (coordinateEvaluation (GenericField K) (component a).1).toRingHom
  rw [coordinateEvaluation_ker]
  exact regularComponent_T_mem (GenericField K) S.G tail _ (component a)
structure IndexedFiberProjectionData
    (S:Stage K I Gamma x p flag) (component:A → StageComponent S)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (ht:∀ a:A,Transcendental (GenericField K)
      (flagEvaluation (GenericField K) (component a).1 lam mu nu
        (MvPolynomial.X (order 0))))
    (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
    (a:IndexedFactorFiber component lam mu nu order ht q):Prop where
  relationMax:(indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal
  factor_mem:stageFiberTargetMap S lam mu nu order q hq
    (originalData S (component a.1)).factor∈
      Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)}
  surface_mem:indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)∈
    indexedFiberRelation component lam mu nu order ht q hq a
  contract:(indexedFiberRelation component lam mu nu order ht q hq a).comap
    (stageFiberTargetMap S lam mu nu order q hq)=componentPrime S (component a.1)
  tail_eq:indexedFiberTail q hq (stageTailPlane S lam mu nu order)=
    stageFiberTargetMap S lam mu nu order q hq
      (numerator K S.F (ContactTwoTailParameters6735Research.w+1))*
        stageFiberScalar S lam mu nu order q hq
theorem indexedFiberProjectionData
    (S:Stage K I Gamma x p flag) (component:A → StageComponent S)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (ht:∀ a:A,Transcendental (GenericField K)
      (flagEvaluation (GenericField K) (component a).1 lam mu nu
        (MvPolynomial.X (order 0))))
    (hfinite:∀ a:A,
      letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      FiniteDimensional (RatFunc (GenericField K))
        (CoordinateField (GenericField K) (component a).1))
    (hgen:∀ a:A,
      letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      IntermediateField.adjoin (RatFunc (GenericField K))
        ({flagEvaluation (GenericField K) (component a).1 lam mu nu
            (MvPolynomial.X (order 2)),
          flagEvaluation (GenericField K) (component a).1 lam mu nu
            (MvPolynomial.X (order 1))}:
          Set (CoordinateField (GenericField K) (component a).1))=⊤)
    (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
    (a:IndexedFactorFiber component lam mu nu order ht q):
    IndexedFiberProjectionData S component lam mu nu order ht q hq a:=by
  let phi:=polynomialEmbedding K
  let plane:=flagPlaneMap (GenericField K) lam mu nu order
  let localize:=fiberLocalizePlane q hq
  let J:=indexedFiberRelation component lam mu nu order ht q hq a
  refine ⟨indexedFiberRelation_isMaximal component lam mu nu order ht
    hfinite hgen q hq a,?_,?_,?_,?_⟩
  · rw [Ideal.mem_span_singleton]
    exact map_dvd (localize.comp plane) (originalData S (component a.1)).factor_dvd
  · exact Ideal.mem_map_of_mem localize
      (indexedStageSurface_mem_relation S component lam mu nu order ht a.1)
  · have hplane:(relationKernel (GenericField K)
        (CoordinateField (GenericField K) (component a.1).1) order
        (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
          (ht a.1)).comap plane=(component a.1).1:=by
      change (relationKernel (GenericField K)
        (CoordinateField (GenericField K) (component a.1).1) order
        (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
          (ht a.1)).comap
        ((planeMap (GenericField K) order).comp (flagAlgHom lam mu nu).toRingHom)=_
      rw [←Ideal.comap_comap,relationKernel_contract,
        flagEvaluation_kernel_contract]
    change J.comap ((localize.comp plane).comp (surfaceMap phi))=
      componentPrime S (component a.1)
    rw [←Ideal.comap_comap, ←Ideal.comap_comap,
      indexedFiberRelation_under,hplane]
    rfl
  · change localize (plane (globalTailCut phi S.F
      (ContactTwoTailParameters6735Research.w+1)))=
      localize (plane (surfaceMap phi (numerator K S.F
        (ContactTwoTailParameters6735Research.w+1))))*
        localize (plane (MvPolynomial.C
          ((-phi Polynomial.X)^(ContactTwoTailParameters6735Research.w+1))))
    rw [globalTailCut_eq,map_mul,map_mul]
end
end ProximityPrize.SubmissionLower.ContactProperFlagIndexedFiberData6735Research
end
