import ProximityPrize.SubmissionLower.BCHKSRationalPairKernelTransport6400

/-! # An integral locator-kernel vector as a rational polynomial pair -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRationalPairKernelTransport6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Coefficientwise injection carries an integral locator-kernel vector into
the mapped coordinate kernel. -/
noncomputable def score6400MappedKernelCoordinate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hq : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin) :
    LinearMap.ker
      ((score6400LocatorPolynomialMatrix f₀ f₁).map
        (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X]))).mulVecLin :=
  ⟨(algebraMap IRSProfile.Field[X]
      (FractionRing IRSProfile.Field[X])) ∘ q,
    ringHom_comp_mem_ker_map_mulVec
      (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X]))
      (score6400LocatorPolynomialMatrix f₀ f₁) q hq⟩

/-- Package an integral polynomial-kernel vector as the corresponding member
of the rational bounded-pair kernel. -/
noncomputable def score6400IntegralKernelPair
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hq : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin) :
    score6400LocatorRationalPairKernel f₀ f₁ := by
  let K := FractionRing IRSProfile.Field[X]
  let e := polynomialPairCoordinateEquiv K
    locatorOrdinaryRows6400 locatorFrobeniusRows6400
  let W := LinearMap.ker
    ((score6400LocatorPolynomialMatrix f₀ f₁).map
      (algebraMap IRSProfile.Field[X] K)).mulVecLin
  exact submoduleToComapEquiv e W
    (score6400MappedKernelCoordinate f₀ f₁ q hq)

/-- The packaged pair is exactly the mapped polynomial relation pair. -/
theorem score6400IntegralKernelPair_coe
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hq : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin) :
    (score6400IntegralKernelPair f₀ f₁ q hq).1 =
      (locatorFractionDegreeLT locatorOrdinaryRows6400
          (score6400PolynomialLocatorRelationPair q).1.1
          (score6400PolynomialLocatorRelationPair q).1.2,
        locatorFractionDegreeLT locatorFrobeniusRows6400
          (score6400PolynomialLocatorRelationPair q).2.1
          (score6400PolynomialLocatorRelationPair q).2.2) := by
  let K := FractionRing IRSProfile.Field[X]
  let iota : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let e := polynomialPairCoordinateEquiv K
    locatorOrdinaryRows6400 locatorFrobeniusRows6400
  let W := LinearMap.ker
    ((score6400LocatorPolynomialMatrix f₀ f₁).map iota).mulVecLin
  have hcoe := submoduleToComapEquiv_apply_coe e W
    (score6400MappedKernelCoordinate f₀ f₁ q hq)
  have hrelation := score6400_locatorFractionRelationPair_eq_coordinatePair q
  calc
    (score6400IntegralKernelPair f₀ f₁ q hq).1 =
        e.symm (iota ∘ q) := by
          simpa only [score6400IntegralKernelPair, K, iota, e, W,
            score6400MappedKernelCoordinate] using hcoe
    _ = (locatorFractionDegreeLT locatorOrdinaryRows6400
          (score6400PolynomialLocatorRelationPair q).1.1
          (score6400PolynomialLocatorRelationPair q).1.2,
        locatorFractionDegreeLT locatorFrobeniusRows6400
          (score6400PolynomialLocatorRelationPair q).2.1
          (score6400PolynomialLocatorRelationPair q).2.2) := by
          simpa only [K, iota] using hrelation.symm

@[simp]
theorem score6400IntegralKernelPair_fst
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hq : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin) :
    (score6400IntegralKernelPair f₀ f₁ q hq).1.1.1 =
      (score6400PolynomialLocatorRelationPair q).1.1.map
        (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X])) := by
  have h := congrArg
    (fun p : PolynomialPairSpace (FractionRing IRSProfile.Field[X])
      locatorOrdinaryRows6400 locatorFrobeniusRows6400 ↦ p.1.1)
    (score6400IntegralKernelPair_coe f₀ f₁ q hq)
  simpa only [locatorFractionDegreeLT] using h

@[simp]
theorem score6400IntegralKernelPair_snd
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hq : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin) :
    (score6400IntegralKernelPair f₀ f₁ q hq).1.2.1 =
      (score6400PolynomialLocatorRelationPair q).2.1.map
        (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X])) := by
  have h := congrArg
    (fun p : PolynomialPairSpace (FractionRing IRSProfile.Field[X])
      locatorOrdinaryRows6400 locatorFrobeniusRows6400 ↦ p.2.1)
    (score6400IntegralKernelPair_coe f₀ f₁ q hq)
  simpa only [locatorFractionDegreeLT] using h

end BCHKSRationalPairKernelTransport6400
end ProximityPrize.SubmissionLower
