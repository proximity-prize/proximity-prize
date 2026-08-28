import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.GlobalShearZeroCountResearch
import ProximityPrize.SubmissionLower.ContactAdaptiveShearConditional
import ProximityPrize.SubmissionLower.ContactGlobalShearComponentSplitResearch

/-!
# Global-shear agreement-fibre certificate

The middle literal coordinate `R` is replaced by the common separating
parameter `S = R + a Z`.  The affine zero-count theorem therefore needs
separability only for the unchanged Y and Z coordinates, not for R.  This
module transports that exact count to the fibre certificate consumed by the
global incidence ledger.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalShearFiberResearch

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
open ArbitraryRationalProjectionResearch
open CharacteristicFreeInseparableDichotomyResearch
open ContactAdaptiveShearConditional ContactPrimeSeedIncidence
open ContactGlobalShearComponentSplitResearch ContactRegularComponentCover
open ContactPolynomialSolutions ContactTranslation
open GlobalShearZeroCountResearch

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable {K Omega : Type} [Field K] [Field Omega]
variable (phi : Polynomial K →+* Omega)
variable [IsAlgClosed Omega]
variable (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega

/-- Transport the weak sheared zero count to the exact agreement-fibre
certificate.  Notice that there is deliberately no separability assumption
on the original R projection. -/
theorem globalShearFiberCertificate_of_YZ_separable
    (hfinite : ProjectionsFinite Omega P)
    (hsep0 : ∀ h0 : Transcendental Omega (coordinate Omega P 0),
      letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
        rationalBaseAlgebra Omega P 0 h0
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P))
    (hsep2 : ∀ h2 : Transcendental Omega (coordinate Omega P 2),
      letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
        rationalBaseAlgebra Omega P 2 h2
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P))
    (a : Omega)
    (hS : Transcendental Omega (shearedFieldCoordinate Omega P a))
    (hfiniteS :
      letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
        (elementEmbedding Omega (CoordinateField Omega P)
          (shearedFieldCoordinate Omega P a) hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Omega) (CoordinateField Omega P))
    (hsepS :
      letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
        (elementEmbedding Omega (CoordinateField Omega P)
          (shearedFieldCoordinate Omega P a) hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P))
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Gamma : Finset K) (p w dS : ℕ) [CharP Omega p] (hchar : w < p)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ gamma ∈ Gamma, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
    (cap : Fin 3 → ℕ)
    (hdS : dS =
      (letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
        (elementEmbedding Omega (CoordinateField Omega P)
          (shearedFieldCoordinate Omega P a) hS).toRingHom.toAlgebra
       Module.finrank (RatFunc Omega) (CoordinateField Omega P))) :
    GlobalShearFiberCertificate phi P F selected Gamma w dS cap := by
  intro x u0 u1 hproper hcap
  classical
  let fiber := Gamma.filter
    (fun gamma ↦ (selected gamma).eval x = u0 + gamma * u1)
  let points := fiber.image (selectedPoint phi selected)
  have hpointsP : ∀ v ∈ points,
      P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact hpoint gamma (Finset.mem_filter.mp hgamma).1
  have hpointsA : ∀ v ∈ points,
      MvPolynomial.aeval v (agreementPolynomial phi F w x u0 u1) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hGamma, hagree⟩ := Finset.mem_filter.mp hgamma
    exact (selected_agreement_zero_iff phi F selected p w hchar gamma
      (hdegree gamma hGamma) (hsolution gamma hGamma) (hregular gamma hGamma)
      x u0 u1).mpr hagree
  have hcount := finite_zero_points_le_global_sheared_box
    Omega P hfinite hsep0 hsep2 a hS hfiniteS hsepS
    (agreementPolynomial phi F w x u0 u1) hproper cap hcap
    points hpointsP hpointsA
  have hcard : points.card = fiber.card :=
    Finset.card_image_of_injective _ (selectedPoint_injective phi selected)
  rw [hcard] at hcount
  rw [globalShearCost_eq, hdS]
  exact hcount

/-- Regular-component specialization: summed Y/Z budgets below the
characteristic discharge the two literal-coordinate separability inputs.
This is the exact per-component consumer of the global common-shear data. -/
theorem regularComponent_globalShearFiberCertificate
    (G T H : MvPolynomial (Fin 3) Omega)
    (C : RegularComponent Omega G T H)
    (p : ℕ) [CharP Omega p] (hp : p ≠ 0)
    (hfinite : ∀ D : RegularComponent Omega G T H,
      ProjectionsFinite Omega D.1)
    (BY BZ : ℕ)
    (hYsum : (∑ D : RegularComponent Omega G T H,
      actualCoordinateDegree Omega D.1 0) ≤ BY)
    (hZsum : (∑ D : RegularComponent Omega G T H,
      actualCoordinateDegree Omega D.1 2) ≤ BZ)
    (hBYp : BY < p) (hBZp : BZ < p)
    (a : Omega)
    (hS : Transcendental Omega (shearedFieldCoordinate Omega C.1 a))
    (hfiniteS :
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (shearedFieldCoordinate Omega C.1 a) hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
    (hsepS :
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (shearedFieldCoordinate Omega C.1 a) hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Gamma : Finset K) (w dS : ℕ) (hchar : w < p)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ gamma ∈ Gamma, C.1 ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
    (cap : Fin 3 → ℕ)
    (hdS : dS =
      (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (shearedFieldCoordinate Omega C.1 a) hS).toRingHom.toAlgebra
       Module.finrank (RatFunc Omega) (CoordinateField Omega C.1))) :
    GlobalShearFiberCertificate phi C.1 F selected Gamma w dS cap := by
  have hsep0 : ∀ h0 : Transcendental Omega (coordinate Omega C.1 0),
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        rationalBaseAlgebra Omega C.1 0 h0
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1) := by
    intro h0
    exact family_coordinate_isSeparable_of_sum_degree_lt_char
      Omega (fun D : RegularComponent Omega G T H ↦ D.1)
      p hp hfinite 0 BY hYsum hBYp C h0
  have hsep2 : ∀ h2 : Transcendental Omega (coordinate Omega C.1 2),
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        rationalBaseAlgebra Omega C.1 2 h2
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1) := by
    intro h2
    exact family_coordinate_isSeparable_of_sum_degree_lt_char
      Omega (fun D : RegularComponent Omega G T H ↦ D.1)
      p hp hfinite 2 BZ hZsum hBZp C h2
  exact globalShearFiberCertificate_of_YZ_separable phi C.1
    (hfinite C) hsep0 hsep2 a hS hfiniteS hsepS F selected Gamma
    p w dS hchar hdegree hsolution hregular hpoint cap hdS

end

end ProximityPrize.SubmissionLower.ContactGlobalShearFiberResearch

#print axioms ProximityPrize.SubmissionLower.ContactGlobalShearFiberResearch.globalShearFiberCertificate_of_YZ_separable
#print axioms ProximityPrize.SubmissionLower.ContactGlobalShearFiberResearch.regularComponent_globalShearFiberCertificate
