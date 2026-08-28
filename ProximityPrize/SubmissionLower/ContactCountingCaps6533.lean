import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactCountingCaps
import ProximityPrize.SubmissionLower.ContactParameters6533

/-!
# Implicit-branch cap adapter for the 65.67 row

The generic cap and characteristic-gate proofs predate the isolated 65.67
degree-vector namespace.  `legacyVector` is only a representation adapter;
all numbers in the resulting caps come from `ContactParameters6533`.
-/

namespace ProximityPrize.SubmissionLower.ContactCountingCaps6533

open ContactParameters6533 ContactInterpolation ContactGenericSurface
open ContactCountingCaps ContactPrimeSeedIncidence

noncomputable section

def legacyVector (v : ContactParameters6533.DegreeVector) :
    ContactAlignmentParameters.DegreeVector := ⟨v.y, v.r, v.z⟩

variable {K Ω : Type} [Field K] [Field Ω]

theorem fixed_implicit_agreement_caps
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ implicitYCap)
    (hR : F.degreeOf 2 ≤ 1) (hZ : F.degreeOf 3 ≤ algebraicCap)
    (x u₀ u₁ : K) :
    HasCaps (agreementPolynomial φ F w x u₀ u₁) (legacyVector liftedAgreement) := by
  have h := surface_agreement_caps φ F implicitYCap 1 algebraicCap (by decide)
    hY hR hZ w (fun j ↦ (j.factorial : K)⁻¹) x u₀ u₁
  simpa [agreementPolynomial, agreementCaps, legacyVector, liftedAgreement] using h

theorem fixed_implicit_surface_caps_below_characteristic :
    ∀ j, capAt (legacyVector liftedSurface) j < prime := by
  intro j
  fin_cases j <;>
    norm_num [capAt, legacyVector, liftedSurface, implicitYCap,
      implicitWeightedCap, algebraicCap, weightedCap,
      ContactParameters6533.multiplicity, agreements, n, errors,
      w, slopeCap, seedTotalCap, prime]

theorem fixed_implicit_characteristic_gates
    (G T : MvPolynomial (Fin 3) Ω)
    (hG : HasCaps G (legacyVector liftedSurface))
    (hT : HasCaps T (legacyVector implicitCut)) :
    (∀ j, G.degreeOf j < prime) ∧
      ∀ j k : Fin 3, j ≠ k →
        T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < prime := by
  apply actual_characteristic_gates G T _ _ prime hG hT
    fixed_implicit_surface_caps_below_characteristic
  · norm_num [ContactAlignmentParameters.mixed, legacyVector, liftedSurface,
      implicitCut, ContactAlignmentParameters.unitY, implicitYCap,
      implicitWeightedCap, algebraicCap, weightedCap,
      ContactParameters6533.multiplicity, agreements, n, errors,
      w, slopeCap, seedTotalCap, prime]
  · norm_num [ContactAlignmentParameters.mixed, legacyVector, liftedSurface,
      implicitCut, ContactAlignmentParameters.unitR, implicitYCap,
      implicitWeightedCap, algebraicCap, weightedCap,
      ContactParameters6533.multiplicity, agreements, n, errors,
      w, slopeCap, seedTotalCap, prime]
  · norm_num [ContactAlignmentParameters.mixed, legacyVector, liftedSurface,
      implicitCut, ContactAlignmentParameters.unitZ, implicitYCap,
      implicitWeightedCap, algebraicCap, weightedCap,
      ContactParameters6533.multiplicity, agreements, n, errors,
      w, slopeCap, seedTotalCap, prime]

end
end ProximityPrize.SubmissionLower.ContactCountingCaps6533

#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps6533.fixed_implicit_agreement_caps
#print axioms ProximityPrize.SubmissionLower.ContactCountingCaps6533.fixed_implicit_characteristic_gates
