import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

namespace ProximityPrize.SubmissionLower.Koala6831CarrierPrime

open MvPolynomial

variable {R σ : Type*} [CommRing R] [IsDomain R]

theorem irreducible_of_linear_primitive (F : MvPolynomial σ R) (hdegree : F.totalDegree = 1)
    (hprimitive : ∀ a : R, (∀ d, a ∣ F.coeff d) → IsUnit a) : Irreducible F := by
  refine ⟨?_, ?_⟩
  · intro hu
    have hzero := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · intro A B hAB
    have hF : F ≠ 0 := by
      intro h
      rw [h, totalDegree_zero] at hdegree
      omega
    have hprod : A * B ≠ 0 := hAB ▸ hF
    have hA : A ≠ 0 := (mul_ne_zero_iff.mp hprod).1
    have hB : B ≠ 0 := (mul_ne_zero_iff.mp hprod).2
    have hsum : A.totalDegree + B.totalDegree = 1 := by
      rw [← totalDegree_mul_of_isDomain hA hB, ← hAB, hdegree]
    have constant_factor_unit (D P : MvPolynomial σ R)
        (hD : D.totalDegree = 0) (hFD : F = D * P) : IsUnit D := by
      have hconst := totalDegree_eq_zero_iff_eq_C.mp hD
      rw [hconst]
      apply IsUnit.map C
      apply hprimitive
      intro d
      refine ⟨P.coeff d, ?_⟩
      rw [hFD, hconst, coeff_C_mul]
      simp
    rcases (show A.totalDegree = 0 ∨ B.totalDegree = 0 by omega) with hz | hz
    · exact Or.inl (constant_factor_unit A B hz hAB)
    · exact Or.inr (constant_factor_unit B A hz (hAB.trans (mul_comm _ _)))

end ProximityPrize.SubmissionLower.Koala6831CarrierPrime
