import ProximityPrize.SubmissionLower.PartG048


section Compact_RootMultiplicityDichotomy
/-! The algebraic split behind the second-jet helper/height argument. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityDichotomy
noncomputable section
set_option autoImplicit false
variable {L : Type*} [Field L]

theorem derivative_or_high_multiplicity (P : Polynomial L) (hP : P ≠ 0)
    (t : L) (k : ℕ) (hk : (k.factorial : L) ≠ 0) :
    (∃ d ≤ k, ((Polynomial.derivative)^[d] P).eval t ≠ 0) ∨
      (Polynomial.X-Polynomial.C t)^(k+1) ∣ P := by
  classical
  rcases Classical.em (∀ d ≤ k, ((Polynomial.derivative)^[d] P).eval t = 0) with hroot | hroot
  · right
    have hm := Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
      hP hroot (mem_nonZeroDivisors_iff_ne_zero.mpr hk)
    exact (pow_dvd_pow (Polynomial.X-Polynomial.C t) hm).trans (P.pow_rootMultiplicity_dvd t)
  · left
    push_neg at hroot
    exact hroot

end
end ProximityPrize.SubmissionLower.RootMultiplicityDichotomy

end Compact_RootMultiplicityDichotomy
