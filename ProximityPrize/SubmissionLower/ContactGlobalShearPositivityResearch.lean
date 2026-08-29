import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveShearConditional

/-! .






 -/

namespace ProximityPrize.SubmissionLower.ContactGlobalShearPositivityResearch

open ActualCurveCoordinateField ActualCurveZeroCount
open ContactAdaptiveShearConditional
open CharacteristicFreeInseparableDichotomyResearch

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K]
variable (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

/-- .
 -/
theorem transcendental_add_smul_of_transcendental_isAlgebraic
    (r z : CoordinateField K P) (a : K)
    (hr : Transcendental K r) (hz : IsAlgebraic K z) :
    Transcendental K (r + a • z) := by
  intro hs
  apply hr
  have hscaled : IsAlgebraic K (a • z) := hz.smul a
  have hsub : IsAlgebraic K ((r + a • z) - a • z) := hs.sub hscaled
  simpa using hsub

/-- .




 -/
theorem globalShearCost_pos_of_seedCoordinate_isAlgebraic
    (hfinite : ProjectionsFinite K P)
    (hnonpoint : ∀ v : Fin 3 → K,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hZ : IsAlgebraic K (coordinate K P 2))
    (a : K) (dS : ℕ) (cap : Fin 3 → ℕ)
    (hSdegree : Transcendental K
        (coordinate K P 1 + a • coordinate K P 2) → 1 ≤ dS)
    (hcapY : 1 ≤ cap 0) (hcapS : 1 ≤ cap 1) :
    1 ≤ globalShearCost P dS cap := by
  obtain ⟨j, hj⟩ :=
    exists_transcendental_coordinate_of_ne_point_kernel K P hnonpoint
  rw [globalShearCost_eq]
  fin_cases j
  · have hdY : 1 ≤ actualCoordinateDegree K P 0 :=
      coordinateDegree_pos_of_transcendental_finite P hfinite 0 hj
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ cap 0 * actualCoordinateDegree K P 0 :=
        Nat.mul_le_mul hcapY hdY
      _ ≤ cap 0 * actualCoordinateDegree K P 0 + cap 1 * dS +
          (cap 2 + cap 1) * actualCoordinateDegree K P 2 := by omega
  · have hS : Transcendental K
        (coordinate K P 1 + a • coordinate K P 2) :=
      transcendental_add_smul_of_transcendental_isAlgebraic
        K P _ _ a hj hZ
    have hdS : 1 ≤ dS := hSdegree hS
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ cap 1 * dS := Nat.mul_le_mul hcapS hdS
      _ ≤ cap 0 * actualCoordinateDegree K P 0 + cap 1 * dS +
          (cap 2 + cap 1) * actualCoordinateDegree K P 2 := by omega
  · exact (hj hZ).elim

end


end ProximityPrize.SubmissionLower.ContactGlobalShearPositivityResearch
