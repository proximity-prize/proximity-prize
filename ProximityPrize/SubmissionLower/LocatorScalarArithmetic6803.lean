import ProximityPrize.SubmissionLower.PackedLegacy

/-!
# Seedless scalar interpolation arithmetic for the 68.03 row

Rather than require an unproved rank saving for the old `(96,132,28)`
kernel, this receipt moves to `(97,133,29)`.  The resulting list allowance is
slightly larger, but the grouped derivative ledger has far more than enough
margin to absorb it.
-/

namespace ProximityPrize.SubmissionLower.LocatorScalarArithmetic6803

open scoped BigOperators
open ProximityPrize.Benchmark RCN279

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80781
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def prime : ℕ := 2130706433
def multiplicity : ℕ := 97
def yTotalCap : ℕ := 133
def slopeCap : ℕ := 29
def weightedCap : ℕ := multiplicity * agreements
def listBudget : ℕ := 5224816755
def capY : ℕ := 1 + 2 * w * yTotalCap
def capR : ℕ := w * (2 * slopeCap - 1)
def regularListNumerator : ℕ :=
  (n - w) * (capY * slopeCap + capR * yTotalCap)
def singularListCap : ℕ := (2 * slopeCap - 1) * yTotalCap
def listNumerator : ℕ := regularListNumerator + singularListCap * gap

theorem parameter_values :
    agreements = 181363 ∧ gap = 50292 ∧ weightedCap = 17592211 ∧
      capY = 34864887 ∧ capR = 7471047 ∧ singularListCap = 7581 := by
  native_decide

theorem coefficient_count_exact :
    coefficientCount weightedCap w yTotalCap slopeCap = 28561064000 := by
  native_decide

theorem local_rank_exact :
    localRankBound multiplicity yTotalCap slopeCap = 108950 := by
  native_decide

theorem nullity_exact :
    coefficientCount weightedCap w yTotalCap slopeCap -
      n * localRankBound multiplicity yTotalCap slopeCap = 475200 := by
  rw [coefficient_count_exact, local_rank_exact]
  native_decide

theorem interpolation_gate :
    n * localRankBound multiplicity yTotalCap slopeCap <
      coefficientCount weightedCap w yTotalCap slopeCap := by
  rw [coefficient_count_exact, local_rank_exact]
  native_decide

theorem list_numerator_exact : listNumerator = 262766484218754 := by
  native_decide

theorem list_numerator_fits : listNumerator < listBudget * gap := by
  native_decide

theorem exists_seedless_interpolant
    (received : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w yTotalCap slopeCap ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        RCN119.slopeDifference IRSProfile.Field ^ (multiplicity - r) ∣
          (RCN319.homogenizedTranslation IRSProfile.Field
            (IRSProfile.domain i) (received i) 0 Q).coeff r := by
  obtain ⟨theta, htheta, hzero⟩ := exists_nonzero_kernel_array
    IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
    IRSProfile.domain received (by
      rw [show Fintype.card IRSProfile.Index = n by
        norm_num [IRSProfile.Index, n]]
      exact interpolation_gate)
  refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
    reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
    reconstruct_mem_box IRSProfile.Field _ _ _ _ theta, ?_⟩
  intro i r
  have hdiv := all_blocks_divisible_of_kernel IRSProfile.Field
    weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received
    theta hzero i r
  rw [← translation_reconstruct_coeff IRSProfile.Field weightedCap w
    yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
  exact hdiv

end

end ProximityPrize.SubmissionLower.LocatorScalarArithmetic6803
