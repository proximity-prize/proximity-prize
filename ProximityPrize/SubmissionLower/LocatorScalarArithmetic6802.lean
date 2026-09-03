import ProximityPrize.SubmissionLower.LocatorResidual6802

namespace ProximityPrize.SubmissionLower.LocatorScalarArithmetic6802

open scoped BigOperators
open ProximityPrize.Benchmark RCN279 RCN285

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80771
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def prime : ℕ := 2130706433
def multiplicity : ℕ := 95
def yTotalCap : ℕ := 131
def slopeCap : ℕ := 28
def weightedCap : ℕ := multiplicity * agreements
def listBudget : ℕ := 4966260664
def capY : ℕ := 1 + 2 * w * yTotalCap
def capR : ℕ := w * (2 * slopeCap - 1)
def regularListNumerator : ℕ :=
  (n - w) * (capY * slopeCap + capR * yTotalCap)
def singularListCap : ℕ := (2 * slopeCap - 1) * yTotalCap
def listNumerator : ℕ := regularListNumerator + singularListCap * gap

/-- One coefficient row for the 68.02 seedless interpolant.  Keeping this
receipt in the `RCN279` geometry avoids accidentally selecting the unrelated
fast-kernel coefficient oracle through an `open` declaration. -/
def coefficientRow (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range 29,
    min 1 (132 - i - j) * (17230435 - 131071 * i - 131070 * j)

/-- One local contact-rank row in the original seedless-contact oracle. -/
def rankRow (r : ℕ) : ℕ :=
  RCN285.seedlessContactRankBound (min r 131) 131 28 (95 - r)

theorem coefficient_chunk_0 :
    (∑ i ∈ Finset.range 16, coefficientRow i) = 6687364040 := by decide

theorem coefficient_chunk_16 :
    (∑ i ∈ Finset.range 16, coefficientRow (16 + i)) = 5714292936 := by decide

theorem coefficient_chunk_32 :
    (∑ i ∈ Finset.range 16, coefficientRow (32 + i)) = 4741221832 := by decide

theorem coefficient_chunk_48 :
    (∑ i ∈ Finset.range 16, coefficientRow (48 + i)) = 3768150728 := by decide

theorem coefficient_chunk_64 :
    (∑ i ∈ Finset.range 16, coefficientRow (64 + i)) = 2795079624 := by decide

theorem coefficient_chunk_80 :
    (∑ i ∈ Finset.range 16, coefficientRow (80 + i)) = 1822008520 := by decide

theorem coefficient_chunk_96 :
    (∑ i ∈ Finset.range 16, coefficientRow (96 + i)) = 862500188 := by decide

theorem coefficient_chunk_112 :
    (∑ i ∈ Finset.range 16, coefficientRow (112 + i)) = 185041840 := by decide

theorem coefficient_chunk_128 :
    (∑ i ∈ Finset.range 4, coefficientRow (128 + i)) = 1912060 := by decide

theorem rank_chunk_0 :
    (∑ r ∈ Finset.range 24, rankRow r) = 8700 := by decide

theorem rank_chunk_24 :
    (∑ r ∈ Finset.range 24, rankRow (24 + r)) = 25404 := by decide

theorem rank_chunk_48 :
    (∑ r ∈ Finset.range 24, rankRow (48 + r)) = 41428 := by decide

theorem rank_chunk_72 :
    (∑ r ∈ Finset.range 23, rankRow (72 + r)) = 25852 := by decide

theorem coefficient_count_exact :
    coefficientCount weightedCap w yTotalCap slopeCap = 26577571768 := by
  change (∑ i ∈ Finset.range 132, coefficientRow i) = _
  rw [Finset.sum_range_add coefficientRow 128 4,
    Finset.sum_range_add coefficientRow 112 16,
    Finset.sum_range_add coefficientRow 96 16,
    Finset.sum_range_add coefficientRow 80 16,
    Finset.sum_range_add coefficientRow 64 16,
    Finset.sum_range_add coefficientRow 48 16,
    Finset.sum_range_add coefficientRow 32 16,
    Finset.sum_range_add coefficientRow 16 16,
    coefficient_chunk_0, coefficient_chunk_16, coefficient_chunk_32,
    coefficient_chunk_48, coefficient_chunk_64, coefficient_chunk_80,
    coefficient_chunk_96, coefficient_chunk_112, coefficient_chunk_128]

theorem local_rank_exact :
    localRankBound multiplicity yTotalCap slopeCap = 101384 := by
  change (∑ r ∈ Finset.range 95, rankRow r) = _
  rw [Finset.sum_range_add rankRow 72 23,
    Finset.sum_range_add rankRow 48 24,
    Finset.sum_range_add rankRow 24 24,
    rank_chunk_0, rank_chunk_24, rank_chunk_48, rank_chunk_72]

theorem nullity_exact :
    coefficientCount weightedCap w yTotalCap slopeCap -
      n * localRankBound multiplicity yTotalCap slopeCap = 364472 := by
  rw [coefficient_count_exact, local_rank_exact]
  decide

theorem interpolation_gate :
    n * localRankBound multiplicity yTotalCap slopeCap <
      coefficientCount weightedCap w yTotalCap slopeCap := by
  rw [coefficient_count_exact, local_rank_exact]
  decide

theorem list_numerator_fits : listNumerator < listBudget * gap := by decide

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

end ProximityPrize.SubmissionLower.LocatorScalarArithmetic6802
