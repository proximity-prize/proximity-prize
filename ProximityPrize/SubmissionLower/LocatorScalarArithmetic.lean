import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.E9
/- Scalar interpolation certificate for 80289 errors.
   The (multiplicity, Y+R cap, R cap) profile is (48,66,14).
   Finite sums are split into small certificates before recombination. -/
namespace ProximityPrize.SubmissionLower.LocatorScalarArithmetic
open scoped BigOperators
open ProximityPrize.Benchmark
open RCN279
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80289
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def prime : ℕ := 2130706433
def multiplicity : ℕ := 50
def yTotalCap : ℕ := 69
def slopeCap : ℕ := 14
def weightedCap : ℕ := multiplicity * agreements
def listBudget : ℕ := 1300000000
def capY : ℕ := 1 + 2*w*yTotalCap
def capR : ℕ := w*(2*slopeCap - 1)
def regularListNumerator : ℕ := (n-w)*(capY*slopeCap + capR*yTotalCap)
def singularListCap : ℕ := (2*slopeCap - 1)*yTotalCap
def listNumerator : ℕ := regularListNumerator + singularListCap*gap
private def coefficientRow (i : ℕ) : ℕ :=
 ∑ j ∈ Finset.range (slopeCap + 1),
   min 1 (yTotalCap + 1 - i - j) * (weightedCap - w*i - (w-1)*j)
private theorem coefficient_0 :
 (∑ i ∈ Finset.range 10, coefficientRow i) = 1137816075 := by decide
private theorem coefficient_10 :
 (∑ i ∈ Finset.range 10, coefficientRow (10+i)) = 941209575 := by decide
private theorem coefficient_20 :
 (∑ i ∈ Finset.range 10, coefficientRow (20+i)) = 744603075 := by decide
private theorem coefficient_30 :
 (∑ i ∈ Finset.range 10, coefficientRow (30+i)) = 547996575 := by decide
private theorem coefficient_40 :
 (∑ i ∈ Finset.range 10, coefficientRow (40+i)) = 351390075 := by decide
private theorem coefficient_50 :
 (∑ i ∈ Finset.range 10, coefficientRow (50+i)) = 156916355 := by decide
private theorem coefficient_60 :
 (∑ i ∈ Finset.range 10, coefficientRow (60+i)) = 24313685 := by decide
theorem coefficient_count_exact :
   coefficientCount weightedCap w yTotalCap slopeCap = 3904245415 := by
 change (∑ i ∈ Finset.range 70, coefficientRow i) = _
 rw [Finset.sum_range_add coefficientRow 60 10,
   Finset.sum_range_add coefficientRow 50 10,
   Finset.sum_range_add coefficientRow 40 10,
   Finset.sum_range_add coefficientRow 30 10,
   Finset.sum_range_add coefficientRow 20 10,
   Finset.sum_range_add coefficientRow 10 10,
   coefficient_0, coefficient_10, coefficient_20, coefficient_30,
   coefficient_40, coefficient_50, coefficient_60] <;> norm_num
private def rankRow (r : ℕ) : ℕ :=
 RCN285.seedlessContactRankBound (min r yTotalCap) yTotalCap slopeCap
   (multiplicity-r)
private theorem rank_0 :
 (∑ i ∈ Finset.range 10, rankRow i) = 825 := by decide
private theorem rank_10 :
 (∑ i ∈ Finset.range 10, rankRow (10+i)) = 2325 := by decide
private theorem rank_20 :
 (∑ i ∈ Finset.range 10, rankRow (20+i)) = 3825 := by decide
private theorem rank_30 :
 (∑ i ∈ Finset.range 10, rankRow (30+i)) = 5055 := by decide
private theorem rank_40 :
 (∑ i ∈ Finset.range 10, rankRow (40+i)) = 2860 := by decide
theorem local_rank_exact :
   localRankBound multiplicity yTotalCap slopeCap = 14890 := by
 change (∑ i ∈ Finset.range 50, rankRow i) = _
 rw [Finset.sum_range_add rankRow 40 10,
   Finset.sum_range_add rankRow 30 10,
   Finset.sum_range_add rankRow 20 10,
   Finset.sum_range_add rankRow 10 10,
   rank_0, rank_10, rank_20, rank_30, rank_40] <;> norm_num
theorem nullity_exact :
   coefficientCount weightedCap w yTotalCap slopeCap -
     n*localRankBound multiplicity yTotalCap slopeCap = 921255 := by
 rw [coefficient_count_exact, local_rank_exact]
 decide
theorem interpolation_gate :
   n*localRankBound multiplicity yTotalCap slopeCap <
     coefficientCount weightedCap w yTotalCap slopeCap := by
 rw [coefficient_count_exact, local_rank_exact]
 decide
theorem list_numeric_values :
   agreements=181855 ∧ gap=50784 ∧ weightedCap=9092750 ∧
   singularListCap=1863 ∧ listNumerator=65197699995099 ∧
   listNumerator/gap+1=1283823646 ∧
   listNumerator<1283823646*gap ∧ 1283823646<listBudget := by decide
theorem list_numerator_fits : listNumerator < listBudget*gap := by decide
theorem characteristic_gates : 0 < slopeCap ∧ slopeCap < prime ∧ yTotalCap < prime ∧
   (2*slopeCap - 1)*weightedCap < prime ∧ singularListCap < prime := by decide
theorem shape_gates : multiplicity - 1 + slopeCap ≤ yTotalCap ∧
   weightedCap + slopeCap ≤ w * (yTotalCap + 1) := by decide
theorem exists_seedless_interpolant (received : IRSProfile.Index → IRSProfile.Field) :
   ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0 ∧ Q ∈ globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ∧
     ∀ (i : IRSProfile.Index) (r : ℕ),
       RCN119.slopeDifference IRSProfile.Field ^ (multiplicity-r) ∣
         (RCN319.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r := by
 obtain ⟨theta, htheta, hzero⟩ := exists_nonzero_kernel_array
   IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index = n by norm_num [IRSProfile.Index, n]]
     exact interpolation_gate)
 refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
   reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
   reconstruct_mem_box IRSProfile.Field _ _ _ _ theta, ?_⟩
 intro i r
 have hdiv := all_blocks_divisible_of_kernel IRSProfile.Field
   weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received theta hzero i r
 rw [← translation_reconstruct_coeff IRSProfile.Field weightedCap w
   yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
 exact hdiv
end
end ProximityPrize.SubmissionLower.LocatorScalarArithmetic
