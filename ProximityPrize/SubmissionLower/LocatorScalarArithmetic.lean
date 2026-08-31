import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.E9
namespace ProximityPrize.SubmissionLower.LocatorScalarArithmetic
open scoped BigOperators
open ProximityPrize.Benchmark
open RCN279
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80378
def agreements:ℕ:=n - errors
def gap:ℕ:=agreements - w
def prime:ℕ:=2130706433
def multiplicity:ℕ:=54
def yTotalCap:ℕ:=74
def slopeCap:ℕ:=16
def weightedCap:ℕ:=multiplicity * agreements
def listBudget:ℕ:=1600000000
def capY:ℕ:=1 + 2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap - 1)
def regularListNumerator:ℕ:=(n-w)*(capY*slopeCap + capR*yTotalCap)
def singularListCap:ℕ:=(2*slopeCap - 1)*yTotalCap
def listNumerator:ℕ:=regularListNumerator + singularListCap*gap
private def coefficientRow (i:ℕ):ℕ :=
 ∑ j ∈ Finset.range (slopeCap + 1),
   min 1 (yTotalCap + 1 - i - j) * (weightedCap - w*i - (w-1)*j)
private theorem coefficient_0 :
 (∑ i ∈ Finset.range 10, coefficientRow i) = 1390087365:=by decide
private theorem coefficient_10 :
 (∑ i ∈ Finset.range 10, coefficientRow (10+i)) = 1167266665:=by decide
private theorem coefficient_20 :
 (∑ i ∈ Finset.range 10, coefficientRow (20+i)) = 944445965:=by decide
private theorem coefficient_30 :
 (∑ i ∈ Finset.range 10, coefficientRow (30+i)) = 721625265:=by decide
private theorem coefficient_40 :
 (∑ i ∈ Finset.range 10, coefficientRow (40+i)) = 498804565:=by decide
private theorem coefficient_50 :
 (∑ i ∈ Finset.range 10, coefficientRow (50+i)) = 275998810:=by decide
private theorem coefficient_60 :
 (∑ i ∈ Finset.range 10, coefficientRow (60+i)) = 82970430:=by decide
private theorem coefficient_70 :
 (∑ i ∈ Finset.range 5, coefficientRow (70+i)) = 4363090:=by decide
theorem coefficient_count_exact :
   coefficientCount weightedCap w yTotalCap slopeCap = 5085562155:=by
 change (∑ i ∈ Finset.range 75, coefficientRow i) = _
 rw [Finset.sum_range_add coefficientRow 70 5,
   Finset.sum_range_add coefficientRow 60 10,
   Finset.sum_range_add coefficientRow 50 10,
   Finset.sum_range_add coefficientRow 40 10,
   Finset.sum_range_add coefficientRow 30 10,
   Finset.sum_range_add coefficientRow 20 10,
   Finset.sum_range_add coefficientRow 10 10,
   coefficient_0, coefficient_10, coefficient_20, coefficient_30,
   coefficient_40, coefficient_50, coefficient_60, coefficient_70] <;> norm_num
private def rankRow (r:ℕ):ℕ :=
 RCN285.seedlessContactRankBound (min r yTotalCap) yTotalCap slopeCap
   (multiplicity-r)
private theorem rank_0 :
 (∑ i ∈ Finset.range 8, rankRow i) = 612:=by decide
private theorem rank_8 :
 (∑ i ∈ Finset.range 8, rankRow (8+i)) = 1700:=by decide
private theorem rank_16 :
 (∑ i ∈ Finset.range 8, rankRow (16+i)) = 2788:=by decide
private theorem rank_24 :
 (∑ i ∈ Finset.range 8, rankRow (24+i)) = 3876:=by decide
private theorem rank_32 :
 (∑ i ∈ Finset.range 8, rankRow (32+i)) = 4891:=by decide
private theorem rank_40 :
 (∑ i ∈ Finset.range 8, rankRow (40+i)) = 4200:=by decide
private theorem rank_48 :
 (∑ i ∈ Finset.range 6, rankRow (48+i)) = 1330:=by decide
theorem local_rank_exact :
   localRankBound multiplicity yTotalCap slopeCap = 19397:=by
 change (∑ i ∈ Finset.range 54, rankRow i) = _
 rw [Finset.sum_range_add rankRow 48 6,
   Finset.sum_range_add rankRow 40 8,
   Finset.sum_range_add rankRow 32 8,
   Finset.sum_range_add rankRow 24 8,
   Finset.sum_range_add rankRow 16 8,
   Finset.sum_range_add rankRow 8 8,
   rank_0, rank_8, rank_16, rank_24, rank_32, rank_40, rank_48] <;> norm_num
theorem nullity_exact :
   coefficientCount weightedCap w yTotalCap slopeCap -
     n*localRankBound multiplicity yTotalCap slopeCap = 754987:=by
 rw [coefficient_count_exact, local_rank_exact]
 decide
theorem interpolation_gate :
   n*localRankBound multiplicity yTotalCap slopeCap <
     coefficientCount weightedCap w yTotalCap slopeCap:=by
 rw [coefficient_count_exact, local_rank_exact]
 decide
theorem list_numeric_values :
   agreements=181766 ∧ gap=50695 ∧ weightedCap=9815364 ∧
   singularListCap=2294 ∧ listNumerator=80092668522644 ∧
   listNumerator/gap+1=1579892860 ∧
   listNumerator<1579892860*gap ∧ 1579892860<listBudget:=by decide
theorem list_numerator_fits:listNumerator < listBudget*gap:=by decide
theorem characteristic_gates:0 < slopeCap ∧ slopeCap < prime ∧ yTotalCap < prime ∧
   (2*slopeCap - 1)*weightedCap < prime ∧ singularListCap < prime:=by decide
theorem shape_gates:multiplicity - 1 + slopeCap ≤ yTotalCap ∧
   weightedCap + slopeCap ≤ w * (yTotalCap + 1):=by decide
theorem exists_seedless_interpolant (received:IRSProfile.Index → IRSProfile.Field) :
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0 ∧ Q ∈ globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       RCN119.slopeDifference IRSProfile.Field ^ (multiplicity-r) ∣
         (RCN319.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
 obtain ⟨theta, htheta, hzero⟩:=exists_nonzero_kernel_array
   IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index = n by norm_num [IRSProfile.Index, n]]
     exact interpolation_gate)
 refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
   reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
   reconstruct_mem_box IRSProfile.Field _ _ _ _ theta, ?_⟩
 intro i r
 have hdiv:=all_blocks_divisible_of_kernel IRSProfile.Field
   weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received theta hzero i r
 rw [← translation_reconstruct_coeff IRSProfile.Field weightedCap w
   yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
 exact hdiv
end
end ProximityPrize.SubmissionLower.LocatorScalarArithmetic
