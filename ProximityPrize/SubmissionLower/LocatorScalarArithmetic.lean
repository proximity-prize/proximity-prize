import ProximityPrize.SubmissionLower.E9
namespace ProximityPrize.SubmissionLower.LocatorScalarArithmetic
open scoped BigOperators
open ProximityPrize.Benchmark RCN279
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80624
def agreements:ℕ:=n - errors
def gap:ℕ:=agreements - w
def prime:ℕ:=2130706433
def multiplicity:ℕ:=76
def yTotalCap:ℕ:=104
def slopeCap:ℕ:=22
def weightedCap:ℕ:=multiplicity * agreements
def listBudget:ℕ:=3081204481
def capY:ℕ:=1 + 2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap - 1)
def regularListNumerator:ℕ:=(n-w)*(capY*slopeCap + capR*yTotalCap)
def singularListCap:ℕ:=(2*slopeCap - 1)*yTotalCap
def listNumerator:ℕ:=regularListNumerator + singularListCap*gap
private def coefficientRow (i:ℕ):ℕ:=
 ∑ j ∈ Finset.range (slopeCap + 1),
   min 1 (yTotalCap + 1 - i - j) * (weightedCap - w*i - (w-1)*j)
private theorem coefficient_0:
 (∑ i ∈ Finset.range 10,coefficientRow i) =2705704015:=by decide
private theorem coefficient_10:
 (∑ i ∈ Finset.range 10,coefficientRow (10+i)) =2404240715:=by decide
private theorem coefficient_20:
 (∑ i ∈ Finset.range 10,coefficientRow (20+i)) =2102777415:=by decide
private theorem coefficient_30:
 (∑ i ∈ Finset.range 10,coefficientRow (30+i)) =1801314115:=by decide
private theorem coefficient_40:
 (∑ i ∈ Finset.range 10,coefficientRow (40+i)) =1499850815:=by decide
private theorem coefficient_50:
 (∑ i ∈ Finset.range 10,coefficientRow (50+i)) =1198387515:=by decide
private theorem coefficient_60:
 (∑ i ∈ Finset.range 10,coefficientRow (60+i)) =896924215:=by decide
private theorem coefficient_70:
 (∑ i ∈ Finset.range 10,coefficientRow (70+i)) =595460915:=by decide
private theorem coefficient_80:
 (∑ i ∈ Finset.range 10,coefficientRow (80+i)) =300411211:=by decide
private theorem coefficient_90:
 (∑ i ∈ Finset.range 10,coefficientRow (90+i)) =88013160:=by decide
private theorem coefficient_100:
 (∑ i ∈ Finset.range 5,coefficientRow (100+i)) =5083480:=by decide
theorem coefficient_count_exact:
   coefficientCount weightedCap w yTotalCap slopeCap=13598167571:=by
 change (∑ i ∈ Finset.range 105,coefficientRow i) =_
 rw [Finset.sum_range_add coefficientRow 100 5,
   Finset.sum_range_add coefficientRow 90 10,
   Finset.sum_range_add coefficientRow 80 10,
   Finset.sum_range_add coefficientRow 70 10,
   Finset.sum_range_add coefficientRow 60 10,
   Finset.sum_range_add coefficientRow 50 10,
   Finset.sum_range_add coefficientRow 40 10,
   Finset.sum_range_add coefficientRow 30 10,
   Finset.sum_range_add coefficientRow 20 10,
   Finset.sum_range_add coefficientRow 10 10,
   coefficient_0,coefficient_10,coefficient_20,coefficient_30,coefficient_40,coefficient_50,coefficient_60,coefficient_70,coefficient_80,coefficient_90,coefficient_100] <;> norm_num
private def rankRow (r:ℕ):ℕ:=
 RCN285.seedlessContactRankBound (min r yTotalCap) yTotalCap slopeCap
   (multiplicity-r)
private theorem rank_0:
 (∑ i ∈ Finset.range 8,rankRow i) =828:=by decide
private theorem rank_8:
 (∑ i ∈ Finset.range 8,rankRow (8+i)) =2300:=by decide
private theorem rank_16:
 (∑ i ∈ Finset.range 8,rankRow (16+i)) =3772:=by decide
private theorem rank_24:
 (∑ i ∈ Finset.range 8,rankRow (24+i)) =5244:=by decide
private theorem rank_32:
 (∑ i ∈ Finset.range 8,rankRow (32+i)) =6716:=by decide
private theorem rank_40:
 (∑ i ∈ Finset.range 8,rankRow (40+i)) =8188:=by decide
private theorem rank_48:
 (∑ i ∈ Finset.range 8,rankRow (48+i)) =9557:=by decide
private theorem rank_56:
 (∑ i ∈ Finset.range 8,rankRow (56+i)) =8760:=by decide
private theorem rank_64:
 (∑ i ∈ Finset.range 8,rankRow (64+i)) =5560:=by decide
private theorem rank_72:
 (∑ i ∈ Finset.range 4,rankRow (72+i)) =940:=by decide
theorem local_rank_exact:
   localRankBound multiplicity yTotalCap slopeCap=51865:=by
 change (∑ i ∈ Finset.range 76,rankRow i) =_
 rw [Finset.sum_range_add rankRow 72 4,
   Finset.sum_range_add rankRow 64 8,
   Finset.sum_range_add rankRow 56 8,
   Finset.sum_range_add rankRow 48 8,
   Finset.sum_range_add rankRow 40 8,
   Finset.sum_range_add rankRow 32 8,
   Finset.sum_range_add rankRow 24 8,
   Finset.sum_range_add rankRow 16 8,
   Finset.sum_range_add rankRow 8 8,
   rank_0,rank_8,rank_16,rank_24,rank_32,rank_40,rank_48,rank_56,rank_64,rank_72] <;> norm_num
theorem interpolation_gate:
   n*localRankBound multiplicity yTotalCap slopeCap <
     coefficientCount weightedCap w yTotalCap slopeCap:=by
 rw [coefficient_count_exact,local_rank_exact]
 decide
theorem list_numerator_fits:listNumerator < listBudget*gap:=by decide
theorem exists_seedless_interpolant (received:IRSProfile.Index → IRSProfile.Field) :
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0 ∧ Q ∈ globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       RCN119.slopeDifference IRSProfile.Field ^ (multiplicity-r) ∣
         (RCN319.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
 obtain ⟨theta,htheta,hzero⟩:=exists_nonzero_kernel_array
   IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index=n by norm_num [IRSProfile.Index,n]]
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
