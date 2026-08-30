import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1
namespace ProximityPrize.SubmissionLower.LocatorArithmetic
open ProximityPrize.Benchmark
open scoped BigOperators NNReal
open RCN100 RCN119 RCN302
open RCN318 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80191
def agreements : ℕ := 181953
def gap : ℕ := 50882
def prime : ℕ := 2130706433
def budget : ℕ := 274980727060991165
def LA : ℕ := 100000
def LB : ℕ := 1471
def weightedA : ℕ := 12736710
def weightedC : ℕ := 8187885
def weightedB : ℕ := 15829911
def fixedRegularCap : ℕ := 273049439447551806
theorem kernelA_rank : localRankBound 70 100000 20 = 4034312100 := by decide
theorem kernelC_rank : localRankBound 45 100000 13 = 1121192233 := by decide
theorem kernelB_rank : localRankBound 87 1471 27 = 116417896 := by decide
theorem kernelA_nullity :
   coefficientCount 12736710 131071 100000 20 -
     262144 * localRankBound 70 100000 20 = 4953442449347 := by
 rw [kernelA_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
   12736710 131071 100000 20 98 (by decide) (by decide)]
 decide
theorem kernelC_nullity :
   coefficientCount 8187885 131071 100000 13 -
     262144 * localRankBound 45 100000 13 = 76094548201 := by
 rw [kernelC_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
   8187885 131071 100000 13 63 (by decide) (by decide)]
 decide
theorem kernelB_nullity :
   coefficientCount 15829911 131071 1471 27 -
     262144 * localRankBound 87 1471 27 = 198775591 := by
 rw [kernelB_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
   15829911 131071 1471 27 121 (by decide) (by decide)]
 decide
theorem C_ys60_quotient_upper :
   coefficientCount 192567 131071 99939 13 = 31536943407 := by
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   192567 131071 99939 13 2 (by decide) (by decide)]
 decide
theorem kernelC_ys60_quotient_lt (r : ℕ) (hr : r ≤ 13) :
   coefficientCount (8187885 - (61 * 131071 - r)) 131071
     (100000 - 61) (13 - r) <
   coefficientCount 8187885 131071 100000 13 -
     262144 * localRankBound 45 100000 13 := by
 rw [kernelC_nullity]
 have hmono := RCN180.Numeric6733.coefficientCount_mono_D_s
   (D := 8187885 - (61 * 131071 - r)) (D' := 192567)
   (w := 131071) (L := 99939) (s := 13 - r) (s' := 13)
   (by omega) (by omega)
 rw [C_ys60_quotient_upper] at hmono
 exact hmono.trans_lt (by decide)
theorem kernelB_total_quotient_lt :
   coefficientCount 15829911 131071 1 27 <
   coefficientCount 15829911 131071 1471 27 -
     262144 * localRankBound 87 1471 27 := by
 rw [kernelB_nullity]
 decide
def fixedSingular : TightParameters := ⟨n, w, agreements, weightedC, 1469, 13⟩
def residualStage : UnequalParameters := ⟨n, w, agreements, 120, 27, LB, 97, 20, LA⟩
def residualSingular : TightParameters := ⟨n, w, agreements, weightedB, LB, 27⟩
theorem fixedSingular_exact : fixedSingular.countCap = 116140099101467 := by decide
theorem residualStage_exact : residualStage.regularCountCap = 777393781818067 := by decide
theorem residualSingular_exact : residualSingular.countCap = 1010836438993856 := by decide
structure SingularGates (P : TightParameters) : Prop where
 s_pos : 1 ≤ P.s
 s_small : P.s < prime
 w_pos : 1 ≤ P.w
 w_small : P.w < prime
 kD : P.w < P.kappa * P.D
 algebraic_pos : 1 ≤ P.algebraicCap
 implicit_small : P.implicitYCap < prime
 algebraic_small : P.algebraicCap < prime
 mixed_small : 2 * P.implicitYCap * P.algebraicCap < prime
 wa : P.w < P.a
 an : P.a ≤ P.n
theorem fixed_singular_gates : SingularGates fixedSingular := by constructor <;> decide
def ledger : ℕ := fixedRegularCap + fixedSingular.countCap +
 residualStage.regularCountCap + residualSingular.countCap + 1
theorem ledger_exact : ledger = 274953809767465197 := by
 rw [ledger, fixedRegularCap, fixedSingular_exact,
   residualStage_exact, residualSingular_exact]
theorem ledger_lt : ledger < budget := by rw [ledger_exact]; decide
def radiusNumerator : ℕ := 10264575
def radiusDenominator : ℕ := 33554432
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
theorem radius_floor :
   ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
 norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
   errors, IRSProfile.Index]
theorem radius_admissible :
   radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
 constructor <;> norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
   IRSProfile.minRelativeDistance]
theorem score_root_integer : (2 : ℕ)^43 * 1000000^100 ≤ 1347234^100 := by decide
theorem score_radius_integer :
   (23289857 : ℕ)^128 * (2^67 * 1347234) ≤ 1000000 * 33554432^128 := by decide
theorem two_rpow_fraction_le :
   (2 : ℝ≥0)^((43 : ℝ)/100) ≤ (1347234 : ℝ≥0)/1000000 := by
 have hroot : ((2 : ℝ≥0)^(43 : ℕ))^((100 : ℝ)⁻¹) ≤ (1347234 : ℝ≥0)/1000000 := by
   rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
   rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
   exact_mod_cast score_root_integer
 calc
   (2 : ℝ≥0)^((43 : ℝ)/100) = ((2 : ℝ≥0)^(43 : ℕ))^((100 : ℝ)⁻¹) := by
     rw [← NNReal.rpow_natCast_mul]
     norm_num [div_eq_mul_inv]
   _ ≤ _ := hroot
theorem radius_power_bound :
   (1 - radius)^IRSProfile.repetitions ≤
     ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1347234) := by
 have hsub : (1 - radius : ℝ≥0) = 23289857/33554432 := by
   have hr : radius ≤ 1 := by
     rw [← NNReal.coe_le_coe]
     norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
   apply NNReal.coe_injective
   rw [NNReal.coe_sub hr]
   norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
 change (1 - radius)^128 ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1347234)
 rw [hsub, div_pow, div_mul_div_comm, one_mul,
   div_le_div_iff₀ (by positivity) (by positivity)]
 exact_mod_cast score_radius_integer
theorem score_target_le :
   (1 - radius)^IRSProfile.repetitions ≤ claimedError 6743 := by
 have hscale : (1000000 : ℝ≥0)/1347234 ≤ (2 : ℝ≥0)^(-((43 : ℝ)/100)) := by
   calc
     (1000000 : ℝ≥0)/1347234 = 1/((1347234 : ℝ≥0)/1000000) := by norm_num
     _ ≤ 1/((2 : ℝ≥0)^((43 : ℝ)/100)) :=
       one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
     _ = _ := by rw [one_div, NNReal.rpow_neg]
 calc
   (1 - radius)^IRSProfile.repetitions ≤
       ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1347234) := radius_power_bound
   _ ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (2 : ℝ≥0)^(-((43 : ℝ)/100)) :=
     mul_le_mul_of_nonneg_left hscale (by positivity)
   _ = claimedError 6743 := by
     unfold claimedError
     rw [show -((((6743 : ℕ) : ℝ)/100)) =
         -((67 : ℕ) : ℝ) + -((43 : ℝ)/100) by norm_num,
       NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
     simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
end
end ProximityPrize.SubmissionLower.LocatorArithmetic
