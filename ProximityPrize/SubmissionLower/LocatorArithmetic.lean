import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1

namespace ProximityPrize.SubmissionLower.LocatorArithmetic
open ProximityPrize.Benchmark
open scoped NNReal
open RCN100 RCN119 RCN302 RCN318 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80299
def agreements : ℕ := 181845
def gap : ℕ := 50774
def prime : ℕ := 2130706433
def budget : ℕ := 274980726811395087
def LA : ℕ := 109000
def LY : ℕ := 100000
def LB : ℕ := 1799
def weightedY : ℕ := 9092250
def weightedR : ℕ := 9092250
def weightedA77 : ℕ := 14002065
def weightedAmbient : ℕ := 16184205
def weightedB : ℕ := 17638965
def fixedRegularCap : ℕ := 271500000000000000

theorem row_values : agreements + errors = n ∧ agreements - w = gap ∧
    weightedY = 50 * agreements ∧ weightedR = 50 * agreements ∧
    weightedA77 = 77 * agreements ∧ weightedAmbient = 89 * agreements ∧
    weightedB = 97 * agreements ∧ w < agreements ∧
    w + 1 ≤ weightedY ∧ weightedAmbient < prime := by decide

def fixedSingular : TightParameters := ⟨n, w, agreements, weightedR, 1796, 14⟩
def residualStage : UnequalParameters := ⟨n, w, agreements, 134, 30, LB, 123, 27, LA⟩
def residualSingular : TightParameters := ⟨n, w, agreements, weightedB, LB, 30⟩

theorem fixedSingular_exact : fixedSingular.countCap = 184296506270351 := by decide
theorem residualStage_exact : residualStage.regularCountCap = 1135985662308744 := by decide
theorem residualSingular_exact : residualSingular.countCap = 1710742257511041 := by decide

def ledger : ℕ := fixedRegularCap + fixedSingular.countCap +
  residualStage.regularCountCap + residualSingular.countCap + 1
theorem ledger_exact : ledger = 274531024426090137 := by
  rw [ledger, fixedRegularCap, fixedSingular_exact,
    residualStage_exact, residualSingular_exact]
theorem ledger_lt : ledger < budget := by rw [ledger_exact]; decide

def radiusNumerator : ℕ := 10278369
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

theorem score_root_integer : (2 : ℕ)^54 * 1000000^100 ≤ 1453973^100 := by decide
theorem score_radius_integer :
    (23276063 : ℕ)^128 * (2^67 * 1453973) ≤ 1000000 * 33554432^128 := by decide

theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((54 : ℝ)/100) ≤ (1453973 : ℝ≥0)/1000000 := by
  have hroot : ((2 : ℝ≥0)^(54 : ℕ))^((100 : ℝ)⁻¹) ≤
      (1453973 : ℝ≥0)/1000000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0)^((54 : ℝ)/100) = ((2 : ℝ≥0)^(54 : ℕ))^((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot

theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1453973) := by
  have hsub : (1 - radius : ℝ≥0) = 23276063/33554432 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1453973)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer

theorem score_target_le :
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6754 := by
  have hscale : (1000000 : ℝ≥0)/1453973 ≤
      (2 : ℝ≥0)^(-((54 : ℝ)/100)) := by
    calc
      (1000000 : ℝ≥0)/1453973 = 1/((1453973 : ℝ≥0)/1000000) := by norm_num
      _ ≤ 1/((2 : ℝ≥0)^((54 : ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1453973) := radius_power_bound
    _ ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (2 : ℝ≥0)^(-((54 : ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6754 := by
      unfold claimedError
      rw [show -((((6754 : ℕ) : ℝ)/100)) =
          -((67 : ℕ) : ℝ) + -((54 : ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end
end ProximityPrize.SubmissionLower.LocatorArithmetic
