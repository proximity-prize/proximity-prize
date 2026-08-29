import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingParameters6719Research
import ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch

/-! .
 -/
namespace ProximityPrize.SubmissionLower.ContactMovingSeedless6719Research

open ProximityPrize.Benchmark
open ContactSeedlessInterpolationResearch
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 79964
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def prime : ℕ := 2130706433
def multiplicity : ℕ := 37
def yTotalCap : ℕ := 51
def slopeCap : ℕ := 10
def weightedCap : ℕ := multiplicity * agreements
def listBudget : ℕ := 700000000
def capY : ℕ := 1 + 2*w*yTotalCap
def capR : ℕ := w*(2*slopeCap - 1)
def regularListNumerator : ℕ := (n-w)*(capY*slopeCap + capR*yTotalCap)
def singularListCap : ℕ := (2*slopeCap - 1)*yTotalCap
def listNumerator : ℕ := regularListNumerator + singularListCap*gap

theorem coefficient_count_exact :
    coefficientCount weightedCap w yTotalCap slopeCap = 1594748804 := by decide
theorem local_rank_exact :
    localRankBound multiplicity yTotalCap slopeCap = 6083 := by decide
theorem nullity_exact :
    coefficientCount weightedCap w yTotalCap slopeCap -
      n*localRankBound multiplicity yTotalCap slopeCap = 126852 := by
  rw [coefficient_count_exact, local_rank_exact]
  decide
theorem interpolation_gate :
    n*localRankBound multiplicity yTotalCap slopeCap <
      coefficientCount weightedCap w yTotalCap slopeCap := by
  rw [coefficient_count_exact, local_rank_exact]
  decide

theorem list_numeric_values :
    agreements = 182180 ∧ gap = 51109 ∧ weightedCap = 6740660 ∧
    singularListCap = 969 ∧ listNumerator = 34170810640338 ∧
    listNumerator/gap + 1 = 668586955 ∧
    listNumerator < 668586955*gap ∧ 668586955 < listBudget := by decide

theorem list_numerator_fits : listNumerator < listBudget*gap := by decide
theorem characteristic_gates : 0 < slopeCap ∧ slopeCap < prime ∧ yTotalCap < prime ∧
    (2*slopeCap - 1)*weightedCap < prime ∧ singularListCap < prime := by decide

/-- . -/
theorem exists_seedless_interpolant (received : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧ Q ∈ globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        ContactFlagRankKernel6641Research.slopeDifference IRSProfile.Field ^ (multiplicity-r) ∣
          (ContactTranslation.homogenizedTranslation IRSProfile.Field
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

def radius : ℝ≥0 := claimedRadius 319859 1048576
def score : ℕ := 6720
theorem radius_numerator_exact : 319859 = 4*errors+3 := by decide
theorem radius_floor :
    ⌊(radius : ℝ)*(Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
  norm_num [radius, claimedRadius, errors, IRSProfile.Index]
theorem radius_cell_cross :
    319859*Fintype.card IRSProfile.Index < (errors+1)*1048576 := by
  norm_num [IRSProfile.Index, errors]
theorem radius_gap : w < Fintype.card IRSProfile.Index-errors := by
  norm_num [IRSProfile.Index, errors, w]
theorem radius_admissible :
    radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [radius, claimedRadius, IRSProfile.minRelativeDistance]

/-- . -/
theorem root_power_integer : (2 : ℕ) * 10000^5 ≤ 11487^5 := by decide
theorem radius_power_integer :
    (728717 : ℕ)^128 * (2^67*11487) ≤ 10000*1048576^128 := by decide

theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((1 : ℝ)/5) ≤ (11487 : ℝ≥0)/10000 := by
  have hroot : ((2 : ℝ≥0)^(1 : ℕ))^((5 : ℝ)⁻¹) ≤
      (11487 : ℝ≥0)/10000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 5)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast root_power_integer
  calc
    (2 : ℝ≥0)^((1 : ℝ)/5) =
        ((2 : ℝ≥0)^(1 : ℕ))^((5 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (11487 : ℝ≥0)/10000 := hroot

theorem radius_power_rational_bound :
    (1-radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0)/2^(67 : ℕ))*(10000/11487) := by
  have hsub : (1-radius : ℝ≥0) = 728717/1048576 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius]
  change (1-radius)^128 ≤ ((1 : ℝ≥0)/2^(67 : ℕ))*(10000/11487)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast radius_power_integer

theorem radius_score : (1-radius)^IRSProfile.repetitions ≤ claimedError score := by
  have hscale : (10000 : ℝ≥0)/11487 ≤ (2 : ℝ≥0)^(-((1 : ℝ)/5)) := by
    calc
      (10000 : ℝ≥0)/11487 = 1/((11487 : ℝ≥0)/10000) := by norm_num
      _ ≤ 1/((2 : ℝ≥0)^((1 : ℝ)/5)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = (2 : ℝ≥0)^(-((1 : ℝ)/5)) := by rw [one_div, NNReal.rpow_neg]
  calc
    (1-radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0)/2^(67 : ℕ))*(10000/11487) :=
      radius_power_rational_bound
    _ ≤ ((1 : ℝ≥0)/2^(67 : ℕ))*(2 : ℝ≥0)^(-((1 : ℝ)/5)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError score := by
      unfold claimedError score
      rw [show -((((6720 : ℕ) : ℝ)/100)) =
          -((67 : ℕ) : ℝ) + -((1 : ℝ)/5) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

theorem field_cardinality : Fintype.card IRSProfile.Field = prime^6 := by
  norm_num [prime, IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]

theorem field_capacity_split :
    2^(128 : ℕ) * (ContactMovingParameters6719Research.mcaBudget + listBudget) ≤
      Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  decide

/-- .
 -/
theorem protocolClaim6719_of_reduction
    (hred : ToyProblem.Impl.IRS.certifiedGammaError IRSProfile.totalDimension
      IRSProfile.interleaving IRSProfile.domain radius ≤ reductionTarget) :
    ProtocolClaim 6720 319859 1048576 := by
  exact ⟨radius_admissible, hred, radius_score⟩

end
end ProximityPrize.SubmissionLower.ContactMovingSeedless6719Research
