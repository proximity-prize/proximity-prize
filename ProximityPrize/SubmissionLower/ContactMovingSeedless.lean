import ProximityPrize.SubmissionLower.ContactMovingParameters
import ProximityPrize.SubmissionLower.ContactSeedlessInterpolation

namespace ProximityPrize.SubmissionLower.ContactMovingSeedless

open ProximityPrize.Benchmark
open ContactSeedlessInterpolation
open ContactMovingParameters
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def multiplicity : ℕ := 40
def yTotalCap : ℕ := 55
def slopeCap : ℕ := 12
def weightedCap : ℕ := multiplicity * (n - errors)

theorem coefficient_count_exact :
    coefficientCount weightedCap w yTotalCap slopeCap = 2147060604 := by decide
theorem local_rank_exact :
    localRankBound multiplicity yTotalCap slopeCap = 8190 := by decide
theorem interpolation_gate :
    n*localRankBound multiplicity yTotalCap slopeCap <
      coefficientCount weightedCap w yTotalCap slopeCap := by
  rw [coefficient_count_exact, local_rank_exact]
  decide

theorem exists_seedless_interpolant (received : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧ Q ∈ globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        ContactFlagRankKernel.slopeDifference IRSProfile.Field ^ (multiplicity-r) ∣
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

def radius : ℝ≥0 := claimedRadius 10250623 33554432
theorem radius_floor :
    ⌊(radius : ℝ)*(Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
  norm_num [radius, claimedRadius, errors, IRSProfile.Index]
theorem radius_admissible :
    radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [radius, claimedRadius, IRSProfile.minRelativeDistance]

theorem root_power_integer : (2 : ℕ)^8 * 600^25 ≤ 749^25 := by decide
theorem radius_power_integer :
    (23303809 : ℕ)^128 * (2^67*749) ≤ 600*33554432^128 := by decide

theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((8 : ℝ)/25) ≤ (749 : ℝ≥0)/600 := by
  have hroot : ((2 : ℝ≥0)^(8 : ℕ))^((25 : ℝ)⁻¹) ≤ (749 : ℝ≥0)/600 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ)<25)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast root_power_integer
  calc
    (2 : ℝ≥0)^((8 : ℝ)/25)=((2 : ℝ≥0)^(8 : ℕ))^((25 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (749 : ℝ≥0)/600 := hroot

theorem radius_power_rational_bound :
    (1-radius)^IRSProfile.repetitions ≤ ((1 : ℝ≥0)/2^(67 : ℕ))*(600/749) := by
  have hsub : (1-radius : ℝ≥0)=23303809/33554432 := by
    have hr : radius≤1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius]
  change (1-radius)^128 ≤ ((1 : ℝ≥0)/2^(67 : ℕ))*(600/749)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast radius_power_integer

theorem radius_score : (1-radius)^IRSProfile.repetitions ≤ claimedError 6732 := by
  have hscale : (600 : ℝ≥0)/749 ≤ (2 : ℝ≥0)^(-((8 : ℝ)/25)) := by
    calc
      (600 : ℝ≥0)/749=1/((749 : ℝ≥0)/600) := by norm_num
      _ ≤ 1/((2 : ℝ≥0)^((8 : ℝ)/25)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = (2 : ℝ≥0)^(-((8 : ℝ)/25)) := by rw [one_div,NNReal.rpow_neg]
  calc
    (1-radius)^IRSProfile.repetitions ≤ ((1 : ℝ≥0)/2^(67 : ℕ))*(600/749) :=
      radius_power_rational_bound
    _ ≤ ((1 : ℝ≥0)/2^(67 : ℕ))*(2 : ℝ≥0)^(-((8 : ℝ)/25)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6732 := by
      unfold claimedError
      rw [show -((((6732 : ℕ) : ℝ)/100)) =
          -((67 : ℕ) : ℝ)+-((8 : ℝ)/25) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0)≠0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]

theorem field_cardinality : Fintype.card IRSProfile.Field = 2130706433^6 := by
  norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]

theorem field_capacity_split :
    2^(128 : ℕ) * (ContactMovingParameters.mcaBudget + 1000000000) ≤
      Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  decide

end
end ProximityPrize.SubmissionLower.ContactMovingSeedless
