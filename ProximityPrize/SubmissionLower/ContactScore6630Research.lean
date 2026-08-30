import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.ContactScore6630Research
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section
def radius6630:ℝ≥0:=claimedRadius 319467 1048576
def errors6630:ℕ:=79866
def score6630:ℕ:=6710
theorem radius_numerator_exact:319467=4*errors6630+3:=by
  norm_num [errors6630]
theorem radius6630_floor:
    ⌊(radius6630:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊=
      errors6630:=by
  norm_num [radius6630,claimedRadius,errors6630,IRSProfile.Index]
theorem radius6630_cell_cross:
    319467*Fintype.card IRSProfile.Index <
      (errors6630+1)*1048576:=by
  norm_num [IRSProfile.Index,errors6630]
theorem radius6630_gap:
    131071 < Fintype.card IRSProfile.Index-errors6630:=by
  norm_num [IRSProfile.Index,errors6630]
theorem radius6630_admissible:
    radius6630∈Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
  constructor <;>
    norm_num [radius6630,claimedRadius,IRSProfile.minRelativeDistance]
theorem two_rpow_one_tenth_le:
    (2:ℝ≥0)^((1:ℝ)/10) ≤ (134:ℝ≥0)/125:=by
  have hroot:
      ((2:ℝ≥0)^(1:ℕ))^((10:ℝ)⁻¹) ≤
        (134:ℝ≥0)/125:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 10)]
    norm_num [NNReal.rpow_natCast,div_pow,le_div_iff₀]
  calc
    (2:ℝ≥0)^((1:ℝ)/10)=
        ((2:ℝ≥0)^(1:ℕ))^((10:ℝ)⁻¹):=by
      rw [←NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (134:ℝ≥0)/125:=hroot
theorem radius6630_power_rational_bound:
    (1-radius6630)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ))*(125/134):=by
  rw [←NNReal.coe_le_coe]
  norm_num [radius6630,claimedRadius,IRSProfile.repetitions,div_le_iff₀]
theorem radius6630_score:
    (1-radius6630)^IRSProfile.repetitions ≤ claimedError score6630:=by
  have hscale:
      (125:ℝ≥0)/134 ≤ (2:ℝ≥0)^(-((1:ℝ)/10)):=by
    calc
      (125:ℝ≥0)/134=1/((134:ℝ≥0)/125):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((1:ℝ)/10)):=
        one_div_le_one_div_of_le (by positivity) two_rpow_one_tenth_le
      _=(2:ℝ≥0)^(-((1:ℝ)/10)):=by
        rw [one_div,NNReal.rpow_neg]
  calc
    (1-radius6630)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ))*(125/134):=
      radius6630_power_rational_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ))*
        (2:ℝ≥0)^(-((1:ℝ)/10)):=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError score6630:=by
      unfold claimedError score6630
      rw [show-((((6710:ℕ):ℝ)/100))=
          -((67:ℕ):ℝ)+ -((1:ℝ)/10) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0)≠0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end ProximityPrize.SubmissionLower.ContactScore6630Research
