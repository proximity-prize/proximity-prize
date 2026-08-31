import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
import ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch
namespace ProximityPrize.SubmissionLower.ContactMovingSeedless6733Research
open ProximityPrize.Benchmark
open ContactSeedlessInterpolationResearch
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80427
def agreements:ℕ:=n-errors
def gap:ℕ:=agreements-w
def prime:ℕ:=2130706433
def multiplicity:ℕ:=58
def yTotalCap:ℕ:=80
def slopeCap:ℕ:=16
def weightedCap:ℕ:=multiplicity*agreements
def listBudget:ℕ:=1709644758
def capY:ℕ:=1+2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap-1)
def regularListNumerator:ℕ:=(n-w)*(capY*slopeCap+capR*yTotalCap)
def singularListCap:ℕ:=(2*slopeCap-1)*yTotalCap
def listNumerator:ℕ:=regularListNumerator+singularListCap*gap
theorem coefficient_count_exact:
    coefficientCount weightedCap w yTotalCap slopeCap=5949373346:=by native_decide
theorem local_rank_exact:
    localRankBound multiplicity yTotalCap slopeCap=22695:=by native_decide
theorem nullity_exact:
    coefficientCount weightedCap w yTotalCap slopeCap-
      n*localRankBound multiplicity yTotalCap slopeCap=15266:=by
  rw [coefficient_count_exact,local_rank_exact]
  decide
theorem interpolation_gate:
    n*localRankBound multiplicity yTotalCap slopeCap <
      coefficientCount weightedCap w yTotalCap slopeCap:=by
  rw [coefficient_count_exact,local_rank_exact]
  decide
theorem list_numeric_values:
    agreements=181717∧gap=50646∧weightedCap=10539586∧
    singularListCap=2480∧listNumerator=86586668381568∧
    listNumerator/gap+1=1709644758∧
    listNumerator<1709644758*gap∧listBudget=1709644758:=by decide
theorem list_numerator_fits:listNumerator < listBudget*gap:=by decide
theorem characteristic_gates:0 < slopeCap∧slopeCap < prime∧yTotalCap < prime∧
    (2*slopeCap-1)*weightedCap < prime∧singularListCap < prime:=by decide
theorem exists_seedless_interpolant (received:IRSProfile.Index → IRSProfile.Field):
    ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
      Q≠0∧Q∈globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap∧
      ∀ (i:IRSProfile.Index) (r:ℕ),
        ContactFlagRankKernel6641Research.slopeDifference IRSProfile.Field^(multiplicity-r)∣
          (ContactTranslation.homogenizedTranslation IRSProfile.Field
            (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
  obtain ⟨theta,htheta,hzero⟩:=exists_nonzero_kernel_array
    IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
    IRSProfile.domain received (by
      rw [show Fintype.card IRSProfile.Index=n by norm_num [IRSProfile.Index,n]]
      exact interpolation_gate)
  refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
    reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
    reconstruct_mem_box IRSProfile.Field _ _ _ _ theta,?_⟩
  intro i r
  have hdiv:=all_blocks_divisible_of_kernel IRSProfile.Field
    weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received theta hzero i r
  rw [←translation_reconstruct_coeff IRSProfile.Field weightedCap w
    yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
  exact hdiv
def radius:ℝ≥0:=claimedRadius 10294783 33554432
def score:ℕ:=6767
theorem radius_numerator_exact:10294783=128*errors+127:=by decide
theorem radius_floor:
    ⌊(radius:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊=errors:=by
  norm_num [radius,claimedRadius,errors,IRSProfile.Index]
theorem radius_cell_cross:
    10294783*Fintype.card IRSProfile.Index < (errors+1)*33554432:=by
  norm_num [IRSProfile.Index,errors]
theorem radius_gap:w < Fintype.card IRSProfile.Index-errors:=by
  norm_num [IRSProfile.Index,errors,w]
theorem radius_admissible:
    radius∈Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
  constructor <;> norm_num [radius,claimedRadius,IRSProfile.minRelativeDistance]
theorem root_power_integer:(2:ℕ)^67*115^100 ≤ 183^100:=by decide
theorem radius_power_integer:
    (23259649:ℕ)^128*(2^67*183) ≤ 115*33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((67:ℝ)/100) ≤ (183:ℝ≥0)/115:=by
  have hroot:((2:ℝ≥0)^(67:ℕ))^((100:ℝ)⁻¹) ≤ (183:ℝ≥0)/115:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ)<100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast root_power_integer
  calc
    (2:ℝ≥0)^((67:ℝ)/100)=((2:ℝ≥0)^(67:ℕ))^((100:ℝ)⁻¹):=by
      rw [←NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (183:ℝ≥0)/115:=hroot
theorem radius_power_rational_bound:
    (1-radius)^IRSProfile.repetitions ≤ ((1:ℝ≥0)/2^(67:ℕ))*(115/183):=by
  have hsub:(1-radius:ℝ≥0)=23259649/33554432:=by
    have hr:radius≤1:=by
      rw [←NNReal.coe_le_coe]
      norm_num [radius,claimedRadius]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius]
  change (1-radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ))*(115/183)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast radius_power_integer
theorem radius_score:(1-radius)^IRSProfile.repetitions ≤ claimedError score:=by
  have hscale:(115:ℝ≥0)/183 ≤ (2:ℝ≥0)^(-((67:ℝ)/100)):=by
    calc
      (115:ℝ≥0)/183=1/((183:ℝ≥0)/115):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((67:ℝ)/100)):=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=(2:ℝ≥0)^(-((67:ℝ)/100)):=by rw [one_div,NNReal.rpow_neg]
  calc
    (1-radius)^IRSProfile.repetitions ≤ ((1:ℝ≥0)/2^(67:ℕ))*(115/183):=
      radius_power_rational_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ))*(2:ℝ≥0)^(-((67:ℝ)/100)):=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError score:=by
      unfold claimedError score
      rw [show-((((6767:ℕ):ℝ)/100))=
          -((67:ℕ):ℝ)+-((67:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0)≠0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
theorem field_cardinality:Fintype.card IRSProfile.Field=prime^6:=by
  norm_num [prime,IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem field_capacity_split:
    2^(128:ℕ)*(ContactTwoTailParameters6733Research.mcaBudget+listBudget) ≤
      Fintype.card IRSProfile.Field:=by
  rw [field_cardinality]
  decide
theorem protocolClaim6767_of_reduction
    (hred:ToyProblem.Impl.IRS.certifiedGammaError IRSProfile.totalDimension
      IRSProfile.interleaving IRSProfile.domain radius ≤ reductionTarget):
    ProtocolClaim 6767 10294783 33554432:=by
  exact ⟨radius_admissible,hred,radius_score⟩
end
end ProximityPrize.SubmissionLower.ContactMovingSeedless6733Research
