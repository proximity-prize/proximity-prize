import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch
import ProximityPrize.SubmissionLower.Target6751Arithmetic
namespace ProximityPrize.SubmissionLower.ContactMovingSeedless6750Research
open ProximityPrize.Benchmark
open ContactSeedlessInterpolationResearch
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80270
def agreements:ℕ:=n-errors
def gap:ℕ:=agreements-w
def prime:ℕ:=2130706433
def multiplicity:ℕ:=48
def yTotalCap:ℕ:=66
def slopeCap:ℕ:=14
def weightedCap:ℕ:=multiplicity*agreements
def listBudget:ℕ:=1227545962
def mcaBudget:ℕ:=274980726883849125
def capY:ℕ:=1+2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap-1)
def regularListNumerator:ℕ:=(n-w)*(capY*slopeCap+capR*yTotalCap)
def singularListCap:ℕ:=(2*slopeCap-1)*yTotalCap
def listNumerator:ℕ:=regularListNumerator+singularListCap*gap
theorem coefficient_count_exact:
    coefficientCount weightedCap w yTotalCap slopeCap=3569630410:=by decide
theorem local_rank_exact:
    localRankBound multiplicity yTotalCap slopeCap=13615:=by decide
theorem nullity_exact:
    coefficientCount weightedCap w yTotalCap slopeCap-
      n*localRankBound multiplicity yTotalCap slopeCap=539850:=by
  rw [coefficient_count_exact,local_rank_exact]
  decide
theorem interpolation_gate:
    n*localRankBound multiplicity yTotalCap slopeCap <
      coefficientCount weightedCap w yTotalCap slopeCap:=by
  rw [coefficient_count_exact,local_rank_exact]
  decide
theorem list_numeric_values:
    agreements=181874∧gap=50803∧weightedCap=8729952∧
    singularListCap=1782∧listNumerator=62363017500258∧
    listNumerator/gap+1=1227545962∧
    listNumerator<1227545962*gap∧listBudget=1227545962:=by decide
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
def radius:ℝ≥0:=claimedRadius 321083 1048576
def score:ℕ:=6751
theorem radius_numerator_exact:321083=4*errors+3:=by decide
theorem radius_floor:
    ⌊(radius:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊=errors:=by
  norm_num [radius,claimedRadius,errors,IRSProfile.Index]
theorem radius_cell_cross:
    321083*Fintype.card IRSProfile.Index < (errors+1)*1048576:=by
  norm_num [IRSProfile.Index,errors]
theorem radius_gap:w < Fintype.card IRSProfile.Index-errors:=by
  norm_num [IRSProfile.Index,errors,w]
theorem radius_admissible:
    radius∈Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
  constructor <;> norm_num [radius,claimedRadius,IRSProfile.minRelativeDistance]
theorem radius_score:(1-radius)^IRSProfile.repetitions ≤ claimedError score:=by
  exact Target6751Arithmetic.radius_321083_score_6751
theorem field_cardinality:Fintype.card IRSProfile.Field=prime^6:=by
  norm_num [prime,IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem field_capacity_split:
    2^(128:ℕ)*(mcaBudget+listBudget) ≤
      Fintype.card IRSProfile.Field:=by
  rw [field_cardinality]
  decide
theorem protocolClaim6750_of_reduction
    (hred:ToyProblem.Impl.IRS.certifiedGammaError IRSProfile.totalDimension
      IRSProfile.interleaving IRSProfile.domain radius ≤ reductionTarget):
    ProtocolClaim 6751 321083 1048576:=by
  exact ⟨radius_admissible,hred,radius_score⟩
end
end ProximityPrize.SubmissionLower.ContactMovingSeedless6750Research
