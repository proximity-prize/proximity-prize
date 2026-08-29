import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingSeedless6732Research
import ProximityPrize.SubmissionLower.ContactMovingSeedlessGeometry6732Research
import ProximityPrize.SubmissionLower.ContactSeedlessProtocolResearch
import ProximityPrize.SubmissionLower.ContactSeedlessLambdaResearch

namespace ProximityPrize.SubmissionLower.ContactMovingProtocol6732Research

open ProximityPrize.Benchmark
open ContactSeedlessProtocolResearch
open ContactSeedlessLambdaResearch
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
def n : ℕ := 262144
def errors : ℕ := 80112
def agreements : ℕ := n-errors
def listBudget : ℕ := 1000000000
def mcaBudget : ℕ := 274980727111395087
def radius : ℝ≥0 := ContactMovingSeedless6732Research.radius

theorem sixteen_row_separation :
    15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field := by
  rw [show Fintype.card IRSProfile.Field = (2130706433 : ℕ) ^ 6 by
    norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize],
    Nat.choose_eq_descFactorial_div_factorial]
  norm_num [listBudget, Nat.descFactorial_succ, Nat.factorial_succ]

theorem squared_eight_lambda_new
    (delta : ℝ)
    (hcell : (delta : ℝ) * (Fintype.card IRSProfile.Index : ℝ) <
      ((errors + 1 : ℕ) : ℝ)) :
    Code.Lambda
      (((IRSProfile.baseCode ^⋈ (Fin 8)) ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin 8 → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))
      delta ≤ (listBudget : ℕ∞) := by
  apply ContactSeedlessLambdaResearch.squared_eight_lambda_le_of_interleaved_list
    IRSProfile.baseCode errors listBudget ?_ delta hcell
  intro received L hrows hclose
  have hclose' : ∀ v ∈ L, agreements ≤
      (Finset.univ.filter (fun i => v i = received i)).card := by
    intro v hv
    simpa [agreements, n, errors, IRSProfile.Index] using hclose v hv
  classical
  letI : DecidableEq (IRSProfile.Index → Fin 16 → IRSProfile.Field) := Classical.decEq _
  letI : DecidableEq (IRSProfile.Index → IRSProfile.Field) := Classical.decEq _
  by_contra hnot
  obtain ⟨D, hDL, hDcard⟩ :=
    Finset.exists_subset_card_eq (show listBudget + 1 ≤ L.card by omega)
  have hsepD : 15 * D.card.choose 2 < Fintype.card IRSProfile.Field := by
    rw [hDcard]
    exact sixteen_row_separation
  obtain ⟨t, ht⟩ := exists_separating_moment_parameter D hsepD
  let projected : Finset (IRSProfile.Index → IRSProfile.Field) :=
    D.image (momentProjection (ι := IRSProfile.Index) (r := 16) t)
  have hprojcard : projected.card = D.card := Finset.card_image_of_injOn ht
  have hcode : ∀ c ∈ projected, c ∈ IRSProfile.baseCode := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
  have hnear : ∀ c ∈ projected, agreements ≤
      (Finset.univ.filter (fun i => c i = momentProjection t received i)).card := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact (hclose' v (hDL hv)).trans
      (Finset.card_le_card (momentProjection_preserves_agreements t v received))
  have hbound := ContactMovingSeedlessGeometry6732Research.irs_scalar_finite_list_card_le
    (momentProjection t received) projected hcode hnear
  change projected.card ≤ listBudget at hbound
  rw [hprojcard, hDcard] at hbound
  omega

theorem lambda_le :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (radius : ℝ) ≤ (listBudget : ℕ∞) := by
  rw [irs_squared_carrier_eq]
  apply squared_eight_lambda_new (radius : ℝ)
  norm_num [radius, ContactMovingSeedless6732Research.radius, claimedRadius,
    errors, IRSProfile.Index]

theorem base_mca_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius : ℝ) ≤
      ENNReal.ofReal ((mcaBudget : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius : ℝ) errors mcaBudget
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (radius : ℝ) by positivity)).mp hA
    rw [show ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors by
      simpa only [radius, errors, ContactMovingSeedless6732Research.errors] using
        ContactMovingSeedless6732Research.radius_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors, ContactMovingSeedless6732Research.errors] at hcomp ⊢
    omega
  · exact halign

theorem mca_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (radius : ℝ) ≤
      (mcaBudget : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius : ℝ) := by
      rw [ContactSeedlessProtocolResearch.irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius, ContactMovingSeedless6732Research.radius,
          claimedRadius])
        (by norm_num [radius, ContactMovingSeedless6732Research.radius,
          claimedRadius])
    _ ≤ ENNReal.ofReal
        ((mcaBudget : ℝ) / Fintype.card IRSProfile.Field) :=
      base_mca_le_of_alignment halign
    _ = (mcaBudget : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

theorem certifiedGammaError_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    certifiedGammaError IRSProfile.code radius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe lambda_le
  have hList :
      (listDecodingRadiusNumerator IRSProfile.repetitions : ENNReal) *
          ((listBudget : ENNReal) + 1) /
        (Fintype.card IRSProfile.Field : ENNReal) ≤
      (listDecodingRadiusNumerator IRSProfile.repetitions : ENNReal) *
          ((listBudget : ENNReal) + 1) /
        (Fintype.card IRSProfile.Field : ENNReal) := le_rfl
  have hBound :=
    certifiedGammaError_le_of_list_and_mca_direct
      (AffineLineGenerator IRSProfile.Field) IRSProfile.code radius listBudget
      (by norm_num [radius, ContactMovingSeedless6732Research.radius, claimedRadius])
      (by norm_num [radius, ContactMovingSeedless6732Research.radius, claimedRadius,
        IRSProfile.minRelativeDistance])
      (by norm_num [IRSProfile.repetitions])
      hLambdaNat (mca_le_of_alignment halign)
  refine hBound.trans ?_
  have hField : (Fintype.card IRSProfile.Field : ENNReal) = (2130706433 : ENNReal) ^ 6 := by
    rw [show Fintype.card IRSProfile.Field = (2130706433 : ℕ) ^ 6 by
      norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]]
    push_cast
    rfl
  rw [hField]
  have hSplitNat :
      (listDecodingRadiusNumerator IRSProfile.repetitions) * (listBudget + 1) + mcaBudget ≤
        (2130706433 : ℕ) ^ 6 / 2 ^ (128 : ℕ) := by
    decide
  have hCapacitySplit :
      ((listDecodingRadiusNumerator IRSProfile.repetitions : ENNReal) *
            ((listBudget : ENNReal) + 1) + (mcaBudget : ENNReal)) /
          ((2130706433 : ENNReal) ^ 6) ≤
        (1 : ENNReal) / 2 ^ (128 : ℕ) := by
    have hPos : (0 : ENNReal) < 2 ^ (128 : ℕ) := by positivity
    have hPrimePos : (0 : ENNReal) < (2130706433 : ENNReal) ^ 6 := by positivity
    rw [div_le_iff₀ (Or.inl (by positivity)) (Or.inr (by positivity))]
    rw [← div_le_iff₀ (Or.inl (by positivity)) (Or.inr (by positivity))]
    rw [show (1 : ENNReal) / 2 ^ (128 : ℕ) * (2130706433 : ENNReal) ^ 6 =
      ((2130706433 : ENNReal) ^ 6) / 2 ^ (128 : ℕ) by ring]
    have hCast :
        ((listDecodingRadiusNumerator IRSProfile.repetitions : ENNReal) *
              ((listBudget : ENNReal) + 1) + (mcaBudget : ENNReal)) =
          (((listDecodingRadiusNumerator IRSProfile.repetitions) * (listBudget + 1) +
            mcaBudget : ℕ) : ENNReal) := by
      push_cast
      rfl
    rw [hCast]
    exact_mod_cast (Nat.le_div_iff_mul_le (by positivity)).mpr
      (by simpa [Nat.mul_comm] using hSplitNat)
  calc
    _ ≤ ((listDecodingRadiusNumerator IRSProfile.repetitions : ENNReal) *
            ((listBudget : ENNReal) + 1) + (mcaBudget : ENNReal)) /
          ((2130706433 : ENNReal) ^ 6) := by
      rw [add_div]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := hCapacitySplit

theorem protocolClaim6732_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    ProtocolClaim 6735 10254463 33554432 where
  admissible := ContactMovingSeedless6732Research.radius_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
    simpa [reductionTarget, ProximityGap.prizeThreshold] using
      certifiedGammaError_le_of_alignment halign
  score := by
    simpa [radius] using ContactMovingSeedless6732Research.score_target_le

end ProximityPrize.SubmissionLower.ContactMovingProtocol6732Research
