import ProximityPrize.SubmissionLower.LowerFoundation


namespace ProximityPrize.SubmissionLower.Koala6844Protocol

open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

def errors : ℕ := 81184
def mcaBudget : ℕ := 271137207725094189
def listBudget : ℕ := 108981179311
def radiusNumerator : ℕ := 332533759
def radiusDenominator : ℕ := 1073741824
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator


theorem radius_admissible : radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    IRSProfile.minRelativeDistance]

private theorem radius_cell :
    (radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ) < ((errors + 1 : ℕ) : ℝ) := by
  norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    errors, IRSProfile.Index]

private theorem score_root_integer :
    (2 : ℕ)^44 * 10000^100 ≤ 13567^100 := by
  decide +kernel

private theorem score_radius_integer :
    (741208065 : ℕ)^128 * (2^68 * 13567) ≤ 10000 * 1073741824^128 := by
  decide +kernel

private theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((44 : ℝ) / 100) ≤ (13567 : ℝ≥0) / 10000 := by
  have hroot : ((2 : ℝ≥0)^(44 : ℕ))^((100 : ℝ)⁻¹) ≤
      (13567 : ℝ≥0) / 10000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0)^((44 : ℝ) / 100) = ((2 : ℝ≥0)^(44 : ℕ))^((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot

private theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2^(68 : ℕ)) * (10000 / 13567) := by
  have hsub : (1 - radius : ℝ≥0) = 741208065 / 1073741824 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1 : ℝ≥0) / 2^(68 : ℕ)) * (10000 / 13567)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer

theorem score_target_le : (1 - radius)^IRSProfile.repetitions ≤ claimedError 6844 := by
  have hscale : (10000 : ℝ≥0) / 13567 ≤ (2 : ℝ≥0)^(-((44 : ℝ) / 100)) := by
    calc
      (10000 : ℝ≥0) / 13567 = 1 / ((13567 : ℝ≥0) / 10000) := by
        norm_num
      _ ≤ 1 / ((2 : ℝ≥0)^((44 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2^(68 : ℕ)) * (10000 / 13567) := radius_power_bound
    _ ≤ ((1 : ℝ≥0) / 2^(68 : ℕ)) * (2 : ℝ≥0)^(-((44 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6844 := by
      unfold claimedError
      rw [show -((((6844 : ℕ) : ℝ) / 100)) =
          -((68 : ℕ) : ℝ) + -((44 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

def ScalarListBoundAt (B : ℕ) : Prop :=
  ∀ (received : IRSProfile.Index → IRSProfile.Field)
    (words : Finset (IRSProfile.Index → IRSProfile.Field)),
    (∀ word ∈ words, word ∈ IRSProfile.baseCode) →
    (∀ word ∈ words, Fintype.card IRSProfile.Index - errors ≤
      (Finset.univ.filter (fun i => word i = received i)).card) →
    words.card ≤ B

abbrev ScalarListBound := ScalarListBoundAt listBudget

private theorem lambda_le {B : ℕ}
    (hlist : ScalarListBoundAt B)
    (hprojection : 15 * (B + 1).choose 2 < Fintype.card IRSProfile.Field) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (radius : ℝ) ≤ (B : ℕ∞) := by
  rw [RCN018.irs_squared_carrier_eq]
  apply RCN280.squared_eight_lambda_le_of_interleaved_list
    IRSProfile.baseCode errors B ?_ (radius : ℝ) radius_cell
  intro received words hrows hclose
  classical
  by_contra hnot
  obtain ⟨subset, hsubset, hsubsetCard⟩ :=
    Finset.exists_subset_card_eq (show B + 1 ≤ words.card by omega)
  obtain ⟨t, ht⟩ := RCN019.exists_separating_moment_parameter subset
    (show 15 * subset.card.choose 2 < Fintype.card IRSProfile.Field by
      rw [hsubsetCard]
      exact hprojection)
  let projected := subset.image (RCN019.momentProjection (ι := IRSProfile.Index) (r := 16) t)
  have hcard : projected.card = subset.card := Finset.card_image_of_injOn ht
  have hcode : ∀ word ∈ projected, word ∈ IRSProfile.baseCode := by
    intro word hword
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hword
    exact RCN019.momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hsubset hv))
  have hnear : ∀ word ∈ projected, Fintype.card IRSProfile.Index - errors ≤
      (Finset.univ.filter (fun i => word i = RCN019.momentProjection t received i)).card := by
    intro word hword
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hword
    exact (hclose v (hsubset hv)).trans
      (Finset.card_le_card (RCN019.momentProjection_preserves_agreements t v received))
  have hbound := hlist (RCN019.momentProjection t received) projected hcode hnear
  rw [hcard, hsubsetCard] at hbound
  omega

private theorem base_mca_le (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode (radius : ℝ) ≤
      ENNReal.ofReal ((mcaBudget : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode (radius : ℝ) errors mcaBudget
  · intro A hA
    have hAgreement : (Fintype.card IRSProfile.Index : ℝ) -
        (Fintype.card IRSProfile.Index : ℝ) * (radius : ℝ) ≤ (A.card : ℝ) := by
      simpa only [mul_sub, mul_one] using hA
    have hCell : (Fintype.card IRSProfile.Index : ℝ) * (radius : ℝ) <
        ((errors + 1 : ℕ) : ℝ) := by
      rw [mul_comm]
      exact radius_cell
    have hReal : (Fintype.card IRSProfile.Index : ℝ) <
        ((A.card + (errors + 1) : ℕ) : ℝ) := by
      calc
        _ = (Fintype.card IRSProfile.Index : ℝ) -
            (Fintype.card IRSProfile.Index : ℝ) * (radius : ℝ) +
            (Fintype.card IRSProfile.Index : ℝ) * (radius : ℝ) := (sub_add_cancel _ _).symm
        _ < (A.card : ℝ) + ((errors + 1 : ℕ) : ℝ) := add_lt_add_of_le_of_lt hAgreement hCell
        _ = _ := (Nat.cast_add _ _).symm
    have hNat : Fintype.card IRSProfile.Index < A.card + (errors + 1) := by
      exact_mod_cast hReal
    omega
  · exact halign

private theorem mca_le (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code (radius : ℝ) ≤
      (mcaBudget : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode (radius : ℝ) := by
      rw [RCN284.irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator])
        (by norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator])
    _ ≤ ENNReal.ofReal ((mcaBudget : ℝ) / Fintype.card IRSProfile.Field) := base_mca_le halign
    _ = (mcaBudget : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- The exact numerator obtained by combining the chosen alignment and scalar list bounds. -/
theorem extractor_error_le {B : ℕ}
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget)
    (hlist : ScalarListBoundAt B)
    (hprojection : 15 * (B + 1).choose 2 < Fintype.card IRSProfile.Field) :
    certifiedGammaError IRSProfile.code radius ≤
      ((mcaBudget + B : ℕ) : ℝ≥0) / (Fintype.card IRSProfile.Field : ℝ≥0) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  rw [← Nat.cast_add]
  have hLambdaNat := ENat.toNat_le_of_le_natCast (lambda_le hlist hprojection)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
        (radius : ℝ)).toNat : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) ≤
      (B : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (mcaBudget : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) +
        (B : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca_le halign) hList
    _ = ((mcaBudget + B : ℕ) : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
private theorem reduction_of_bounds
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget)
    (hlist : ScalarListBound)
    (hprojection : 15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field)
    (hcapacity : 2 ^ (128 : ℕ) * (mcaBudget + listBudget) ≤ Fintype.card IRSProfile.Field) :
    certifiedGammaError IRSProfile.code radius ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  apply (extractor_error_le halign hlist hprojection).trans
  rw [← ENNReal.coe_le_coe]
  push_cast
  rw [← Nat.cast_add]
  apply RCN284.nat_div_le_inv_pow
  · unfold mcaBudget
    omega
  · simpa only [Nat.mul_comm] using hcapacity

abbrev ScalarSeedBound : Prop :=
  RCN050.SelectedNoLargePencilBound IRSProfile.domain 131071 errors mcaBudget

theorem extractor_error_le_of_selected {B : ℕ} (hseed : ScalarSeedBound)
    (hlist : ScalarListBoundAt B)
    (hprojection : 15 * (B + 1).choose 2 < Fintype.card IRSProfile.Field) :
    certifiedGammaError IRSProfile.code radius ≤
      ((mcaBudget + B : ℕ) : ℝ≥0) / (Fintype.card IRSProfile.Field : ℝ≥0) :=
  extractor_error_le (RCN050.alignmentBound_of_selected_count IRSProfile.domain 131071
    errors mcaBudget hseed) hlist hprojection

private theorem protocolClaim_of_bounds
    (hseed : ScalarSeedBound)
    (hlist : ScalarListBound)
    (hprojection : 15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field)
    (hcapacity : 2 ^ (128 : ℕ) * (mcaBudget + listBudget) ≤ Fintype.card IRSProfile.Field) :
    ProtocolClaim 6844 332533759 1073741824 where
  admissible := radius_admissible
  reduction := by
    have halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget :=
      RCN050.alignmentBound_of_selected_count IRSProfile.domain 131071 errors mcaBudget hseed
    change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
    simpa [reductionTarget, ProximityGap.prizeThreshold] using
      reduction_of_bounds halign hlist hprojection hcapacity
  score := score_target_le

theorem protocolClaim_of_scalar_bounds
    (hseed : ScalarSeedBound)
    (hlist : ScalarListBound) : ProtocolClaim 6844 332533759 1073741824 := by
  apply protocolClaim_of_bounds hseed hlist
  · rw [RCN284.field_cardinality, Nat.choose_eq_descFactorial_div_factorial]
    norm_num [listBudget, Nat.descFactorial_succ, Nat.factorial_succ]
  · rw [RCN284.field_cardinality]
    decide +kernel

end

end ProximityPrize.SubmissionLower.Koala6844Protocol

