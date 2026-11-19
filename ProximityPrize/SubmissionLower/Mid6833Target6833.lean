/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the accepted Bome2017 68.32 proof and the 69.69 genuine reduction, after Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.Mid6833IntermediateBridge
import ProximityPrize.SubmissionLower.Mid6833IntermediateWords
namespace ProximityPrize.SubmissionLower.Target6833
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
local instance mid6833Local_Target6833_10  : DecidableEq IRSProfile.Field := Classical.decEq _
local instance mid6833Local_Target6833_11  : DecidableEq IRSProfile.Index := Classical.decEq _
def errors : ℕ := 81095
def mcaBudget : ℕ := 274980690694301924
def radiusNumerator : ℕ := 332167720
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
    (2 : ℕ)^35 * 100000000^100 ≤ 127456063^100 := by
  decide +kernel

private theorem score_radius_integer :
    (741574104 : ℕ)^128 * (2^68 * 127456063) ≤ 100000000 * 1073741824^128 := by
  decide +kernel

private theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((35 : ℝ) / 100) ≤ (127456063 : ℝ≥0) / 100000000 := by
  have hroot : ((2 : ℝ≥0)^(35 : ℕ))^((100 : ℝ)⁻¹) ≤
      (127456063 : ℝ≥0) / 100000000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0)^((35 : ℝ) / 100) = ((2 : ℝ≥0)^(35 : ℕ))^((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot

private theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2^(68 : ℕ)) * (100000000 / 127456063) := by
  have hsub : (1 - radius : ℝ≥0) = 741574104 / 1073741824 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1 : ℝ≥0) / 2^(68 : ℕ)) * (100000000 / 127456063)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer

theorem score_target_le : (1 - radius)^IRSProfile.repetitions ≤ claimedError 6835 := by
  have hscale : (100000000 : ℝ≥0) / 127456063 ≤ (2 : ℝ≥0)^(-((35 : ℝ) / 100)) := by
    calc
      (100000000 : ℝ≥0) / 127456063 = 1 / ((127456063 : ℝ≥0) / 100000000) := by
        norm_num
      _ ≤ 1 / ((2 : ℝ≥0)^((35 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2^(68 : ℕ)) * (100000000 / 127456063) := radius_power_bound
    _ ≤ ((1 : ℝ≥0) / 2^(68 : ℕ)) * (2 : ℝ≥0)^(-((35 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6835 := by
      unfold claimedError
      rw [show -((((6835 : ℕ) : ℝ) / 100)) =
          -((68 : ℕ) : ℝ) + -((35 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

private theorem lambda_le (listBudget : ℕ)
    (hlist : IntermediateScalar.Words 181049 listBudget)
    (hprojection : 15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (radius : ℝ) ≤ (listBudget : ℕ∞) := by
  rw [RCN018.irs_squared_carrier_eq]
  apply RCN280.squared_eight_lambda_le_of_interleaved_list
    IRSProfile.baseCode errors listBudget ?_ (radius : ℝ) radius_cell
  intro received words hrows hclose
  classical
  by_contra hnot
  obtain ⟨subset, hsubset, hsubsetCard⟩ :=
    Finset.exists_subset_card_eq (show listBudget + 1 ≤ words.card by omega)
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
  simp only [IRSProfile.card_index, errors] at hnear
  have hbound := hlist (RCN019.momentProjection t received) projected hcode hnear
  rw [hcard, hsubsetCard] at hbound
  omega

private theorem mca_le (hgiven : AffineLineGivenSetsBound IRSProfile.baseCode (radius : ℝ) mcaBudget) :
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
    _ ≤ ENNReal.ofReal ((mcaBudget : ℝ) / Fintype.card IRSProfile.Field) := mcaError_affineLine_le_of_givenSetsBound IRSProfile.baseCode _ _ hgiven
    _ = (mcaBudget : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

private theorem reduction_of_bounds
    (hgiven : AffineLineGivenSetsBound IRSProfile.baseCode (radius : ℝ) mcaBudget)
    (listBudget : ℕ) (hlist : IntermediateScalar.Words 181049 listBudget)
    (hprojection : 15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field)
    (hcapacity : 2 ^ (128 : ℕ) * (mcaBudget + listBudget) ≤ Fintype.card IRSProfile.Field) :
    certifiedGammaError IRSProfile.code radius ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_natCast (lambda_le listBudget hlist hprojection)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
        (radius : ℝ)).toNat : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) ≤
      (listBudget : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (mcaBudget : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) +
        (listBudget : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca_le hgiven) hList
    _ = ((mcaBudget + listBudget : ℕ) : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply RCN284.nat_div_le_inv_pow
      · unfold mcaBudget
        omega
      · simpa only [Nat.mul_comm] using hcapacity


/-- The projected-support (joint agreement) predicate is itself sufficient at the
new score and seed budget. This interface can use direct recovery of both words. -/
theorem protocol_of_projected (hgiven : AffineLineGivenSetsBound IRSProfile.baseCode (radius : ℝ) mcaBudget) :
    ProtocolClaim 6835 332167720 1073741824 where
  admissible := radius_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
    have proj : 15*(37417093163+1).choose 2 < Fintype.card IRSProfile.Field := by
      rw [RCN284.field_cardinality,Nat.choose_eq_descFactorial_div_factorial]
      norm_num [Nat.descFactorial_succ,Nat.factorial_succ]
    have capacity : 2^(128:ℕ)*(mcaBudget+37417093163) ≤ Fintype.card IRSProfile.Field := by
      rw [RCN284.field_cardinality]; decide +kernel
    simpa [reductionTarget,ProximityGap.prizeThreshold] using reduction_of_bounds hgiven _ IntermediateScalar.words_6833 proj capacity
  score := score_target_le
#print axioms protocol_of_projected

theorem protocol_at (rem : Intermediate.At 181049 274980690694301924) : ProtocolClaim 6835 332167720 1073741824 := by
  apply protocol_of_projected
  exact Intermediate.given_of_at (r:=radius) (by decide) (by decide) (by decide) (by norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]) rem
#print axioms protocol_at
end
end ProximityPrize.SubmissionLower.Target6833
