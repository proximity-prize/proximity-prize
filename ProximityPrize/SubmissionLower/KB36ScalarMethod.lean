/- Bome2017, joint projection accounting for 68.36 after Lucieno and BitWonka. -/
/- Apache-2.0. Adapted from the accepted Bome2017 68.32 proof and the 69.69 genuine reduction, after Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.KB36Score
import ProximityPrize.SubmissionLower.Mid6833IntermediateWords
import ProximityPrize.SubmissionLower.LowerFoundation
namespace ProximityPrize.SubmissionLower.JointProtocol6836
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
local instance methodFieldEq : DecidableEq IRSProfile.Field := Classical.decEq _
local instance methodIndexEq : DecidableEq IRSProfile.Index := Classical.decEq _
private theorem lambda_le (listBudget : ℕ)
    (hlist : IntermediateScalar.Words 181039 listBudget)
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

/-- Keep the rational combination-round error before converting it to the fixed target. -/
theorem error_le_of_bounds
    (hgiven : AffineLineGivenSetsBound IRSProfile.baseCode (radius : ℝ) mcaBudget)
    (listBudget : ℕ) (hlist : IntermediateScalar.Words 181039 listBudget)
    (hprojection : 15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field) :
    certifiedGammaError IRSProfile.code radius ≤
        ((mcaBudget + listBudget : ℕ) : ℝ≥0) / (Fintype.card IRSProfile.Field : ℝ≥0) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  rw [← Nat.cast_add]
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

theorem reduction_of_bounds
    (hgiven : AffineLineGivenSetsBound IRSProfile.baseCode (radius : ℝ) mcaBudget)
    (listBudget : ℕ) (hlist : IntermediateScalar.Words 181039 listBudget)
    (hprojection : 15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field)
    (hcapacity : 2 ^ (128 : ℕ) * (mcaBudget + listBudget) ≤ Fintype.card IRSProfile.Field) :
    certifiedGammaError IRSProfile.code radius ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  apply (error_le_of_bounds hgiven listBudget hlist hprojection).trans
  rw [← ENNReal.coe_le_coe]
  push_cast
  rw [← Nat.cast_add]
  apply RCN284.nat_div_le_inv_pow
  · unfold mcaBudget
    omega
  · simpa only [Nat.mul_comm] using hcapacity

#print axioms reduction_of_bounds
end
end ProximityPrize.SubmissionLower.JointProtocol6836
