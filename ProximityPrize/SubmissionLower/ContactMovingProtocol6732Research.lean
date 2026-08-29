import ProximityPrize.SubmissionLower.ContactMovingSeedlessList6732Research
import ProximityPrize.SubmissionLower.ContactSeedlessProtocolResearch
/-! .
 -/
namespace ProximityPrize.SubmissionLower.ContactMovingProtocol6732Research
open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open AlignmentMomentCurveProjection AlignmentInterleavedLambda
open scoped Classical NNReal
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
def n : ℕ := 262144
def errors : ℕ := 80082
def agreements : ℕ := n-errors
def listBudget : ℕ := 1000000000
def mcaBudget : ℕ := 274980727111395087
def radius : ℝ≥0 := ContactMovingSeedless6732Research.radius
theorem field_capacity_split :
    2^(128 : ℕ)*(mcaBudget+listBudget) ≤ Fintype.card IRSProfile.Field :=
  ContactMovingSeedless6732Research.field_capacity_split
theorem irs_interleaved_finite_list_card_le
    {r : ℕ}
    (received : IRSProfile.Index → Fin r → IRSProfile.Field)
    (L : Finset (IRSProfile.Index → Fin r → IRSProfile.Field))
    (hrows : ∀ v ∈ L, ∀ j : Fin r,
      (fun i => v i j) ∈ IRSProfile.baseCode)
    (hclose : ∀ v ∈ L, agreements ≤
      (Finset.univ.filter (fun i => v i = received i)).card)
    (hseparation : (r - 1) * (listBudget + 1).choose 2 <
      Fintype.card IRSProfile.Field) :
    L.card ≤ listBudget := by
  classical
  letI : DecidableEq (IRSProfile.Index → Fin r → IRSProfile.Field) := Classical.decEq _
  letI : DecidableEq (IRSProfile.Index → IRSProfile.Field) := Classical.decEq _
  by_contra hnot
  obtain ⟨D, hDL, hDcard⟩ :=
    Finset.exists_subset_card_eq (show listBudget + 1 ≤ L.card by omega)
  have hsepD : (r - 1) * D.card.choose 2 < Fintype.card IRSProfile.Field := by
    rw [hDcard]
    exact hseparation
  obtain ⟨t, ht⟩ := exists_separating_moment_parameter D hsepD
  let projected : Finset (IRSProfile.Index → IRSProfile.Field) :=
    D.image (momentProjection (ι := IRSProfile.Index) (r := r) t)
  have hprojcard : projected.card = D.card := Finset.card_image_of_injOn ht
  have hcode : ∀ c ∈ projected, c ∈ IRSProfile.baseCode := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
  have hnear : ∀ c ∈ projected, agreements ≤
      (Finset.univ.filter (fun i => c i = momentProjection t received i)).card := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact (hclose v (hDL hv)).trans
      (Finset.card_le_card (momentProjection_preserves_agreements t v received))
  have hbound := ContactMovingSeedlessGeometry6732Research.irs_scalar_finite_list_card_le (momentProjection t received)
    projected hcode hnear
  change projected.card ≤ listBudget at hbound
  rw [hprojcard, hDcard] at hbound
  omega
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
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
            IRSProfile.Field))
        (radius : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (listBudget : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (mcaBudget : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (listBudget : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca_le_of_alignment halign) hList
    _ = ((mcaBudget + listBudget : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply ContactSeedlessProtocolResearch.nat_div_le_inv_pow
      · norm_num [mcaBudget, listBudget]
      · simpa only [Nat.mul_comm] using field_capacity_split
theorem protocolClaim6732_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    ProtocolClaim 6732 10250623 33554432 where
  admissible := ContactMovingSeedless6732Research.radius_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
    exact (certifiedGammaError_le_of_alignment halign).trans
      (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
  score := ContactMovingSeedless6732Research.radius_score
#print axioms protocolClaim6732_of_alignment
end
end ProximityPrize.SubmissionLower.ContactMovingProtocol6732Research
