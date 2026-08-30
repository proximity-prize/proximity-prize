import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorScalar
import ProximityPrize.SubmissionLower.P1
namespace ProximityPrize.SubmissionLower.LocatorProtocol
open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open RCN018 RCN019
open RCN284
open RCN280
open scoped NNReal
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 5000000
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
def n : ℕ := 262144
def errors : ℕ := 80191
def agreements : ℕ := n-errors
def listBudget : ℕ := 1050403922
def mcaBudget : ℕ := 274980727060991165
def radius : ℝ≥0 := LocatorArithmetic.radius
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
 apply RCN280.squared_eight_lambda_le_of_interleaved_list
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
 have hbound := LocatorScalar.irs_scalar_finite_list_card_le
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
 norm_num [radius, LocatorArithmetic.radius, claimedRadius,
   LocatorArithmetic.radiusNumerator,
   LocatorArithmetic.radiusDenominator,
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
     simpa only [radius, errors, LocatorArithmetic.errors] using
       LocatorArithmetic.radius_floor] at hcomp
   have hn : Fintype.card IRSProfile.Index = 262144 := by
     norm_num [IRSProfile.Index]
   rw [hn]
   norm_num [errors, LocatorArithmetic.errors] at hcomp ⊢
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
     rw [RCN284.irs_code_eq_base_interleaved]
     exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
       IRSProfile.interleaving radius
       (by norm_num [IRSProfile.interleaving])
       (by norm_num [radius, LocatorArithmetic.radius,
         claimedRadius, LocatorArithmetic.radiusNumerator,
         LocatorArithmetic.radiusDenominator])
       (by norm_num [radius, LocatorArithmetic.radius,
         claimedRadius, LocatorArithmetic.radiusNumerator,
         LocatorArithmetic.radiusDenominator])
   _ ≤ ENNReal.ofReal
       ((mcaBudget : ℝ) / Fintype.card IRSProfile.Field) :=
     base_mca_le_of_alignment halign
   _ = (mcaBudget : ENNReal) /
       (Fintype.card IRSProfile.Field : ENNReal) := by
     rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
       ENNReal.ofReal_natCast]
theorem field_capacity_split :
   2 ^ (128 : ℕ) * (mcaBudget + listBudget) ≤
     Fintype.card IRSProfile.Field := by
 rw [RCN284.field_cardinality]
 norm_num [mcaBudget, listBudget]
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
     apply RCN284.nat_div_le_inv_pow
     · norm_num [mcaBudget, listBudget]
     · simpa only [Nat.mul_comm] using field_capacity_split
theorem protocolClaim6743_of_alignment
   (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   ProtocolClaim 6743 10264575 33554432 where
 admissible := LocatorArithmetic.radius_admissible
 reduction := by
   change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
   simpa [reductionTarget, ProximityGap.prizeThreshold] using
     certifiedGammaError_le_of_alignment halign
 score := by
   change (1 - LocatorArithmetic.radius) ^
     IRSProfile.repetitions ≤ claimedError 6743
   exact LocatorArithmetic.score_target_le
end
end ProximityPrize.SubmissionLower.LocatorProtocol
