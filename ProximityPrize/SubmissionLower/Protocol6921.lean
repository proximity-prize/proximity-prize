import ProximityPrize.SubmissionLower.Fast015
import ProximityPrize.SubmissionLower.List6921

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace Protocol6921

open Code CoreDefinitions ToyProblem
open ProximityPrize.Benchmark Sol1.OneCount
open scoped NNReal

noncomputable section
local instance : DecidableEq K := Classical.decEq K

def queryRadius : ℝ≥0 := claimedRadius 335972916 1073741824

theorem query_complement : (1 - queryRadius : ℝ≥0) = 184442227 / 268435456 := by
  apply NNReal.coe_injective
  have hr : queryRadius ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    norm_num [queryRadius, claimedRadius]
  rw [NNReal.coe_sub hr]
  norm_num [queryRadius, claimedRadius]

private theorem score_power_comparison : (184442227 : ℕ) ^ 12800 ≤ 2 ^ 351470 := by
  decide +kernel

theorem score_lower_integer_cross :
    (184442227 : ℕ) ^ 12800 * 2 ^ 6930 ≤ 268435456 ^ 12800 := by
  calc
    _ ≤ 2 ^ 351470 * 2 ^ 6930 := Nat.mul_le_mul_right _ score_power_comparison
    _ = 268435456 ^ 12800 := by
      rw [show (268435456 : ℕ) = 2 ^ 28 by norm_num, ← pow_mul, ← pow_add]

theorem query_score_6921 :
    (1 - queryRadius) ^ IRSProfile.repetitions ≤ claimedError 6930 := by
  change (1 - queryRadius) ^ 128 ≤ claimedError 6930
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (100 : ℕ) ≠ 0)).mp
  rw [← pow_mul, Sol1.C42.claimedError_pow_100, query_complement]
  change ((184442227 : ℝ≥0) / 268435456) ^ 12800 ≤ 1 / (2 : ℝ≥0) ^ 6930
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast score_lower_integer_cross

theorem query_admissible : queryRadius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [queryRadius, claimedRadius, IRSProfile.minRelativeDistance]


def radius : ℝ := List6921.Native.radius6921

theorem queryRadius_coe : (queryRadius : ℝ) = radius := by
  norm_num [queryRadius, claimedRadius, radius, List6921.Native.radius6921]

def mcaAllowance : ℕ := 243545704652772149

def ActualMCACap (B : ℕ) : Prop :=
  ∀ U : Fin 2 → I → Fin IRSProfile.interleaving → K,
    {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius}.ncard ≤ B

def badSlopes (U : Fin 2 → I → Fin IRSProfile.interleaving → K) : Finset K := by
  classical
  exact Finset.univ.filter fun gamma ↦
    IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius

private theorem mem_badSlopes (U : Fin 2 → I → Fin IRSProfile.interleaving → K) (γ : K) :
    γ ∈ badSlopes U ↔ IsMCA (AffineLineGenerator K) IRSProfile.code γ U radius := by
  classical
  simp [badSlopes]

theorem badSlopes_card_eq_ncard (U : Fin 2 → I → Fin IRSProfile.interleaving → K) :
    (badSlopes U).card =
      {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius}.ncard := by
  classical
  have hs : {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius} =
      (badSlopes U : Set K) := by
    ext gamma
    simp [badSlopes]
  rw [hs,Set.ncard_coe_finset]

/-- The actual MCA probability, maximizing over arbitrary native IRS8 word pairs. -/
theorem mca_error_le_of_actualCap (B : ℕ) (hcap : ActualMCACap B) :
    mcaError (AffineLineGenerator K) IRSProfile.code radius ≤
      (B : ENNReal) / (Fintype.card K : ENNReal) := by
  classical
  refine iSup_le fun U ↦ ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  change ENNReal.ofReal (((badSlopes U).card : ℝ) / Fintype.card K) ≤ _
  have hc : (badSlopes U).card ≤ B := by
    rw [badSlopes_card_eq_ncard]
    exact hcap U
  calc
    _ ≤ ENNReal.ofReal ((B : ℝ) / Fintype.card K) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- The independent IRS16 list is already bounded, so only the MCA cap remains. -/
theorem gamma_error_le_of_actualCap (B : ℕ) (hcap : ActualMCACap B)
    (hbudget : (B + List6921.weightedListCap) * 2 ^ 128 ≤ Fintype.card K) :
    ToyProblem.certifiedGammaError IRSProfile.code queryRadius ≤ reductionTarget := by
  have hNat := ENat.toNat_le_of_le_natCast List6921.Native.actual_squared_lambda_le
  have hList :
      ((Code.Lambda (squaredCode : Set (I → A16)) radius).toNat : ENNReal) /
        (Fintype.card K : ENNReal) ≤ (List6921.weightedListCap : ENNReal) / Fintype.card K :=
    ENNReal.div_le_div_right (by exact_mod_cast hNat) _
  have hreal : ((B + List6921.weightedListCap : ℕ) : ℝ) / Fintype.card K ≤ (1 : ℝ) / 2 ^ 128 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast hbudget
  have hENN : ((B + List6921.weightedListCap : ℕ) : ENNReal) / Fintype.card K ≤
      (1 : ENNReal) / 2 ^ 128 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity)] at h
    simpa using h
  rw [← ENNReal.coe_le_coe,ToyProblem.coe_certifiedGammaError]
  rw [queryRadius_coe]
  calc
    _ ≤ (B : ENNReal) / Fintype.card K + (List6921.weightedListCap : ENNReal) / Fintype.card K :=
      add_le_add (mca_error_le_of_actualCap B hcap) hList
    _ = ((B + List6921.weightedListCap : ℕ) : ENNReal) / Fintype.card K := by
      rw [← ENNReal.add_div,Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ 128 := hENN
    _ = (reductionTarget : ENNReal) := by
      norm_num [reductionTarget,ProximityGap.prizeThreshold]

/-- Exact native benchmark type, with one mathematical count and the explicit integer budget. -/
theorem protocolClaim_of_actualCap (B : ℕ) (hcap : ActualMCACap B)
    (hbudget : (B + List6921.weightedListCap) * 2 ^ 128 ≤ (2130706433 : ℕ) ^ 6) :
    ProtocolClaim 6930 335972916 1073741824 where
  admissible := query_admissible
  reduction := by
    change ToyProblem.certifiedGammaError IRSProfile.code queryRadius ≤ reductionTarget
    apply gamma_error_le_of_actualCap B hcap
    rw [Sol1.Reciprocal.Native.field_card]
    exact hbudget
  score := query_score_6921


theorem remaining_budget :
    (mcaAllowance + List6921.weightedListCap) * 2 ^ 128 ≤ (2130706433 : ℕ) ^ 6 := by
  norm_num [mcaAllowance,List6921.weightedListCap]

theorem remaining_allowance_exact :
    mcaAllowance + List6921.weightedListCap = 274980728111395087 := by
  norm_num [mcaAllowance,List6921.weightedListCap]

theorem remaining_budget_maximal :
    (2130706433 : ℕ) ^ 6 < (mcaAllowance + List6921.weightedListCap + 1) * 2 ^ 128 := by
  norm_num [mcaAllowance,List6921.weightedListCap]

/-- The sole unresolved mathematical gate, stated using the actual native IsMCA. -/
def OneCountGoal : Prop := ActualMCACap mcaAllowance

/-- All non-MCA mathematics and arithmetic are discharged for this exact fixed allowance. -/
theorem protocolClaim_of_oneCountGoal (hcap : OneCountGoal) :
    ProtocolClaim 6930 335972916 1073741824 :=
  protocolClaim_of_actualCap mcaAllowance hcap remaining_budget


/-- The exact scalar MCA premise at the claimed radius. -/
def ScalarMCACap : Prop :=
  ∀ (u : Fin 2 → I → K) (Γ : Finset K),
    (∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) →
    Γ.card ≤ mcaAllowance

theorem nativeCap_of_scalarCap (hscalar : ScalarMCACap) :
    OneCountGoal := by
  classical
  intro U
  rw [← badSlopes_card_eq_ncard]
  have hbad : ∀ γ ∈ badSlopes U,
      IsMCA (AffineLineGenerator K) (IRSProfile.baseCode ^⋈ (Fin IRSProfile.interleaving))
        γ U radius := by
    have hcode : IRSProfile.code = (IRSProfile.baseCode ^⋈ (Fin IRSProfile.interleaving)) :=
      Sol1.C64.native_code_eq
    rw [← hcode]
    exact fun γ => (mem_badSlopes U γ).mp
  exact Sol1.C64.restricted_interleaved_card_le IRSProfile.baseCode
    (⊤ : ModuleCode I K K) radius mcaAllowance
    (by rw [Sol1.Reciprocal.Native.field_card]; norm_num [mcaAllowance])
    (fun u _ Γ hΓ => hscalar u Γ hΓ) U (by simp)
    (badSlopes U) hbad

/-- This is the entire protocol bridge needed by a future uniform scalar count. -/
theorem protocolClaim_of_scalarCap (hscalar : ScalarMCACap) :
    ProtocolClaim 6930 335972916 1073741824 :=
  protocolClaim_of_oneCountGoal (nativeCap_of_scalarCap hscalar)


/-- The same bridge accepts a bound on all scalar bad slopes in the polynomial formulation. -/
def ScalarBadSlopeCap : Prop :=
  ∀ (u : Fin 2 → I → K) (Γ : Finset K),
    (∀ γ ∈ Γ, FrobeniusLocator.Principal.BadSlope IRSProfile.domain
      (u 0) (u 1) 131072 180120 γ) →
    Γ.card ≤ mcaAllowance

theorem scalarMCACap_of_badSlopeCap (hcap : ScalarBadSlopeCap) : ScalarMCACap := by
  classical
  intro u Γ hΓ
  apply hcap u Γ
  intro γ hγ
  have hmca := hΓ γ hγ
  change IsMCA (AffineLineGenerator K) (ReedSolomon.code IRSProfile.domain 131072) γ u radius at hmca
  have : NeZero (131072 : ℕ) := ⟨by decide⟩
  apply FrobeniusLocator.Principal.isMCA_implies_badSlope IRSProfile.domain u 131072 180120 radius
    ?_ γ hmca
  intro T hT
  have hcount : (180119 : ℝ) < (Fintype.card I : ℝ) * (1 - radius) := by
    norm_num [I, IRSProfile.Index, radius, List6921.Native.radius6921]
  exact Nat.succ_le_of_lt (by exact_mod_cast hcount.trans_le hT)
theorem protocolClaim_of_badSlopeCap (hcap : ScalarBadSlopeCap) : ProtocolClaim 6930 335972916 1073741824 :=
  protocolClaim_of_scalarCap (scalarMCACap_of_badSlopeCap hcap)

end
end Protocol6921
