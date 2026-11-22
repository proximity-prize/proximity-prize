import ProximityPrize.SubmissionLower.Cell82Intermediate
import ProximityPrize.SubmissionLower.Scalar55RefinedList

set_option Elab.async false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false

namespace Cell82Intermediate

noncomputable section
open Code LinearCode CoreDefinitions ToyProblem FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount (squaredCode A16)
open Sol1.FiniteRowProjection (agreementCard)
open scoped NNReal

abbrev I := P0.I
abbrev K := P0.K
abbrev Words := P0.Words
abbrev node := P0.node
abbrev k := P0.k

abbrev listCap : ℕ := 2325506586623926
abbrev scalarCap : ℕ := 272655221524771161
abbrev heightCap (t : Target) : ℕ := 262144 + k - 2 * agreement t - 1
abbrev rankFee (t : Target) : ℕ := agreement t - k + P0.p * heightCap t
abbrev anchorFee (t : Target) : ℕ := P0.p * heightCap t + 2 * heightCap t + 262144 + 2
abbrev coreBudget (t : Target) : ℕ := scalarCap - rankFee t - anchorFee t

theorem reserve_exact (t : Target) : coreBudget t + anchorFee t + rankFee t = scalarCap := by
  cases t <;> decide

theorem core_receipts :
    coreBudget .s51 = 272512954255861992 ∧
    coreBudget .s52 = 272512869027604642 ∧
    coreBudget .s53 = 272512792322173027 ∧
    coreBudget .s54 = 272512707093915677 := by decide +kernel

/-- The 69.55 fees also leave a common conservative allowance. -/
theorem conservative_core_le (t : Target) : 272512621865658327 ≤ coreBudget t := by
  cases t <;> decide

def realRadius (t : Target) : ℝ := radius t
def BadFamily (t : Target) (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u (realRadius t)

/-- This bound is the sufficient input from the bad-slope proof at the exact agreement count. -/
def SlopeCount (t : Target) : Prop :=
  ∀ (u : Words) (Γ : Finset K),
    (∀ γ ∈ Γ, Principal.BadSlope node (u 0) (u 1) k (agreement t) γ) →
      Γ.card ≤ scalarCap

theorem scalar_list (t : Target) : CJ0.ScalarList (agreement t) listCap := by
  intro w
  have hA : 179876 ≤ agreement t := by cases t <;> decide
  have hsub : CJ0.close (agreement t) w ⊆ CJ0.close 179876 w :=
    fun _ hf => ⟨hf.1, hA.trans hf.2⟩
  obtain ⟨hfin, hcard⟩ := Scalar55RefinedList.scalar_list w
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hcard⟩

theorem agreement_of_threshold (t : Target) {s : ℕ}
    (hs : (Fintype.card I : ℝ) * (1-realRadius t) ≤ s) : agreement t ≤ s := by
  rw [IRSProfile.card_index] at hs
  have p : ((agreement t - 1 : ℕ) : ℝ) < 262144*(1-realRadius t) := by
    cases t <;> norm_num [realRadius, radius, claimedRadius, data]
  have h : agreement t - 1 < s := by exact_mod_cast p.trans_le hs
  omega

variable {t : Target}

theorem scalar_projection_room : scalarCap + 1 < (0x7f000001 : ℕ) ^ 6 := by decide
theorem list_projection_room : (listCap + 1) ^ 2 < (0x7f000001 : ℕ) ^ 6 := by decide
theorem close_agreement_ge (t : Target) (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ realRadius t) : agreement t ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by rw [IRSProfile.card_index]; decide
  have hposR : (0 : ℝ) < Fintype.card I := by exact_mod_cast hpos
  have hradius : realRadius t =
      1 - ((Fintype.card I : ℝ) * (1 - realRadius t)) / Fintype.card I := by
    rw [mul_comm, mul_div_cancel_right₀ _ hposR.ne']
    ring
  have hagree := (Code.relHammingDist_le_one_sub_div_iff hpos).mp
    (show (δᵣ(w,f) : ℝ) ≤ 1 - ((Fintype.card I : ℝ) * (1 - realRadius t)) / Fintype.card I by
      rwa [← hradius])
  have hcard : Code.agree f w ≤ agreementCard f w := by
    unfold Code.agree agreementCard
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  exact (agreement_of_threshold t hagree).trans hcard
theorem squared_lambda_le (hlist : CJ0.ScalarList (agreement t) listCap) :
    Code.Lambda (squaredCode : Set (I → A16)) (realRadius t) ≤ (listCap : ℕ∞) :=
  CJ0.squared_lambda_le hlist (Sol1.C64.native_field_card ▸ list_projection_room.le)
    (realRadius t) (close_agreement_ge t)
def nativeBadSlopes (t : Target) (U : Sol1.C64.NativePair) : Finset K := by
  classical
  exact Finset.univ.filter fun γ => IsMCA (AffineLineGenerator K) IRSProfile.code γ U (realRadius t)
theorem native_cap_of_scalar_cap
    (hscalar : ∀ u Γ, BadFamily t u Γ → Γ.card ≤ scalarCap) (U : Sol1.C64.NativePair) :
    (nativeBadSlopes t U).card ≤ scalarCap := by
  classical
  apply Sol1.C64.restricted_interleaved_card_le IRSProfile.baseCode
    (⊤ : ModuleCode I K K) (realRadius t) scalarCap
    (by rw [Sol1.C64.native_field_card]; exact scalar_projection_room.le)
    (fun u _ Γ hΓ => hscalar u Γ hΓ) U (by simp) (nativeBadSlopes t U)
  intro γ hγ
  change γ ∈ Finset.univ.filter (fun z => IsMCA (AffineLineGenerator K)
    IRSProfile.code z U (realRadius t)) at hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  rw [Sol1.C64.native_code_eq] at hγ
  exact hγ
theorem mca_error_le_of_scalar_cap (hscalar : ∀ u Γ, BadFamily t u Γ → Γ.card ≤ scalarCap) :
    mcaError (AffineLineGenerator K) IRSProfile.code (realRadius t) ≤
      (scalarCap : ENNReal) / (Fintype.card K : ENNReal) := by
  classical
  refine iSup_le fun U => ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  change ENNReal.ofReal (((nativeBadSlopes t U).card : ℝ) / Fintype.card K) ≤ _
  calc
    _ ≤ ENNReal.ofReal ((scalarCap : ℝ) / Fintype.card K) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast native_cap_of_scalar_cap hscalar U)
        (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
theorem error_budget :
    (scalarCap + listCap) * 2 ^ 128 ≤ (0x7f000001 : ℕ) ^ 6 := by decide
theorem gamma_error_le_of_scalar_cap (hlist : CJ0.ScalarList (agreement t) listCap)
    (hscalar : ∀ u Γ, BadFamily t u Γ → Γ.card ≤ scalarCap) :
    ToyProblem.certifiedGammaError IRSProfile.code (radius t) ≤ reductionTarget := by
  have hNat := ENat.toNat_le_of_le_natCast (squared_lambda_le hlist)
  have hList :
      ((Code.Lambda (squaredCode : Set (I → A16)) (realRadius t)).toNat : ENNReal) /
        (Fintype.card K : ENNReal) ≤ (listCap : ENNReal) / Fintype.card K :=
    ENNReal.div_le_div_right (by exact_mod_cast hNat) _
  have hreal : ((scalarCap + listCap : ℕ) : ℝ) / Fintype.card K ≤ (1 : ℝ) / 2 ^ 128 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (Sol1.C64.native_field_card ▸ error_budget :
      (scalarCap + listCap) * 2 ^ 128 ≤ Fintype.card K)
  have hENN : ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K ≤
      (1 : ENNReal) / 2 ^ 128 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity)] at h
    simpa using h
  rw [← ENNReal.coe_le_coe, ToyProblem.coe_certifiedGammaError]
  calc
    _ ≤ (scalarCap : ENNReal) / Fintype.card K + (listCap : ENNReal) / Fintype.card K :=
      add_le_add (mca_error_le_of_scalar_cap hscalar) hList
    _ = ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ 128 := hENN
    _ = (reductionTarget : ENNReal) := by
      norm_num [reductionTarget, ProximityGap.prizeThreshold]
/-- A uniform bound on bad slopes gives the score claim at the maximal cell fraction. -/
theorem of_bad_slopes (t : Target) (bound : SlopeCount t) :
    ProtocolClaim (data t).score (data t).numerator (data t).denominator where
  admissible := radius_admissible t
  reduction := by
    apply gamma_error_le_of_scalar_cap (scalar_list t)
    intro u Γ hΓ
    apply bound u Γ
    intro γ hγ
    let : NeZero k := ⟨by decide⟩
    exact Principal.isMCA_implies_badSlope node u k (agreement t) (realRadius t)
      (fun _ h => agreement_of_threshold t h) γ (hΓ γ hγ)
  score := radius_score t

theorem of_bad_slopes_51 (h : SlopeCount .s51) :
    ProtocolClaim 6951 2893210916864619832 9223372036854662547 := of_bad_slopes .s51 h

theorem of_bad_slopes_52 (h : SlopeCount .s52) :
    ProtocolClaim 6952 2893562760585543664 9223372036854775757 := of_bad_slopes .s52 h

theorem of_bad_slopes_53 (h : SlopeCount .s53) :
    ProtocolClaim 6953 2893879419934332965 9223372036854743289 := of_bad_slopes .s53 h

theorem of_bad_slopes_54 (h : SlopeCount .s54) :
    ProtocolClaim 6954 2894231263655162954 9223372036854557403 := of_bad_slopes .s54 h

#print axioms of_bad_slopes
end
end Cell82Intermediate
