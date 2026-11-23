import ProximityPrize.SubmissionLower.Front6960Core
import ProximityPrize.SubmissionLower.Cell6960Inputs

set_option Elab.async false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false

namespace Protocol6960Plain
noncomputable section
open Code LinearCode CoreDefinitions ToyProblem FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount (squaredCode A16)
open Cell6960Inputs (I K Words node k agreement numerator denominator radius realRadius
  BadFamily nativeBadSlopes close_agreement_ge agreement_of_threshold radius_admissible radius_score)
open scoped NNReal

local notation "t" => Cell6960Inputs.Target.s60

abbrev listCap:ℕ:=2319217998868710
abbrev scalarCap:ℕ:=272661510112526377

theorem scalar_projection_room:scalarCap+1 < (0x7f000001:ℕ) ^ 6:=by decide
theorem list_projection_room:(listCap+1) ^ 2 < (0x7f000001:ℕ) ^ 6:=by decide
theorem squared_lambda_le (hlist : CJ0.ScalarList (agreement t) listCap) :
    Code.Lambda (squaredCode:Set (I→A16)) (realRadius t)≤(listCap:ℕ∞) :=
  CJ0.squared_lambda_le hlist (Sol1.C64.native_field_card ▸ list_projection_room.le)
    (realRadius t) (close_agreement_ge t)
theorem native_cap_of_scalar_cap
    (hscalar : ∀ u Γ,BadFamily t u Γ→Γ.card≤scalarCap) (U:Sol1.C64.NativePair) :
    (nativeBadSlopes t U).card≤scalarCap:=by
  classical
  apply Sol1.C64.restricted_interleaved_card_le IRSProfile.baseCode
    (⊤ : ModuleCode I K K) (realRadius t) scalarCap
    (by rw [Sol1.C64.native_field_card]; exact scalar_projection_room.le)
    (fun u _ Γ hΓ => hscalar u Γ hΓ) U (by simp) (nativeBadSlopes t U)
  intro γ hγ
  change γ ∈ Finset.univ.filter (fun z => IsMCA (AffineLineGenerator K)
    IRSProfile.code z U (realRadius t)) at hγ
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hγ
  rw [Sol1.C64.native_code_eq] at hγ
  exact hγ
theorem mca_error_le_of_scalar_cap (hscalar : ∀ u Γ, BadFamily t u Γ → Γ.card ≤ scalarCap) :
    mcaError (AffineLineGenerator K) IRSProfile.code (realRadius t) ≤
      (scalarCap:ENNReal) / (Fintype.card K:ENNReal):=by
  classical
  refine iSup_le fun U => ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  change ENNReal.ofReal (((nativeBadSlopes t U).card:ℝ) / Fintype.card K)≤_
  calc
    _ ≤ ENNReal.ofReal ((scalarCap : ℝ) / Fintype.card K) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast native_cap_of_scalar_cap hscalar U)
        (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
theorem error_budget :
    (scalarCap+listCap)*2 ^ 128≤(0x7f000001:ℕ) ^ 6:=by decide
theorem gamma_error_le_of_scalar_cap (hlist : CJ0.ScalarList (agreement t) listCap)
    (hscalar : ∀ u Γ,BadFamily t u Γ→Γ.card≤scalarCap) :
    ToyProblem.certifiedGammaError IRSProfile.code (radius t)≤reductionTarget:=by
  have hNat:=ENat.toNat_le_of_le_natCast (squared_lambda_le hlist)
  have hList :
      ((Code.Lambda (squaredCode : Set (I → A16)) (realRadius t)).toNat : ENNReal) /
        (Fintype.card K:ENNReal)≤(listCap:ENNReal) / Fintype.card K :=
    ENNReal.div_le_div_right (by exact_mod_cast hNat) _
  have hreal : ((scalarCap + listCap : ℕ) : ℝ) / Fintype.card K ≤ (1 : ℝ) / 2 ^ 128 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (Sol1.C64.native_field_card ▸ error_budget :
      (scalarCap+listCap)*2 ^ 128≤Fintype.card K)
  have hENN : ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K ≤
      (1:ENNReal) / 2 ^ 128:=by
    have h:=ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast,ENNReal.ofReal_div_of_pos (by positivity)] at h
    simpa using h
  rw [← ENNReal.coe_le_coe,ToyProblem.coe_certifiedGammaError]
  calc
    _ ≤ (scalarCap : ENNReal) / Fintype.card K + (listCap : ENNReal) / Fintype.card K :=
      add_le_add (mca_error_le_of_scalar_cap hscalar) hList
    _ = ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K := by
      rw [← ENNReal.add_div,Nat.cast_add]
    _≤(1:ENNReal) / 2 ^ 128:=hENN
    _ = (reductionTarget : ENNReal) := by
      norm_num [reductionTarget,ProximityGap.prizeThreshold]
theorem of_bad_slopes (hlist : CJ0.ScalarList 179827 listCap)
    (bound : ∀ (u : Words) (Γ : Finset K),
      (∀ γ ∈ Γ, Principal.BadSlope node (u 0) (u 1) k 179827 γ) →
        Γ.card≤scalarCap) :
    ProtocolClaim 6960 337174527 1073741824 where
  admissible:=radius_admissible t
  reduction := by
    apply gamma_error_le_of_scalar_cap hlist
    intro u Γ hΓ
    apply bound u Γ
    intro γ hγ
    let:NeZero k:=⟨by decide⟩
    exact Principal.isMCA_implies_badSlope node u k 179827 (realRadius t)
      (fun _ h => agreement_of_threshold t h) γ (hΓ γ hγ)
  score:=radius_score t

end
end Protocol6960Plain

namespace Front6960Plain
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark Front82706

abbrev coreBudget:ℕ:=272515177455741613
abbrev slopeBudget:ℕ:=Protocol6960Plain.scalarCap
abbrev listCap:ℕ:=Protocol6960Plain.listCap
abbrev CoreCount:=Front6960Core.CoreCount 179827 coreBudget

theorem core_budget_exact:coreBudget+Front6960Core.frontFee=slopeBudget:=by decide

theorem count_of_bad_slopes (hlist : CJ0.ScalarList 179827 listCap) (core : CoreCount)
    (u:Words) (Γ:Finset K)
    (h : ∀ γ ∈ Γ,Principal.BadSlope node (u 0) (u 1) k 179827 γ) :
    Γ.card≤slopeBudget:=by
  have ha:agreement≤179827:=by decide
  rcases Front6960Core.split ha u Γ (Front6960Core.strong_family_of_bad_slopes h) with
      cheap | ⟨Δ,deleted,M,_,hsum,⟨F⟩⟩
  · exact cheap.trans (by decide)
  have hi : M.overhead ≤ (heightCap : ℤ) := by
    have hM:=M.height_bound
    change (M.E.natDegree:ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁≤heightCap
    omega
  by_cases hlo:M.overhead≤0
  · exact (hsum.trans (Nat.add_le_add_right (P1.anchored_list_count hlist M Δ F hlo) _)).trans (by decide)
  · have pos : (0 : ℤ) + 1 ≤ M.overhead := Int.add_one_le_of_lt (lt_of_not_ge hlo)
    exact (hsum.trans (Nat.add_le_add_right (core u deleted M Δ F pos hi) _)).trans
      core_budget_exact.le

theorem of_core_count (hlist : CJ0.ScalarList 179827 listCap) (core : CoreCount) :
    ProtocolClaim 6960 337174527 1073741824 :=
  Protocol6960Plain.of_bad_slopes hlist (count_of_bad_slopes hlist core)

def HeightBand (lo hi : ℤ) : Prop :=
  ∀ (u : Words) (del : Finset I) (M : AnchorModel u del) (Γ : Finset K),
    P1.FamilyAt 179827 M Γ→lo≤M.overhead→M.overhead≤hi→Γ.card≤coreBudget

/-- Combine the exact ordinary counts at the two selected height boundaries. -/
theorem core_of_partition
    (low:HeightBand 1 2570) (mid:HeightBand 2571 8099)
    (high:HeightBand 8100 (heightCap:ℤ)):CoreCount:=by
  intro u del M Γ F lo hi
  by_cases hl:M.overhead≤2570
  · exact low u del M Γ F lo hl
  by_cases hh:8100≤M.overhead
  · exact high u del M Γ F hh hi
  · have begin_mid : (2570 : ℤ) + 1 ≤ M.overhead := Int.add_one_le_of_lt (lt_of_not_ge hl)
    have end_mid:M.overhead≤(8100:ℤ) - 1:=Int.le_sub_one_of_lt (lt_of_not_ge hh)
    exact mid u del M Γ F begin_mid end_mid

theorem of_partition (hlist : CJ0.ScalarList 179827 listCap)
    (low:HeightBand 1 2570) (mid:HeightBand 2571 8099)
    (high:HeightBand 8100 (heightCap:ℤ)) :
    ProtocolClaim 6960 337174527 1073741824 :=
  of_core_count hlist (core_of_partition low mid high)

#print axioms of_core_count
#print axioms of_partition
end
end Front6960Plain
