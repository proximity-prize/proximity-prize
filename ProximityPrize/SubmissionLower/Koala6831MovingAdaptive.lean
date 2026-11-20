import ProximityPrize.SubmissionLower.Koala6831MovingStages
import ProximityPrize.SubmissionLower.Koala6831MovingContact
import ProximityPrize.SubmissionLower.Koala6831MovingSupports
import ProximityPrize.SubmissionLower.LowerGeometry


namespace ProximityPrize.SubmissionLower.Koala6831MovingAdaptive

open RCN081 RCN095 RCN130 RCN156 RCN180 RCN234 RCN266
open LocatorFactorAggregate LocatorLowQuotient LocatorTwoFactorAvoidance
open LocatorBatchProductRoute LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (SourceNumbers)
open Koala6831MovingStages Koala6831Moving

noncomputable section

variable {K : Type} [Field K]
variable {I : Type*} [Fintype I]
local instance movingAdaptiveDecidableEq : DecidableEq K := Classical.decEq K






theorem exhaust_finset_stage {α : Type*} [DecidableEq α] (initial : Finset α)
    (active : Finset α → Prop) (covered : α → Prop)
    (step : ∀ S ⊆ initial, S.Nonempty → active S →
      ∃ U ⊂ S, ∀ a ∈ S \ U, covered a) :
    ∃ U ⊆ initial, (U = ∅ ∨ ¬ active U) ∧ ∀ a ∈ initial \ U, covered a := by
  classical
  have hfinish (S : Finset α) (hsub : S ⊆ initial) :
      ∃ U ⊆ S, (U = ∅ ∨ ¬ active U) ∧ ∀ a ∈ S \ U, covered a := by
    induction S using Finset.strongInductionOn
    rename_i S ih
    by_cases hact : S.Nonempty ∧ active S
    · obtain ⟨V, hV, hcovered⟩ := step S hsub hact.1 hact.2
      obtain ⟨U, hUV, hstop, hrec⟩ := ih V hV (hV.subset.trans hsub)
      refine ⟨U, hUV.trans hV.subset, hstop, fun a ha => ?_⟩
      obtain ⟨haS, haU⟩ := Finset.mem_sdiff.mp ha
      by_cases haV : a ∈ V
      · exact hrec a (Finset.mem_sdiff.mpr ⟨haV, haU⟩)
      · exact hcovered a (Finset.mem_sdiff.mpr ⟨haS, haV⟩)
    · refine ⟨S, fun _ h => h, ?_, fun a ha => ?_⟩
      · by_cases hz : S.Nonempty
        · exact Or.inr (fun hf => hact ⟨hz, hf⟩)
        · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hz)
      · exact ((Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp ha).1).elim
  exact hfinish initial (fun _ h => h)

end

end ProximityPrize.SubmissionLower.Koala6831MovingAdaptive
