import ProximityPrize.SubmissionLower.ExactInitialCharge6815
namespace ProximityPrize.SubmissionLower.TerminalCharge6815
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem exists_terminal {ι : Type*} [DecidableEq ι]
    (count charge : ι → ℕ) (routeable : Finset ι → Prop) (ambient : Finset ι)
    (hroute : ∀ B, B ⊆ ambient → routeable B →
      ∃ U, U ⊂ B ∧ ∀ i ∈ B \ U, count i ≤ charge i) :
    ∃ U, U ⊆ ambient ∧ ¬ routeable U ∧
      ∀ i ∈ ambient \ U, count i ≤ charge i := by
  classical
  have aux : ∀ B : Finset ι, B ⊆ ambient →
      ∃ U, U ⊆ B ∧ ¬ routeable U ∧
        ∀ i ∈ B \ U, count i ≤ charge i := by
    intro B
    induction B using Finset.strongInduction with
    | H B ih =>
      intro hB
      by_cases hr : routeable B
      · obtain ⟨V, hV, hexit⟩ := hroute B hB hr
        obtain ⟨U, hU, hstop, hrest⟩ := ih V hV (hV.subset.trans hB)
        refine ⟨U, hU.trans hV.subset, hstop, ?_⟩
        intro i hi
        obtain ⟨hiB, hiU⟩ := Finset.mem_sdiff.mp hi
        by_cases hiV : i ∈ V
        · exact hrest i (Finset.mem_sdiff.mpr ⟨hiV, hiU⟩)
        · exact hexit i (Finset.mem_sdiff.mpr ⟨hiB, hiV⟩)
      · exact ⟨B, Finset.Subset.refl _, hr, by simp⟩
  exact aux ambient (Finset.Subset.refl _)

end ProximityPrize.SubmissionLower.TerminalCharge6815
