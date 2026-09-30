import ProximityPrize.SubmissionLower.FinalAssembly6815
import ProximityPrize.SubmissionLower.MovingFiberProtocol6815
namespace ProximityPrize.SubmissionLower.Lower80899.FinalClosure
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN095 RCN319 RCN238 RCN259 RCN156 RCN234 Lower80899.Selection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

def ledgerBudget : ℕ := FinalLedgerChecks6815.budget

theorem ledgerBudget_le_mcaBudget : ledgerBudget ≤ MovingFiberProtocol6815.mcaBudget := by
  decide +kernel

variable (hrules : Lower80899.FinalRegularBridge.Rules)
include hrules

theorem selectedNoLargePencilBound6815_tight :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80899 ledgerBudget := by
  have hn : Fintype.card I = 262144 := Fintype.card_fin _
  have he : 262144 - 80899 = 181245 := by decide +kernel
  have hs : Fintype.card I - 80899 = 181245 :=
    (congrArg (fun n : ℕ => n - 80899) hn).trans he
  simp only [SelectedNoLargePencilBound, hs]
  intro U seeds A selected hdegree hA hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hagreement : ∀ gamma ∈ seeds, 181245 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hnoPrime : NoLargeSelectedPencil selected seeds 131071 80899 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact FinalAssembly.selected_pair_count_le hrules
    (U 0) (U 1) S selected seeds ⟨hdegree,hagreement,hnoPrime⟩

theorem selectedNoLargePencilBound6815 :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80899 MovingFiberProtocol6815.mcaBudget := by
  intro U seeds A selected hdegree hA hvalues hno
  exact (selectedNoLargePencilBound6815_tight hrules
    U seeds A selected hdegree hA hvalues hno).trans ledgerBudget_le_mcaBudget

theorem alignmentBound6815 :
    AffineLineAlignmentBound IRSProfile.baseCode MovingFiberProtocol6815.errors MovingFiberProtocol6815.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80899
    MovingFiberProtocol6815.mcaBudget (selectedNoLargePencilBound6815 hrules)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension, MovingFiberProtocol6815.errors] using h

theorem protocolClaim_of_rules : ProtocolClaim 6815 331366399 1073741824 :=
  MovingFiberProtocol6815.protocolClaim6815_of_alignment
    (alignmentBound6815 hrules)

end
end ProximityPrize.SubmissionLower.Lower80899.FinalClosure
