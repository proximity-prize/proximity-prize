import ProximityPrize.SubmissionLower.BoundaryTailAssembly6807
import ProximityPrize.SubmissionLower.BoundaryTailProtocol6807

/-! The 68.07 protocol closure consumes the finite numerical receipts.
Its MCA allowance uses the scalar-list budget from BoundaryTailProtocol6807. -/
namespace ProximityPrize.SubmissionLower.Lower80820.Closure
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN095 RCN319 RCN238 RCN259 RCN156 RCN234 Lower80820.Selection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

def ledgerBudget : ℕ := 274386827080775528

theorem ledgerBudget_le_mcaBudget : ledgerBudget ≤ Profile6807.mcaBudget := by
  decide +kernel

variable {zero : ℕ → ℕ → ℕ} {split : FlagDegree → ℕ}
variable (hbase : BoundaryTailBaseOracle6807.Receipt zero split (PhaseSemantics.phaseCap 0))
  (hpref : PhaseSemantics.PrefixReceiptSound)
  (hthreshold : PhaseSemantics.ThresholdReceiptSound)
  (hruns : PhaseSemantics.RunReceiptSound)
  (hledger : Assembly.LedgerReceiptSound PhaseSemantics.phaseCap ledgerBudget)
include hbase hpref hthreshold hruns hledger

/-- Actual selected-count bound, retaining the full ledger margin. -/
theorem selectedNoLargePencilBound6807_tight :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80820 ledgerBudget := by
  have hn : Fintype.card I = 262144 := Fintype.card_fin _
  have he : 262144 - 80820 = 181324 := by decide +kernel
  have hs : Fintype.card I - 80820 = 181324 :=
    (congrArg (fun n : ℕ => n - 80820) hn).trans he
  simp only [SelectedNoLargePencilBound, hs]
  intro U seeds A selected hdegree hA hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hagreement : ∀ gamma ∈ seeds, 181324 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hnoPrime : NoLargeSelectedPencil selected seeds 131071 80820 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Assembly.selected_pair_count_le hbase hpref hthreshold hruns hledger
    (U 0) (U 1) S selected seeds ⟨hdegree,hagreement,hnoPrime⟩

/-- The scalar-list budget reserves 6097216394 challenges, leaving the exact
MCA allowance 274980722014178693 checked by the protocol module. -/
theorem selectedNoLargePencilBound6807 :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80820 Profile6807.mcaBudget := by
  intro U seeds A selected hdegree hA hvalues hno
  exact (selectedNoLargePencilBound6807_tight hbase hpref hthreshold hruns hledger
    U seeds A selected hdegree hA hvalues hno).trans ledgerBudget_le_mcaBudget

theorem alignmentBound6807_tight :
    AffineLineAlignmentBound IRSProfile.baseCode 80820 ledgerBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80820
    ledgerBudget (selectedNoLargePencilBound6807_tight hbase hpref hthreshold hruns hledger)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension] using h

theorem alignmentBound6807 :
    AffineLineAlignmentBound IRSProfile.baseCode Profile6807.errors Profile6807.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80820
    Profile6807.mcaBudget (selectedNoLargePencilBound6807 hbase hpref hthreshold hruns hledger)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension, Profile6807.errors] using h

theorem protocolClaim6807 : ProtocolClaim 6807 10345087 33554432 :=
  Profile6807.protocolClaim6807_of_alignment
    (alignmentBound6807 hbase hpref hthreshold hruns hledger)

end
end ProximityPrize.SubmissionLower.Lower80820.Closure
