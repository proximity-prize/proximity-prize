import ProximityPrize.SubmissionLower.BoundaryTailAssembly
import ProximityPrize.SubmissionLower.BoundaryTailProtocol

/-! The 68.06 protocol closure consumes the finite numerical receipts.
Its MCA allowance uses the scalar-list budget from BoundaryTailProtocol. -/
namespace ProximityPrize.SubmissionLower.Lower80811.Closure
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN095 RCN319 RCN238 RCN259 RCN156 RCN234 Lower80811.Selection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

def ledgerBudget : ℕ := 274976539400589696

theorem ledgerBudget_le_mcaBudget : ledgerBudget ≤ Profile6806.mcaBudget := by
  decide +kernel

variable {zero : ℕ → ℕ → ℕ} {split : FlagDegree → ℕ}
variable (hbase : BoundaryTailBaseOracle.Receipt zero split (PhaseSemantics.phaseCap 0))
  (hpref : PhaseSemantics.PrefixReceiptSound)
  (hthreshold : PhaseSemantics.ThresholdReceiptSound)
  (hruns : PhaseSemantics.RunReceiptSound)
  (hledger : Assembly.LedgerReceiptSound ledgerBudget)
include hbase hpref hthreshold hruns hledger

/-- Actual selected-count bound, retaining the full ledger margin. -/
theorem selectedNoLargePencilBound6806_tight :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80811 ledgerBudget := by
  have hn : Fintype.card I = 262144 := Fintype.card_fin _
  have he : 262144 - 80811 = 181333 := by decide +kernel
  have hs : Fintype.card I - 80811 = 181333 :=
    (congrArg (fun n : ℕ => n - 80811) hn).trans he
  simp only [SelectedNoLargePencilBound, hs]
  intro U seeds A selected hdegree hA hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hagreement : ∀ gamma ∈ seeds, 181333 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hnoPrime : NoLargeSelectedPencil selected seeds 131071 80811 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Assembly.selected_pair_count_le hbase hpref hthreshold hruns hledger
    (U 0) (U 1) S selected seeds ⟨hdegree,hagreement,hnoPrime⟩

/-- The scalar-list budget reserves 5969997903 challenges, leaving the exact
MCA allowance 274980722141397184 checked by the protocol module. -/
theorem selectedNoLargePencilBound6806 :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80811 Profile6806.mcaBudget := by
  intro U seeds A selected hdegree hA hvalues hno
  exact (selectedNoLargePencilBound6806_tight hbase hpref hthreshold hruns hledger
    U seeds A selected hdegree hA hvalues hno).trans ledgerBudget_le_mcaBudget

theorem alignmentBound6806_tight :
    AffineLineAlignmentBound IRSProfile.baseCode 80811 ledgerBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80811
    ledgerBudget (selectedNoLargePencilBound6806_tight hbase hpref hthreshold hruns hledger)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension] using h

theorem alignmentBound6806 :
    AffineLineAlignmentBound IRSProfile.baseCode Profile6806.errors Profile6806.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80811
    Profile6806.mcaBudget (selectedNoLargePencilBound6806 hbase hpref hthreshold hruns hledger)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension, Profile6806.errors] using h

theorem protocolClaim6806 : ProtocolClaim 6806 338950094847 1099511627776 :=
  Profile6806.protocolClaim6806_of_alignment
    (alignmentBound6806 hbase hpref hthreshold hruns hledger)

end
end ProximityPrize.SubmissionLower.Lower80811.Closure
