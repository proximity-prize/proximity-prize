import ProximityPrize.SubmissionLower.BoundaryTailAssembly6808
import ProximityPrize.SubmissionLower.BoundaryTailProtocol6808

/-! The 68.08 protocol closure consumes the finite numerical receipts.
Its MCA allowance uses the scalar-list budget from BoundaryTailProtocol6808. -/
namespace ProximityPrize.SubmissionLower.Lower80830.Closure
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN095 RCN319 RCN238 RCN259 RCN156 RCN234 Lower80830.Selection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

def ledgerBudget : ℕ := 258791250294373749

theorem ledgerBudget_le_mcaBudget : ledgerBudget ≤ Profile6808.mcaBudget := by
  decide +kernel

variable (hbase : AffineSingleBridge6808.Receipt)
  (hpref : PhaseSemantics.PrefixReceiptSound)
  (hthreshold : PhaseSemantics.ThresholdReceiptSound)
  (hruns : PhaseSemantics.RunReceiptSound)
  (hledger : Assembly.LedgerReceiptSound PhaseSemantics.phaseCap ledgerBudget)
include hbase hpref hthreshold hruns hledger

/-- Actual selected-count bound, retaining the full ledger margin. -/
theorem selectedNoLargePencilBound6808_tight :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80830 ledgerBudget := by
  have hn : Fintype.card I = 262144 := Fintype.card_fin _
  have he : 262144 - 80830 = 181314 := by decide +kernel
  have hs : Fintype.card I - 80830 = 181314 :=
    (congrArg (fun n : ℕ => n - 80830) hn).trans he
  simp only [SelectedNoLargePencilBound, hs]
  intro U seeds A selected hdegree hA hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hagreement : ∀ gamma ∈ seeds, 181314 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hnoPrime : NoLargeSelectedPencil selected seeds 131071 80830 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Assembly.selected_pair_count_le hbase hpref hthreshold hruns hledger
    (U 0) (U 1) S selected seeds ⟨hdegree,hagreement,hnoPrime⟩

/-- The scalar-list budget reserves 6470456390 challenges, leaving the exact
MCA allowance 274980721640938697 checked by the protocol module. -/
theorem selectedNoLargePencilBound6808 :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80830 Profile6808.mcaBudget := by
  intro U seeds A selected hdegree hA hvalues hno
  exact (selectedNoLargePencilBound6808_tight hbase hpref hthreshold hruns hledger
    U seeds A selected hdegree hA hvalues hno).trans ledgerBudget_le_mcaBudget

theorem alignmentBound6808_tight :
    AffineLineAlignmentBound IRSProfile.baseCode 80830 ledgerBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80830
    ledgerBudget (selectedNoLargePencilBound6808_tight hbase hpref hthreshold hruns hledger)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension] using h

theorem alignmentBound6808 :
    AffineLineAlignmentBound IRSProfile.baseCode Profile6808.errors Profile6808.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80830
    Profile6808.mcaBudget (selectedNoLargePencilBound6808 hbase hpref hthreshold hruns hledger)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension, Profile6808.errors] using h

theorem protocolClaim6808 : ProtocolClaim 6808 10346334 33554432 :=
  Profile6808.protocolClaim6808_of_alignment
    (alignmentBound6808 hbase hpref hthreshold hruns hledger)

end
end ProximityPrize.SubmissionLower.Lower80830.Closure
