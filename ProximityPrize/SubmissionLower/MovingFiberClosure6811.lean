import ProximityPrize.SubmissionLower.MovingFiberAssembly6811
import ProximityPrize.SubmissionLower.MovingFiberProtocol6811

/-! The 68.8 protocol closure consumes the finite numerical receipts.
Its MCA allowance uses the scalar-list budget from MovingFiberProtocol6811. -/
namespace ProximityPrize.SubmissionLower.Lower80860.Closure
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN095 RCN319 RCN238 RCN259 RCN156 RCN234 Lower80860.Selection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

def ledgerBudget : ℕ := 274980720358131097

theorem ledgerBudget_le_mcaBudget : ledgerBudget ≤ MovingFiberProtocol6811.mcaBudget := by
  decide +kernel

variable (hbase : ReceiptData.Receipt)
  (hpref : PhaseSemantics.PrefixReceiptSound)
  (hthreshold : PhaseSemantics.ThresholdReceiptSound)
  (hruns : PhaseSemantics.RunReceiptSound)
  (hledger : Assembly.LedgerReceiptSound PhaseSemantics.phaseCap ledgerBudget)
include hbase hpref hthreshold hruns hledger

/-- Actual selected-count bound, retaining the full ledger margin. -/
theorem selectedNoLargePencilBound6811_tight :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80869 ledgerBudget := by
  have hn : Fintype.card I = 262144 := Fintype.card_fin _
  have he : 262144 - 80869 = 181275 := by decide +kernel
  have hs : Fintype.card I - 80869 = 181275 :=
    (congrArg (fun n : ℕ => n - 80869) hn).trans he
  simp only [SelectedNoLargePencilBound, hs]
  intro U seeds A selected hdegree hA hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hagreement : ∀ gamma ∈ seeds, 181275 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hnoPrime : NoLargeSelectedPencil selected seeds 131071 80869 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Assembly.selected_pair_count_le hbase hpref hthreshold hruns hledger
    (U 0) (U 1) S selected seeds ⟨hdegree,hagreement,hnoPrime⟩

/-- The scalar-list budget reserves 7753263990 challenges, leaving the exact
MCA allowance 274980720358131097 checked by the protocol module. -/
theorem selectedNoLargePencilBound6811 :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80869 MovingFiberProtocol6811.mcaBudget := by
  intro U seeds A selected hdegree hA hvalues hno
  exact (selectedNoLargePencilBound6811_tight hbase hpref hthreshold hruns hledger
    U seeds A selected hdegree hA hvalues hno).trans ledgerBudget_le_mcaBudget

theorem alignmentBound6811 :
    AffineLineAlignmentBound IRSProfile.baseCode MovingFiberProtocol6811.errors MovingFiberProtocol6811.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80869
    MovingFiberProtocol6811.mcaBudget (selectedNoLargePencilBound6811 hbase hpref hthreshold hruns hledger)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension, MovingFiberProtocol6811.errors] using h

theorem protocolClaim6811 : ProtocolClaim 6812 331243519 1073741824 :=
  MovingFiberProtocol6811.protocolClaim6811_of_alignment
    (alignmentBound6811 hbase hpref hthreshold hruns hledger)

end
end ProximityPrize.SubmissionLower.Lower80860.Closure

namespace ProximityPrize.SubmissionLower.MovingFiberCertificateCore6811
open RCN095 LocatorFactorAggregate Lower80860
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem ledgerReceipt (h : ReceiptData.Receipt) :
    Assembly.LedgerReceiptSound PhaseSemantics.phaseCap Closure.ledgerBudget := by
  constructor
  · decide +kernel
  · intro r v z hr hR hY hT
    have hh := LedgerAudit.RunsValid.sound (ReceiptData.rowContext r v)
      (ReceiptData.lookup r v).ledgerRuns 0 z (h r v hr hR hY).ledger (Nat.zero_le _) (by
        change z < 9679-(r+v)
        omega)
    simpa only [Assembly.combined,Closure.ledgerBudget,LedgerAudit.ledger,LedgerAudit.bound,
      PhaseSemantics.phaseCap,LocatorPhase6800Oracle.rawFlag,
      ReceiptData.rowContext,MovingFiberReceiptTypes6811.context,
      total,middle,Nat.mul_zero,Nat.add_zero,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

theorem protocolClaim_of_receipt (h : ReceiptData.Receipt) :
    ProximityPrize.Benchmark.ProtocolClaim 6812 331243519 1073741824 :=
  Closure.protocolClaim6811 h (ReceiptBridge.prefix_at h) (ReceiptBridge.threshold_at h)
    (ReceiptBridge.runs_at h) (ledgerReceipt h)

#print axioms protocolClaim_of_receipt
end ProximityPrize.SubmissionLower.MovingFiberCertificateCore6811
