import ProximityPrize.SubmissionLower.BoundaryTailCheckedR316807
import ProximityPrize.SubmissionLower.BoundaryTailClosure6807

namespace ProximityPrize.SubmissionLower.BoundaryTailCertificate6807
open RCN095 LocatorFactorAggregate
open BoundaryTailFiniteChecks6807 BoundaryTailRowsChecked6807
open BoundaryTailBaseChecksCore6807 BoundaryTailBaseChecksData6807 BoundaryTailBaseFast6807
open Lower80820
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem geometry_all (r v : ℕ) (hr : 1 ≤ r) (hR : r ≤ 31) (hY : r+v ≤ 146) : GeometryAt r v := by
  interval_cases r
  · exact geometry_1 v (List.mem_range.mpr (by omega))
  · exact geometry_2 v (List.mem_range.mpr (by omega))
  · exact geometry_3 v (List.mem_range.mpr (by omega))
  · exact geometry_4 v (List.mem_range.mpr (by omega))
  · exact geometry_5 v (List.mem_range.mpr (by omega))
  · exact geometry_6 v (List.mem_range.mpr (by omega))
  · exact geometry_7 v (List.mem_range.mpr (by omega))
  · exact geometry_8 v (List.mem_range.mpr (by omega))
  · exact geometry_9 v (List.mem_range.mpr (by omega))
  · exact geometry_10 v (List.mem_range.mpr (by omega))
  · exact geometry_11 v (List.mem_range.mpr (by omega))
  · exact geometry_12 v (List.mem_range.mpr (by omega))
  · exact geometry_13 v (List.mem_range.mpr (by omega))
  · exact geometry_14 v (List.mem_range.mpr (by omega))
  · exact geometry_15 v (List.mem_range.mpr (by omega))
  · exact geometry_16 v (List.mem_range.mpr (by omega))
  · exact geometry_17 v (List.mem_range.mpr (by omega))
  · exact geometry_18 v (List.mem_range.mpr (by omega))
  · exact geometry_19 v (List.mem_range.mpr (by omega))
  · exact geometry_20 v (List.mem_range.mpr (by omega))
  · exact geometry_21 v (List.mem_range.mpr (by omega))
  · exact geometry_22 v (List.mem_range.mpr (by omega))
  · exact geometry_23 v (List.mem_range.mpr (by omega))
  · exact geometry_24 v (List.mem_range.mpr (by omega))
  · exact geometry_25 v (List.mem_range.mpr (by omega))
  · exact geometry_26 v (List.mem_range.mpr (by omega))
  · exact geometry_27 v (List.mem_range.mpr (by omega))
  · exact geometry_28 v (List.mem_range.mpr (by omega))
  · exact geometry_29 v (List.mem_range.mpr (by omega))
  · exact geometry_30 v (List.mem_range.mpr (by omega))
  · exact geometry_31 v (List.mem_range.mpr (by omega))

theorem strict_all (r v : ℕ) (hr : 1 ≤ r) (hR : r ≤ 31) (hY : r+v ≤ 146) : BoundaryTailFiniteChecks6807.StrictAt r v := by
  interval_cases r
  · exact strict_1 v (List.mem_range.mpr (by omega))
  · exact strict_2 v (List.mem_range.mpr (by omega))
  · exact strict_3 v (List.mem_range.mpr (by omega))
  · exact strict_4 v (List.mem_range.mpr (by omega))
  · exact strict_5 v (List.mem_range.mpr (by omega))
  · exact strict_6 v (List.mem_range.mpr (by omega))
  · exact strict_7 v (List.mem_range.mpr (by omega))
  · exact strict_8 v (List.mem_range.mpr (by omega))
  · exact strict_9 v (List.mem_range.mpr (by omega))
  · exact strict_10 v (List.mem_range.mpr (by omega))
  · exact strict_11 v (List.mem_range.mpr (by omega))
  · exact strict_12 v (List.mem_range.mpr (by omega))
  · exact strict_13 v (List.mem_range.mpr (by omega))
  · exact strict_14 v (List.mem_range.mpr (by omega))
  · exact strict_15 v (List.mem_range.mpr (by omega))
  · exact strict_16 v (List.mem_range.mpr (by omega))
  · exact strict_17 v (List.mem_range.mpr (by omega))
  · exact strict_18 v (List.mem_range.mpr (by omega))
  · exact strict_19 v (List.mem_range.mpr (by omega))
  · exact strict_20 v (List.mem_range.mpr (by omega))
  · exact strict_21 v (List.mem_range.mpr (by omega))
  · exact strict_22 v (List.mem_range.mpr (by omega))
  · exact strict_23 v (List.mem_range.mpr (by omega))
  · exact strict_24 v (List.mem_range.mpr (by omega))
  · exact strict_25 v (List.mem_range.mpr (by omega))
  · exact strict_26 v (List.mem_range.mpr (by omega))
  · exact strict_27 v (List.mem_range.mpr (by omega))
  · exact strict_28 v (List.mem_range.mpr (by omega))
  · exact strict_29 v (List.mem_range.mpr (by omega))
  · exact strict_30 v (List.mem_range.mpr (by omega))
  · exact strict_31 v (List.mem_range.mpr (by omega))

theorem phase_all (r v : ℕ) (hr : 1 ≤ r) (hR : r ≤ 31) (hY : r+v ≤ 146) : PhaseAt r v := by
  interval_cases r
  · exact phase_1 v (List.mem_range.mpr (by omega))
  · exact phase_2 v (List.mem_range.mpr (by omega))
  · exact phase_3 v (List.mem_range.mpr (by omega))
  · exact phase_4 v (List.mem_range.mpr (by omega))
  · exact phase_5 v (List.mem_range.mpr (by omega))
  · exact phase_6 v (List.mem_range.mpr (by omega))
  · exact phase_7 v (List.mem_range.mpr (by omega))
  · exact phase_8 v (List.mem_range.mpr (by omega))
  · exact phase_9 v (List.mem_range.mpr (by omega))
  · exact phase_10 v (List.mem_range.mpr (by omega))
  · exact phase_11 v (List.mem_range.mpr (by omega))
  · exact phase_12 v (List.mem_range.mpr (by omega))
  · exact phase_13 v (List.mem_range.mpr (by omega))
  · exact phase_14 v (List.mem_range.mpr (by omega))
  · exact phase_15 v (List.mem_range.mpr (by omega))
  · exact phase_16 v (List.mem_range.mpr (by omega))
  · exact phase_17 v (List.mem_range.mpr (by omega))
  · exact phase_18 v (List.mem_range.mpr (by omega))
  · exact phase_19 v (List.mem_range.mpr (by omega))
  · exact phase_20 v (List.mem_range.mpr (by omega))
  · exact phase_21 v (List.mem_range.mpr (by omega))
  · exact phase_22 v (List.mem_range.mpr (by omega))
  · exact phase_23 v (List.mem_range.mpr (by omega))
  · exact phase_24 v (List.mem_range.mpr (by omega))
  · exact phase_25 v (List.mem_range.mpr (by omega))
  · exact phase_26 v (List.mem_range.mpr (by omega))
  · exact phase_27 v (List.mem_range.mpr (by omega))
  · exact phase_28 v (List.mem_range.mpr (by omega))
  · exact phase_29 v (List.mem_range.mpr (by omega))
  · exact phase_30 v (List.mem_range.mpr (by omega))
  · exact phase_31 v (List.mem_range.mpr (by omega))

theorem threshold_all (r v : ℕ) (hr : 1 ≤ r) (hR : r ≤ 31) (hY : r+v ≤ 146) : BoundaryTailFiniteChecks6807.ThresholdAt r v := by
  interval_cases r
  · exact threshold_1 v (List.mem_range.mpr (by omega))
  · exact threshold_2 v (List.mem_range.mpr (by omega))
  · exact threshold_3 v (List.mem_range.mpr (by omega))
  · exact threshold_4 v (List.mem_range.mpr (by omega))
  · exact threshold_5 v (List.mem_range.mpr (by omega))
  · exact threshold_6 v (List.mem_range.mpr (by omega))
  · exact threshold_7 v (List.mem_range.mpr (by omega))
  · exact threshold_8 v (List.mem_range.mpr (by omega))
  · exact threshold_9 v (List.mem_range.mpr (by omega))
  · exact threshold_10 v (List.mem_range.mpr (by omega))
  · exact threshold_11 v (List.mem_range.mpr (by omega))
  · exact threshold_12 v (List.mem_range.mpr (by omega))
  · exact threshold_13 v (List.mem_range.mpr (by omega))
  · exact threshold_14 v (List.mem_range.mpr (by omega))
  · exact threshold_15 v (List.mem_range.mpr (by omega))
  · exact threshold_16 v (List.mem_range.mpr (by omega))
  · exact threshold_17 v (List.mem_range.mpr (by omega))
  · exact threshold_18 v (List.mem_range.mpr (by omega))
  · exact threshold_19 v (List.mem_range.mpr (by omega))
  · exact threshold_20 v (List.mem_range.mpr (by omega))
  · exact threshold_21 v (List.mem_range.mpr (by omega))
  · exact threshold_22 v (List.mem_range.mpr (by omega))
  · exact threshold_23 v (List.mem_range.mpr (by omega))
  · exact threshold_24 v (List.mem_range.mpr (by omega))
  · exact threshold_25 v (List.mem_range.mpr (by omega))
  · exact threshold_26 v (List.mem_range.mpr (by omega))
  · exact threshold_27 v (List.mem_range.mpr (by omega))
  · exact threshold_28 v (List.mem_range.mpr (by omega))
  · exact threshold_29 v (List.mem_range.mpr (by omega))
  · exact threshold_30 v (List.mem_range.mpr (by omega))
  · exact threshold_31 v (List.mem_range.mpr (by omega))

theorem ledger_all (r v : ℕ) (hr : 1 ≤ r) (hR : r ≤ 31) (hY : r+v ≤ 146) : LedgerAt r v := by
  interval_cases r
  · exact ledger_1 v (List.mem_range.mpr (by omega))
  · exact ledger_2 v (List.mem_range.mpr (by omega))
  · exact ledger_3 v (List.mem_range.mpr (by omega))
  · exact ledger_4 v (List.mem_range.mpr (by omega))
  · exact ledger_5 v (List.mem_range.mpr (by omega))
  · exact ledger_6 v (List.mem_range.mpr (by omega))
  · exact ledger_7 v (List.mem_range.mpr (by omega))
  · exact ledger_8 v (List.mem_range.mpr (by omega))
  · exact ledger_9 v (List.mem_range.mpr (by omega))
  · exact ledger_10 v (List.mem_range.mpr (by omega))
  · exact ledger_11 v (List.mem_range.mpr (by omega))
  · exact ledger_12 v (List.mem_range.mpr (by omega))
  · exact ledger_13 v (List.mem_range.mpr (by omega))
  · exact ledger_14 v (List.mem_range.mpr (by omega))
  · exact ledger_15 v (List.mem_range.mpr (by omega))
  · exact ledger_16 v (List.mem_range.mpr (by omega))
  · exact ledger_17 v (List.mem_range.mpr (by omega))
  · exact ledger_18 v (List.mem_range.mpr (by omega))
  · exact ledger_19 v (List.mem_range.mpr (by omega))
  · exact ledger_20 v (List.mem_range.mpr (by omega))
  · exact ledger_21 v (List.mem_range.mpr (by omega))
  · exact ledger_22 v (List.mem_range.mpr (by omega))
  · exact ledger_23 v (List.mem_range.mpr (by omega))
  · exact ledger_24 v (List.mem_range.mpr (by omega))
  · exact ledger_25 v (List.mem_range.mpr (by omega))
  · exact ledger_26 v (List.mem_range.mpr (by omega))
  · exact ledger_27 v (List.mem_range.mpr (by omega))
  · exact ledger_28 v (List.mem_range.mpr (by omega))
  · exact ledger_29 v (List.mem_range.mpr (by omega))
  · exact ledger_30 v (List.mem_range.mpr (by omega))
  · exact ledger_31 v (List.mem_range.mpr (by omega))

theorem baseReceipt : BoundaryTailBaseOracle6807.Receipt
    BoundaryTailStrictData6807.zero BoundaryTailStrictData6807.cap (PhaseSemantics.phaseCap 0) := by
  have h := receipt_of_checks carriers runs
    (fun r v hr hR hY => (geometry_all r v hr hR hY).1)
    (fun r v hr hR hY => zeroAtFast_sound r v
      (zeroAtFast_of_strict (BoundaryTailBaseFastData6807.row r v) r v
        (strict_all r v hr hR hY) (geometry_all r v hr hR hY).2.2.2))
    (fun r v hr hR hY => strictAtFast_sound (BoundaryTailBaseFastData6807.row r v) r v
      (geometry_all r v hr hR hY).2.2.1 (strict_all r v hr hR hY))
    (fun r v hr hR hY => (geometry_all r v hr hR hY).2.1)
  exact h

theorem prefixReceipt : PhaseSemantics.PrefixReceiptSound := by
  intro r v hr hR hY
  exact (phase_all r v hr hR hY).1

theorem runsReceipt : PhaseSemantics.RunReceiptSound := by
  intro r v hr hR hY
  exact (phase_all r v hr hR hY).2

theorem thresholdReceipt : PhaseSemantics.ThresholdReceiptSound := by
  intro r v hr hR hY j hj
  exact CompressedData.zowh r v j (threshold_all r v hr hR hY j hj)

private theorem ledger_transfer (a b c d e f : ℕ) (hc : c=e) (hd : d=f)
    (h : a+b+e+f+18000000000000+(1414787909621379+53378732331792) ≤ 274386827080775528) :
    a+b+c+d+18000000000000+1414787909621379+36*1482742564772 ≤ 274386827080775528 := by
  omega

theorem ledgerReceipt : Assembly.LedgerReceiptSound PhaseSemantics.phaseCap Closure.ledgerBudget := by
  constructor
  · decide +kernel
  · intro r v z hr hR hY hT
    have h := LedgerAudit.RunsValid.sound (PhaseData.rowContext r v) (LedgerData.lookup r v)
      0 z (ledger_all r v hr hR hY) (Nat.zero_le _) (by change z < 7785-(r+v); omega)
    change PhaseRows.capBefore (PhaseData.rowContext r v) 10 z +
      Initial.initialAComplement (LocatorPhase6800Oracle.rawFlag r v z) +
      r * AsymmetricChainPolynomial80820.unit (r+v) (r+v+z) r +
      (34-r) * AsymmetricChainPolynomial80820.unit (153-(r+v)) (33395-(r+v+z)) (34-r) +
      18000000000000 + (1414787909621379+53378732331792) ≤ 274386827080775528 at h
    change PhaseRows.capBefore (PhaseData.rowContext r v) 10 z +
      Initial.initialAComplement (LocatorPhase6800Oracle.rawFlag r v z) +
      r * AsymmetricChainPolynomial80820.unit (v+r) (z+v+r) r +
      (34-r) * AsymmetricChainPolynomial80820.unit (153-(v+r)) (33395-(z+v+r)) (34-r) +
      18000000000000 + 1414787909621379 + 36*1482742564772 ≤ 274386827080775528
    have hu : AsymmetricChainPolynomial80820.unit (v+r) (z+v+r) r =
        AsymmetricChainPolynomial80820.unit (r+v) (r+v+z) r :=
      congrArg₂ (fun y t => AsymmetricChainPolynomial80820.unit y t r)
        (show v+r = r+v by omega) (show z+v+r = r+v+z by omega)
    have hv : AsymmetricChainPolynomial80820.unit (153-(v+r)) (33395-(z+v+r)) (34-r) =
        AsymmetricChainPolynomial80820.unit (153-(r+v)) (33395-(r+v+z)) (34-r) :=
      congrArg₂ (fun y t => AsymmetricChainPolynomial80820.unit (153-y) (33395-t) (34-r))
        (show v+r = r+v by omega) (show z+v+r = r+v+z by omega)
    exact ledger_transfer _ _ _ _ _ _ (congrArg (fun u => r*u) hu)
      (congrArg (fun u => (34-r)*u) hv) h

theorem protocolClaim : ProximityPrize.Benchmark.ProtocolClaim 6807 10345087 33554432 :=
  Closure.protocolClaim6807 baseReceipt prefixReceipt thresholdReceipt runsReceipt ledgerReceipt

end ProximityPrize.SubmissionLower.BoundaryTailCertificate6807
