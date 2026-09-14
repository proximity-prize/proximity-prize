import ProximityPrize.SubmissionLower.HigherAffineCheckedR346810
namespace ProximityPrize.SubmissionLower.HigherFiniteCertificate6810
open HigherAffineFiniteChecks6810 HigherAffineRowsChecked6810 Lower80850
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem single_all (r v : ℕ) (hr : 1≤r) (hR : r≤34) (hY : r+v≤156) : SingleAt r v := by
  interval_cases r
  · exact single_1 v (List.mem_range.mpr (by omega))
  · exact single_2 v (List.mem_range.mpr (by omega))
  · exact single_3 v (List.mem_range.mpr (by omega))
  · exact single_4 v (List.mem_range.mpr (by omega))
  · exact single_5 v (List.mem_range.mpr (by omega))
  · exact single_6 v (List.mem_range.mpr (by omega))
  · exact single_7 v (List.mem_range.mpr (by omega))
  · exact single_8 v (List.mem_range.mpr (by omega))
  · exact single_9 v (List.mem_range.mpr (by omega))
  · exact single_10 v (List.mem_range.mpr (by omega))
  · exact single_11 v (List.mem_range.mpr (by omega))
  · exact single_12 v (List.mem_range.mpr (by omega))
  · exact single_13 v (List.mem_range.mpr (by omega))
  · exact single_14 v (List.mem_range.mpr (by omega))
  · exact single_15 v (List.mem_range.mpr (by omega))
  · exact single_16 v (List.mem_range.mpr (by omega))
  · exact single_17 v (List.mem_range.mpr (by omega))
  · exact single_18 v (List.mem_range.mpr (by omega))
  · exact single_19 v (List.mem_range.mpr (by omega))
  · exact single_20 v (List.mem_range.mpr (by omega))
  · exact single_21 v (List.mem_range.mpr (by omega))
  · exact single_22 v (List.mem_range.mpr (by omega))
  · exact single_23 v (List.mem_range.mpr (by omega))
  · exact single_24 v (List.mem_range.mpr (by omega))
  · exact single_25 v (List.mem_range.mpr (by omega))
  · exact single_26 v (List.mem_range.mpr (by omega))
  · exact single_27 v (List.mem_range.mpr (by omega))
  · exact single_28 v (List.mem_range.mpr (by omega))
  · exact single_29 v (List.mem_range.mpr (by omega))
  · exact single_30 v (List.mem_range.mpr (by omega))
  · exact single_31 v (List.mem_range.mpr (by omega))
  · exact single_32 v (List.mem_range.mpr (by omega))
  · exact single_33 v (List.mem_range.mpr (by omega))
  · exact single_34 v (List.mem_range.mpr (by omega))

theorem phase_all (r v : ℕ) (hr : 1≤r) (hR : r≤34) (hY : r+v≤156) : PhaseAt r v := by
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
  · exact phase_32 v (List.mem_range.mpr (by omega))
  · exact phase_33 v (List.mem_range.mpr (by omega))
  · exact phase_34 v (List.mem_range.mpr (by omega))

theorem threshold_all (r v : ℕ) (hr : 1≤r) (hR : r≤34) (hY : r+v≤156) : HigherAffineFiniteChecks6810.ThresholdAt r v := by
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
  · exact threshold_32 v (List.mem_range.mpr (by omega))
  · exact threshold_33 v (List.mem_range.mpr (by omega))
  · exact threshold_34 v (List.mem_range.mpr (by omega))

theorem ledger_all (r v : ℕ) (hr : 1≤r) (hR : r≤34) (hY : r+v≤156) : LedgerAt r v := by
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
  · exact ledger_32 v (List.mem_range.mpr (by omega))
  · exact ledger_33 v (List.mem_range.mpr (by omega))
  · exact ledger_34 v (List.mem_range.mpr (by omega))

theorem baseReceipt : HigherAffineRateBridge6810.Receipt :=
  ⟨fun r v hr hR hY => (single_all r v hr hR hY).1,
    fun r v hr hR hY => (single_all r v hr hR hY).2⟩

theorem prefixReceipt : PhaseSemantics.PrefixReceiptSound := by
  intro r v hr hR hY
  exact (phase_all r v hr hR hY).1

theorem runsReceipt : PhaseSemantics.RunReceiptSound := by
  intro r v hr hR hY
  exact (phase_all r v hr hR hY).2

theorem thresholdReceipt : PhaseSemantics.ThresholdReceiptSound := by
  intro r v hr hR hY j hj
  exact CompressedData.zowh r v j (threshold_all r v hr hR hY j hj)

theorem all_state_ledger (r v z : ℕ) (hr : 1≤r) (hR : r≤34)
    (hY : r+v≤156) (hT : r+v+z≤8865) :
    LedgerAudit.ledger (PhaseData.rowContext r v) z ≤ LedgerAudit.bound := by
  exact LedgerAudit.RunsValid.sound (PhaseData.rowContext r v) (LedgerData.lookup r v)
    0 z (ledger_all r v hr hR hY) (Nat.zero_le _) (by change z < 8866-(r+v); omega)

theorem all_state_budget (r v z : ℕ) (hr : 1≤r) (hR : r≤34)
    (hY : r+v≤156) (hT : r+v+z≤8865) :
    LedgerAudit.ledger (PhaseData.rowContext r v) z ≤ 274980720907353624 :=
  (all_state_ledger r v z hr hR hY hT).trans (by decide +kernel)

#print axioms all_state_budget
end ProximityPrize.SubmissionLower.HigherFiniteCertificate6810
