import ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6811

namespace ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6811
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-- Every numerical condition for one actual row, before lookup transport. -/
structure DirectAt (r v : Nat) (row parent prior : Numbers) : Prop where
  single : SingleValid r v row
  base : BaseValid row.base r v (10170-r-v) 0 row.baseChoices
  threshold : ThresholdsValid r v row
  phases : Lower80860.PhaseRows.RowRunsValid (context r v row parent) row.phaseRuns
  ledger : Lower80860.LedgerAudit.RunsValid (context r v row parent) 0 row.ledgerRuns
  prefixR : ∀ j : Fin 10, (parent.prefixValues[j.val]?).getD 0 ≤ (row.prefixValues[j.val]?).getD 0
  prefixV : 1≤v → ∀ j : Fin 10, (prior.prefixValues[j.val]?).getD 0 ≤ (row.prefixValues[j.val]?).getD 0

/-- Phases 7, 8, 9 reuse the sources of phases 3, 4, 5 (`TenPhase.sound`), and the
receipts store identical thresholds and runs for them; so only phases 0..6 are checked,
plus the six cheap equalities. -/
def ThresholdsCore (r v : Nat) (row : Numbers) : Prop :=
  ∀ j : Fin 7, ThresholdValid (Lower80860.TenPhase.sound j.val).source r v
    (Lower80860.PhaseRows.thresholdAt row.threshold j.val) ((row.thresholdRuns[j.val]?).getD [])
instance (r v : Nat) (row : Numbers) : Decidable (ThresholdsCore r v row) := by
  unfold ThresholdsCore; infer_instance

def ThresholdsDup (row : Numbers) : Prop :=
  ∀ k : Fin 3, Lower80860.PhaseRows.thresholdAt row.threshold (k.val+7) =
      Lower80860.PhaseRows.thresholdAt row.threshold (k.val+3) ∧
    (row.thresholdRuns[k.val+7]?).getD [] = (row.thresholdRuns[k.val+3]?).getD []
instance (row : Numbers) : Decidable (ThresholdsDup row) := by
  unfold ThresholdsDup; infer_instance

theorem thresholds_of_core {r v : Nat} {row : Numbers}
    (h1 : ThresholdsCore r v row) (h2 : ThresholdsDup row) : ThresholdsValid r v row := by
  intro j
  by_cases hj : j.val < 7
  · exact h1 ⟨j.val, hj⟩
  · have hk : j.val - 7 < 3 := by omega
    have hjv : j.val = (j.val - 7) + 7 := by omega
    have hs : Lower80860.TenPhase.sound j.val = Lower80860.TenPhase.sound ((j.val-7)+3) := by
      rw [hjv]
      rcases (show j.val - 7 = 0 ∨ j.val - 7 = 1 ∨ j.val - 7 = 2 by omega) with h | h | h <;>
        simp only [h] <;> rfl
    have hd := h2 ⟨j.val-7, hk⟩
    rw [hs, hjv, hd.1, hd.2]
    exact h1 ⟨(j.val-7)+3, by omega⟩

def DirectChecks (r v : Nat) (row parent prior : Numbers) : Prop :=
  SingleValid r v row ∧ BaseValid row.base r v (10170-r-v) 0 row.baseChoices ∧
  (ThresholdsDup row ∧ ThresholdsCore r v row) ∧ Lower80860.PhaseRows.RowRunsValid (context r v row parent) row.phaseRuns ∧
  Lower80860.LedgerAudit.RunsValid (context r v row parent) 0 row.ledgerRuns ∧
  (∀ j : Fin 10, (parent.prefixValues[j.val]?).getD 0 ≤ (row.prefixValues[j.val]?).getD 0) ∧
  (1≤v → ∀ j : Fin 10, (prior.prefixValues[j.val]?).getD 0 ≤ (row.prefixValues[j.val]?).getD 0)
instance (r v : Nat) (row parent prior : Numbers) : Decidable (DirectChecks r v row parent prior) := by
  unfold DirectChecks; infer_instance

theorem DirectAt.of_checks {r v : Nat} {row parent prior : Numbers}
    (h : DirectChecks r v row parent prior) : DirectAt r v row parent prior :=
  ⟨h.1,h.2.1,thresholds_of_core h.2.2.1.2 h.2.2.1.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

end ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6811
