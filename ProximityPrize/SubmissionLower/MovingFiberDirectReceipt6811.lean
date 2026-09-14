import ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6811

namespace ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6811
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-- Every numerical condition for one actual row, before lookup transport. -/
structure DirectAt (r v : Nat) (row parent prior : Numbers) : Prop where
  single : SingleValid r v row
  base : BaseValid row.base r v (9276-r-v) 0 row.baseChoices
  threshold : ThresholdsValid r v row
  phases : Lower80860.PhaseRows.RowRunsValid (context r v row parent) row.phaseRuns
  ledger : Lower80860.LedgerAudit.RunsValid (context r v row parent) 0 row.ledgerRuns
  prefixR : ∀ j : Fin 10, (parent.prefixValues[j.val]?).getD 0 ≤ (row.prefixValues[j.val]?).getD 0
  prefixV : 1≤v → ∀ j : Fin 10, (prior.prefixValues[j.val]?).getD 0 ≤ (row.prefixValues[j.val]?).getD 0

def DirectChecks (r v : Nat) (row parent prior : Numbers) : Prop :=
  SingleValid r v row ∧ BaseValid row.base r v (9276-r-v) 0 row.baseChoices ∧
  ThresholdsValid r v row ∧ Lower80860.PhaseRows.RowRunsValid (context r v row parent) row.phaseRuns ∧
  Lower80860.LedgerAudit.RunsValid (context r v row parent) 0 row.ledgerRuns ∧
  (∀ j : Fin 10, (parent.prefixValues[j.val]?).getD 0 ≤ (row.prefixValues[j.val]?).getD 0) ∧
  (1≤v → ∀ j : Fin 10, (prior.prefixValues[j.val]?).getD 0 ≤ (row.prefixValues[j.val]?).getD 0)
instance (r v : Nat) (row parent prior : Numbers) : Decidable (DirectChecks r v row parent prior) := by
  unfold DirectChecks; infer_instance

theorem DirectAt.of_checks {r v : Nat} {row parent prior : Numbers}
    (h : DirectChecks r v row parent prior) : DirectAt r v row parent prior :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

end ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6811
