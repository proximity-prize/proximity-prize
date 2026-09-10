import ProximityPrize.SubmissionLower.BoundaryTailLedgerChecked06

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
open Lower80801.LedgerData Lower80801.LedgerAudit Lower80801.PhaseData
open ProximityPrize.SubmissionLower.Lower80801.Assembly
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (rawFlag)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem checked (r v z : ℕ) (hr : 1 ≤ r) (hr30 : r ≤ 30)
    (hy : r+v ≤ 139) (ht : r+v+z ≤ 7199) :
    ledger (rowContext r v) z ≤ bound := by
  have hv : v ∈ List.range (140-r) := List.mem_range.mpr (by omega)
  have hc : RunsValid (rowContext r v) 0 (lookup r v) := by
    interval_cases r <;> first
      | exact checkedR1 v hv
      | exact checkedR2 v hv
      | exact checkedR3 v hv
      | exact checkedR4 v hv
      | exact checkedR5 v hv
      | exact checkedR6 v hv
      | exact checkedR7 v hv
      | exact checkedR8 v hv
      | exact checkedR9 v hv
      | exact checkedR10 v hv
      | exact checkedR11 v hv
      | exact checkedR12 v hv
      | exact checkedR13 v hv
      | exact checkedR14 v hv
      | exact checkedR15 v hv
      | exact checkedR16 v hv
      | exact checkedR17 v hv
      | exact checkedR18 v hv
      | exact checkedR19 v hv
      | exact checkedR20 v hv
      | exact checkedR21 v hv
      | exact checkedR22 v hv
      | exact checkedR23 v hv
      | exact checkedR24 v hv
      | exact checkedR25 v hv
      | exact checkedR26 v hv
      | exact checkedR27 v hv
      | exact checkedR28 v hv
      | exact checkedR29 v hv
      | exact checkedR30 v hv
  exact RunsValid.sound _ _ 0 z hc (Nat.zero_le _) (by dsimp [rowContext]; omega)

theorem ledgerReceipt : Assembly.LedgerReceiptSound 253080253061200723 := by
  constructor
  · decide +kernel
  · intro r v z hr hr30 hy ht
    have h := checked r v z hr hr30 hy ht
    simpa only [Assembly.LedgerReceiptSound, Assembly.combined, LedgerAudit.ledger, LedgerAudit.bound,
      PhaseSemantics.phaseCap, PhaseData.rowContext, middle, total, rawFlag,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
end ProximityPrize.SubmissionLower.Lower80801.LedgerChecked
