import ProximityPrize.SubmissionLower.LowerGeometry
namespace ProximityPrize.SubmissionLower.MovingFiberSingleCore6815
set_option autoImplicit false

structure Carrier where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  deriving DecidableEq, Repr

structure Run where
  stop : ℕ
  who : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.MovingFiberSingleCore6815

namespace ProximityPrize.SubmissionLower.Lower80899.PhaseRows
set_option autoImplicit false

structure PhaseRun where
  stop : ℕ
  witness : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80899.PhaseRows

namespace ProximityPrize.SubmissionLower.Lower80899.LedgerAudit
set_option autoImplicit false

structure LedgerRun where
  stop : ℕ
  witness : ℕ
  mode : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80899.LedgerAudit

namespace ProximityPrize.SubmissionLower.Lower80899.CompressedBand
set_option autoImplicit false

structure Run where
  stop : ℕ
  code : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80899.CompressedBand

namespace ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814
open LocatorPhase6800Oracle Lower80899.PhaseRows
set_option autoImplicit false

structure BaseRun where
  stop : Nat
  sheet : Nat
  deriving DecidableEq, Repr

structure Numbers where
  carrier : MovingFiberSingleCore6815.Carrier
  base : BaseRow
  threshold : Array Nat
  prefixValues : Array Nat
  singletons : List MovingFiberSingleCore6815.Run
  baseChoices : List BaseRun
  phaseRuns : Array (List PhaseRun)
  ledgerRuns : List Lower80899.LedgerAudit.LedgerRun
  thresholdRuns : Array (List Lower80899.CompressedBand.Run)

end ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814
