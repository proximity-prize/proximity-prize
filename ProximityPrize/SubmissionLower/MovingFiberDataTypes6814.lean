import ProximityPrize.SubmissionLower.LowerGeometry

/-! The row data types of the moving-fiber receipts.

They live apart from the checkers so that the generated row tables
(`MovingFiberContextData6814R*`) import `LowerGeometry` only and elaborate while the checker
modules build, instead of after them. Names and namespaces are those of the modules that
use them. -/

namespace ProximityPrize.SubmissionLower.MovingFiberSingleCore6814
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

end ProximityPrize.SubmissionLower.MovingFiberSingleCore6814

namespace ProximityPrize.SubmissionLower.Lower80889.PhaseRows
set_option autoImplicit false

structure PhaseRun where
  stop : ℕ
  witness : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80889.PhaseRows

namespace ProximityPrize.SubmissionLower.Lower80889.LedgerAudit
set_option autoImplicit false

structure LedgerRun where
  stop : ℕ
  witness : ℕ
  mode : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80889.LedgerAudit

namespace ProximityPrize.SubmissionLower.Lower80889.CompressedBand
set_option autoImplicit false

structure Run where
  stop : ℕ
  code : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80889.CompressedBand

namespace ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814
open LocatorPhase6800Oracle Lower80889.PhaseRows
set_option autoImplicit false

structure BaseRun where
  stop : Nat
  sheet : Nat
  deriving DecidableEq, Repr

structure Numbers where
  carrier : MovingFiberSingleCore6814.Carrier
  base : BaseRow
  threshold : Array Nat
  prefixValues : Array Nat
  singletons : List MovingFiberSingleCore6814.Run
  baseChoices : List BaseRun
  phaseRuns : Array (List PhaseRun)
  ledgerRuns : List Lower80889.LedgerAudit.LedgerRun
  thresholdRuns : Array (List Lower80889.CompressedBand.Run)

def defaults : Numbers := ⟨⟨0,0,0,0,0⟩,⟨0,0,0,0,0,[]⟩,#[],#[],[],[],#[],[],#[]⟩

end ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814
