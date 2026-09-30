import ProximityPrize.SubmissionLower.FinalCurves6815
namespace ProximityPrize.SubmissionLower.LedgerCompact6815
open FinalCurves6815
set_option autoImplicit false

def aux (slopes : Array ℕ) : ℕ → ℕ → List Piece
  | 0,_ => []
  | n+1,c =>
    let digits := c/4194304%32
    let rest := c/134217728
    ⟨c%16384,rest%(16^digits),(slopes[c/16384%256]?).getD 0⟩ :: aux slopes n (rest/(16^digits))
def decode (slopes : Array ℕ) (code : ℕ) : List Piece := aux slopes (code%256) (code/256)

end ProximityPrize.SubmissionLower.LedgerCompact6815
