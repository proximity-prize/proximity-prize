import ProximityPrize.SubmissionLower.AnchorSpace82170
import ProximityPrize.SubmissionLower.AnchorReceipts

set_option maxRecDepth 28000
set_option maxHeartbeats 3000000
set_option Elab.async false

namespace AnchorCuts82170
open K1_13 K1_13_1_1 SoundnessAnchor AnchorSpace82170

/-- One reduction in block rank, in addition to the earlier five-factor saving. -/
structure Cut (s : ℕ) where
  index : ℕ
  gain : ℕ
  powers : Powers
  checked : boundAt (min s (cap s)) s (offset index) powers + gain + improvement s index ≤
    blockBudget s (offset index)

open private fastBlock_eq from ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic

def certify (s r gain : ℕ) (v : Powers)
    (h : boundAt (min s (cap s)) s (offset r) v + gain + improvement s r ≤ fastBlock s r) :
    Cut s := ⟨r, gain, v, (fastBlock_eq s r) ▸ h⟩

end AnchorCuts82170
