-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229MomentAppend.lean.
import ProximityPrize.SubmissionLower.Peer653High53Moments4

set_option autoImplicit false

namespace Peer653High53BankProof

open P1_7_1_3 (blockEstimate block_append)

/-- Join adjacent checked blocks and add their certified totals. -/
theorem append_checked {B J start a b x y : ℕ}
    (left : blockEstimate B J start a = x)
    (right : blockEstimate B J (start + a) b = y) :
    blockEstimate B J start (a + b) = x + y :=
  block_append left right rfl rfl rfl

end Peer653High53BankProof
