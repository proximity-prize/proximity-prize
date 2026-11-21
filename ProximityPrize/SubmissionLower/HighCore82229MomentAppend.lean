import ProximityPrize.SubmissionLower.HighCore82229Moments4

set_option autoImplicit false

namespace HighCore82229BankProof

open P1_7_1_3 (blockEstimate block_append)

/-- Join adjacent checked blocks and add their certified totals. -/
theorem append_checked {B J start a b x y : ℕ}
    (left : blockEstimate B J start a = x)
    (right : blockEstimate B J (start + a) b = y) :
    blockEstimate B J start (a + b) = x + y :=
  block_append left right rfl rfl rfl

end HighCore82229BankProof
