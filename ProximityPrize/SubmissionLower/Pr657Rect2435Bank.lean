import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData
import ProximityPrize.SubmissionLower.HighCore82258BankProof

namespace Pr657Rect2435Receipts

theorem terminal_ok : P3_7_1.BankOK terminal := by
  have h:=HighCore82258BankProof.listed_ok .h2367 (HighCore82258.terminal .h2367) (Or.inl rfl)
  exact ⟨h.nodes,h.moment⟩

end Pr657Rect2435Receipts
