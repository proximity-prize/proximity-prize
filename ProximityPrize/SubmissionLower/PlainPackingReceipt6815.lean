import ProximityPrize.SubmissionLower.PackingFast6815
import ProximityPrize.SubmissionLower.PlainReceiptData6815
namespace ProximityPrize.SubmissionLower.PlainPackingReceipt6815
def Packed (a b c : Array ℕ) : Prop :=
  PackingCheck6815.convolution a.toList b.toList c.toList=true
theorem cert {a b c : Array ℕ}
    (h : PackingCheck6815.convolutionS a.toList b.toList c.toList=true) : Packed a b c :=
  PackingCheck6815.convolutionS_sound _ _ _ h
end ProximityPrize.SubmissionLower.PlainPackingReceipt6815
