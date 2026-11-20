import ProximityPrize.SubmissionLower.PoleDebitDefs
import ProximityPrize.SubmissionLower.CertifiedDebit

namespace BankDebit
open K1 K1_14 K1_14_1
open scoped BigOperators

theorem floor (h : ℕ) (lo : 2442 ≤ h) (hi : h ≤ 32970)
    (D : PoleData h) (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ)
    (hw : rawWidthCond h s W) (hB : 4 ≤ s.B) (hU : s.B ≤ s.U) :
    rawVolumeAt h s W ≤ debit h s +
      ∑ t ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word s t) := by
  have hb := CertifiedDebit.source_with_receipt h lo hi D Crt word s W hw _
    (FourGrid.gridCoefficient_saving hB hU)
  simpa only [debit,extra,poleSeedDebit,Nat.mul_sub,Nat.mul_assoc] using hb

/-- The pole rank part also applies outside the older numerical interface. -/
theorem contacted_rank (h : ℕ) (hh : 0 < h) (hp : h < K1.p)
    (D : PoleData h) (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ)
    (hB : 4 ≤ s.B) (hU : s.B ≤ s.U) :
    Module.finrank L (contacted h word s W) ≤
      poleCredit h s + (2*h)*extra s + Module.finrank L (complete Crt word s W) := by
  have orig := StructuredSource.physical_to_complete h hh hp D Crt word s W
  have charge := CertifiedDebit.charge_comparison s h _ (FourGrid.gridCoefficient_saving hB hU)
  have out := orig.trans (Nat.add_le_add_right charge _)
  simpa only [extra,poleSeedDebit,Nat.mul_sub,Nat.mul_assoc] using out
end BankDebit
