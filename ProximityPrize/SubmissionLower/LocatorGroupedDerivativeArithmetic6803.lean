import ProximityPrize.SubmissionLower.PackedLegacy

/-! Arithmetic adapters for turning a scaled grouped incidence bound into a
cardinality allowance. -/

namespace ProximityPrize.SubmissionLower.LocatorGroupedDerivativeArithmetic6803

open RCN260

set_option autoImplicit false

/-- A grouped incidence term has the ordinary regular numerator plus one
extra proper-cut charge already multiplied by the agreement gap.  Division
therefore adds that charge exactly, with no rounding loss. -/
theorem count_le_regularCountCap_add
    (P : UnequalParameters) (count extra : ℕ)
    (hgap : 0 < P.gap)
    (hscaled : count * P.gap ≤
      P.regularNumerator + P.gap * extra) :
    count ≤ P.regularCountCap + extra := by
  rw [UnequalParameters.regularCountCap]
  calc
    count = count * P.gap / P.gap := by
      simpa [Nat.mul_comm] using (Nat.mul_div_right count hgap).symm
    _ ≤ (P.regularNumerator + P.gap * extra) / P.gap :=
      Nat.div_le_div_right hscaled
    _ = P.regularNumerator / P.gap + extra := by
      exact Nat.add_mul_div_left P.regularNumerator extra hgap

end ProximityPrize.SubmissionLower.LocatorGroupedDerivativeArithmetic6803
