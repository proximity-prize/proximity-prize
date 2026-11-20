import ProximityPrize.SubmissionLower.FourGrid
import ProximityPrize.SubmissionLower.Fast065

namespace BankDebit
open K1_14 K1_14_1

/-- Scalar debit per pole after the common raw-volume credit. -/
def extra (s : Shape) : ℕ :=
  (s.U+1)*shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q)) -
    (s.U-s.B+1)*FourGrid.gridCoefficient s.B s.J

def debit (h : ℕ) (s : Shape) : ℕ := physicalDebit s + (2*h)*extra s

theorem debit_le (h : ℕ) (s : Shape) : debit h s ≤ sourceDebit h s := by
  unfold debit sourceDebit physicalDebit extra
  simpa only [Nat.mul_assoc] using
    (Nat.add_le_add_left (Nat.mul_le_mul_left (2*h) (Nat.sub_le
      ((s.U+1)*shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q)))
      ((s.U-s.B+1)*FourGrid.gridCoefficient s.B s.J)))
      (triangle s.U * 262144 * shapeSum s (fun q i => s.m + min q s.J - (q+2*i))))

end BankDebit
