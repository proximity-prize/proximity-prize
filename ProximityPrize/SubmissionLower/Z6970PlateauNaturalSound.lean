import ProximityPrize.SubmissionLower.Z6970PlateauNaturalModel
import ProximityPrize.SubmissionLower.Z6970PlateauNaturalBill
import ProximityPrize.SubmissionLower.Z6970PlateauNaturalSwitch

set_option autoImplicit false
namespace ExpandedPlateauNatural6970
open ExpandedPlateauSum6970 (spanLength)

theorem strip_eq (f c r : ℕ) (hf : f ≤ 500) (hr : r ≤ 2) :
    (strip f c r : ℤ) = ExpandedPlateauEnvelope6970.strip f c r := by
  by_cases empty : spanLength c f r = 0
  · simp [strip, ExpandedPlateauEnvelope6970.strip,empty]
  · simp only [strip, ExpandedPlateauEnvelope6970.strip, empty, ite_false]
    let pair := rays f c r
    change (integrate 0 (spanLength c f r) pair.1 pair.2 : ℤ) = _
    have mapped := mapped_rays f c r hf hr empty
    have m1 : toLine pair.1 = (ExpandedPlateauSum6970.lines (c:ℤ) f r).1 := congrArg Prod.fst mapped
    have m2 : pair.2.map toLine = (ExpandedPlateauSum6970.lines (c:ℤ) f r).2 := congrArg Prod.snd mapped
    rw [natural_integral bill_eq stop_eq 0 (spanLength c f r) pair.1 pair.2 (by simp [pair,rays]) (by simp [pair,rays]),m1,m2]
    rfl

theorem column_eq (f c : ℕ) (hf : f ≤ 500) :
    (column f c : ℤ) = ExpandedPlateauEnvelope6970.column f c := by
  simp only [column, ExpandedPlateauEnvelope6970.column, Nat.cast_add, strip_eq f c 0 hf (by decide),
    strip_eq f c 1 hf (by decide), strip_eq f c 2 hf (by decide)]

theorem total_eq (f start n : ℕ) (hf : f ≤ 500) :
    (columns f start n : ℤ) = ExpandedPlateauEnvelope6970.columns f start n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((columns f start n + column f (start+n) : ℕ) : ℤ) =
      ExpandedPlateauEnvelope6970.columns f start n + ExpandedPlateauEnvelope6970.column f (start+n)
    rw [Nat.cast_add, ih, column_eq f (start+n) hf]

theorem equivalent_columns (f start n : ℕ) (hf : f ≤ 500) :
    ExpandedPlateauSum6970.columnChunk f start n = (columns f start n : ℤ) :=
  (ExpandedPlateauEnvelope6970.equivalent_columns f start n).trans (total_eq f start n hf).symm

end ExpandedPlateauNatural6970
