import ProximityPrize.SubmissionLower.LocatorHybridCellsC1

/-!
# C2 hybrid characteristic gates at agreement 181363

These are the numeric gates from the 68.02 C2 hybrid argument with the
retuned narrow box `(total, middle, slope) = (6676, 135, 29)` and error cap
`80781`.  Keeping them in a separate module prevents the new proof from
silently inheriting the old agreement constants.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridGatesC26803

open RCN095 LocatorHybridCells LocatorHybridCellsC1

set_option autoImplicit false

theorem reduced_mixed_gate (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 29) (hY : b + s + 3 ≤ 135)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (RCN327.w + 1)) <
        2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 268 := by omega
  have hs : 2 * (s + 2) - 2 ≤ 56 := by omega
  have hfS : flag.all ≤ 29 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 135 := hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 268) * 29 +
        135 * (56 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left
            (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY
          (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433 := by norm_num [RCN327.w]

theorem sharp_mixed_gate (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 29) (hY : b + s + 3 ≤ 135)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * (RCN327.w + 1)) <
        2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 268 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 57 := by omega
  have hfS : flag.all ≤ 29 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 135 := hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 268) * 29 +
        135 * (57 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left
            (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY
          (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433 := by norm_num [RCN327.w]

theorem product_gate (a b s : ℕ) (flag : FlagDegree)
    (hT : a + b + s + 3 ≤ 6676)
    (hft : flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) <
      2130706433 := by
  have h1 : flag.zOnly + flag.yz + flag.all ≤ 6676 := hft.trans hT
  have h2 : a + b + s + 4 ≤ 6677 := by omega
  calc
    _ ≤ 2 * 6676 * 6677 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
    _ < 2130706433 := by norm_num

theorem rational_gate (t y r : ℕ) (hb : r + 2 ≤ y) :
    80781 + 1 ≤ (cellHybridCoordinateC1 t y r).yz :=
  hybridC1Gate_of_le t y r 80781 hb (by norm_num)

theorem flag_characteristic (a b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 29) (hY : b + s + 3 ≤ 135)
    (hT : a + b + s + 3 ≤ 6676)
    (hflag : flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433 := by
  omega

theorem identity_mixed_gate (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 29) (hY : b + s + 3 ≤ 135)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + RCN327.w * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * RCN327.w) <
        2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 268 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 57 := by omega
  have hfS : flag.all ≤ 29 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 135 := hfy.trans hY
  calc
    _ ≤ (1 + RCN327.w * 268) * 29 + 135 * (57 * RCN327.w) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left RCN327.w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right RCN327.w hs))
    _ < 2130706433 := by norm_num [RCN327.w]

end ProximityPrize.SubmissionLower.LocatorHybridGatesC26803
