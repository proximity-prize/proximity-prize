/-
NUMERIC CHARACTERISTIC GATES — C2 / 6787 ROW.

Caps: slope `s + 2 ≤ 23`, ys `b + s + 3 ≤ 110`, total `a + b + s + 3 ≤ 3922`,
prime `2130706433`, errors `80624`.

The C2 provider runs on the REDUCED first tail, whose mixed-degree gate carries
`2 * (s + 2) - 2` where the sharp one carries `2 * (s + 2) - 1`; both shapes are
provided so the same file serves the provider and the identity branch.
-/
import ProximityPrize.SubmissionLower.LocatorHybridCellsC1

namespace ProximityPrize.SubmissionLower.LocatorHybridGatesC2
open RCN095 LocatorHybridCells LocatorHybridCellsC1

/-- Provider gate for the REDUCED first tail (`2 * (s + 2) - 2`). -/
theorem reduced_mixed_gateC2 (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 23) (hY : b + s + 3 ≤ 110)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (RCN327.w + 1)) <
        2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 218 := by omega
  have hs : 2 * (s + 2) - 2 ≤ 44 := by omega
  have hfS : flag.all ≤ 23 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 110 := hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 218) * 23 + 110 * (44 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433 := by norm_num [RCN327.w]

/-- Provider gate for the SHARP first tail, kept for the C1 comparison. -/
theorem sharp_mixed_gateC2 (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 23) (hY : b + s + 3 ≤ 110)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * (RCN327.w + 1)) <
        2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 218 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 45 := by omega
  have hfS : flag.all ≤ 23 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 110 := hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 218) * 23 + 110 * (45 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433 := by norm_num [RCN327.w]

theorem product_gateC2 (a b s : ℕ) (flag : FlagDegree)
    (hT : a + b + s + 3 ≤ 3922)
    (hft : flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < 2130706433 := by
  have h1 : flag.zOnly + flag.yz + flag.all ≤ 3922 := hft.trans hT
  have h2 : a + b + s + 4 ≤ 3923 := by omega
  calc
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) ≤ 2 * 3922 * 3923 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
    _ < 2130706433 := by norm_num

/-- The single coordinate gate at `errors = 80624`. -/
theorem rational_gateC2 (t y r : ℕ) (hb : r + 2 ≤ y) :
    80624 + 1 ≤ (cellHybridCoordinateC1 t y r).yz :=
  hybridC1Gate_of_le t y r 80624 hb (by norm_num)

theorem flag_characteristicC2 (a b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 23) (hY : b + s + 3 ≤ 110) (hT : a + b + s + 3 ≤ 3922)
    (hflag : flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433 := by
  omega

/-- `LocatorFixedStage.identity_mixed_gate` at the 6787 caps (uses `w`, not `w+1`). -/
theorem identity_mixed_gateC2 (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 23) (hY : b + s + 3 ≤ 110)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + RCN327.w * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * RCN327.w) < 2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 218 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 45 := by omega
  have hfS : flag.all ≤ 23 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 110 := hfy.trans hY
  calc
    _ ≤ (1 + RCN327.w * 218) * 23 + 110 * (45 * RCN327.w) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left RCN327.w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right RCN327.w hs))
    _ < 2130706433 := by norm_num [RCN327.w]

end ProximityPrize.SubmissionLower.LocatorHybridGatesC2
