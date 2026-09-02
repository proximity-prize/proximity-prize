/-
NUMERIC CHARACTERISTIC GATES — C2 / 6786 ROW.

Caps: slope `s + 2 ≤ 24`, ys `b + s + 3 ≤ 113`, total `a + b + s + 3 ≤ 3808`,
prime `2130706433`, errors `80614`.

The C2 provider runs on the REDUCED first tail, whose mixed-degree gate carries
`2 * (s + 2) - 2` where the sharp one carries `2 * (s + 2) - 1`; both shapes are
provided so the same file serves the provider and the identity branch.
-/
import ProximityPrize.SubmissionLower.LocatorHybridCellsC1

namespace ProximityPrize.SubmissionLower.LocatorHybridGatesC2
open RCN095 LocatorHybridCells LocatorHybridCellsC1

/-- Provider gate for the REDUCED first tail (`2 * (s + 2) - 2`). -/
theorem reduced_mixed_gateC2 (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 24) (hY : b + s + 3 ≤ 113)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (RCN327.w + 1)) <
        2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 224 := by omega
  have hs : 2 * (s + 2) - 2 ≤ 46 := by omega
  have hfS : flag.all ≤ 24 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 113 := hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 224) * 24 + 113 * (46 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433 := by norm_num [RCN327.w]

/-- Provider gate for the SHARP first tail, kept for the C1 comparison. -/
theorem sharp_mixed_gateC2 (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 24) (hY : b + s + 3 ≤ 113)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * (RCN327.w + 1)) <
        2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 224 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 47 := by omega
  have hfS : flag.all ≤ 24 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 113 := hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 224) * 24 + 113 * (47 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433 := by norm_num [RCN327.w]

theorem product_gateC2 (a b s : ℕ) (flag : FlagDegree)
    (hT : a + b + s + 3 ≤ 3808)
    (hft : flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < 2130706433 := by
  have h1 : flag.zOnly + flag.yz + flag.all ≤ 3808 := hft.trans hT
  have h2 : a + b + s + 4 ≤ 3809 := by omega
  calc
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) ≤ 2 * 3808 * 3809 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
    _ < 2130706433 := by norm_num

/-- The single coordinate gate at `errors = 80614`. -/
theorem rational_gateC2 (t y r : ℕ) (hb : r + 2 ≤ y) :
    80614 + 1 ≤ (cellHybridCoordinateC1 t y r).yz :=
  hybridC1Gate_of_le t y r 80614 hb (by norm_num)

theorem flag_characteristicC2 (a b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 24) (hY : b + s + 3 ≤ 113) (hT : a + b + s + 3 ≤ 3808)
    (hflag : flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433 := by
  omega

/-- `LocatorFixedStage.identity_mixed_gate` at the 6786 caps (uses `w`, not `w+1`). -/
theorem identity_mixed_gateC2 (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 24) (hY : b + s + 3 ≤ 113)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + RCN327.w * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * RCN327.w) < 2130706433 := by
  have hy : 2 * (b + s + 3) - 2 ≤ 224 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 47 := by omega
  have hfS : flag.all ≤ 24 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 113 := hfy.trans hY
  calc
    _ ≤ (1 + RCN327.w * 224) * 24 + 113 * (47 * RCN327.w) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left RCN327.w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right RCN327.w hs))
    _ < 2130706433 := by norm_num [RCN327.w]

end ProximityPrize.SubmissionLower.LocatorHybridGatesC2
