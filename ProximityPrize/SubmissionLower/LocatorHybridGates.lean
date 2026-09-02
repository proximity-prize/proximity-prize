import ProximityPrize.SubmissionLower.LocatorHybridCells

/-! Numeric characteristic gates for the hybrid provider on the fixed stage
(`s + 2 ≤ 20`, `b + s + 3 ≤ 92`, `a + b + s + 3 ≤ 3319`, prime `2130706433`). -/

namespace ProximityPrize.SubmissionLower.LocatorHybridGates
open RCN095 LocatorHybridCells

theorem sharp_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 20) (hY:b + s + 3 ≤ 92)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * (RCN327.w + 1)) < 2130706433:=by
  have hy:2 * (b + s + 3) - 2 ≤ 182:=by omega
  have hs:2 * (s + 2) - 1 ≤ 39:=by omega
  have hfS:flag.all ≤ 20:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 92:=hfy.trans hY
  calc
    _ ≤ (1 + (RCN327.w + 1) * 182) * 20 + 92 * (39 * (RCN327.w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left (RCN327.w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (RCN327.w + 1) hs))
    _ < 2130706433:=by norm_num [RCN327.w]

theorem product_gate (a b s:ℕ) (flag:FlagDegree)
    (hT:a + b + s + 3 ≤ 3319)
    (hft:flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < 2130706433:=by
  have h1:flag.zOnly + flag.yz + flag.all ≤ 3319:=hft.trans hT
  have h2:a + b + s + 4 ≤ 3320:=by omega
  calc
    2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) ≤ 2 * 3319 * 3320 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
    _ < 2130706433:=by norm_num

theorem rational_gate (t y r:ℕ) (hb:r + 2 ≤ y) :
    80565 + 1 ≤ (cellRational t y r).yz:=
  rationalGate_of_le t y r 80565 hb (by norm_num)

end ProximityPrize.SubmissionLower.LocatorHybridGates
