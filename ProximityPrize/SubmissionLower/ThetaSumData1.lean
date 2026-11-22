import ProximityPrize.SubmissionLower.ThetaSumDefs
import ProximityPrize.SubmissionLower.ThetaSumData0 -- serialize candidate build

/-! Kernel-checked chunks of the theta savings sum (generated; values from the exact ledger). -/

namespace ThetaSum

theorem c1562 : chunk 1562 8 = 30311447 := by decide +kernel
theorem a1562 : chunk 1562 8 = 30311447 := c1562
theorem c1570 : chunk 1570 8 = 34850786 := by decide +kernel
theorem a1570 : chunk 1562 16 = 65162233 := by
  have h := chunk_join a1562 c1570
  exact h
theorem c1578 : chunk 1578 8 = 39910726 := by decide +kernel
theorem a1578 : chunk 1562 24 = 105072959 := by
  have h := chunk_join a1570 c1578
  exact h
theorem c1586 : chunk 1586 8 = 45529667 := by decide +kernel
theorem a1586 : chunk 1562 32 = 150602626 := by
  have h := chunk_join a1578 c1586
  exact h
theorem c1594 : chunk 1594 8 = 51747374 := by decide +kernel
theorem a1594 : chunk 1562 40 = 202350000 := by
  have h := chunk_join a1586 c1594
  exact h
theorem c1602 : chunk 1602 8 = 58463586 := by decide +kernel
theorem a1602 : chunk 1562 48 = 260813586 := by
  have h := chunk_join a1594 c1602
  exact h
theorem c1610 : chunk 1610 8 = 65644308 := by decide +kernel
theorem a1610 : chunk 1562 56 = 326457894 := by
  have h := chunk_join a1602 c1610
  exact h
theorem c1618 : chunk 1618 8 = 73526696 := by decide +kernel
theorem a1618 : chunk 1562 64 = 399984590 := by
  have h := chunk_join a1610 c1618
  exact h
theorem c1626 : chunk 1626 8 = 82156757 := by decide +kernel
theorem a1626 : chunk 1562 72 = 482141347 := by
  have h := chunk_join a1618 c1626
  exact h
theorem c1634 : chunk 1634 8 = 91574606 := by decide +kernel
theorem a1634 : chunk 1562 80 = 573715953 := by
  have h := chunk_join a1626 c1634
  exact h
theorem c1642 : chunk 1642 8 = 101538979 := by decide +kernel
theorem a1642 : chunk 1562 88 = 675254932 := by
  have h := chunk_join a1634 c1642
  exact h
theorem c1650 : chunk 1650 8 = 112213158 := by decide +kernel
theorem a1650 : chunk 1562 96 = 787468090 := by
  have h := chunk_join a1642 c1650
  exact h
theorem c1658 : chunk 1658 8 = 123801322 := by decide +kernel
theorem a1658 : chunk 1562 104 = 911269412 := by
  have h := chunk_join a1650 c1658
  exact h
theorem c1666 : chunk 1666 8 = 136312756 := by decide +kernel
theorem a1666 : chunk 1562 112 = 1047582168 := by
  have h := chunk_join a1658 c1666
  exact h
theorem c1674 : chunk 1674 8 = 149426916 := by decide +kernel
theorem a1674 : chunk 1562 120 = 1197009084 := by
  have h := chunk_join a1666 c1674
  exact h
theorem c1682 : chunk 1682 8 = 163483281 := by decide +kernel
theorem a1682 : chunk 1562 128 = 1360492365 := by
  have h := chunk_join a1674 c1682
  exact h
theorem c1690 : chunk 1690 8 = 178626496 := by decide +kernel
theorem a1690 : chunk 1562 136 = 1539118861 := by
  have h := chunk_join a1682 c1690
  exact h
theorem c1698 : chunk 1698 8 = 194498833 := by decide +kernel
theorem a1698 : chunk 1562 144 = 1733617694 := by
  have h := chunk_join a1690 c1698
  exact h
theorem c1706 : chunk 1706 8 = 211344620 := by decide +kernel
theorem a1706 : chunk 1562 152 = 1944962314 := by
  have h := chunk_join a1698 c1706
  exact h
theorem c1714 : chunk 1714 8 = 229377224 := by decide +kernel
theorem a1714 : chunk 1562 160 = 2174339538 := by
  have h := chunk_join a1706 c1714
  exact h
theorem c1722 : chunk 1722 8 = 248168338 := by decide +kernel
theorem a1722 : chunk 1562 168 = 2422507876 := by
  have h := chunk_join a1714 c1722
  exact h
theorem c1730 : chunk 1730 8 = 268143958 := by decide +kernel
theorem a1730 : chunk 1562 176 = 2690651834 := by
  have h := chunk_join a1722 c1730
  exact h
theorem c1738 : chunk 1738 8 = 289219027 := by decide +kernel
theorem a1738 : chunk 1562 184 = 2979870861 := by
  have h := chunk_join a1730 c1738
  exact h
theorem c1746 : chunk 1746 8 = 311216214 := by decide +kernel
theorem a1746 : chunk 1562 192 = 3291087075 := by
  have h := chunk_join a1738 c1746
  exact h
theorem c1754 : chunk 1754 8 = 334555754 := by decide +kernel
theorem a1754 : chunk 1562 200 = 3625642829 := by
  have h := chunk_join a1746 c1754
  exact h
theorem c1762 : chunk 1762 8 = 358769688 := by decide +kernel
theorem a1762 : chunk 1562 208 = 3984412517 := by
  have h := chunk_join a1754 c1762
  exact h

theorem part1 : chunk 1562 208 = 3984412517 := a1762

end ThetaSum
