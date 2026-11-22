import ProximityPrize.SubmissionLower.ThetaSumClip

/-! Kernel-checked chunks of the theta savings sum (generated; values from the exact ledger). -/

namespace ThetaSum

theorem c2602 : chunk 2602 8 = 2034144493 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2602 : chunk 2602 8 = 2034144493 := c2602
theorem c2610 : chunk 2610 8 = 1973850242 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2610 : chunk 2602 16 = 4007994735 := by
  have h := chunk_join a2602 c2610
  exact h
theorem c2618 : chunk 2618 8 = 1913766154 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2618 : chunk 2602 24 = 5921760889 := by
  have h := chunk_join a2610 c2618
  exact h
theorem c2626 : chunk 2626 8 = 1853932169 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2626 : chunk 2602 32 = 7775693058 := by
  have h := chunk_join a2618 c2626
  exact h
theorem c2634 : chunk 2634 8 = 1794508371 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2634 : chunk 2602 40 = 9570201429 := by
  have h := chunk_join a2626 c2634
  exact h
theorem c2642 : chunk 2642 8 = 1735466738 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2642 : chunk 2602 48 = 11305668167 := by
  have h := chunk_join a2634 c2642
  exact h
theorem c2650 : chunk 2650 8 = 1676902637 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2650 : chunk 2602 56 = 12982570804 := by
  have h := chunk_join a2642 c2650
  exact h
theorem c2658 : chunk 2658 8 = 1618922613 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2658 : chunk 2602 64 = 14601493417 := by
  have h := chunk_join a2650 c2658
  exact h
theorem c2666 : chunk 2666 8 = 1561522694 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2666 : chunk 2602 72 = 16163016111 := by
  have h := chunk_join a2658 c2666
  exact h
theorem c2674 : chunk 2674 8 = 1504761411 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2674 : chunk 2602 80 = 17667777522 := by
  have h := chunk_join a2666 c2674
  exact h
theorem c2682 : chunk 2682 8 = 1448715862 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2682 : chunk 2602 88 = 19116493384 := by
  have h := chunk_join a2674 c2682
  exact h
theorem c2690 : chunk 2690 8 = 1393461235 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2690 : chunk 2602 96 = 20509954619 := by
  have h := chunk_join a2682 c2690
  exact h
theorem c2698 : chunk 2698 8 = 1339000091 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2698 : chunk 2602 104 = 21848954710 := by
  have h := chunk_join a2690 c2698
  exact h
theorem c2706 : chunk 2706 8 = 1285381160 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2706 : chunk 2602 112 = 23134335870 := by
  have h := chunk_join a2698 c2706
  exact h
theorem c2714 : chunk 2714 8 = 1232643850 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2714 : chunk 2602 120 = 24366979720 := by
  have h := chunk_join a2706 c2714
  exact h
theorem c2722 : chunk 2722 8 = 1180879150 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2722 : chunk 2602 128 = 25547858870 := by
  have h := chunk_join a2714 c2722
  exact h
theorem c2730 : chunk 2730 8 = 1130115446 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2730 : chunk 2602 136 = 26677974316 := by
  have h := chunk_join a2722 c2730
  exact h
theorem c2738 : chunk 2738 8 = 1080330959 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2738 : chunk 2602 144 = 27758305275 := by
  have h := chunk_join a2730 c2738
  exact h
theorem c2746 : chunk 2746 8 = 1031554903 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2746 : chunk 2602 152 = 28789860178 := by
  have h := chunk_join a2738 c2746
  exact h
theorem c2754 : chunk 2754 8 = 983871288 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2754 : chunk 2602 160 = 29773731466 := by
  have h := chunk_join a2746 c2754
  exact h
theorem c2762 : chunk 2762 8 = 937295801 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2762 : chunk 2602 168 = 30711027267 := by
  have h := chunk_join a2754 c2762
  exact h
theorem c2770 : chunk 2770 8 = 891836925 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2770 : chunk 2602 176 = 31602864192 := by
  have h := chunk_join a2762 c2770
  exact h
theorem c2778 : chunk 2778 8 = 847509518 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2778 : chunk 2602 184 = 32450373710 := by
  have h := chunk_join a2770 c2778
  exact h
theorem c2786 : chunk 2786 8 = 804365340 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2786 : chunk 2602 192 = 33254739050 := by
  have h := chunk_join a2778 c2786
  exact h
theorem c2794 : chunk 2794 8 = 762417576 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2794 : chunk 2602 200 = 34017156626 := by
  have h := chunk_join a2786 c2794
  exact h
theorem c2802 : chunk 2802 8 = 721659854 := by
  rw [← ThetaSumClip.fastChunk_eq _ _ (by decide) (by decide)]
  decide +kernel
theorem a2802 : chunk 2602 208 = 34738816480 := by
  have h := chunk_join a2794 c2802
  exact h

theorem part6 : chunk 2602 208 = 34738816480 := a2802

end ThetaSum
