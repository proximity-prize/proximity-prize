import ProximityPrize.SubmissionLower.ThetaSumDefs
import ProximityPrize.SubmissionLower.ThetaSumData6 -- serialize candidate build

/-! Kernel-checked chunks of the theta savings sum (generated; values from the exact ledger). -/

namespace ThetaSum

theorem c2810 : chunk 2810 8 = 682152498 := by decide +kernel
theorem a2810 : chunk 2810 8 = 682152498 := c2810
theorem c2818 : chunk 2818 8 = 643795759 := by decide +kernel
theorem a2818 : chunk 2810 16 = 1325948257 := by
  have h := chunk_join a2810 c2818
  exact h
theorem c2826 : chunk 2826 8 = 606718378 := by decide +kernel
theorem a2826 : chunk 2810 24 = 1932666635 := by
  have h := chunk_join a2818 c2826
  exact h
theorem c2834 : chunk 2834 8 = 570842418 := by decide +kernel
theorem a2834 : chunk 2810 32 = 2503509053 := by
  have h := chunk_join a2826 c2834
  exact h
theorem c2842 : chunk 2842 8 = 536250195 := by decide +kernel
theorem a2842 : chunk 2810 40 = 3039759248 := by
  have h := chunk_join a2834 c2842
  exact h
theorem c2850 : chunk 2850 8 = 502849771 := by decide +kernel
theorem a2850 : chunk 2810 48 = 3542609019 := by
  have h := chunk_join a2842 c2850
  exact h
theorem c2858 : chunk 2858 8 = 470735214 := by decide +kernel
theorem a2858 : chunk 2810 56 = 4013344233 := by
  have h := chunk_join a2850 c2858
  exact h
theorem c2866 : chunk 2866 8 = 439800329 := by decide +kernel
theorem a2866 : chunk 2810 64 = 4453144562 := by
  have h := chunk_join a2858 c2866
  exact h
theorem c2874 : chunk 2874 8 = 410128851 := by decide +kernel
theorem a2874 : chunk 2810 72 = 4863273413 := by
  have h := chunk_join a2866 c2874
  exact h
theorem c2882 : chunk 2882 8 = 381642796 := by decide +kernel
theorem a2882 : chunk 2810 80 = 5244916209 := by
  have h := chunk_join a2874 c2882
  exact h
theorem c2890 : chunk 2890 8 = 354308410 := by decide +kernel
theorem a2890 : chunk 2810 88 = 5599224619 := by
  have h := chunk_join a2882 c2890
  exact h
theorem c2898 : chunk 2898 8 = 328247914 := by decide +kernel
theorem a2898 : chunk 2810 96 = 5927472533 := by
  have h := chunk_join a2890 c2898
  exact h
theorem c2906 : chunk 2906 8 = 303372023 := by decide +kernel
theorem a2906 : chunk 2810 104 = 6230844556 := by
  have h := chunk_join a2898 c2906
  exact h
theorem c2914 : chunk 2914 8 = 279624151 := by decide +kernel
theorem a2914 : chunk 2810 112 = 6510468707 := by
  have h := chunk_join a2906 c2914
  exact h
theorem c2922 : chunk 2922 8 = 257024372 := by decide +kernel
theorem a2922 : chunk 2810 120 = 6767493079 := by
  have h := chunk_join a2914 c2922
  exact h
theorem c2930 : chunk 2930 8 = 235533445 := by decide +kernel
theorem a2930 : chunk 2810 128 = 7003026524 := by
  have h := chunk_join a2922 c2930
  exact h
theorem c2938 : chunk 2938 8 = 215172883 := by decide +kernel
theorem a2938 : chunk 2810 136 = 7218199407 := by
  have h := chunk_join a2930 c2938
  exact h
theorem c2946 : chunk 2946 8 = 195935954 := by decide +kernel
theorem a2946 : chunk 2810 144 = 7414135361 := by
  have h := chunk_join a2938 c2946
  exact h
theorem c2954 : chunk 2954 8 = 177635944 := by decide +kernel
theorem a2954 : chunk 2810 152 = 7591771305 := by
  have h := chunk_join a2946 c2954
  exact h
theorem c2962 : chunk 2962 8 = 160456605 := by decide +kernel
theorem a2962 : chunk 2810 160 = 7752227910 := by
  have h := chunk_join a2954 c2962
  exact h
theorem c2970 : chunk 2970 8 = 144287926 := by decide +kernel
theorem a2970 : chunk 2810 168 = 7896515836 := by
  have h := chunk_join a2962 c2970
  exact h
theorem c2978 : chunk 2978 8 = 129060343 := by decide +kernel
theorem a2978 : chunk 2810 176 = 8025576179 := by
  have h := chunk_join a2970 c2978
  exact h
theorem c2986 : chunk 2986 8 = 114843385 := by decide +kernel
theorem a2986 : chunk 2810 184 = 8140419564 := by
  have h := chunk_join a2978 c2986
  exact h
theorem c2994 : chunk 2994 8 = 101447175 := by decide +kernel
theorem a2994 : chunk 2810 192 = 8241866739 := by
  have h := chunk_join a2986 c2994
  exact h
theorem c3002 : chunk 3002 8 = 89007105 := by decide +kernel
theorem a3002 : chunk 2810 200 = 8330873844 := by
  have h := chunk_join a2994 c3002
  exact h
theorem c3010 : chunk 3010 2 = 20403696 := by decide +kernel
theorem a3010 : chunk 2810 202 = 8351277540 := by
  have h := chunk_join a3002 c3010
  exact h

theorem part7 : chunk 2810 202 = 8351277540 := a3010

end ThetaSum
