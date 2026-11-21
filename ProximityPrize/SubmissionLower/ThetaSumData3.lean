import ProximityPrize.SubmissionLower.ThetaSumDefs

/-! Kernel-checked chunks of the theta savings sum (generated; values from the exact ledger). -/

namespace ThetaSum

theorem c1978 : chunk 1978 8 = 1473662355 := by decide +kernel
theorem a1978 : chunk 1978 8 = 1473662355 := c1978
theorem c1986 : chunk 1986 8 = 1530771836 := by decide +kernel
theorem a1986 : chunk 1978 16 = 3004434191 := by
  have h := chunk_join a1978 c1986
  exact h
theorem c1994 : chunk 1994 8 = 1588735960 := by decide +kernel
theorem a1994 : chunk 1978 24 = 4593170151 := by
  have h := chunk_join a1986 c1994
  exact h
theorem c2002 : chunk 2002 8 = 1647503815 := by decide +kernel
theorem a2002 : chunk 1978 32 = 6240673966 := by
  have h := chunk_join a1994 c2002
  exact h
theorem c2010 : chunk 2010 8 = 1707011342 := by decide +kernel
theorem a2010 : chunk 1978 40 = 7947685308 := by
  have h := chunk_join a2002 c2010
  exact h
theorem c2018 : chunk 2018 8 = 1767210386 := by decide +kernel
theorem a2018 : chunk 1978 48 = 9714895694 := by
  have h := chunk_join a2010 c2018
  exact h
theorem c2026 : chunk 2026 8 = 1828027038 := by decide +kernel
theorem a2026 : chunk 1978 56 = 11542922732 := by
  have h := chunk_join a2018 c2026
  exact h
theorem c2034 : chunk 2034 8 = 1889404499 := by decide +kernel
theorem a2034 : chunk 1978 64 = 13432327231 := by
  have h := chunk_join a2026 c2034
  exact h
theorem c2042 : chunk 2042 8 = 1951272636 := by decide +kernel
theorem a2042 : chunk 1978 72 = 15383599867 := by
  have h := chunk_join a2034 c2042
  exact h
theorem c2050 : chunk 2050 8 = 2013560244 := by decide +kernel
theorem a2050 : chunk 1978 80 = 17397160111 := by
  have h := chunk_join a2042 c2050
  exact h
theorem c2058 : chunk 2058 8 = 2076157901 := by decide +kernel
theorem a2058 : chunk 1978 88 = 19473318012 := by
  have h := chunk_join a2050 c2058
  exact h
theorem c2066 : chunk 2066 8 = 2138981803 := by decide +kernel
theorem a2066 : chunk 1978 96 = 21612299815 := by
  have h := chunk_join a2058 c2066
  exact h
theorem c2074 : chunk 2074 8 = 2201984099 := by decide +kernel
theorem a2074 : chunk 1978 104 = 23814283914 := by
  have h := chunk_join a2066 c2074
  exact h
theorem c2082 : chunk 2082 8 = 2265073412 := by decide +kernel
theorem a2082 : chunk 1978 112 = 26079357326 := by
  have h := chunk_join a2074 c2082
  exact h
theorem c2090 : chunk 2090 8 = 2328140358 := by decide +kernel
theorem a2090 : chunk 1978 120 = 28407497684 := by
  have h := chunk_join a2082 c2090
  exact h
theorem c2098 : chunk 2098 8 = 2391016286 := by decide +kernel
theorem a2098 : chunk 1978 128 = 30798513970 := by
  have h := chunk_join a2090 c2098
  exact h
theorem c2106 : chunk 2106 8 = 2453700849 := by decide +kernel
theorem a2106 : chunk 1978 136 = 33252214819 := by
  have h := chunk_join a2098 c2106
  exact h
theorem c2114 : chunk 2114 8 = 2516072647 := by decide +kernel
theorem a2114 : chunk 1978 144 = 35768287466 := by
  have h := chunk_join a2106 c2114
  exact h
theorem c2122 : chunk 2122 8 = 2577913563 := by decide +kernel
theorem a2122 : chunk 1978 152 = 38346201029 := by
  have h := chunk_join a2114 c2122
  exact h
theorem c2130 : chunk 2130 8 = 2639236937 := by decide +kernel
theorem a2130 : chunk 1978 160 = 40985437966 := by
  have h := chunk_join a2122 c2130
  exact h
theorem c2138 : chunk 2138 8 = 2699847212 := by decide +kernel
theorem a2138 : chunk 1978 168 = 43685285178 := by
  have h := chunk_join a2130 c2138
  exact h
theorem c2146 : chunk 2146 8 = 2759598180 := by decide +kernel
theorem a2146 : chunk 1978 176 = 46444883358 := by
  have h := chunk_join a2138 c2146
  exact h
theorem c2154 : chunk 2154 8 = 2818453708 := by decide +kernel
theorem a2154 : chunk 1978 184 = 49263337066 := by
  have h := chunk_join a2146 c2154
  exact h
theorem c2162 : chunk 2162 8 = 2876124078 := by decide +kernel
theorem a2162 : chunk 1978 192 = 52139461144 := by
  have h := chunk_join a2154 c2162
  exact h
theorem c2170 : chunk 2170 8 = 2932649983 := by decide +kernel
theorem a2170 : chunk 1978 200 = 55072111127 := by
  have h := chunk_join a2162 c2170
  exact h
theorem c2178 : chunk 2178 8 = 2987690443 := by decide +kernel
theorem a2178 : chunk 1978 208 = 58059801570 := by
  have h := chunk_join a2170 c2178
  exact h

theorem part3 : chunk 1978 208 = 58059801570 := a2178

end ThetaSum
