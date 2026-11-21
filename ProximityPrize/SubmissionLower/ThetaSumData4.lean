import ProximityPrize.SubmissionLower.ThetaSumDefs

/-! Kernel-checked chunks of the theta savings sum (generated; values from the exact ledger). -/

namespace ThetaSum

theorem c2186 : chunk 2186 8 = 3041275156 := by decide +kernel
theorem a2186 : chunk 2186 8 = 3041275156 := c2186
theorem c2194 : chunk 2194 8 = 3093094634 := by decide +kernel
theorem a2194 : chunk 2186 16 = 6134369790 := by
  have h := chunk_join a2186 c2194
  exact h
theorem c2202 : chunk 2202 8 = 3143098113 := by decide +kernel
theorem a2202 : chunk 2186 24 = 9277467903 := by
  have h := chunk_join a2194 c2202
  exact h
theorem c2210 : chunk 2210 8 = 3191062940 := by decide +kernel
theorem a2210 : chunk 2186 32 = 12468530843 := by
  have h := chunk_join a2202 c2210
  exact h
theorem c2218 : chunk 2218 8 = 3236781283 := by decide +kernel
theorem a2218 : chunk 2186 40 = 15705312126 := by
  have h := chunk_join a2210 c2218
  exact h
theorem c2226 : chunk 2226 8 = 3280186801 := by decide +kernel
theorem a2226 : chunk 2186 48 = 18985498927 := by
  have h := chunk_join a2218 c2226
  exact h
theorem c2234 : chunk 2234 8 = 3320992702 := by decide +kernel
theorem a2234 : chunk 2186 56 = 22306491629 := by
  have h := chunk_join a2226 c2234
  exact h
theorem c2242 : chunk 2242 8 = 3359012034 := by decide +kernel
theorem a2242 : chunk 2186 64 = 25665503663 := by
  have h := chunk_join a2234 c2242
  exact h
theorem c2250 : chunk 2250 8 = 3394134473 := by decide +kernel
theorem a2250 : chunk 2186 72 = 29059638136 := by
  have h := chunk_join a2242 c2250
  exact h
theorem c2258 : chunk 2258 8 = 3426093335 := by decide +kernel
theorem a2258 : chunk 2186 80 = 32485731471 := by
  have h := chunk_join a2250 c2258
  exact h
theorem c2266 : chunk 2266 8 = 3454679266 := by decide +kernel
theorem a2266 : chunk 2186 88 = 35940410737 := by
  have h := chunk_join a2258 c2266
  exact h
theorem c2274 : chunk 2274 8 = 3479692473 := by decide +kernel
theorem a2274 : chunk 2186 96 = 39420103210 := by
  have h := chunk_join a2266 c2274
  exact h
theorem c2282 : chunk 2282 8 = 3500928879 := by decide +kernel
theorem a2282 : chunk 2186 104 = 42921032089 := by
  have h := chunk_join a2274 c2282
  exact h
theorem c2290 : chunk 2290 8 = 3518170813 := by decide +kernel
theorem a2290 : chunk 2186 112 = 46439202902 := by
  have h := chunk_join a2282 c2290
  exact h
theorem c2298 : chunk 2298 8 = 3531176933 := by decide +kernel
theorem a2298 : chunk 2186 120 = 49970379835 := by
  have h := chunk_join a2290 c2298
  exact h
theorem c2306 : chunk 2306 8 = 3539783426 := by decide +kernel
theorem a2306 : chunk 2186 128 = 53510163261 := by
  have h := chunk_join a2298 c2306
  exact h
theorem c2314 : chunk 2314 8 = 3544105486 := by decide +kernel
theorem a2314 : chunk 2186 136 = 57054268747 := by
  have h := chunk_join a2306 c2314
  exact h
theorem c2322 : chunk 2322 8 = 3544306611 := by decide +kernel
theorem a2322 : chunk 2186 144 = 60598575358 := by
  have h := chunk_join a2314 c2322
  exact h
theorem c2330 : chunk 2330 8 = 3540524225 := by decide +kernel
theorem a2330 : chunk 2186 152 = 64139099583 := by
  have h := chunk_join a2322 c2330
  exact h
theorem c2338 : chunk 2338 8 = 3532922436 := by decide +kernel
theorem a2338 : chunk 2186 160 = 67672022019 := by
  have h := chunk_join a2330 c2338
  exact h
theorem c2346 : chunk 2346 8 = 3521666060 := by decide +kernel
theorem a2346 : chunk 2186 168 = 71193688079 := by
  have h := chunk_join a2338 c2346
  exact h
theorem c2354 : chunk 2354 8 = 3506883802 := by decide +kernel
theorem a2354 : chunk 2186 176 = 74700571881 := by
  have h := chunk_join a2346 c2354
  exact h
theorem c2362 : chunk 2362 8 = 3488739334 := by decide +kernel
theorem a2362 : chunk 2186 184 = 78189311215 := by
  have h := chunk_join a2354 c2362
  exact h
theorem c2370 : chunk 2370 8 = 3467394507 := by decide +kernel
theorem a2370 : chunk 2186 192 = 81656705722 := by
  have h := chunk_join a2362 c2370
  exact h
theorem c2378 : chunk 2378 8 = 3442984984 := by decide +kernel
theorem a2378 : chunk 2186 200 = 85099690706 := by
  have h := chunk_join a2370 c2378
  exact h
theorem c2386 : chunk 2386 8 = 3415637505 := by decide +kernel
theorem a2386 : chunk 2186 208 = 88515328211 := by
  have h := chunk_join a2378 c2386
  exact h

theorem part4 : chunk 2186 208 = 88515328211 := a2386

end ThetaSum
