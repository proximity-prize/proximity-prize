import ProximityPrize.SubmissionLower.ThetaSumDefs

/-! Kernel-checked chunks of the theta savings sum (generated; values from the exact ledger). -/

namespace ThetaSum

theorem c2394 : chunk 2394 8 = 3385536512 := by decide +kernel
theorem a2394 : chunk 2394 8 = 3385536512 := c2394
theorem c2402 : chunk 2402 8 = 3352760155 := by decide +kernel
theorem a2402 : chunk 2394 16 = 6738296667 := by
  have h := chunk_join a2394 c2402
  exact h
theorem c2410 : chunk 2410 8 = 3317472085 := by decide +kernel
theorem a2410 : chunk 2394 24 = 10055768752 := by
  have h := chunk_join a2402 c2410
  exact h
theorem c2418 : chunk 2418 8 = 3279830219 := by decide +kernel
theorem a2418 : chunk 2394 32 = 13335598971 := by
  have h := chunk_join a2410 c2418
  exact h
theorem c2426 : chunk 2426 8 = 3239947997 := by decide +kernel
theorem a2426 : chunk 2394 40 = 16575546968 := by
  have h := chunk_join a2418 c2426
  exact h
theorem c2434 : chunk 2434 8 = 3197961412 := by decide +kernel
theorem a2434 : chunk 2394 48 = 19773508380 := by
  have h := chunk_join a2426 c2434
  exact h
theorem c2442 : chunk 2442 8 = 3153973310 := by decide +kernel
theorem a2442 : chunk 2394 56 = 22927481690 := by
  have h := chunk_join a2434 c2442
  exact h
theorem c2450 : chunk 2450 8 = 3108142179 := by decide +kernel
theorem a2450 : chunk 2394 64 = 26035623869 := by
  have h := chunk_join a2442 c2450
  exact h
theorem c2458 : chunk 2458 8 = 3060598696 := by decide +kernel
theorem a2458 : chunk 2394 72 = 29096222565 := by
  have h := chunk_join a2450 c2458
  exact h
theorem c2466 : chunk 2466 8 = 3011397845 := by decide +kernel
theorem a2466 : chunk 2394 80 = 32107620410 := by
  have h := chunk_join a2458 c2466
  exact h
theorem c2474 : chunk 2474 8 = 2960756507 := by decide +kernel
theorem a2474 : chunk 2394 88 = 35068376917 := by
  have h := chunk_join a2466 c2474
  exact h
theorem c2482 : chunk 2482 8 = 2908687617 := by decide +kernel
theorem a2482 : chunk 2394 96 = 37977064534 := by
  have h := chunk_join a2474 c2482
  exact h
theorem c2490 : chunk 2490 8 = 2855372492 := by decide +kernel
theorem a2490 : chunk 2394 104 = 40832437026 := by
  have h := chunk_join a2482 c2490
  exact h
theorem c2498 : chunk 2498 8 = 2800940234 := by decide +kernel
theorem a2498 : chunk 2394 112 = 43633377260 := by
  have h := chunk_join a2490 c2498
  exact h
theorem c2506 : chunk 2506 8 = 2745403124 := by decide +kernel
theorem a2506 : chunk 2394 120 = 46378780384 := by
  have h := chunk_join a2498 c2506
  exact h
theorem c2514 : chunk 2514 8 = 2688989619 := by decide +kernel
theorem a2514 : chunk 2394 128 = 49067770003 := by
  have h := chunk_join a2506 c2514
  exact h
theorem c2522 : chunk 2522 8 = 2631691759 := by decide +kernel
theorem a2522 : chunk 2394 136 = 51699461762 := by
  have h := chunk_join a2514 c2522
  exact h
theorem c2530 : chunk 2530 8 = 2573684293 := by decide +kernel
theorem a2530 : chunk 2394 144 = 54273146055 := by
  have h := chunk_join a2522 c2530
  exact h
theorem c2538 : chunk 2538 8 = 2515068519 := by decide +kernel
theorem a2538 : chunk 2394 152 = 56788214574 := by
  have h := chunk_join a2530 c2538
  exact h
theorem c2546 : chunk 2546 8 = 2455864364 := by decide +kernel
theorem a2546 : chunk 2394 160 = 59244078938 := by
  have h := chunk_join a2538 c2546
  exact h
theorem c2554 : chunk 2554 8 = 2396282383 := by decide +kernel
theorem a2554 : chunk 2394 168 = 61640361321 := by
  have h := chunk_join a2546 c2554
  exact h
theorem c2562 : chunk 2562 8 = 2336299796 := by decide +kernel
theorem a2562 : chunk 2394 176 = 63976661117 := by
  have h := chunk_join a2554 c2562
  exact h
theorem c2570 : chunk 2570 8 = 2276054163 := by decide +kernel
theorem a2570 : chunk 2394 184 = 66252715280 := by
  have h := chunk_join a2562 c2570
  exact h
theorem c2578 : chunk 2578 8 = 2215634126 := by decide +kernel
theorem a2578 : chunk 2394 192 = 68468349406 := by
  have h := chunk_join a2570 c2578
  exact h
theorem c2586 : chunk 2586 8 = 2155127073 := by decide +kernel
theorem a2586 : chunk 2394 200 = 70623476479 := by
  have h := chunk_join a2578 c2586
  exact h
theorem c2594 : chunk 2594 8 = 2094604750 := by decide +kernel
theorem a2594 : chunk 2394 208 = 72718081229 := by
  have h := chunk_join a2586 c2594
  exact h

theorem part5 : chunk 2394 208 = 72718081229 := a2594

end ThetaSum
