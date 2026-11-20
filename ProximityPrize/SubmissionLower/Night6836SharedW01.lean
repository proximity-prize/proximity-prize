/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w30 : P33.Window := ⟨5,63,5487,5070,233908287107041833,41175,50000,5000000,81920000000⟩
def h30_0 : Height w30 := ⟨41175,50000,by decide +kernel⟩
def pick30 (cl : ℕ) : Height w30 := h30_0
private theorem k30_1_0 : check w30 pick30 1 t801 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k30_1_1 : check w30 pick30 1 t834 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k30_1_2 : check w30 pick30 1 t835 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w30 pick30 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t801 t834 k30_1_0 k30_1_1
private theorem k30_1_3 : check w30 pick30 1 t2292 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k30_1_4 : check w30 pick30 1 t2299 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k30_1_5 : check w30 pick30 1 t2300 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w30 pick30 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t2292 t2299 k30_1_3 k30_1_4
private theorem k30_1_6 : check w30 pick30 1 t2301 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w30 pick30 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t835 t2300 k30_1_2 k30_1_5
private theorem k30_1_7 : check w30 pick30 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k30_1_8 : check w30 pick30 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k30_1_9 : check w30 pick30 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w30 pick30 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k30_1_7 k30_1_8
private theorem k30_1_10 : check w30 pick30 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k30_1_11 : check w30 pick30 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k30_1_12 : check w30 pick30 1 t787 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w30 pick30 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t786 k30_1_10 k30_1_11
private theorem k30_1_13 : check w30 pick30 1 t2259 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w30 pick30 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t787 k30_1_9 k30_1_12
private theorem k30_1_14 : check w30 pick30 1 t2302 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w30 pick30 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2301 t2259 k30_1_6 k30_1_13
theorem cov30_1 : PA.Covered 1 (OZ.Valid 1 w30.low w30.t w30.y w30.r w30.cap) (P33.root 1) :=
  Night6836Tree.sound w30 pick30 1 t2302 _ k30_1_14
theorem cov30_2 : PA.Covered 2 (OZ.Valid 2 w30.low w30.t w30.y w30.r w30.cap) (P33.root 2) :=
  Night6836Tree.sound w30 pick30 2 t563 _ (by decide +kernel)
theorem cov30_3 : PA.Covered 3 (OZ.Valid 3 w30.low w30.t w30.y w30.r w30.cap) (P33.root 3) :=
  Night6836Tree.sound w30 pick30 3 t564 _ (by decide +kernel)
theorem cov30_4 : PA.Covered 4 (OZ.Valid 4 w30.low w30.t w30.y w30.r w30.cap) (P33.root 4) :=
  Night6836Tree.sound w30 pick30 4 t565 _ (by decide +kernel)
theorem cov30_5 : PA.Covered 5 (OZ.Valid 5 w30.low w30.t w30.y w30.r w30.cap) (P33.root 5) :=
  Night6836Tree.sound w30 pick30 5 t566 _ (by decide +kernel)
theorem cov30_6 : PA.Covered 6 (OZ.Valid 6 w30.low w30.t w30.y w30.r w30.cap) (P33.root 6) :=
  Night6836Tree.sound w30 pick30 6 t567 _ (by decide +kernel)
theorem cov30_7 : PA.Covered 7 (OZ.Valid 7 w30.low w30.t w30.y w30.r w30.cap) (P33.root 7) :=
  Night6836Tree.sound w30 pick30 7 t2134 _ (by decide +kernel)
theorem window30 : P33.WindowCount w30 := by
  apply P33.window_count w30 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov30_1
  · exact cov30_2
  · exact cov30_3
  · exact cov30_4
  · exact cov30_5
  · exact cov30_6
  · exact cov30_7
def w31 : P33.Window := ⟨5,64,5069,4637,238417968926566013,49301,50000,5000000,81920000000⟩
def h31_0 : Height w31 := ⟨49301,50000,by decide +kernel⟩
def pick31 (cl : ℕ) : Height w31 := h31_0
private theorem k31_1_0 : check w31 pick31 1 t2307 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k31_1_1 : check w31 pick31 1 t2318 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k31_1_2 : check w31 pick31 1 t2319 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w31 pick31 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t2307 t2318 k31_1_0 k31_1_1
private theorem k31_1_3 : check w31 pick31 1 t2334 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k31_1_4 : check w31 pick31 1 t2353 ⟨1,7,2,16,1,52,111,145⟩ = true := by decide +kernel
private theorem k31_1_5 : check w31 pick31 1 t2354 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w31 pick31 1 ⟨1,7,2,16,1,52,84,145⟩ 3 110 t2334 t2353 k31_1_3 k31_1_4
private theorem k31_1_6 : check w31 pick31 1 t2355 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w31 pick31 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t2319 t2354 k31_1_2 k31_1_5
private theorem k31_1_7 : check w31 pick31 1 t2373 ⟨1,7,2,16,1,52,146,179⟩ = true := by decide +kernel
private theorem k31_1_8 : check w31 pick31 1 t2374 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k31_1_9 : check w31 pick31 1 t2375 ⟨1,7,2,16,1,52,146,206⟩ = true := glue w31 pick31 1 ⟨1,7,2,16,1,52,146,206⟩ 3 179 t2373 t2374 k31_1_7 k31_1_8
private theorem k31_1_10 : check w31 pick31 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k31_1_11 : check w31 pick31 1 t2395 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k31_1_12 : check w31 pick31 1 t2396 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w31 pick31 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t2395 k31_1_10 k31_1_11
private theorem k31_1_13 : check w31 pick31 1 t2397 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w31 pick31 1 ⟨1,7,2,16,1,52,146,450⟩ 3 206 t2375 t2396 k31_1_9 k31_1_12
private theorem k31_1_14 : check w31 pick31 1 t2398 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w31 pick31 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t2355 t2397 k31_1_6 k31_1_13
theorem cov31_1 : PA.Covered 1 (OZ.Valid 1 w31.low w31.t w31.y w31.r w31.cap) (P33.root 1) :=
  Night6836Tree.sound w31 pick31 1 t2398 _ k31_1_14
theorem cov31_2 : PA.Covered 2 (OZ.Valid 2 w31.low w31.t w31.y w31.r w31.cap) (P33.root 2) :=
  Night6836Tree.sound w31 pick31 2 t2403 _ (by decide +kernel)
theorem cov31_3 : PA.Covered 3 (OZ.Valid 3 w31.low w31.t w31.y w31.r w31.cap) (P33.root 3) :=
  Night6836Tree.sound w31 pick31 3 t564 _ (by decide +kernel)
theorem cov31_4 : PA.Covered 4 (OZ.Valid 4 w31.low w31.t w31.y w31.r w31.cap) (P33.root 4) :=
  Night6836Tree.sound w31 pick31 4 t565 _ (by decide +kernel)
theorem cov31_5 : PA.Covered 5 (OZ.Valid 5 w31.low w31.t w31.y w31.r w31.cap) (P33.root 5) :=
  Night6836Tree.sound w31 pick31 5 t566 _ (by decide +kernel)
theorem cov31_6 : PA.Covered 6 (OZ.Valid 6 w31.low w31.t w31.y w31.r w31.cap) (P33.root 6) :=
  Night6836Tree.sound w31 pick31 6 t567 _ (by decide +kernel)
theorem cov31_7 : PA.Covered 7 (OZ.Valid 7 w31.low w31.t w31.y w31.r w31.cap) (P33.root 7) :=
  Night6836Tree.sound w31 pick31 7 t2134 _ (by decide +kernel)
theorem window31 : P33.WindowCount w31 := by
  apply P33.window_count w31 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov31_1
  · exact cov31_2
  · exact cov31_3
  · exact cov31_4
  · exact cov31_5
  · exact cov31_6
  · exact cov31_7
def w32 : P33.Window := ⟨5,65,4636,4227,238159058914504902,58802,50000,5000000,81920000000⟩
def h32_0 : Height w32 := ⟨58802,50000,by decide +kernel⟩
def pick32 (cl : ℕ) : Height w32 := h32_0
private theorem k32_1_0 : check w32 pick32 1 t2425 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k32_1_1 : check w32 pick32 1 t2426 ⟨1,7,2,16,1,52,56,76⟩ = true := by decide +kernel
private theorem k32_1_2 : check w32 pick32 1 t2427 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w32 pick32 1 ⟨1,7,2,16,1,52,1,76⟩ 3 55 t2425 t2426 k32_1_0 k32_1_1
private theorem k32_1_3 : check w32 pick32 1 t2439 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k32_1_4 : check w32 pick32 1 t2454 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k32_1_5 : check w32 pick32 1 t2455 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w32 pick32 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t2439 t2454 k32_1_3 k32_1_4
private theorem k32_1_6 : check w32 pick32 1 t2456 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w32 pick32 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2427 t2455 k32_1_2 k32_1_5
private theorem k32_1_7 : check w32 pick32 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k32_1_8 : check w32 pick32 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k32_1_9 : check w32 pick32 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w32 pick32 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k32_1_7 k32_1_8
private theorem k32_1_10 : check w32 pick32 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k32_1_11 : check w32 pick32 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k32_1_12 : check w32 pick32 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w32 pick32 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k32_1_10 k32_1_11
private theorem k32_1_13 : check w32 pick32 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w32 pick32 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k32_1_9 k32_1_12
private theorem k32_1_14 : check w32 pick32 1 t2462 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w32 pick32 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2456 t2461 k32_1_6 k32_1_13
theorem cov32_1 : PA.Covered 1 (OZ.Valid 1 w32.low w32.t w32.y w32.r w32.cap) (P33.root 1) :=
  Night6836Tree.sound w32 pick32 1 t2462 _ k32_1_14
theorem cov32_2 : PA.Covered 2 (OZ.Valid 2 w32.low w32.t w32.y w32.r w32.cap) (P33.root 2) :=
  Night6836Tree.sound w32 pick32 2 t2479 _ (by decide +kernel)
theorem cov32_3 : PA.Covered 3 (OZ.Valid 3 w32.low w32.t w32.y w32.r w32.cap) (P33.root 3) :=
  Night6836Tree.sound w32 pick32 3 t564 _ (by decide +kernel)
theorem cov32_4 : PA.Covered 4 (OZ.Valid 4 w32.low w32.t w32.y w32.r w32.cap) (P33.root 4) :=
  Night6836Tree.sound w32 pick32 4 t565 _ (by decide +kernel)
theorem cov32_5 : PA.Covered 5 (OZ.Valid 5 w32.low w32.t w32.y w32.r w32.cap) (P33.root 5) :=
  Night6836Tree.sound w32 pick32 5 t566 _ (by decide +kernel)
theorem cov32_6 : PA.Covered 6 (OZ.Valid 6 w32.low w32.t w32.y w32.r w32.cap) (P33.root 6) :=
  Night6836Tree.sound w32 pick32 6 t567 _ (by decide +kernel)
theorem cov32_7 : PA.Covered 7 (OZ.Valid 7 w32.low w32.t w32.y w32.r w32.cap) (P33.root 7) :=
  Night6836Tree.sound w32 pick32 7 t2134 _ (by decide +kernel)
theorem window32 : P33.WindowCount w32 := by
  apply P33.window_count w32 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov32_1
  · exact cov32_2
  · exact cov32_3
  · exact cov32_4
  · exact cov32_5
  · exact cov32_6
  · exact cov32_7
def w33 : P33.Window := ⟨5,66,4188,4162,232476447826958048,61650,50000,5000000,81920000000⟩
def h33_0 : Height w33 := ⟨61650,50000,by decide +kernel⟩
def pick33 (cl : ℕ) : Height w33 := h33_0
private theorem k33_1_0 : check w33 pick33 1 t2524 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k33_1_1 : check w33 pick33 1 t2541 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k33_1_2 : check w33 pick33 1 t2559 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k33_1_3 : check w33 pick33 1 t2560 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w33 pick33 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t2541 t2559 k33_1_1 k33_1_2
private theorem k33_1_4 : check w33 pick33 1 t2561 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w33 pick33 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t2524 t2560 k33_1_0 k33_1_3
private theorem k33_1_5 : check w33 pick33 1 t2576 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k33_1_6 : check w33 pick33 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k33_1_7 : check w33 pick33 1 t2577 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w33 pick33 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t2576 t382 k33_1_5 k33_1_6
private theorem k33_1_8 : check w33 pick33 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k33_1_9 : check w33 pick33 1 t2587 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k33_1_10 : check w33 pick33 1 t2588 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w33 pick33 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t2587 k33_1_8 k33_1_9
private theorem k33_1_11 : check w33 pick33 1 t2589 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w33 pick33 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t2577 t2588 k33_1_7 k33_1_10
private theorem k33_1_12 : check w33 pick33 1 t2590 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w33 pick33 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t2561 t2589 k33_1_4 k33_1_11
theorem cov33_1 : PA.Covered 1 (OZ.Valid 1 w33.low w33.t w33.y w33.r w33.cap) (P33.root 1) :=
  Night6836Tree.sound w33 pick33 1 t2590 _ k33_1_12
theorem cov33_2 : PA.Covered 2 (OZ.Valid 2 w33.low w33.t w33.y w33.r w33.cap) (P33.root 2) :=
  Night6836Tree.sound w33 pick33 2 t2603 _ (by decide +kernel)
theorem cov33_3 : PA.Covered 3 (OZ.Valid 3 w33.low w33.t w33.y w33.r w33.cap) (P33.root 3) :=
  Night6836Tree.sound w33 pick33 3 t564 _ (by decide +kernel)
theorem cov33_4 : PA.Covered 4 (OZ.Valid 4 w33.low w33.t w33.y w33.r w33.cap) (P33.root 4) :=
  Night6836Tree.sound w33 pick33 4 t565 _ (by decide +kernel)
theorem cov33_5 : PA.Covered 5 (OZ.Valid 5 w33.low w33.t w33.y w33.r w33.cap) (P33.root 5) :=
  Night6836Tree.sound w33 pick33 5 t566 _ (by decide +kernel)
theorem cov33_6 : PA.Covered 6 (OZ.Valid 6 w33.low w33.t w33.y w33.r w33.cap) (P33.root 6) :=
  Night6836Tree.sound w33 pick33 6 t567 _ (by decide +kernel)
theorem cov33_7 : PA.Covered 7 (OZ.Valid 7 w33.low w33.t w33.y w33.r w33.cap) (P33.root 7) :=
  Night6836Tree.sound w33 pick33 7 t2134 _ (by decide +kernel)
theorem window33 : P33.WindowCount w33 := by
  apply P33.window_count w33 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov33_1
  · exact cov33_2
  · exact cov33_3
  · exact cov33_4
  · exact cov33_5
  · exact cov33_6
  · exact cov33_7
def w34 : P33.Window := ⟨10,19,7853,7820,226198890763237302,8098,15000,5000000,81920000000⟩
def h34_0 : Height w34 := ⟨8098,15000,by decide +kernel⟩
def h34_1 : Height w34 := ⟨13142,12000,by decide +kernel⟩
def pick34 (cl : ℕ) : Height w34 := if cl<14 then (h34_0) else (h34_1)
private theorem k34_1_0 : check w34 pick34 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k34_1_1 : check w34 pick34 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k34_1_2 : check w34 pick34 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w34 pick34 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k34_1_0 k34_1_1
private theorem k34_1_3 : check w34 pick34 1 t2676 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k34_1_4 : check w34 pick34 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k34_1_5 : check w34 pick34 1 t2688 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w34 pick34 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2676 t2687 k34_1_3 k34_1_4
private theorem k34_1_6 : check w34 pick34 1 t2689 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w34 pick34 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2688 k34_1_2 k34_1_5
private theorem k34_1_7 : check w34 pick34 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k34_1_8 : check w34 pick34 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k34_1_9 : check w34 pick34 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w34 pick34 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k34_1_7 k34_1_8
private theorem k34_1_10 : check w34 pick34 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k34_1_11 : check w34 pick34 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k34_1_12 : check w34 pick34 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w34 pick34 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k34_1_10 k34_1_11
private theorem k34_1_13 : check w34 pick34 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w34 pick34 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k34_1_9 k34_1_12
private theorem k34_1_14 : check w34 pick34 1 t2690 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w34 pick34 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2689 t2461 k34_1_6 k34_1_13
theorem cov34_1 : PA.Covered 1 (OZ.Valid 1 w34.low w34.t w34.y w34.r w34.cap) (P33.root 1) :=
  Night6836Tree.sound w34 pick34 1 t2690 _ k34_1_14
theorem cov34_2 : PA.Covered 2 (OZ.Valid 2 w34.low w34.t w34.y w34.r w34.cap) (P33.root 2) :=
  Night6836Tree.sound w34 pick34 2 t2745 _ (by decide +kernel)
theorem cov34_3 : PA.Covered 3 (OZ.Valid 3 w34.low w34.t w34.y w34.r w34.cap) (P33.root 3) :=
  Night6836Tree.sound w34 pick34 3 t564 _ (by decide +kernel)
theorem cov34_4 : PA.Covered 4 (OZ.Valid 4 w34.low w34.t w34.y w34.r w34.cap) (P33.root 4) :=
  Night6836Tree.sound w34 pick34 4 t565 _ (by decide +kernel)
theorem cov34_5 : PA.Covered 5 (OZ.Valid 5 w34.low w34.t w34.y w34.r w34.cap) (P33.root 5) :=
  Night6836Tree.sound w34 pick34 5 t566 _ (by decide +kernel)
theorem cov34_6 : PA.Covered 6 (OZ.Valid 6 w34.low w34.t w34.y w34.r w34.cap) (P33.root 6) :=
  Night6836Tree.sound w34 pick34 6 t567 _ (by decide +kernel)
theorem cov34_7 : PA.Covered 7 (OZ.Valid 7 w34.low w34.t w34.y w34.r w34.cap) (P33.root 7) :=
  Night6836Tree.sound w34 pick34 7 t568 _ (by decide +kernel)
theorem window34 : P33.WindowCount w34 := by
  apply P33.window_count w34 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov34_1
  · exact cov34_2
  · exact cov34_3
  · exact cov34_4
  · exact cov34_5
  · exact cov34_6
  · exact cov34_7
def w35 : P33.Window := ⟨10,20,7819,7785,230103074036642718,9342,15000,5000000,81920000000⟩
def h35_0 : Height w35 := ⟨9342,15000,by decide +kernel⟩
def h35_1 : Height w35 := ⟨14704,12000,by decide +kernel⟩
def pick35 (cl : ℕ) : Height w35 := if cl<32 then (h35_0) else (h35_1)
private theorem k35_1_0 : check w35 pick35 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k35_1_1 : check w35 pick35 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k35_1_2 : check w35 pick35 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w35 pick35 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k35_1_0 k35_1_1
private theorem k35_1_3 : check w35 pick35 1 t2676 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k35_1_4 : check w35 pick35 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k35_1_5 : check w35 pick35 1 t2688 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w35 pick35 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2676 t2687 k35_1_3 k35_1_4
private theorem k35_1_6 : check w35 pick35 1 t2689 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w35 pick35 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2688 k35_1_2 k35_1_5
private theorem k35_1_7 : check w35 pick35 1 t325 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k35_1_8 : check w35 pick35 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k35_1_9 : check w35 pick35 1 t383 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w35 pick35 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t325 t382 k35_1_7 k35_1_8
private theorem k35_1_10 : check w35 pick35 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k35_1_11 : check w35 pick35 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k35_1_12 : check w35 pick35 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w35 pick35 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k35_1_10 k35_1_11
private theorem k35_1_13 : check w35 pick35 1 t500 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w35 pick35 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t383 t499 k35_1_9 k35_1_12
private theorem k35_1_14 : check w35 pick35 1 t2746 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w35 pick35 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2689 t500 k35_1_6 k35_1_13
theorem cov35_1 : PA.Covered 1 (OZ.Valid 1 w35.low w35.t w35.y w35.r w35.cap) (P33.root 1) :=
  Night6836Tree.sound w35 pick35 1 t2746 _ k35_1_14
theorem cov35_2 : PA.Covered 2 (OZ.Valid 2 w35.low w35.t w35.y w35.r w35.cap) (P33.root 2) :=
  Night6836Tree.sound w35 pick35 2 t2745 _ (by decide +kernel)
theorem cov35_3 : PA.Covered 3 (OZ.Valid 3 w35.low w35.t w35.y w35.r w35.cap) (P33.root 3) :=
  Night6836Tree.sound w35 pick35 3 t564 _ (by decide +kernel)
theorem cov35_4 : PA.Covered 4 (OZ.Valid 4 w35.low w35.t w35.y w35.r w35.cap) (P33.root 4) :=
  Night6836Tree.sound w35 pick35 4 t565 _ (by decide +kernel)
theorem cov35_5 : PA.Covered 5 (OZ.Valid 5 w35.low w35.t w35.y w35.r w35.cap) (P33.root 5) :=
  Night6836Tree.sound w35 pick35 5 t566 _ (by decide +kernel)
theorem cov35_6 : PA.Covered 6 (OZ.Valid 6 w35.low w35.t w35.y w35.r w35.cap) (P33.root 6) :=
  Night6836Tree.sound w35 pick35 6 t567 _ (by decide +kernel)
theorem cov35_7 : PA.Covered 7 (OZ.Valid 7 w35.low w35.t w35.y w35.r w35.cap) (P33.root 7) :=
  Night6836Tree.sound w35 pick35 7 t568 _ (by decide +kernel)
theorem window35 : P33.WindowCount w35 := by
  apply P33.window_count w35 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov35_1
  · exact cov35_2
  · exact cov35_3
  · exact cov35_4
  · exact cov35_5
  · exact cov35_6
  · exact cov35_7
def w36 : P33.Window := ⟨10,21,7020,6021,203962615081530609,14088,19000,5000000,81920000000⟩
def h36_0 : Height w36 := ⟨14088,19000,by decide +kernel⟩
def h36_1 : Height w36 := ⟨22205,15000,by decide +kernel⟩
def pick36 (cl : ℕ) : Height w36 := if cl<41 then (h36_0) else (h36_1)
private theorem k36_1_0 : check w36 pick36 1 t2748 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k36_1_1 : check w36 pick36 1 t2764 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k36_1_2 : check w36 pick36 1 t2765 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w36 pick36 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t2748 t2764 k36_1_0 k36_1_1
private theorem k36_1_3 : check w36 pick36 1 t2676 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k36_1_4 : check w36 pick36 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k36_1_5 : check w36 pick36 1 t2688 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w36 pick36 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2676 t2687 k36_1_3 k36_1_4
private theorem k36_1_6 : check w36 pick36 1 t2766 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w36 pick36 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2765 t2688 k36_1_2 k36_1_5
private theorem k36_1_7 : check w36 pick36 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k36_1_8 : check w36 pick36 1 t2783 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k36_1_9 : check w36 pick36 1 t2784 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w36 pick36 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t2783 k36_1_7 k36_1_8
private theorem k36_1_10 : check w36 pick36 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k36_1_11 : check w36 pick36 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k36_1_12 : check w36 pick36 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w36 pick36 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k36_1_10 k36_1_11
private theorem k36_1_13 : check w36 pick36 1 t2785 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w36 pick36 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2784 t499 k36_1_9 k36_1_12
private theorem k36_1_14 : check w36 pick36 1 t2786 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w36 pick36 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2766 t2785 k36_1_6 k36_1_13
theorem cov36_1 : PA.Covered 1 (OZ.Valid 1 w36.low w36.t w36.y w36.r w36.cap) (P33.root 1) :=
  Night6836Tree.sound w36 pick36 1 t2786 _ k36_1_14
theorem cov36_2 : PA.Covered 2 (OZ.Valid 2 w36.low w36.t w36.y w36.r w36.cap) (P33.root 2) :=
  Night6836Tree.sound w36 pick36 2 t2798 _ (by decide +kernel)
theorem cov36_3 : PA.Covered 3 (OZ.Valid 3 w36.low w36.t w36.y w36.r w36.cap) (P33.root 3) :=
  Night6836Tree.sound w36 pick36 3 t564 _ (by decide +kernel)
theorem cov36_4 : PA.Covered 4 (OZ.Valid 4 w36.low w36.t w36.y w36.r w36.cap) (P33.root 4) :=
  Night6836Tree.sound w36 pick36 4 t565 _ (by decide +kernel)
theorem cov36_5 : PA.Covered 5 (OZ.Valid 5 w36.low w36.t w36.y w36.r w36.cap) (P33.root 5) :=
  Night6836Tree.sound w36 pick36 5 t566 _ (by decide +kernel)
theorem cov36_6 : PA.Covered 6 (OZ.Valid 6 w36.low w36.t w36.y w36.r w36.cap) (P33.root 6) :=
  Night6836Tree.sound w36 pick36 6 t567 _ (by decide +kernel)
theorem cov36_7 : PA.Covered 7 (OZ.Valid 7 w36.low w36.t w36.y w36.r w36.cap) (P33.root 7) :=
  Night6836Tree.sound w36 pick36 7 t568 _ (by decide +kernel)
theorem window36 : P33.WindowCount w36 := by
  apply P33.window_count w36 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov36_1
  · exact cov36_2
  · exact cov36_3
  · exact cov36_4
  · exact cov36_5
  · exact cov36_6
  · exact cov36_7
def w37 : P33.Window := ⟨10,21,7784,7751,233933999668754588,10602,15000,5000000,81920000000⟩
def h37_0 : Height w37 := ⟨10602,15000,by decide +kernel⟩
def h37_1 : Height w37 := ⟨16290,12000,by decide +kernel⟩
def pick37 (cl : ℕ) : Height w37 := if cl<32 then (h37_0) else (h37_1)
private theorem k37_1_0 : check w37 pick37 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k37_1_1 : check w37 pick37 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k37_1_2 : check w37 pick37 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w37 pick37 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k37_1_0 k37_1_1
private theorem k37_1_3 : check w37 pick37 1 t2676 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k37_1_4 : check w37 pick37 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k37_1_5 : check w37 pick37 1 t2688 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w37 pick37 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2676 t2687 k37_1_3 k37_1_4
private theorem k37_1_6 : check w37 pick37 1 t2689 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w37 pick37 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2688 k37_1_2 k37_1_5
private theorem k37_1_7 : check w37 pick37 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k37_1_8 : check w37 pick37 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k37_1_9 : check w37 pick37 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w37 pick37 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k37_1_7 k37_1_8
private theorem k37_1_10 : check w37 pick37 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k37_1_11 : check w37 pick37 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k37_1_12 : check w37 pick37 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w37 pick37 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k37_1_10 k37_1_11
private theorem k37_1_13 : check w37 pick37 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w37 pick37 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k37_1_9 k37_1_12
private theorem k37_1_14 : check w37 pick37 1 t2690 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w37 pick37 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2689 t2461 k37_1_6 k37_1_13
theorem cov37_1 : PA.Covered 1 (OZ.Valid 1 w37.low w37.t w37.y w37.r w37.cap) (P33.root 1) :=
  Night6836Tree.sound w37 pick37 1 t2690 _ k37_1_14
theorem cov37_2 : PA.Covered 2 (OZ.Valid 2 w37.low w37.t w37.y w37.r w37.cap) (P33.root 2) :=
  Night6836Tree.sound w37 pick37 2 t2745 _ (by decide +kernel)
theorem cov37_3 : PA.Covered 3 (OZ.Valid 3 w37.low w37.t w37.y w37.r w37.cap) (P33.root 3) :=
  Night6836Tree.sound w37 pick37 3 t564 _ (by decide +kernel)
theorem cov37_4 : PA.Covered 4 (OZ.Valid 4 w37.low w37.t w37.y w37.r w37.cap) (P33.root 4) :=
  Night6836Tree.sound w37 pick37 4 t565 _ (by decide +kernel)
theorem cov37_5 : PA.Covered 5 (OZ.Valid 5 w37.low w37.t w37.y w37.r w37.cap) (P33.root 5) :=
  Night6836Tree.sound w37 pick37 5 t566 _ (by decide +kernel)
theorem cov37_6 : PA.Covered 6 (OZ.Valid 6 w37.low w37.t w37.y w37.r w37.cap) (P33.root 6) :=
  Night6836Tree.sound w37 pick37 6 t567 _ (by decide +kernel)
theorem cov37_7 : PA.Covered 7 (OZ.Valid 7 w37.low w37.t w37.y w37.r w37.cap) (P33.root 7) :=
  Night6836Tree.sound w37 pick37 7 t568 _ (by decide +kernel)
theorem window37 : P33.WindowCount w37 := by
  apply P33.window_count w37 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov37_1
  · exact cov37_2
  · exact cov37_3
  · exact cov37_4
  · exact cov37_5
  · exact cov37_6
  · exact cov37_7
def w38 : P33.Window := ⟨10,22,6821,5822,203219085084855338,11792,23000,5000000,81920000000⟩
def h38_0 : Height w38 := ⟨11792,23000,by decide +kernel⟩
def h38_1 : Height w38 := ⟨17119,19000,by decide +kernel⟩
def h38_2 : Height w38 := ⟨26561,15000,by decide +kernel⟩
def pick38 (cl : ℕ) : Height w38 := if cl<2 then (h38_0) else (if cl<100 then (h38_1) else (h38_2))
private theorem k38_1_0 : check w38 pick38 1 t2748 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k38_1_1 : check w38 pick38 1 t2764 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k38_1_2 : check w38 pick38 1 t2765 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w38 pick38 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t2748 t2764 k38_1_0 k38_1_1
private theorem k38_1_3 : check w38 pick38 1 t2805 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k38_1_4 : check w38 pick38 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k38_1_5 : check w38 pick38 1 t2806 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w38 pick38 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2805 t2687 k38_1_3 k38_1_4
private theorem k38_1_6 : check w38 pick38 1 t2807 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w38 pick38 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2765 t2806 k38_1_2 k38_1_5
private theorem k38_1_7 : check w38 pick38 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k38_1_8 : check w38 pick38 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k38_1_9 : check w38 pick38 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w38 pick38 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k38_1_7 k38_1_8
private theorem k38_1_10 : check w38 pick38 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k38_1_11 : check w38 pick38 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k38_1_12 : check w38 pick38 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w38 pick38 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k38_1_10 k38_1_11
private theorem k38_1_13 : check w38 pick38 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w38 pick38 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k38_1_9 k38_1_12
private theorem k38_1_14 : check w38 pick38 1 t2808 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w38 pick38 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2807 t2461 k38_1_6 k38_1_13
theorem cov38_1 : PA.Covered 1 (OZ.Valid 1 w38.low w38.t w38.y w38.r w38.cap) (P33.root 1) :=
  Night6836Tree.sound w38 pick38 1 t2808 _ k38_1_14
theorem cov38_2 : PA.Covered 2 (OZ.Valid 2 w38.low w38.t w38.y w38.r w38.cap) (P33.root 2) :=
  Night6836Tree.sound w38 pick38 2 t2798 _ (by decide +kernel)
theorem cov38_3 : PA.Covered 3 (OZ.Valid 3 w38.low w38.t w38.y w38.r w38.cap) (P33.root 3) :=
  Night6836Tree.sound w38 pick38 3 t564 _ (by decide +kernel)
theorem cov38_4 : PA.Covered 4 (OZ.Valid 4 w38.low w38.t w38.y w38.r w38.cap) (P33.root 4) :=
  Night6836Tree.sound w38 pick38 4 t565 _ (by decide +kernel)
theorem cov38_5 : PA.Covered 5 (OZ.Valid 5 w38.low w38.t w38.y w38.r w38.cap) (P33.root 5) :=
  Night6836Tree.sound w38 pick38 5 t566 _ (by decide +kernel)
theorem cov38_6 : PA.Covered 6 (OZ.Valid 6 w38.low w38.t w38.y w38.r w38.cap) (P33.root 6) :=
  Night6836Tree.sound w38 pick38 6 t567 _ (by decide +kernel)
theorem cov38_7 : PA.Covered 7 (OZ.Valid 7 w38.low w38.t w38.y w38.r w38.cap) (P33.root 7) :=
  Night6836Tree.sound w38 pick38 7 t568 _ (by decide +kernel)
theorem window38 : P33.WindowCount w38 := by
  apply P33.window_count w38 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov38_1
  · exact cov38_2
  · exact cov38_3
  · exact cov38_4
  · exact cov38_5
  · exact cov38_6
  · exact cov38_7
def w39 : P33.Window := ⟨10,22,7750,7715,237751152928802698,11889,15000,5000000,81920000000⟩
def h39_0 : Height w39 := ⟨11889,15000,by decide +kernel⟩
def h39_1 : Height w39 := ⟨17918,12000,by decide +kernel⟩
def pick39 (cl : ℕ) : Height w39 := if cl<40 then (h39_0) else (h39_1)
private theorem k39_1_0 : check w39 pick39 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k39_1_1 : check w39 pick39 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k39_1_2 : check w39 pick39 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w39 pick39 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k39_1_0 k39_1_1
private theorem k39_1_3 : check w39 pick39 1 t2676 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k39_1_4 : check w39 pick39 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k39_1_5 : check w39 pick39 1 t2688 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w39 pick39 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2676 t2687 k39_1_3 k39_1_4
private theorem k39_1_6 : check w39 pick39 1 t2689 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w39 pick39 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2688 k39_1_2 k39_1_5
private theorem k39_1_7 : check w39 pick39 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k39_1_8 : check w39 pick39 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k39_1_9 : check w39 pick39 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w39 pick39 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k39_1_7 k39_1_8
private theorem k39_1_10 : check w39 pick39 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k39_1_11 : check w39 pick39 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k39_1_12 : check w39 pick39 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w39 pick39 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k39_1_10 k39_1_11
private theorem k39_1_13 : check w39 pick39 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w39 pick39 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k39_1_9 k39_1_12
private theorem k39_1_14 : check w39 pick39 1 t2690 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w39 pick39 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2689 t2461 k39_1_6 k39_1_13
theorem cov39_1 : PA.Covered 1 (OZ.Valid 1 w39.low w39.t w39.y w39.r w39.cap) (P33.root 1) :=
  Night6836Tree.sound w39 pick39 1 t2690 _ k39_1_14
theorem cov39_2 : PA.Covered 2 (OZ.Valid 2 w39.low w39.t w39.y w39.r w39.cap) (P33.root 2) :=
  Night6836Tree.sound w39 pick39 2 t2745 _ (by decide +kernel)
theorem cov39_3 : PA.Covered 3 (OZ.Valid 3 w39.low w39.t w39.y w39.r w39.cap) (P33.root 3) :=
  Night6836Tree.sound w39 pick39 3 t564 _ (by decide +kernel)
theorem cov39_4 : PA.Covered 4 (OZ.Valid 4 w39.low w39.t w39.y w39.r w39.cap) (P33.root 4) :=
  Night6836Tree.sound w39 pick39 4 t565 _ (by decide +kernel)
theorem cov39_5 : PA.Covered 5 (OZ.Valid 5 w39.low w39.t w39.y w39.r w39.cap) (P33.root 5) :=
  Night6836Tree.sound w39 pick39 5 t566 _ (by decide +kernel)
theorem cov39_6 : PA.Covered 6 (OZ.Valid 6 w39.low w39.t w39.y w39.r w39.cap) (P33.root 6) :=
  Night6836Tree.sound w39 pick39 6 t567 _ (by decide +kernel)
theorem cov39_7 : PA.Covered 7 (OZ.Valid 7 w39.low w39.t w39.y w39.r w39.cap) (P33.root 7) :=
  Night6836Tree.sound w39 pick39 7 t568 _ (by decide +kernel)
theorem window39 : P33.WindowCount w39 := by
  apply P33.window_count w39 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov39_1
  · exact cov39_2
  · exact cov39_3
  · exact cov39_4
  · exact cov39_5
  · exact cov39_6
  · exact cov39_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w40 : P33.Window := ⟨10,23,7714,7680,241462488394257187,13193,15000,5000000,81920000000⟩
def h40_0 : Height w40 := ⟨13193,15000,by decide +kernel⟩
def h40_1 : Height w40 := ⟨19572,12000,by decide +kernel⟩
def pick40 (cl : ℕ) : Height w40 := if cl<51 then (h40_0) else (h40_1)
private theorem k40_1_0 : check w40 pick40 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k40_1_1 : check w40 pick40 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k40_1_2 : check w40 pick40 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w40 pick40 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k40_1_0 k40_1_1
private theorem k40_1_3 : check w40 pick40 1 t2805 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k40_1_4 : check w40 pick40 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k40_1_5 : check w40 pick40 1 t2806 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w40 pick40 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2805 t2687 k40_1_3 k40_1_4
private theorem k40_1_6 : check w40 pick40 1 t2809 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w40 pick40 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2806 k40_1_2 k40_1_5
private theorem k40_1_7 : check w40 pick40 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k40_1_8 : check w40 pick40 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k40_1_9 : check w40 pick40 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w40 pick40 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k40_1_7 k40_1_8
private theorem k40_1_10 : check w40 pick40 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k40_1_11 : check w40 pick40 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k40_1_12 : check w40 pick40 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w40 pick40 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k40_1_10 k40_1_11
private theorem k40_1_13 : check w40 pick40 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w40 pick40 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k40_1_9 k40_1_12
private theorem k40_1_14 : check w40 pick40 1 t2810 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w40 pick40 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2809 t2461 k40_1_6 k40_1_13
theorem cov40_1 : PA.Covered 1 (OZ.Valid 1 w40.low w40.t w40.y w40.r w40.cap) (P33.root 1) :=
  Night6836Tree.sound w40 pick40 1 t2810 _ k40_1_14
theorem cov40_2 : PA.Covered 2 (OZ.Valid 2 w40.low w40.t w40.y w40.r w40.cap) (P33.root 2) :=
  Night6836Tree.sound w40 pick40 2 t2745 _ (by decide +kernel)
theorem cov40_3 : PA.Covered 3 (OZ.Valid 3 w40.low w40.t w40.y w40.r w40.cap) (P33.root 3) :=
  Night6836Tree.sound w40 pick40 3 t564 _ (by decide +kernel)
theorem cov40_4 : PA.Covered 4 (OZ.Valid 4 w40.low w40.t w40.y w40.r w40.cap) (P33.root 4) :=
  Night6836Tree.sound w40 pick40 4 t565 _ (by decide +kernel)
theorem cov40_5 : PA.Covered 5 (OZ.Valid 5 w40.low w40.t w40.y w40.r w40.cap) (P33.root 5) :=
  Night6836Tree.sound w40 pick40 5 t566 _ (by decide +kernel)
theorem cov40_6 : PA.Covered 6 (OZ.Valid 6 w40.low w40.t w40.y w40.r w40.cap) (P33.root 6) :=
  Night6836Tree.sound w40 pick40 6 t567 _ (by decide +kernel)
theorem cov40_7 : PA.Covered 7 (OZ.Valid 7 w40.low w40.t w40.y w40.r w40.cap) (P33.root 7) :=
  Night6836Tree.sound w40 pick40 7 t568 _ (by decide +kernel)
theorem window40 : P33.WindowCount w40 := by
  apply P33.window_count w40 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov40_1
  · exact cov40_2
  · exact cov40_3
  · exact cov40_4
  · exact cov40_5
  · exact cov40_6
  · exact cov40_7
def w41 : P33.Window := ⟨10,24,7679,7594,239026479378608582,10719,18000,5000000,81920000000⟩
def h41_0 : Height w41 := ⟨10719,18000,by decide +kernel⟩
def h41_1 : Height w41 := ⟨14781,15000,by decide +kernel⟩
def h41_2 : Height w41 := ⟨21662,12000,by decide +kernel⟩
def pick41 (cl : ℕ) : Height w41 := if cl<2 then (h41_0) else (if cl<83 then (h41_1) else (h41_2))
private theorem k41_1_0 : check w41 pick41 1 t2748 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k41_1_1 : check w41 pick41 1 t2764 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k41_1_2 : check w41 pick41 1 t2765 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w41 pick41 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t2748 t2764 k41_1_0 k41_1_1
private theorem k41_1_3 : check w41 pick41 1 t2805 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k41_1_4 : check w41 pick41 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k41_1_5 : check w41 pick41 1 t2806 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w41 pick41 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2805 t2687 k41_1_3 k41_1_4
private theorem k41_1_6 : check w41 pick41 1 t2807 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w41 pick41 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2765 t2806 k41_1_2 k41_1_5
private theorem k41_1_7 : check w41 pick41 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k41_1_8 : check w41 pick41 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k41_1_9 : check w41 pick41 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w41 pick41 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k41_1_7 k41_1_8
private theorem k41_1_10 : check w41 pick41 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k41_1_11 : check w41 pick41 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k41_1_12 : check w41 pick41 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w41 pick41 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k41_1_10 k41_1_11
private theorem k41_1_13 : check w41 pick41 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w41 pick41 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k41_1_9 k41_1_12
private theorem k41_1_14 : check w41 pick41 1 t2808 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w41 pick41 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2807 t2461 k41_1_6 k41_1_13
theorem cov41_1 : PA.Covered 1 (OZ.Valid 1 w41.low w41.t w41.y w41.r w41.cap) (P33.root 1) :=
  Night6836Tree.sound w41 pick41 1 t2808 _ k41_1_14
theorem cov41_2 : PA.Covered 2 (OZ.Valid 2 w41.low w41.t w41.y w41.r w41.cap) (P33.root 2) :=
  Night6836Tree.sound w41 pick41 2 t2745 _ (by decide +kernel)
theorem cov41_3 : PA.Covered 3 (OZ.Valid 3 w41.low w41.t w41.y w41.r w41.cap) (P33.root 3) :=
  Night6836Tree.sound w41 pick41 3 t564 _ (by decide +kernel)
theorem cov41_4 : PA.Covered 4 (OZ.Valid 4 w41.low w41.t w41.y w41.r w41.cap) (P33.root 4) :=
  Night6836Tree.sound w41 pick41 4 t565 _ (by decide +kernel)
theorem cov41_5 : PA.Covered 5 (OZ.Valid 5 w41.low w41.t w41.y w41.r w41.cap) (P33.root 5) :=
  Night6836Tree.sound w41 pick41 5 t566 _ (by decide +kernel)
theorem cov41_6 : PA.Covered 6 (OZ.Valid 6 w41.low w41.t w41.y w41.r w41.cap) (P33.root 6) :=
  Night6836Tree.sound w41 pick41 6 t567 _ (by decide +kernel)
theorem cov41_7 : PA.Covered 7 (OZ.Valid 7 w41.low w41.t w41.y w41.r w41.cap) (P33.root 7) :=
  Night6836Tree.sound w41 pick41 7 t568 _ (by decide +kernel)
theorem window41 : P33.WindowCount w41 := by
  apply P33.window_count w41 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov41_1
  · exact cov41_2
  · exact cov41_3
  · exact cov41_4
  · exact cov41_5
  · exact cov41_6
  · exact cov41_7
def w42 : P33.Window := ⟨10,25,5824,4825,189553681395331032,20110,27000,5000000,81920000000⟩
def h42_0 : Height w42 := ⟨20110,27000,by decide +kernel⟩
def h42_1 : Height w42 := ⟨26165,23000,by decide +kernel⟩
def h42_2 : Height w42 := ⟨35937,19000,by decide +kernel⟩
def pick42 (cl : ℕ) : Height w42 := if cl<6 then (h42_0) else (if cl<117 then (h42_1) else (h42_2))
private theorem k42_1_0 : check w42 pick42 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k42_1_1 : check w42 pick42 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k42_1_2 : check w42 pick42 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w42 pick42 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k42_1_0 k42_1_1
private theorem k42_1_3 : check w42 pick42 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k42_1_4 : check w42 pick42 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k42_1_5 : check w42 pick42 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w42 pick42 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k42_1_3 k42_1_4
private theorem k42_1_6 : check w42 pick42 1 t2814 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w42 pick42 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2813 k42_1_2 k42_1_5
private theorem k42_1_7 : check w42 pick42 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k42_1_8 : check w42 pick42 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k42_1_9 : check w42 pick42 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w42 pick42 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k42_1_7 k42_1_8
private theorem k42_1_10 : check w42 pick42 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k42_1_11 : check w42 pick42 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k42_1_12 : check w42 pick42 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w42 pick42 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k42_1_10 k42_1_11
private theorem k42_1_13 : check w42 pick42 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w42 pick42 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k42_1_9 k42_1_12
private theorem k42_1_14 : check w42 pick42 1 t2815 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w42 pick42 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2814 t2461 k42_1_6 k42_1_13
theorem cov42_1 : PA.Covered 1 (OZ.Valid 1 w42.low w42.t w42.y w42.r w42.cap) (P33.root 1) :=
  Night6836Tree.sound w42 pick42 1 t2815 _ k42_1_14
theorem cov42_2 : PA.Covered 2 (OZ.Valid 2 w42.low w42.t w42.y w42.r w42.cap) (P33.root 2) :=
  Night6836Tree.sound w42 pick42 2 t2745 _ (by decide +kernel)
theorem cov42_3 : PA.Covered 3 (OZ.Valid 3 w42.low w42.t w42.y w42.r w42.cap) (P33.root 3) :=
  Night6836Tree.sound w42 pick42 3 t564 _ (by decide +kernel)
theorem cov42_4 : PA.Covered 4 (OZ.Valid 4 w42.low w42.t w42.y w42.r w42.cap) (P33.root 4) :=
  Night6836Tree.sound w42 pick42 4 t565 _ (by decide +kernel)
theorem cov42_5 : PA.Covered 5 (OZ.Valid 5 w42.low w42.t w42.y w42.r w42.cap) (P33.root 5) :=
  Night6836Tree.sound w42 pick42 5 t566 _ (by decide +kernel)
theorem cov42_6 : PA.Covered 6 (OZ.Valid 6 w42.low w42.t w42.y w42.r w42.cap) (P33.root 6) :=
  Night6836Tree.sound w42 pick42 6 t567 _ (by decide +kernel)
theorem cov42_7 : PA.Covered 7 (OZ.Valid 7 w42.low w42.t w42.y w42.r w42.cap) (P33.root 7) :=
  Night6836Tree.sound w42 pick42 7 t2134 _ (by decide +kernel)
theorem window42 : P33.WindowCount w42 := by
  apply P33.window_count w42 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov42_1
  · exact cov42_2
  · exact cov42_3
  · exact cov42_4
  · exact cov42_5
  · exact cov42_6
  · exact cov42_7
def w43 : P33.Window := ⟨10,25,7415,6466,241356885295748081,13969,21000,5000000,81920000000⟩
def h43_0 : Height w43 := ⟨13969,21000,by decide +kernel⟩
def h43_1 : Height w43 := ⟨18090,18000,by decide +kernel⟩
def h43_2 : Height w43 := ⟨24359,15000,by decide +kernel⟩
def pick43 (cl : ℕ) : Height w43 := if cl<3 then (h43_0) else (if cl<46 then (h43_1) else (h43_2))
private theorem k43_1_0 : check w43 pick43 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k43_1_1 : check w43 pick43 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k43_1_2 : check w43 pick43 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w43 pick43 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k43_1_0 k43_1_1
private theorem k43_1_3 : check w43 pick43 1 t2805 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k43_1_4 : check w43 pick43 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k43_1_5 : check w43 pick43 1 t2806 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w43 pick43 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2805 t2687 k43_1_3 k43_1_4
private theorem k43_1_6 : check w43 pick43 1 t2809 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w43 pick43 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2806 k43_1_2 k43_1_5
private theorem k43_1_7 : check w43 pick43 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k43_1_8 : check w43 pick43 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k43_1_9 : check w43 pick43 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w43 pick43 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k43_1_7 k43_1_8
private theorem k43_1_10 : check w43 pick43 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k43_1_11 : check w43 pick43 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k43_1_12 : check w43 pick43 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w43 pick43 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k43_1_10 k43_1_11
private theorem k43_1_13 : check w43 pick43 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w43 pick43 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k43_1_9 k43_1_12
private theorem k43_1_14 : check w43 pick43 1 t2810 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w43 pick43 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2809 t2461 k43_1_6 k43_1_13
theorem cov43_1 : PA.Covered 1 (OZ.Valid 1 w43.low w43.t w43.y w43.r w43.cap) (P33.root 1) :=
  Night6836Tree.sound w43 pick43 1 t2810 _ k43_1_14
theorem cov43_2 : PA.Covered 2 (OZ.Valid 2 w43.low w43.t w43.y w43.r w43.cap) (P33.root 2) :=
  Night6836Tree.sound w43 pick43 2 t2745 _ (by decide +kernel)
theorem cov43_3 : PA.Covered 3 (OZ.Valid 3 w43.low w43.t w43.y w43.r w43.cap) (P33.root 3) :=
  Night6836Tree.sound w43 pick43 3 t564 _ (by decide +kernel)
theorem cov43_4 : PA.Covered 4 (OZ.Valid 4 w43.low w43.t w43.y w43.r w43.cap) (P33.root 4) :=
  Night6836Tree.sound w43 pick43 4 t565 _ (by decide +kernel)
theorem cov43_5 : PA.Covered 5 (OZ.Valid 5 w43.low w43.t w43.y w43.r w43.cap) (P33.root 5) :=
  Night6836Tree.sound w43 pick43 5 t566 _ (by decide +kernel)
theorem cov43_6 : PA.Covered 6 (OZ.Valid 6 w43.low w43.t w43.y w43.r w43.cap) (P33.root 6) :=
  Night6836Tree.sound w43 pick43 6 t567 _ (by decide +kernel)
theorem cov43_7 : PA.Covered 7 (OZ.Valid 7 w43.low w43.t w43.y w43.r w43.cap) (P33.root 7) :=
  Night6836Tree.sound w43 pick43 7 t568 _ (by decide +kernel)
theorem window43 : P33.WindowCount w43 := by
  apply P33.window_count w43 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov43_1
  · exact cov43_2
  · exact cov43_3
  · exact cov43_4
  · exact cov43_5
  · exact cov43_6
  · exact cov43_7
def w44 : P33.Window := ⟨10,25,7643,7608,243878455521271284,11696,18000,5000000,81920000000⟩
def h44_0 : Height w44 := ⟨11696,18000,by decide +kernel⟩
def h44_1 : Height w44 := ⟨15875,15000,by decide +kernel⟩
def h44_2 : Height w44 := ⟨22995,12000,by decide +kernel⟩
def pick44 (cl : ℕ) : Height w44 := if cl<4 then (h44_0) else (if cl<100 then (h44_1) else (h44_2))
private theorem k44_1_0 : check w44 pick44 1 t2748 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k44_1_1 : check w44 pick44 1 t2764 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k44_1_2 : check w44 pick44 1 t2765 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w44 pick44 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t2748 t2764 k44_1_0 k44_1_1
private theorem k44_1_3 : check w44 pick44 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k44_1_4 : check w44 pick44 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k44_1_5 : check w44 pick44 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w44 pick44 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k44_1_3 k44_1_4
private theorem k44_1_6 : check w44 pick44 1 t2816 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w44 pick44 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2765 t2813 k44_1_2 k44_1_5
private theorem k44_1_7 : check w44 pick44 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k44_1_8 : check w44 pick44 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k44_1_9 : check w44 pick44 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w44 pick44 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k44_1_7 k44_1_8
private theorem k44_1_10 : check w44 pick44 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k44_1_11 : check w44 pick44 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k44_1_12 : check w44 pick44 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w44 pick44 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k44_1_10 k44_1_11
private theorem k44_1_13 : check w44 pick44 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w44 pick44 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k44_1_9 k44_1_12
private theorem k44_1_14 : check w44 pick44 1 t2817 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w44 pick44 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2816 t2461 k44_1_6 k44_1_13
theorem cov44_1 : PA.Covered 1 (OZ.Valid 1 w44.low w44.t w44.y w44.r w44.cap) (P33.root 1) :=
  Night6836Tree.sound w44 pick44 1 t2817 _ k44_1_14
theorem cov44_2 : PA.Covered 2 (OZ.Valid 2 w44.low w44.t w44.y w44.r w44.cap) (P33.root 2) :=
  Night6836Tree.sound w44 pick44 2 t2745 _ (by decide +kernel)
theorem cov44_3 : PA.Covered 3 (OZ.Valid 3 w44.low w44.t w44.y w44.r w44.cap) (P33.root 3) :=
  Night6836Tree.sound w44 pick44 3 t564 _ (by decide +kernel)
theorem cov44_4 : PA.Covered 4 (OZ.Valid 4 w44.low w44.t w44.y w44.r w44.cap) (P33.root 4) :=
  Night6836Tree.sound w44 pick44 4 t565 _ (by decide +kernel)
theorem cov44_5 : PA.Covered 5 (OZ.Valid 5 w44.low w44.t w44.y w44.r w44.cap) (P33.root 5) :=
  Night6836Tree.sound w44 pick44 5 t566 _ (by decide +kernel)
theorem cov44_6 : PA.Covered 6 (OZ.Valid 6 w44.low w44.t w44.y w44.r w44.cap) (P33.root 6) :=
  Night6836Tree.sound w44 pick44 6 t567 _ (by decide +kernel)
theorem cov44_7 : PA.Covered 7 (OZ.Valid 7 w44.low w44.t w44.y w44.r w44.cap) (P33.root 7) :=
  Night6836Tree.sound w44 pick44 7 t568 _ (by decide +kernel)
theorem window44 : P33.WindowCount w44 := by
  apply P33.window_count w44 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov44_1
  · exact cov44_2
  · exact cov44_3
  · exact cov44_4
  · exact cov44_5
  · exact cov44_6
  · exact cov44_7
def w45 : P33.Window := ⟨10,26,5825,4826,193217512018518538,21775,27000,5000000,81920000000⟩
def h45_0 : Height w45 := ⟨21775,27000,by decide +kernel⟩
def h45_1 : Height w45 := ⟨28028,23000,by decide +kernel⟩
def h45_2 : Height w45 := ⟨38175,19000,by decide +kernel⟩
def pick45 (cl : ℕ) : Height w45 := if cl<10 then (h45_0) else (if cl<146 then (h45_1) else (h45_2))
private theorem k45_1_0 : check w45 pick45 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k45_1_1 : check w45 pick45 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k45_1_2 : check w45 pick45 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w45 pick45 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k45_1_0 k45_1_1
private theorem k45_1_3 : check w45 pick45 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k45_1_4 : check w45 pick45 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k45_1_5 : check w45 pick45 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w45 pick45 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k45_1_3 k45_1_4
private theorem k45_1_6 : check w45 pick45 1 t2814 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w45 pick45 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2813 k45_1_2 k45_1_5
private theorem k45_1_7 : check w45 pick45 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k45_1_8 : check w45 pick45 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k45_1_9 : check w45 pick45 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w45 pick45 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k45_1_7 k45_1_8
private theorem k45_1_10 : check w45 pick45 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k45_1_11 : check w45 pick45 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k45_1_12 : check w45 pick45 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w45 pick45 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k45_1_10 k45_1_11
private theorem k45_1_13 : check w45 pick45 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w45 pick45 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k45_1_9 k45_1_12
private theorem k45_1_14 : check w45 pick45 1 t2815 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w45 pick45 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2814 t2461 k45_1_6 k45_1_13
theorem cov45_1 : PA.Covered 1 (OZ.Valid 1 w45.low w45.t w45.y w45.r w45.cap) (P33.root 1) :=
  Night6836Tree.sound w45 pick45 1 t2815 _ k45_1_14
theorem cov45_2 : PA.Covered 2 (OZ.Valid 2 w45.low w45.t w45.y w45.r w45.cap) (P33.root 2) :=
  Night6836Tree.sound w45 pick45 2 t2745 _ (by decide +kernel)
theorem cov45_3 : PA.Covered 3 (OZ.Valid 3 w45.low w45.t w45.y w45.r w45.cap) (P33.root 3) :=
  Night6836Tree.sound w45 pick45 3 t564 _ (by decide +kernel)
theorem cov45_4 : PA.Covered 4 (OZ.Valid 4 w45.low w45.t w45.y w45.r w45.cap) (P33.root 4) :=
  Night6836Tree.sound w45 pick45 4 t565 _ (by decide +kernel)
theorem cov45_5 : PA.Covered 5 (OZ.Valid 5 w45.low w45.t w45.y w45.r w45.cap) (P33.root 5) :=
  Night6836Tree.sound w45 pick45 5 t566 _ (by decide +kernel)
theorem cov45_6 : PA.Covered 6 (OZ.Valid 6 w45.low w45.t w45.y w45.r w45.cap) (P33.root 6) :=
  Night6836Tree.sound w45 pick45 6 t567 _ (by decide +kernel)
theorem cov45_7 : PA.Covered 7 (OZ.Valid 7 w45.low w45.t w45.y w45.r w45.cap) (P33.root 7) :=
  Night6836Tree.sound w45 pick45 7 t2134 _ (by decide +kernel)
theorem window45 : P33.WindowCount w45 := by
  apply P33.window_count w45 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov45_1
  · exact cov45_2
  · exact cov45_3
  · exact cov45_4
  · exact cov45_5
  · exact cov45_6
  · exact cov45_7
def w46 : P33.Window := ⟨10,26,7593,6644,243289488720924400,14120,21000,5000000,81920000000⟩
def h46_0 : Height w46 := ⟨14120,21000,by decide +kernel⟩
def h46_1 : Height w46 := ⟨18136,18000,by decide +kernel⟩
def h46_2 : Height w46 := ⟨24158,15000,by decide +kernel⟩
def h46_3 : Height w46 := ⟨36165,12000,by decide +kernel⟩
def pick46 (cl : ℕ) : Height w46 := if cl<40 then (if cl<2 then (h46_0) else (h46_1)) else (if cl<922 then (h46_2) else (h46_3))
private theorem k46_1_0 : check w46 pick46 1 t2748 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k46_1_1 : check w46 pick46 1 t2764 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k46_1_2 : check w46 pick46 1 t2765 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w46 pick46 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t2748 t2764 k46_1_0 k46_1_1
private theorem k46_1_3 : check w46 pick46 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k46_1_4 : check w46 pick46 1 t2822 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k46_1_5 : check w46 pick46 1 t2823 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w46 pick46 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2822 k46_1_3 k46_1_4
private theorem k46_1_6 : check w46 pick46 1 t2824 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w46 pick46 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2765 t2823 k46_1_2 k46_1_5
private theorem k46_1_7 : check w46 pick46 1 t2839 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k46_1_8 : check w46 pick46 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k46_1_9 : check w46 pick46 1 t2847 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w46 pick46 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t2839 t2846 k46_1_7 k46_1_8
private theorem k46_1_10 : check w46 pick46 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k46_1_11 : check w46 pick46 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k46_1_12 : check w46 pick46 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w46 pick46 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k46_1_10 k46_1_11
private theorem k46_1_13 : check w46 pick46 1 t2856 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w46 pick46 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t2847 t2855 k46_1_9 k46_1_12
private theorem k46_1_14 : check w46 pick46 1 t2857 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w46 pick46 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2824 t2856 k46_1_6 k46_1_13
theorem cov46_1 : PA.Covered 1 (OZ.Valid 1 w46.low w46.t w46.y w46.r w46.cap) (P33.root 1) :=
  Night6836Tree.sound w46 pick46 1 t2857 _ k46_1_14
private theorem k46_2_0 : check w46 pick46 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k46_2_1 : check w46 pick46 2 t2922 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k46_2_2 : check w46 pick46 2 t2923 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w46 pick46 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t2922 k46_2_0 k46_2_1
theorem cov46_2 : PA.Covered 2 (OZ.Valid 2 w46.low w46.t w46.y w46.r w46.cap) (P33.root 2) :=
  Night6836Tree.sound w46 pick46 2 t2923 _ k46_2_2
theorem cov46_3 : PA.Covered 3 (OZ.Valid 3 w46.low w46.t w46.y w46.r w46.cap) (P33.root 3) :=
  Night6836Tree.sound w46 pick46 3 t564 _ (by decide +kernel)
theorem cov46_4 : PA.Covered 4 (OZ.Valid 4 w46.low w46.t w46.y w46.r w46.cap) (P33.root 4) :=
  Night6836Tree.sound w46 pick46 4 t565 _ (by decide +kernel)
theorem cov46_5 : PA.Covered 5 (OZ.Valid 5 w46.low w46.t w46.y w46.r w46.cap) (P33.root 5) :=
  Night6836Tree.sound w46 pick46 5 t566 _ (by decide +kernel)
theorem cov46_6 : PA.Covered 6 (OZ.Valid 6 w46.low w46.t w46.y w46.r w46.cap) (P33.root 6) :=
  Night6836Tree.sound w46 pick46 6 t567 _ (by decide +kernel)
theorem cov46_7 : PA.Covered 7 (OZ.Valid 7 w46.low w46.t w46.y w46.r w46.cap) (P33.root 7) :=
  Night6836Tree.sound w46 pick46 7 t568 _ (by decide +kernel)
theorem window46 : P33.WindowCount w46 := by
  apply P33.window_count w46 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov46_1
  · exact cov46_2
  · exact cov46_3
  · exact cov46_4
  · exact cov46_5
  · exact cov46_6
  · exact cov46_7
def w47 : P33.Window := ⟨10,26,7607,7572,244382016373096067,12893,18000,5000000,81920000000⟩
def h47_0 : Height w47 := ⟨12893,18000,by decide +kernel⟩
def h47_1 : Height w47 := ⟨17249,15000,by decide +kernel⟩
def h47_2 : Height w47 := ⟨24760,12000,by decide +kernel⟩
def pick47 (cl : ℕ) : Height w47 := if cl<5 then (h47_0) else (if cl<135 then (h47_1) else (h47_2))
private theorem k47_1_0 : check w47 pick47 1 t2748 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k47_1_1 : check w47 pick47 1 t2764 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k47_1_2 : check w47 pick47 1 t2765 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w47 pick47 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t2748 t2764 k47_1_0 k47_1_1
private theorem k47_1_3 : check w47 pick47 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k47_1_4 : check w47 pick47 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k47_1_5 : check w47 pick47 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w47 pick47 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k47_1_3 k47_1_4
private theorem k47_1_6 : check w47 pick47 1 t2816 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w47 pick47 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2765 t2813 k47_1_2 k47_1_5
private theorem k47_1_7 : check w47 pick47 1 t2925 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k47_1_8 : check w47 pick47 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k47_1_9 : check w47 pick47 1 t2926 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w47 pick47 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t2925 t2846 k47_1_7 k47_1_8
private theorem k47_1_10 : check w47 pick47 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k47_1_11 : check w47 pick47 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k47_1_12 : check w47 pick47 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w47 pick47 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k47_1_10 k47_1_11
private theorem k47_1_13 : check w47 pick47 1 t2927 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w47 pick47 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t2926 t2855 k47_1_9 k47_1_12
private theorem k47_1_14 : check w47 pick47 1 t2928 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w47 pick47 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2816 t2927 k47_1_6 k47_1_13
theorem cov47_1 : PA.Covered 1 (OZ.Valid 1 w47.low w47.t w47.y w47.r w47.cap) (P33.root 1) :=
  Night6836Tree.sound w47 pick47 1 t2928 _ k47_1_14
private theorem k47_2_0 : check w47 pick47 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k47_2_1 : check w47 pick47 2 t2922 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k47_2_2 : check w47 pick47 2 t2923 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w47 pick47 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t2922 k47_2_0 k47_2_1
theorem cov47_2 : PA.Covered 2 (OZ.Valid 2 w47.low w47.t w47.y w47.r w47.cap) (P33.root 2) :=
  Night6836Tree.sound w47 pick47 2 t2923 _ k47_2_2
theorem cov47_3 : PA.Covered 3 (OZ.Valid 3 w47.low w47.t w47.y w47.r w47.cap) (P33.root 3) :=
  Night6836Tree.sound w47 pick47 3 t564 _ (by decide +kernel)
theorem cov47_4 : PA.Covered 4 (OZ.Valid 4 w47.low w47.t w47.y w47.r w47.cap) (P33.root 4) :=
  Night6836Tree.sound w47 pick47 4 t565 _ (by decide +kernel)
theorem cov47_5 : PA.Covered 5 (OZ.Valid 5 w47.low w47.t w47.y w47.r w47.cap) (P33.root 5) :=
  Night6836Tree.sound w47 pick47 5 t566 _ (by decide +kernel)
theorem cov47_6 : PA.Covered 6 (OZ.Valid 6 w47.low w47.t w47.y w47.r w47.cap) (P33.root 6) :=
  Night6836Tree.sound w47 pick47 6 t567 _ (by decide +kernel)
theorem cov47_7 : PA.Covered 7 (OZ.Valid 7 w47.low w47.t w47.y w47.r w47.cap) (P33.root 7) :=
  Night6836Tree.sound w47 pick47 7 t568 _ (by decide +kernel)
theorem window47 : P33.WindowCount w47 := by
  apply P33.window_count w47 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov47_1
  · exact cov47_2
  · exact cov47_3
  · exact cov47_4
  · exact cov47_5
  · exact cov47_6
  · exact cov47_7
def w48 : P33.Window := ⟨10,27,7571,7535,244354328871052226,14112,18000,5000000,81920000000⟩
def h48_0 : Height w48 := ⟨14112,18000,by decide +kernel⟩
def h48_1 : Height w48 := ⟨18653,15000,by decide +kernel⟩
def h48_2 : Height w48 := ⟨26571,12000,by decide +kernel⟩
def pick48 (cl : ℕ) : Height w48 := if cl<6 then (h48_0) else (if cl<170 then (h48_1) else (h48_2))
private theorem k48_1_0 : check w48 pick48 1 t2952 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k48_1_1 : check w48 pick48 1 t2969 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k48_1_2 : check w48 pick48 1 t2970 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w48 pick48 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2952 t2969 k48_1_0 k48_1_1
private theorem k48_1_3 : check w48 pick48 1 t2988 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k48_1_4 : check w48 pick48 1 t3003 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k48_1_5 : check w48 pick48 1 t3004 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w48 pick48 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2988 t3003 k48_1_3 k48_1_4
private theorem k48_1_6 : check w48 pick48 1 t3005 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w48 pick48 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2970 t3004 k48_1_2 k48_1_5
private theorem k48_1_7 : check w48 pick48 1 t2839 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k48_1_8 : check w48 pick48 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k48_1_9 : check w48 pick48 1 t2847 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w48 pick48 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t2839 t2846 k48_1_7 k48_1_8
private theorem k48_1_10 : check w48 pick48 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k48_1_11 : check w48 pick48 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k48_1_12 : check w48 pick48 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w48 pick48 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k48_1_10 k48_1_11
private theorem k48_1_13 : check w48 pick48 1 t2856 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w48 pick48 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t2847 t2855 k48_1_9 k48_1_12
private theorem k48_1_14 : check w48 pick48 1 t3006 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w48 pick48 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3005 t2856 k48_1_6 k48_1_13
theorem cov48_1 : PA.Covered 1 (OZ.Valid 1 w48.low w48.t w48.y w48.r w48.cap) (P33.root 1) :=
  Night6836Tree.sound w48 pick48 1 t3006 _ k48_1_14
private theorem k48_2_0 : check w48 pick48 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k48_2_1 : check w48 pick48 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k48_2_2 : check w48 pick48 2 t3027 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w48 pick48 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t3026 k48_2_0 k48_2_1
theorem cov48_2 : PA.Covered 2 (OZ.Valid 2 w48.low w48.t w48.y w48.r w48.cap) (P33.root 2) :=
  Night6836Tree.sound w48 pick48 2 t3027 _ k48_2_2
theorem cov48_3 : PA.Covered 3 (OZ.Valid 3 w48.low w48.t w48.y w48.r w48.cap) (P33.root 3) :=
  Night6836Tree.sound w48 pick48 3 t564 _ (by decide +kernel)
theorem cov48_4 : PA.Covered 4 (OZ.Valid 4 w48.low w48.t w48.y w48.r w48.cap) (P33.root 4) :=
  Night6836Tree.sound w48 pick48 4 t565 _ (by decide +kernel)
theorem cov48_5 : PA.Covered 5 (OZ.Valid 5 w48.low w48.t w48.y w48.r w48.cap) (P33.root 5) :=
  Night6836Tree.sound w48 pick48 5 t566 _ (by decide +kernel)
theorem cov48_6 : PA.Covered 6 (OZ.Valid 6 w48.low w48.t w48.y w48.r w48.cap) (P33.root 6) :=
  Night6836Tree.sound w48 pick48 6 t567 _ (by decide +kernel)
theorem cov48_7 : PA.Covered 7 (OZ.Valid 7 w48.low w48.t w48.y w48.r w48.cap) (P33.root 7) :=
  Night6836Tree.sound w48 pick48 7 t568 _ (by decide +kernel)
theorem window48 : P33.WindowCount w48 := by
  apply P33.window_count w48 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov48_1
  · exact cov48_2
  · exact cov48_3
  · exact cov48_4
  · exact cov48_5
  · exact cov48_6
  · exact cov48_7
def w49 : P33.Window := ⟨10,28,5827,4828,200547051623061099,25102,27000,5000000,81920000000⟩
def h49_0 : Height w49 := ⟨25102,27000,by decide +kernel⟩
def h49_1 : Height w49 := ⟨31748,23000,by decide +kernel⟩
def h49_2 : Height w49 := ⟨42641,19000,by decide +kernel⟩
def pick49 (cl : ℕ) : Height w49 := if cl<14 then (h49_0) else (if cl<203 then (h49_1) else (h49_2))
private theorem k49_1_0 : check w49 pick49 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k49_1_1 : check w49 pick49 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k49_1_2 : check w49 pick49 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w49 pick49 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k49_1_0 k49_1_1
private theorem k49_1_3 : check w49 pick49 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k49_1_4 : check w49 pick49 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k49_1_5 : check w49 pick49 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w49 pick49 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k49_1_3 k49_1_4
private theorem k49_1_6 : check w49 pick49 1 t2814 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w49 pick49 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2813 k49_1_2 k49_1_5
private theorem k49_1_7 : check w49 pick49 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k49_1_8 : check w49 pick49 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k49_1_9 : check w49 pick49 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w49 pick49 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k49_1_7 k49_1_8
private theorem k49_1_10 : check w49 pick49 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k49_1_11 : check w49 pick49 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k49_1_12 : check w49 pick49 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w49 pick49 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k49_1_10 k49_1_11
private theorem k49_1_13 : check w49 pick49 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w49 pick49 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k49_1_9 k49_1_12
private theorem k49_1_14 : check w49 pick49 1 t2815 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w49 pick49 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2814 t2461 k49_1_6 k49_1_13
theorem cov49_1 : PA.Covered 1 (OZ.Valid 1 w49.low w49.t w49.y w49.r w49.cap) (P33.root 1) :=
  Night6836Tree.sound w49 pick49 1 t2815 _ k49_1_14
theorem cov49_2 : PA.Covered 2 (OZ.Valid 2 w49.low w49.t w49.y w49.r w49.cap) (P33.root 2) :=
  Night6836Tree.sound w49 pick49 2 t2745 _ (by decide +kernel)
theorem cov49_3 : PA.Covered 3 (OZ.Valid 3 w49.low w49.t w49.y w49.r w49.cap) (P33.root 3) :=
  Night6836Tree.sound w49 pick49 3 t564 _ (by decide +kernel)
theorem cov49_4 : PA.Covered 4 (OZ.Valid 4 w49.low w49.t w49.y w49.r w49.cap) (P33.root 4) :=
  Night6836Tree.sound w49 pick49 4 t565 _ (by decide +kernel)
theorem cov49_5 : PA.Covered 5 (OZ.Valid 5 w49.low w49.t w49.y w49.r w49.cap) (P33.root 5) :=
  Night6836Tree.sound w49 pick49 5 t566 _ (by decide +kernel)
theorem cov49_6 : PA.Covered 6 (OZ.Valid 6 w49.low w49.t w49.y w49.r w49.cap) (P33.root 6) :=
  Night6836Tree.sound w49 pick49 6 t567 _ (by decide +kernel)
theorem cov49_7 : PA.Covered 7 (OZ.Valid 7 w49.low w49.t w49.y w49.r w49.cap) (P33.root 7) :=
  Night6836Tree.sound w49 pick49 7 t2134 _ (by decide +kernel)
theorem window49 : P33.WindowCount w49 := by
  apply P33.window_count w49 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov49_1
  · exact cov49_2
  · exact cov49_3
  · exact cov49_4
  · exact cov49_5
  · exact cov49_6
  · exact cov49_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w50 : P33.Window := ⟨10,28,7534,7497,239780942233432061,15355,18000,5000000,81920000000⟩
def h50_0 : Height w50 := ⟨15355,18000,by decide +kernel⟩
def h50_1 : Height w50 := ⟨20088,15000,by decide +kernel⟩
def h50_2 : Height w50 := ⟨28431,12000,by decide +kernel⟩
def pick50 (cl : ℕ) : Height w50 := if cl<10 then (h50_0) else (if cl<215 then (h50_1) else (h50_2))
private theorem k50_1_0 : check w50 pick50 1 t3036 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k50_1_1 : check w50 pick50 1 t2969 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k50_1_2 : check w50 pick50 1 t3037 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w50 pick50 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3036 t2969 k50_1_0 k50_1_1
private theorem k50_1_3 : check w50 pick50 1 t2988 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k50_1_4 : check w50 pick50 1 t3003 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k50_1_5 : check w50 pick50 1 t3004 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w50 pick50 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2988 t3003 k50_1_3 k50_1_4
private theorem k50_1_6 : check w50 pick50 1 t3038 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w50 pick50 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3037 t3004 k50_1_2 k50_1_5
private theorem k50_1_7 : check w50 pick50 1 t2839 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k50_1_8 : check w50 pick50 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k50_1_9 : check w50 pick50 1 t2847 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w50 pick50 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t2839 t2846 k50_1_7 k50_1_8
private theorem k50_1_10 : check w50 pick50 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k50_1_11 : check w50 pick50 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k50_1_12 : check w50 pick50 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w50 pick50 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k50_1_10 k50_1_11
private theorem k50_1_13 : check w50 pick50 1 t2856 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w50 pick50 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t2847 t2855 k50_1_9 k50_1_12
private theorem k50_1_14 : check w50 pick50 1 t3039 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w50 pick50 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3038 t2856 k50_1_6 k50_1_13
theorem cov50_1 : PA.Covered 1 (OZ.Valid 1 w50.low w50.t w50.y w50.r w50.cap) (P33.root 1) :=
  Night6836Tree.sound w50 pick50 1 t3039 _ k50_1_14
private theorem k50_2_0 : check w50 pick50 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k50_2_1 : check w50 pick50 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k50_2_2 : check w50 pick50 2 t3027 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w50 pick50 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t3026 k50_2_0 k50_2_1
theorem cov50_2 : PA.Covered 2 (OZ.Valid 2 w50.low w50.t w50.y w50.r w50.cap) (P33.root 2) :=
  Night6836Tree.sound w50 pick50 2 t3027 _ k50_2_2
theorem cov50_3 : PA.Covered 3 (OZ.Valid 3 w50.low w50.t w50.y w50.r w50.cap) (P33.root 3) :=
  Night6836Tree.sound w50 pick50 3 t564 _ (by decide +kernel)
theorem cov50_4 : PA.Covered 4 (OZ.Valid 4 w50.low w50.t w50.y w50.r w50.cap) (P33.root 4) :=
  Night6836Tree.sound w50 pick50 4 t565 _ (by decide +kernel)
theorem cov50_5 : PA.Covered 5 (OZ.Valid 5 w50.low w50.t w50.y w50.r w50.cap) (P33.root 5) :=
  Night6836Tree.sound w50 pick50 5 t566 _ (by decide +kernel)
theorem cov50_6 : PA.Covered 6 (OZ.Valid 6 w50.low w50.t w50.y w50.r w50.cap) (P33.root 6) :=
  Night6836Tree.sound w50 pick50 6 t567 _ (by decide +kernel)
theorem cov50_7 : PA.Covered 7 (OZ.Valid 7 w50.low w50.t w50.y w50.r w50.cap) (P33.root 7) :=
  Night6836Tree.sound w50 pick50 7 t568 _ (by decide +kernel)
theorem window50 : P33.WindowCount w50 := by
  apply P33.window_count w50 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov50_1
  · exact cov50_2
  · exact cov50_3
  · exact cov50_4
  · exact cov50_5
  · exact cov50_6
  · exact cov50_7
def w51 : P33.Window := ⟨10,29,7496,7455,244618629508411898,16641,18000,5000000,81920000000⟩
def h51_0 : Height w51 := ⟨16641,18000,by decide +kernel⟩
def h51_1 : Height w51 := ⟨21578,15000,by decide +kernel⟩
def h51_2 : Height w51 := ⟨30377,12000,by decide +kernel⟩
def pick51 (cl : ℕ) : Height w51 := if cl<12 then (h51_0) else (if cl<267 then (h51_1) else (h51_2))
private theorem k51_1_0 : check w51 pick51 1 t3036 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k51_1_1 : check w51 pick51 1 t2969 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k51_1_2 : check w51 pick51 1 t3037 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w51 pick51 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3036 t2969 k51_1_0 k51_1_1
private theorem k51_1_3 : check w51 pick51 1 t2988 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k51_1_4 : check w51 pick51 1 t3003 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k51_1_5 : check w51 pick51 1 t3004 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w51 pick51 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2988 t3003 k51_1_3 k51_1_4
private theorem k51_1_6 : check w51 pick51 1 t3038 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w51 pick51 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3037 t3004 k51_1_2 k51_1_5
private theorem k51_1_7 : check w51 pick51 1 t2839 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k51_1_8 : check w51 pick51 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k51_1_9 : check w51 pick51 1 t2847 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w51 pick51 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t2839 t2846 k51_1_7 k51_1_8
private theorem k51_1_10 : check w51 pick51 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k51_1_11 : check w51 pick51 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k51_1_12 : check w51 pick51 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w51 pick51 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k51_1_10 k51_1_11
private theorem k51_1_13 : check w51 pick51 1 t2856 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w51 pick51 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t2847 t2855 k51_1_9 k51_1_12
private theorem k51_1_14 : check w51 pick51 1 t3039 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w51 pick51 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3038 t2856 k51_1_6 k51_1_13
theorem cov51_1 : PA.Covered 1 (OZ.Valid 1 w51.low w51.t w51.y w51.r w51.cap) (P33.root 1) :=
  Night6836Tree.sound w51 pick51 1 t3039 _ k51_1_14
private theorem k51_2_0 : check w51 pick51 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k51_2_1 : check w51 pick51 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k51_2_2 : check w51 pick51 2 t3027 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w51 pick51 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t3026 k51_2_0 k51_2_1
theorem cov51_2 : PA.Covered 2 (OZ.Valid 2 w51.low w51.t w51.y w51.r w51.cap) (P33.root 2) :=
  Night6836Tree.sound w51 pick51 2 t3027 _ k51_2_2
theorem cov51_3 : PA.Covered 3 (OZ.Valid 3 w51.low w51.t w51.y w51.r w51.cap) (P33.root 3) :=
  Night6836Tree.sound w51 pick51 3 t564 _ (by decide +kernel)
theorem cov51_4 : PA.Covered 4 (OZ.Valid 4 w51.low w51.t w51.y w51.r w51.cap) (P33.root 4) :=
  Night6836Tree.sound w51 pick51 4 t565 _ (by decide +kernel)
theorem cov51_5 : PA.Covered 5 (OZ.Valid 5 w51.low w51.t w51.y w51.r w51.cap) (P33.root 5) :=
  Night6836Tree.sound w51 pick51 5 t566 _ (by decide +kernel)
theorem cov51_6 : PA.Covered 6 (OZ.Valid 6 w51.low w51.t w51.y w51.r w51.cap) (P33.root 6) :=
  Night6836Tree.sound w51 pick51 6 t567 _ (by decide +kernel)
theorem cov51_7 : PA.Covered 7 (OZ.Valid 7 w51.low w51.t w51.y w51.r w51.cap) (P33.root 7) :=
  Night6836Tree.sound w51 pick51 7 t568 _ (by decide +kernel)
theorem window51 : P33.WindowCount w51 := by
  apply P33.window_count w51 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov51_1
  · exact cov51_2
  · exact cov51_3
  · exact cov51_4
  · exact cov51_5
  · exact cov51_6
  · exact cov51_7
def w52 : P33.Window := ⟨10,30,5429,4430,195411550752329680,28825,31000,5000000,81920000000⟩
def h52_0 : Height w52 := ⟨28825,31000,by decide +kernel⟩
def h52_1 : Height w52 := ⟨34898,27000,by decide +kernel⟩
def h52_2 : Height w52 := ⟨43722,23000,by decide +kernel⟩
def h52_3 : Height w52 := ⟨59488,19000,by decide +kernel⟩
def pick52 (cl : ℕ) : Height w52 := if cl<70 then (if cl<6 then (h52_0) else (h52_1)) else (if cl<922 then (h52_2) else (h52_3))
private theorem k52_1_0 : check w52 pick52 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k52_1_1 : check w52 pick52 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k52_1_2 : check w52 pick52 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w52 pick52 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k52_1_0 k52_1_1
private theorem k52_1_3 : check w52 pick52 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k52_1_4 : check w52 pick52 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k52_1_5 : check w52 pick52 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w52 pick52 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k52_1_3 k52_1_4
private theorem k52_1_6 : check w52 pick52 1 t2814 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w52 pick52 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2813 k52_1_2 k52_1_5
private theorem k52_1_7 : check w52 pick52 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k52_1_8 : check w52 pick52 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k52_1_9 : check w52 pick52 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w52 pick52 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k52_1_7 k52_1_8
private theorem k52_1_10 : check w52 pick52 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k52_1_11 : check w52 pick52 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k52_1_12 : check w52 pick52 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w52 pick52 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k52_1_10 k52_1_11
private theorem k52_1_13 : check w52 pick52 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w52 pick52 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k52_1_9 k52_1_12
private theorem k52_1_14 : check w52 pick52 1 t2815 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w52 pick52 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2814 t2461 k52_1_6 k52_1_13
theorem cov52_1 : PA.Covered 1 (OZ.Valid 1 w52.low w52.t w52.y w52.r w52.cap) (P33.root 1) :=
  Night6836Tree.sound w52 pick52 1 t2815 _ k52_1_14
theorem cov52_2 : PA.Covered 2 (OZ.Valid 2 w52.low w52.t w52.y w52.r w52.cap) (P33.root 2) :=
  Night6836Tree.sound w52 pick52 2 t2745 _ (by decide +kernel)
theorem cov52_3 : PA.Covered 3 (OZ.Valid 3 w52.low w52.t w52.y w52.r w52.cap) (P33.root 3) :=
  Night6836Tree.sound w52 pick52 3 t564 _ (by decide +kernel)
theorem cov52_4 : PA.Covered 4 (OZ.Valid 4 w52.low w52.t w52.y w52.r w52.cap) (P33.root 4) :=
  Night6836Tree.sound w52 pick52 4 t565 _ (by decide +kernel)
theorem cov52_5 : PA.Covered 5 (OZ.Valid 5 w52.low w52.t w52.y w52.r w52.cap) (P33.root 5) :=
  Night6836Tree.sound w52 pick52 5 t566 _ (by decide +kernel)
theorem cov52_6 : PA.Covered 6 (OZ.Valid 6 w52.low w52.t w52.y w52.r w52.cap) (P33.root 6) :=
  Night6836Tree.sound w52 pick52 6 t567 _ (by decide +kernel)
theorem cov52_7 : PA.Covered 7 (OZ.Valid 7 w52.low w52.t w52.y w52.r w52.cap) (P33.root 7) :=
  Night6836Tree.sound w52 pick52 7 t2134 _ (by decide +kernel)
theorem window52 : P33.WindowCount w52 := by
  apply P33.window_count w52 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov52_1
  · exact cov52_2
  · exact cov52_3
  · exact cov52_4
  · exact cov52_5
  · exact cov52_6
  · exact cov52_7
def w53 : P33.Window := ⟨10,30,7454,7233,237313251710821708,19035,18000,5000000,81920000000⟩
def h53_0 : Height w53 := ⟨19035,18000,by decide +kernel⟩
def h53_1 : Height w53 := ⟨24504,15000,by decide +kernel⟩
def h53_2 : Height w53 := ⟨34604,12000,by decide +kernel⟩
def pick53 (cl : ℕ) : Height w53 := if cl<32 then (h53_0) else (if cl<531 then (h53_1) else (h53_2))
private theorem k53_1_0 : check w53 pick53 1 t3036 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k53_1_1 : check w53 pick53 1 t2969 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k53_1_2 : check w53 pick53 1 t3037 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w53 pick53 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3036 t2969 k53_1_0 k53_1_1
private theorem k53_1_3 : check w53 pick53 1 t2988 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k53_1_4 : check w53 pick53 1 t3003 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k53_1_5 : check w53 pick53 1 t3004 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w53 pick53 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2988 t3003 k53_1_3 k53_1_4
private theorem k53_1_6 : check w53 pick53 1 t3038 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w53 pick53 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3037 t3004 k53_1_2 k53_1_5
private theorem k53_1_7 : check w53 pick53 1 t2839 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k53_1_8 : check w53 pick53 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k53_1_9 : check w53 pick53 1 t2847 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w53 pick53 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t2839 t2846 k53_1_7 k53_1_8
private theorem k53_1_10 : check w53 pick53 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k53_1_11 : check w53 pick53 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k53_1_12 : check w53 pick53 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w53 pick53 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k53_1_10 k53_1_11
private theorem k53_1_13 : check w53 pick53 1 t2856 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w53 pick53 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t2847 t2855 k53_1_9 k53_1_12
private theorem k53_1_14 : check w53 pick53 1 t3039 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w53 pick53 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3038 t2856 k53_1_6 k53_1_13
theorem cov53_1 : PA.Covered 1 (OZ.Valid 1 w53.low w53.t w53.y w53.r w53.cap) (P33.root 1) :=
  Night6836Tree.sound w53 pick53 1 t3039 _ k53_1_14
private theorem k53_2_0 : check w53 pick53 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k53_2_1 : check w53 pick53 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k53_2_2 : check w53 pick53 2 t3059 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w53 pick53 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3026 k53_2_0 k53_2_1
theorem cov53_2 : PA.Covered 2 (OZ.Valid 2 w53.low w53.t w53.y w53.r w53.cap) (P33.root 2) :=
  Night6836Tree.sound w53 pick53 2 t3059 _ k53_2_2
theorem cov53_3 : PA.Covered 3 (OZ.Valid 3 w53.low w53.t w53.y w53.r w53.cap) (P33.root 3) :=
  Night6836Tree.sound w53 pick53 3 t564 _ (by decide +kernel)
theorem cov53_4 : PA.Covered 4 (OZ.Valid 4 w53.low w53.t w53.y w53.r w53.cap) (P33.root 4) :=
  Night6836Tree.sound w53 pick53 4 t565 _ (by decide +kernel)
theorem cov53_5 : PA.Covered 5 (OZ.Valid 5 w53.low w53.t w53.y w53.r w53.cap) (P33.root 5) :=
  Night6836Tree.sound w53 pick53 5 t566 _ (by decide +kernel)
theorem cov53_6 : PA.Covered 6 (OZ.Valid 6 w53.low w53.t w53.y w53.r w53.cap) (P33.root 6) :=
  Night6836Tree.sound w53 pick53 6 t567 _ (by decide +kernel)
theorem cov53_7 : PA.Covered 7 (OZ.Valid 7 w53.low w53.t w53.y w53.r w53.cap) (P33.root 7) :=
  Night6836Tree.sound w53 pick53 7 t568 _ (by decide +kernel)
theorem window53 : P33.WindowCount w53 := by
  apply P33.window_count w53 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov53_1
  · exact cov53_2
  · exact cov53_3
  · exact cov53_4
  · exact cov53_5
  · exact cov53_6
  · exact cov53_7
def w54 : P33.Window := ⟨10,31,5430,4431,199845686727169689,30578,31000,5000000,81920000000⟩
def h54_0 : Height w54 := ⟨30578,31000,by decide +kernel⟩
def h54_1 : Height w54 := ⟨36808,27000,by decide +kernel⟩
def h54_2 : Height w54 := ⟨45894,23000,by decide +kernel⟩
def h54_3 : Height w54 := ⟨62181,19000,by decide +kernel⟩
def pick54 (cl : ℕ) : Height w54 := if cl<83 then (if cl<6 then (h54_0) else (h54_1)) else (if cl<922 then (h54_2) else (h54_3))
private theorem k54_1_0 : check w54 pick54 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k54_1_1 : check w54 pick54 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k54_1_2 : check w54 pick54 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w54 pick54 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k54_1_0 k54_1_1
private theorem k54_1_3 : check w54 pick54 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k54_1_4 : check w54 pick54 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k54_1_5 : check w54 pick54 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w54 pick54 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k54_1_3 k54_1_4
private theorem k54_1_6 : check w54 pick54 1 t2814 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w54 pick54 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2813 k54_1_2 k54_1_5
private theorem k54_1_7 : check w54 pick54 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k54_1_8 : check w54 pick54 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k54_1_9 : check w54 pick54 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w54 pick54 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k54_1_7 k54_1_8
private theorem k54_1_10 : check w54 pick54 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k54_1_11 : check w54 pick54 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k54_1_12 : check w54 pick54 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w54 pick54 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k54_1_10 k54_1_11
private theorem k54_1_13 : check w54 pick54 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w54 pick54 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k54_1_9 k54_1_12
private theorem k54_1_14 : check w54 pick54 1 t2815 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w54 pick54 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2814 t2461 k54_1_6 k54_1_13
theorem cov54_1 : PA.Covered 1 (OZ.Valid 1 w54.low w54.t w54.y w54.r w54.cap) (P33.root 1) :=
  Night6836Tree.sound w54 pick54 1 t2815 _ k54_1_14
theorem cov54_2 : PA.Covered 2 (OZ.Valid 2 w54.low w54.t w54.y w54.r w54.cap) (P33.root 2) :=
  Night6836Tree.sound w54 pick54 2 t2745 _ (by decide +kernel)
theorem cov54_3 : PA.Covered 3 (OZ.Valid 3 w54.low w54.t w54.y w54.r w54.cap) (P33.root 3) :=
  Night6836Tree.sound w54 pick54 3 t564 _ (by decide +kernel)
theorem cov54_4 : PA.Covered 4 (OZ.Valid 4 w54.low w54.t w54.y w54.r w54.cap) (P33.root 4) :=
  Night6836Tree.sound w54 pick54 4 t565 _ (by decide +kernel)
theorem cov54_5 : PA.Covered 5 (OZ.Valid 5 w54.low w54.t w54.y w54.r w54.cap) (P33.root 5) :=
  Night6836Tree.sound w54 pick54 5 t566 _ (by decide +kernel)
theorem cov54_6 : PA.Covered 6 (OZ.Valid 6 w54.low w54.t w54.y w54.r w54.cap) (P33.root 6) :=
  Night6836Tree.sound w54 pick54 6 t567 _ (by decide +kernel)
theorem cov54_7 : PA.Covered 7 (OZ.Valid 7 w54.low w54.t w54.y w54.r w54.cap) (P33.root 7) :=
  Night6836Tree.sound w54 pick54 7 t2134 _ (by decide +kernel)
theorem window54 : P33.WindowCount w54 := by
  apply P33.window_count w54 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov54_1
  · exact cov54_2
  · exact cov54_3
  · exact cov54_4
  · exact cov54_5
  · exact cov54_6
  · exact cov54_7
def w55 : P33.Window := ⟨10,31,7412,7370,242148475423383968,19287,18000,5000000,81920000000⟩
def h55_0 : Height w55 := ⟨19287,18000,by decide +kernel⟩
def h55_1 : Height w55 := ⟨24656,15000,by decide +kernel⟩
def h55_2 : Height w55 := ⟨34430,12000,by decide +kernel⟩
def pick55 (cl : ℕ) : Height w55 := if cl<32 then (h55_0) else (if cl<389 then (h55_1) else (h55_2))
private theorem k55_1_0 : check w55 pick55 1 t3036 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k55_1_1 : check w55 pick55 1 t2969 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k55_1_2 : check w55 pick55 1 t3037 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w55 pick55 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3036 t2969 k55_1_0 k55_1_1
private theorem k55_1_3 : check w55 pick55 1 t2988 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k55_1_4 : check w55 pick55 1 t3003 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k55_1_5 : check w55 pick55 1 t3004 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w55 pick55 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2988 t3003 k55_1_3 k55_1_4
private theorem k55_1_6 : check w55 pick55 1 t3038 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w55 pick55 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3037 t3004 k55_1_2 k55_1_5
private theorem k55_1_7 : check w55 pick55 1 t2839 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k55_1_8 : check w55 pick55 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k55_1_9 : check w55 pick55 1 t2847 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w55 pick55 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t2839 t2846 k55_1_7 k55_1_8
private theorem k55_1_10 : check w55 pick55 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k55_1_11 : check w55 pick55 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k55_1_12 : check w55 pick55 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w55 pick55 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k55_1_10 k55_1_11
private theorem k55_1_13 : check w55 pick55 1 t2856 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w55 pick55 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t2847 t2855 k55_1_9 k55_1_12
private theorem k55_1_14 : check w55 pick55 1 t3039 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w55 pick55 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3038 t2856 k55_1_6 k55_1_13
theorem cov55_1 : PA.Covered 1 (OZ.Valid 1 w55.low w55.t w55.y w55.r w55.cap) (P33.root 1) :=
  Night6836Tree.sound w55 pick55 1 t3039 _ k55_1_14
private theorem k55_2_0 : check w55 pick55 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k55_2_1 : check w55 pick55 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k55_2_2 : check w55 pick55 2 t3059 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w55 pick55 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3026 k55_2_0 k55_2_1
theorem cov55_2 : PA.Covered 2 (OZ.Valid 2 w55.low w55.t w55.y w55.r w55.cap) (P33.root 2) :=
  Night6836Tree.sound w55 pick55 2 t3059 _ k55_2_2
theorem cov55_3 : PA.Covered 3 (OZ.Valid 3 w55.low w55.t w55.y w55.r w55.cap) (P33.root 3) :=
  Night6836Tree.sound w55 pick55 3 t564 _ (by decide +kernel)
theorem cov55_4 : PA.Covered 4 (OZ.Valid 4 w55.low w55.t w55.y w55.r w55.cap) (P33.root 4) :=
  Night6836Tree.sound w55 pick55 4 t565 _ (by decide +kernel)
theorem cov55_5 : PA.Covered 5 (OZ.Valid 5 w55.low w55.t w55.y w55.r w55.cap) (P33.root 5) :=
  Night6836Tree.sound w55 pick55 5 t566 _ (by decide +kernel)
theorem cov55_6 : PA.Covered 6 (OZ.Valid 6 w55.low w55.t w55.y w55.r w55.cap) (P33.root 6) :=
  Night6836Tree.sound w55 pick55 6 t567 _ (by decide +kernel)
theorem cov55_7 : PA.Covered 7 (OZ.Valid 7 w55.low w55.t w55.y w55.r w55.cap) (P33.root 7) :=
  Night6836Tree.sound w55 pick55 7 t568 _ (by decide +kernel)
theorem window55 : P33.WindowCount w55 := by
  apply P33.window_count w55 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov55_1
  · exact cov55_2
  · exact cov55_3
  · exact cov55_4
  · exact cov55_5
  · exact cov55_6
  · exact cov55_7
def w56 : P33.Window := ⟨10,32,7369,7239,245196709350484237,17275,21000,5000000,81920000000⟩
def h56_0 : Height w56 := ⟨17275,21000,by decide +kernel⟩
def h56_1 : Height w56 := ⟨21234,18000,by decide +kernel⟩
def h56_2 : Height w56 := ⟨27004,15000,by decide +kernel⟩
def h56_3 : Height w56 := ⟨37748,12000,by decide +kernel⟩
def pick56 (cl : ℕ) : Height w56 := if cl<32 then (if cl<2 then (h56_0) else (h56_1)) else (if cl<853 then (h56_2) else (h56_3))
private theorem k56_1_0 : check w56 pick56 1 t3067 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k56_1_1 : check w56 pick56 1 t3081 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k56_1_2 : check w56 pick56 1 t3082 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w56 pick56 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3067 t3081 k56_1_0 k56_1_1
private theorem k56_1_3 : check w56 pick56 1 t2988 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k56_1_4 : check w56 pick56 1 t3003 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k56_1_5 : check w56 pick56 1 t3004 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w56 pick56 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2988 t3003 k56_1_3 k56_1_4
private theorem k56_1_6 : check w56 pick56 1 t3083 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w56 pick56 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3082 t3004 k56_1_2 k56_1_5
private theorem k56_1_7 : check w56 pick56 1 t3087 ⟨1,7,2,16,1,20,139,199⟩ = true := by decide +kernel
private theorem k56_1_8 : check w56 pick56 1 t3099 ⟨1,7,2,16,21,52,139,199⟩ = true := by decide +kernel
private theorem k56_1_9 : check w56 pick56 1 t3100 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w56 pick56 1 ⟨1,7,2,16,1,52,139,199⟩ 2 20 t3087 t3099 k56_1_7 k56_1_8
private theorem k56_1_10 : check w56 pick56 1 t3102 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k56_1_11 : check w56 pick56 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k56_1_12 : check w56 pick56 1 t3103 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w56 pick56 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t3102 t786 k56_1_10 k56_1_11
private theorem k56_1_13 : check w56 pick56 1 t3104 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w56 pick56 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t3100 t3103 k56_1_9 k56_1_12
private theorem k56_1_14 : check w56 pick56 1 t3105 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w56 pick56 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3083 t3104 k56_1_6 k56_1_13
theorem cov56_1 : PA.Covered 1 (OZ.Valid 1 w56.low w56.t w56.y w56.r w56.cap) (P33.root 1) :=
  Night6836Tree.sound w56 pick56 1 t3105 _ k56_1_14
private theorem k56_2_0 : check w56 pick56 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k56_2_1 : check w56 pick56 2 t3115 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k56_2_2 : check w56 pick56 2 t3116 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w56 pick56 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3115 k56_2_0 k56_2_1
theorem cov56_2 : PA.Covered 2 (OZ.Valid 2 w56.low w56.t w56.y w56.r w56.cap) (P33.root 2) :=
  Night6836Tree.sound w56 pick56 2 t3116 _ k56_2_2
theorem cov56_3 : PA.Covered 3 (OZ.Valid 3 w56.low w56.t w56.y w56.r w56.cap) (P33.root 3) :=
  Night6836Tree.sound w56 pick56 3 t564 _ (by decide +kernel)
theorem cov56_4 : PA.Covered 4 (OZ.Valid 4 w56.low w56.t w56.y w56.r w56.cap) (P33.root 4) :=
  Night6836Tree.sound w56 pick56 4 t565 _ (by decide +kernel)
theorem cov56_5 : PA.Covered 5 (OZ.Valid 5 w56.low w56.t w56.y w56.r w56.cap) (P33.root 5) :=
  Night6836Tree.sound w56 pick56 5 t566 _ (by decide +kernel)
theorem cov56_6 : PA.Covered 6 (OZ.Valid 6 w56.low w56.t w56.y w56.r w56.cap) (P33.root 6) :=
  Night6836Tree.sound w56 pick56 6 t567 _ (by decide +kernel)
theorem cov56_7 : PA.Covered 7 (OZ.Valid 7 w56.low w56.t w56.y w56.r w56.cap) (P33.root 7) :=
  Night6836Tree.sound w56 pick56 7 t568 _ (by decide +kernel)
theorem window56 : P33.WindowCount w56 := by
  apply P33.window_count w56 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov56_1
  · exact cov56_2
  · exact cov56_3
  · exact cov56_4
  · exact cov56_5
  · exact cov56_6
  · exact cov56_7
def w57 : P33.Window := ⟨10,33,6253,5304,240162851280131771,27016,27000,5000000,81920000000⟩
def h57_0 : Height w57 := ⟨27016,27000,by decide +kernel⟩
def h57_1 : Height w57 := ⟨31406,24000,by decide +kernel⟩
def h57_2 : Height w57 := ⟨37283,21000,by decide +kernel⟩
def h57_3 : Height w57 := ⟨46185,18000,by decide +kernel⟩
def pick57 (cl : ℕ) : Height w57 := if cl<36 then (if cl<5 then (h57_0) else (h57_1)) else (if cl<273 then (h57_2) else (h57_3))
private theorem k57_1_0 : check w57 pick57 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k57_1_1 : check w57 pick57 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k57_1_2 : check w57 pick57 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w57 pick57 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k57_1_0 k57_1_1
private theorem k57_1_3 : check w57 pick57 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k57_1_4 : check w57 pick57 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k57_1_5 : check w57 pick57 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w57 pick57 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k57_1_3 k57_1_4
private theorem k57_1_6 : check w57 pick57 1 t2814 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w57 pick57 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2813 k57_1_2 k57_1_5
private theorem k57_1_7 : check w57 pick57 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k57_1_8 : check w57 pick57 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k57_1_9 : check w57 pick57 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w57 pick57 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k57_1_7 k57_1_8
private theorem k57_1_10 : check w57 pick57 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k57_1_11 : check w57 pick57 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k57_1_12 : check w57 pick57 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w57 pick57 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k57_1_10 k57_1_11
private theorem k57_1_13 : check w57 pick57 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w57 pick57 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k57_1_9 k57_1_12
private theorem k57_1_14 : check w57 pick57 1 t2815 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w57 pick57 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2814 t2461 k57_1_6 k57_1_13
theorem cov57_1 : PA.Covered 1 (OZ.Valid 1 w57.low w57.t w57.y w57.r w57.cap) (P33.root 1) :=
  Night6836Tree.sound w57 pick57 1 t2815 _ k57_1_14
theorem cov57_2 : PA.Covered 2 (OZ.Valid 2 w57.low w57.t w57.y w57.r w57.cap) (P33.root 2) :=
  Night6836Tree.sound w57 pick57 2 t2745 _ (by decide +kernel)
theorem cov57_3 : PA.Covered 3 (OZ.Valid 3 w57.low w57.t w57.y w57.r w57.cap) (P33.root 3) :=
  Night6836Tree.sound w57 pick57 3 t564 _ (by decide +kernel)
theorem cov57_4 : PA.Covered 4 (OZ.Valid 4 w57.low w57.t w57.y w57.r w57.cap) (P33.root 4) :=
  Night6836Tree.sound w57 pick57 4 t565 _ (by decide +kernel)
theorem cov57_5 : PA.Covered 5 (OZ.Valid 5 w57.low w57.t w57.y w57.r w57.cap) (P33.root 5) :=
  Night6836Tree.sound w57 pick57 5 t566 _ (by decide +kernel)
theorem cov57_6 : PA.Covered 6 (OZ.Valid 6 w57.low w57.t w57.y w57.r w57.cap) (P33.root 6) :=
  Night6836Tree.sound w57 pick57 6 t567 _ (by decide +kernel)
theorem cov57_7 : PA.Covered 7 (OZ.Valid 7 w57.low w57.t w57.y w57.r w57.cap) (P33.root 7) :=
  Night6836Tree.sound w57 pick57 7 t2134 _ (by decide +kernel)
theorem window57 : P33.WindowCount w57 := by
  apply P33.window_count w57 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov57_1
  · exact cov57_2
  · exact cov57_3
  · exact cov57_4
  · exact cov57_5
  · exact cov57_6
  · exact cov57_7
def w58 : P33.Window := ⟨10,33,7203,6254,244406347833943725,21545,24000,5000000,81920000000⟩
def h58_0 : Height w58 := ⟨21545,24000,by decide +kernel⟩
def h58_1 : Height w58 := ⟨25608,21000,by decide +kernel⟩
def h58_2 : Height w58 := ⟨31197,18000,by decide +kernel⟩
def h58_3 : Height w58 := ⟨40250,15000,by decide +kernel⟩
def pick58 (cl : ℕ) : Height w58 := if cl<32 then (if cl<2 then (h58_0) else (h58_1)) else (if cl<284 then (h58_2) else (h58_3))
private theorem k58_1_0 : check w58 pick58 1 t3067 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k58_1_1 : check w58 pick58 1 t3081 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k58_1_2 : check w58 pick58 1 t3082 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w58 pick58 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3067 t3081 k58_1_0 k58_1_1
private theorem k58_1_3 : check w58 pick58 1 t2988 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k58_1_4 : check w58 pick58 1 t3003 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k58_1_5 : check w58 pick58 1 t3004 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w58 pick58 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2988 t3003 k58_1_3 k58_1_4
private theorem k58_1_6 : check w58 pick58 1 t3083 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w58 pick58 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3082 t3004 k58_1_2 k58_1_5
private theorem k58_1_7 : check w58 pick58 1 t3120 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k58_1_8 : check w58 pick58 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k58_1_9 : check w58 pick58 1 t3124 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w58 pick58 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3120 t3123 k58_1_7 k58_1_8
private theorem k58_1_10 : check w58 pick58 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k58_1_11 : check w58 pick58 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k58_1_12 : check w58 pick58 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w58 pick58 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k58_1_10 k58_1_11
private theorem k58_1_13 : check w58 pick58 1 t3125 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w58 pick58 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3124 t1079 k58_1_9 k58_1_12
private theorem k58_1_14 : check w58 pick58 1 t3126 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w58 pick58 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3083 t3125 k58_1_6 k58_1_13
theorem cov58_1 : PA.Covered 1 (OZ.Valid 1 w58.low w58.t w58.y w58.r w58.cap) (P33.root 1) :=
  Night6836Tree.sound w58 pick58 1 t3126 _ k58_1_14
private theorem k58_2_0 : check w58 pick58 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k58_2_1 : check w58 pick58 2 t3134 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k58_2_2 : check w58 pick58 2 t3135 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w58 pick58 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3134 k58_2_0 k58_2_1
theorem cov58_2 : PA.Covered 2 (OZ.Valid 2 w58.low w58.t w58.y w58.r w58.cap) (P33.root 2) :=
  Night6836Tree.sound w58 pick58 2 t3135 _ k58_2_2
theorem cov58_3 : PA.Covered 3 (OZ.Valid 3 w58.low w58.t w58.y w58.r w58.cap) (P33.root 3) :=
  Night6836Tree.sound w58 pick58 3 t564 _ (by decide +kernel)
theorem cov58_4 : PA.Covered 4 (OZ.Valid 4 w58.low w58.t w58.y w58.r w58.cap) (P33.root 4) :=
  Night6836Tree.sound w58 pick58 4 t565 _ (by decide +kernel)
theorem cov58_5 : PA.Covered 5 (OZ.Valid 5 w58.low w58.t w58.y w58.r w58.cap) (P33.root 5) :=
  Night6836Tree.sound w58 pick58 5 t566 _ (by decide +kernel)
theorem cov58_6 : PA.Covered 6 (OZ.Valid 6 w58.low w58.t w58.y w58.r w58.cap) (P33.root 6) :=
  Night6836Tree.sound w58 pick58 6 t567 _ (by decide +kernel)
theorem cov58_7 : PA.Covered 7 (OZ.Valid 7 w58.low w58.t w58.y w58.r w58.cap) (P33.root 7) :=
  Night6836Tree.sound w58 pick58 7 t568 _ (by decide +kernel)
theorem window58 : P33.WindowCount w58 := by
  apply P33.window_count w58 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov58_1
  · exact cov58_2
  · exact cov58_3
  · exact cov58_4
  · exact cov58_5
  · exact cov58_6
  · exact cov58_7
def w59 : P33.Window := ⟨10,33,7326,7283,245344909955171019,18045,21000,5000000,81920000000⟩
def h59_0 : Height w59 := ⟨18045,21000,by decide +kernel⟩
def h59_1 : Height w59 := ⟨22046,18000,by decide +kernel⟩
def h59_2 : Height w59 := ⟨27881,15000,by decide +kernel⟩
def h59_3 : Height w59 := ⟨38725,12000,by decide +kernel⟩
def pick59 (cl : ℕ) : Height w59 := if cl<36 then (if cl<2 then (h59_0) else (h59_1)) else (if cl<853 then (h59_2) else (h59_3))
private theorem k59_1_0 : check w59 pick59 1 t3146 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k59_1_1 : check w59 pick59 1 t3174 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k59_1_2 : check w59 pick59 1 t3175 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w59 pick59 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t3146 t3174 k59_1_0 k59_1_1
private theorem k59_1_3 : check w59 pick59 1 t3192 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k59_1_4 : check w59 pick59 1 t3195 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k59_1_5 : check w59 pick59 1 t3196 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w59 pick59 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t3192 t3195 k59_1_3 k59_1_4
private theorem k59_1_6 : check w59 pick59 1 t3197 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w59 pick59 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t3175 t3196 k59_1_2 k59_1_5
private theorem k59_1_7 : check w59 pick59 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k59_1_8 : check w59 pick59 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k59_1_9 : check w59 pick59 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w59 pick59 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k59_1_7 k59_1_8
private theorem k59_1_10 : check w59 pick59 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k59_1_11 : check w59 pick59 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k59_1_12 : check w59 pick59 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w59 pick59 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k59_1_10 k59_1_11
private theorem k59_1_13 : check w59 pick59 1 t3201 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w59 pick59 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t1079 k59_1_9 k59_1_12
private theorem k59_1_14 : check w59 pick59 1 t3202 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w59 pick59 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3197 t3201 k59_1_6 k59_1_13
theorem cov59_1 : PA.Covered 1 (OZ.Valid 1 w59.low w59.t w59.y w59.r w59.cap) (P33.root 1) :=
  Night6836Tree.sound w59 pick59 1 t3202 _ k59_1_14
private theorem k59_2_0 : check w59 pick59 2 t3206 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k59_2_1 : check w59 pick59 2 t3219 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k59_2_2 : check w59 pick59 2 t3220 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w59 pick59 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t3206 t3219 k59_2_0 k59_2_1
theorem cov59_2 : PA.Covered 2 (OZ.Valid 2 w59.low w59.t w59.y w59.r w59.cap) (P33.root 2) :=
  Night6836Tree.sound w59 pick59 2 t3220 _ k59_2_2
theorem cov59_3 : PA.Covered 3 (OZ.Valid 3 w59.low w59.t w59.y w59.r w59.cap) (P33.root 3) :=
  Night6836Tree.sound w59 pick59 3 t564 _ (by decide +kernel)
theorem cov59_4 : PA.Covered 4 (OZ.Valid 4 w59.low w59.t w59.y w59.r w59.cap) (P33.root 4) :=
  Night6836Tree.sound w59 pick59 4 t565 _ (by decide +kernel)
theorem cov59_5 : PA.Covered 5 (OZ.Valid 5 w59.low w59.t w59.y w59.r w59.cap) (P33.root 5) :=
  Night6836Tree.sound w59 pick59 5 t566 _ (by decide +kernel)
theorem cov59_6 : PA.Covered 6 (OZ.Valid 6 w59.low w59.t w59.y w59.r w59.cap) (P33.root 6) :=
  Night6836Tree.sound w59 pick59 6 t567 _ (by decide +kernel)
theorem cov59_7 : PA.Covered 7 (OZ.Valid 7 w59.low w59.t w59.y w59.r w59.cap) (P33.root 7) :=
  Night6836Tree.sound w59 pick59 7 t568 _ (by decide +kernel)
theorem window59 : P33.WindowCount w59 := by
  apply P33.window_count w59 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov59_1
  · exact cov59_2
  · exact cov59_3
  · exact cov59_4
  · exact cov59_5
  · exact cov59_6
  · exact cov59_7
end ProximityPrize.SubmissionLower.Night6836Bank
