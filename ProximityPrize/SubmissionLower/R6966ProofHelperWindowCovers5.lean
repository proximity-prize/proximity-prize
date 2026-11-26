import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def bank25 : Witness :=
  ⟨3, true, 1, 45, 3200, 4466, 966, 38678, 985382249037824, 10911373353653⟩

theorem bank25_nodes : P1_7_1.nodeRows bank25.shape = bank25.nodes :=
  node_check bank25 (by decide) (by decide) (by decide)

private theorem bank25_2330_2334 : Positive bank25 2330 2334 := by
  decide +kernel

private theorem bank25_2335_2347 : Positive bank25 2335 2347 := by
  decide +kernel

private theorem bank25_2348_2381 : Positive bank25 2348 2381 := by
  decide +kernel

private theorem bank25_2382_2470 : Positive bank25 2382 2470 := by
  decide +kernel

private theorem bank25_2471_2499 : Positive bank25 2471 2499 := by
  decide +kernel

theorem bank25_cover : ∃ ends, Cover bank25 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2470, 2499],
    ⟨(by decide), (by decide), bank25_2330_2334,
      (by decide), (by decide), bank25_2335_2347,
      (by decide), (by decide), bank25_2348_2381,
      (by decide), (by decide), bank25_2382_2470,
      (by decide), (by decide), bank25_2471_2499, rfl⟩⟩

def bank26 : Witness :=
  ⟨3, true, 10, 60, 3850, 5373, 1193, 12616, 1750065639325696, 23323058345148⟩

theorem bank26_nodes : P1_7_1.nodeRows bank26.shape = bank26.nodes :=
  node_check bank26 (by decide) (by decide) (by decide)

private theorem bank26_2330_2338 : Positive bank26 2330 2338 := by
  decide +kernel

private theorem bank26_2339_2361 : Positive bank26 2339 2361 := by
  decide +kernel

private theorem bank26_2362_2421 : Positive bank26 2362 2421 := by
  decide +kernel

private theorem bank26_2422_2499 : Positive bank26 2422 2499 := by
  decide +kernel

theorem bank26_cover : ∃ ends, Cover bank26 firstHeight ends := by
  exact ⟨[2338, 2361, 2421, 2499],
    ⟨(by decide), (by decide), bank26_2330_2338,
      (by decide), (by decide), bank26_2339_2361,
      (by decide), (by decide), bank26_2362_2421,
      (by decide), (by decide), bank26_2422_2499, rfl⟩⟩

def bank27 : Witness :=
  ⟨3, true, 12, 80, 3600, 5024, 1116, 10751, 1431377948442624, 17836593186390⟩

theorem bank27_nodes : P1_7_1.nodeRows bank27.shape = bank27.nodes :=
  node_check bank27 (by decide) (by decide) (by decide)

private theorem bank27_2330_2331 : Positive bank27 2330 2331 := by
  decide +kernel

private theorem bank27_2332_2336 : Positive bank27 2332 2336 := by
  decide +kernel

private theorem bank27_2337_2349 : Positive bank27 2337 2349 := by
  decide +kernel

private theorem bank27_2350_2383 : Positive bank27 2350 2383 := by
  decide +kernel

private theorem bank27_2384_2471 : Positive bank27 2384 2471 := by
  decide +kernel

private theorem bank27_2472_2499 : Positive bank27 2472 2499 := by
  decide +kernel

theorem bank27_cover : ∃ ends, Cover bank27 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2471, 2499],
    ⟨(by decide), (by decide), bank27_2330_2331,
      (by decide), (by decide), bank27_2332_2336,
      (by decide), (by decide), bank27_2337_2349,
      (by decide), (by decide), bank27_2350_2383,
      (by decide), (by decide), bank27_2384_2471,
      (by decide), (by decide), bank27_2472_2499, rfl⟩⟩

def bank28 : Witness :=
  ⟨3, true, 19, 150, 3600, 5021, 1116, 10751, 1431377948442624, 17802311516993⟩

theorem bank28_nodes : P1_7_1.nodeRows bank28.shape = bank28.nodes :=
  node_check bank28 (by decide) (by decide) (by decide)

private theorem bank28_2330_2334 : Positive bank28 2330 2334 := by
  decide +kernel

private theorem bank28_2335_2347 : Positive bank28 2335 2347 := by
  decide +kernel

private theorem bank28_2348_2381 : Positive bank28 2348 2381 := by
  decide +kernel

private theorem bank28_2382_2469 : Positive bank28 2382 2469 := by
  decide +kernel

private theorem bank28_2470_2499 : Positive bank28 2470 2499 := by
  decide +kernel

theorem bank28_cover : ∃ ends, Cover bank28 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2469, 2499],
    ⟨(by decide), (by decide), bank28_2330_2334,
      (by decide), (by decide), bank28_2335_2347,
      (by decide), (by decide), bank28_2348_2381,
      (by decide), (by decide), bank28_2382_2469,
      (by decide), (by decide), bank28_2470_2499, rfl⟩⟩

def bank29 : Witness :=
  ⟨3, true, 96, 260, 2800, 3900, 845, 13667, 660120691015680, 6355562702121⟩

theorem bank29_nodes : P1_7_1.nodeRows bank29.shape = bank29.nodes :=
  node_check bank29 (by decide) (by decide) (by decide)

private theorem bank29_2330_2341 : Positive bank29 2330 2341 := by
  decide +kernel

private theorem bank29_2342_2373 : Positive bank29 2342 2373 := by
  decide +kernel

private theorem bank29_2374_2457 : Positive bank29 2374 2457 := by
  decide +kernel

private theorem bank29_2458_2499 : Positive bank29 2458 2499 := by
  decide +kernel

theorem bank29_cover : ∃ ends, Cover bank29 firstHeight ends := by
  exact ⟨[2341, 2373, 2457, 2499],
    ⟨(by decide), (by decide), bank29_2330_2341,
      (by decide), (by decide), bank29_2342_2373,
      (by decide), (by decide), bank29_2374_2457,
      (by decide), (by decide), bank29_2458_2499, rfl⟩⟩

end Research6966.HelperWindowCatalogue
