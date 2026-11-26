import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def bank20 : Witness :=
  ⟨2, false, 19, 30, 3850, 5374, 1162, 72277, 1715401077555200, 22863342836494⟩

theorem bank20_nodes : P1_7_1.nodeRows bank20.shape = bank20.nodes :=
  node_check bank20 (by decide) (by decide) (by decide)

private theorem bank20_2330_2332 : Positive bank20 2330 2332 := by
  decide +kernel

private theorem bank20_2333_2340 : Positive bank20 2333 2340 := by
  decide +kernel

private theorem bank20_2341_2361 : Positive bank20 2341 2361 := by
  decide +kernel

private theorem bank20_2362_2415 : Positive bank20 2362 2415 := by
  decide +kernel

private theorem bank20_2416_2499 : Positive bank20 2416 2499 := by
  decide +kernel

theorem bank20_cover : ∃ ends, Cover bank20 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2415, 2499],
    ⟨(by decide), (by decide), bank20_2330_2332,
      (by decide), (by decide), bank20_2333_2340,
      (by decide), (by decide), bank20_2341_2361,
      (by decide), (by decide), bank20_2362_2415,
      (by decide), (by decide), bank20_2416_2499, rfl⟩⟩

def bank21 : Witness :=
  ⟨2, false, 24, 45, 3850, 5374, 1193, 50764, 1750065639325696, 23337042054253⟩

theorem bank21_nodes : P1_7_1.nodeRows bank21.shape = bank21.nodes :=
  node_check bank21 (by decide) (by decide) (by decide)

private theorem bank21_2330_2333 : Positive bank21 2330 2333 := by
  decide +kernel

private theorem bank21_2334_2343 : Positive bank21 2334 2343 := by
  decide +kernel

private theorem bank21_2344_2369 : Positive bank21 2344 2369 := by
  decide +kernel

private theorem bank21_2370_2436 : Positive bank21 2370 2436 := by
  decide +kernel

private theorem bank21_2437_2499 : Positive bank21 2437 2499 := by
  decide +kernel

theorem bank21_cover : ∃ ends, Cover bank21 firstHeight ends := by
  exact ⟨[2333, 2343, 2369, 2436, 2499],
    ⟨(by decide), (by decide), bank21_2330_2333,
      (by decide), (by decide), bank21_2334_2343,
      (by decide), (by decide), bank21_2344_2369,
      (by decide), (by decide), bank21_2370_2436,
      (by decide), (by decide), bank21_2437_2499, rfl⟩⟩

def bank22 : Witness :=
  ⟨3, true, 6, 45, 3200, 4466, 966, 22088, 985382249037824, 10911373353653⟩

theorem bank22_nodes : P1_7_1.nodeRows bank22.shape = bank22.nodes :=
  node_check bank22 (by decide) (by decide) (by decide)

private theorem bank22_2330_2330 : Positive bank22 2330 2330 := by
  decide +kernel

private theorem bank22_2331_2333 : Positive bank22 2331 2333 := by
  decide +kernel

private theorem bank22_2334_2341 : Positive bank22 2334 2341 := by
  decide +kernel

private theorem bank22_2342_2361 : Positive bank22 2342 2361 := by
  decide +kernel

private theorem bank22_2362_2414 : Positive bank22 2362 2414 := by
  decide +kernel

private theorem bank22_2415_2499 : Positive bank22 2415 2499 := by
  decide +kernel

theorem bank22_cover : ∃ ends, Cover bank22 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2361, 2414, 2499],
    ⟨(by decide), (by decide), bank22_2330_2330,
      (by decide), (by decide), bank22_2331_2333,
      (by decide), (by decide), bank22_2334_2341,
      (by decide), (by decide), bank22_2342_2361,
      (by decide), (by decide), bank22_2362_2414,
      (by decide), (by decide), bank22_2415_2499, rfl⟩⟩

def bank23 : Witness :=
  ⟨3, true, 5, 45, 3200, 4466, 966, 25922, 985382249037824, 10911373353653⟩

theorem bank23_nodes : P1_7_1.nodeRows bank23.shape = bank23.nodes :=
  node_check bank23 (by decide) (by decide) (by decide)

private theorem bank23_2330_2335 : Positive bank23 2330 2335 := by
  decide +kernel

private theorem bank23_2336_2350 : Positive bank23 2336 2350 := by
  decide +kernel

private theorem bank23_2351_2390 : Positive bank23 2351 2390 := by
  decide +kernel

private theorem bank23_2391_2494 : Positive bank23 2391 2494 := by
  decide +kernel

private theorem bank23_2495_2499 : Positive bank23 2495 2499 := by
  decide +kernel

theorem bank23_cover : ∃ ends, Cover bank23 firstHeight ends := by
  exact ⟨[2335, 2350, 2390, 2494, 2499],
    ⟨(by decide), (by decide), bank23_2330_2335,
      (by decide), (by decide), bank23_2336_2350,
      (by decide), (by decide), bank23_2351_2390,
      (by decide), (by decide), bank23_2391_2494,
      (by decide), (by decide), bank23_2495_2499, rfl⟩⟩

def bank24 : Witness :=
  ⟨3, true, 2, 45, 3200, 4466, 966, 35703, 985382249037824, 10911373353653⟩

theorem bank24_nodes : P1_7_1.nodeRows bank24.shape = bank24.nodes :=
  node_check bank24 (by decide) (by decide) (by decide)

private theorem bank24_2330_2335 : Positive bank24 2330 2335 := by
  decide +kernel

private theorem bank24_2336_2351 : Positive bank24 2336 2351 := by
  decide +kernel

private theorem bank24_2352_2393 : Positive bank24 2352 2393 := by
  decide +kernel

private theorem bank24_2394_2499 : Positive bank24 2394 2499 := by
  decide +kernel

theorem bank24_cover : ∃ ends, Cover bank24 firstHeight ends := by
  exact ⟨[2335, 2351, 2393, 2499],
    ⟨(by decide), (by decide), bank24_2330_2335,
      (by decide), (by decide), bank24_2336_2351,
      (by decide), (by decide), bank24_2352_2393,
      (by decide), (by decide), bank24_2394_2499, rfl⟩⟩

end Research6966.HelperWindowCatalogue
