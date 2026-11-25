import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def bank35 : Witness :=
  ⟨4, true, 48, 180, 2450, 3414, 739, 8457, 442165884354560, 3730461615698⟩

theorem bank35_nodes : P1_7_1.nodeRows bank35.shape = bank35.nodes :=
  node_check bank35 (by decide) (by decide) (by decide)

private theorem bank35_2330_2332 : Positive bank35 2330 2332 := by
  decide +kernel

private theorem bank35_2333_2339 : Positive bank35 2333 2339 := by
  decide +kernel

private theorem bank35_2340_2358 : Positive bank35 2340 2358 := by
  decide +kernel

private theorem bank35_2359_2408 : Positive bank35 2359 2408 := by
  decide +kernel

private theorem bank35_2409_2499 : Positive bank35 2409 2499 := by
  decide +kernel

theorem bank35_cover : ∃ ends, Cover bank35 firstHeight ends := by
  exact ⟨[2332, 2339, 2358, 2408, 2499],
    ⟨(by decide), (by decide), bank35_2330_2332,
      (by decide), (by decide), bank35_2333_2339,
      (by decide), (by decide), bank35_2340_2358,
      (by decide), (by decide), bank35_2359_2408,
      (by decide), (by decide), bank35_2409_2499, rfl⟩⟩
#print axioms bank35_cover

def bank36 : Witness :=
  ⟨4, true, 512, 220, 1800, 2505, 558, 20389, 179155180978176, 1106646928910⟩

theorem bank36_nodes : P1_7_1.nodeRows bank36.shape = bank36.nodes :=
  node_check bank36 (by decide) (by decide) (by decide)

private theorem bank36_2330_2330 : Positive bank36 2330 2330 := by
  decide +kernel

private theorem bank36_2331_2332 : Positive bank36 2331 2332 := by
  decide +kernel

private theorem bank36_2333_2338 : Positive bank36 2333 2338 := by
  decide +kernel

private theorem bank36_2339_2354 : Positive bank36 2339 2354 := by
  decide +kernel

private theorem bank36_2355_2396 : Positive bank36 2355 2396 := by
  decide +kernel

private theorem bank36_2397_2499 : Positive bank36 2397 2499 := by
  decide +kernel

theorem bank36_cover : ∃ ends, Cover bank36 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2354, 2396, 2499],
    ⟨(by decide), (by decide), bank36_2330_2330,
      (by decide), (by decide), bank36_2331_2332,
      (by decide), (by decide), bank36_2333_2338,
      (by decide), (by decide), bank36_2339_2354,
      (by decide), (by decide), bank36_2355_2396,
      (by decide), (by decide), bank36_2397_2499, rfl⟩⟩
#print axioms bank36_cover

def bank37 : Witness :=
  ⟨5, true, 1, 80, 2800, 3906, 868, 17374, 673724585476096, 6522029371619⟩

theorem bank37_nodes : P1_7_1.nodeRows bank37.shape = bank37.nodes :=
  node_check bank37 (by decide) (by decide) (by decide)

private theorem bank37_2330_2332 : Positive bank37 2330 2332 := by
  decide +kernel

private theorem bank37_2333_2340 : Positive bank37 2333 2340 := by
  decide +kernel

private theorem bank37_2341_2361 : Positive bank37 2341 2361 := by
  decide +kernel

private theorem bank37_2362_2415 : Positive bank37 2362 2415 := by
  decide +kernel

private theorem bank37_2416_2499 : Positive bank37 2416 2499 := by
  decide +kernel

theorem bank37_cover : ∃ ends, Cover bank37 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2415, 2499],
    ⟨(by decide), (by decide), bank37_2330_2332,
      (by decide), (by decide), bank37_2333_2340,
      (by decide), (by decide), bank37_2341_2361,
      (by decide), (by decide), bank37_2362_2415,
      (by decide), (by decide), bank37_2416_2499, rfl⟩⟩
#print axioms bank37_cover

def bank38 : Witness :=
  ⟨5, true, 256, 310, 2800, 3898, 828, 22088, 649967151087616, 6245211525094⟩

theorem bank38_nodes : P1_7_1.nodeRows bank38.shape = bank38.nodes :=
  node_check bank38 (by decide) (by decide) (by decide)

private theorem bank38_2330_2334 : Positive bank38 2330 2334 := by
  decide +kernel

private theorem bank38_2335_2347 : Positive bank38 2335 2347 := by
  decide +kernel

private theorem bank38_2348_2382 : Positive bank38 2348 2382 := by
  decide +kernel

private theorem bank38_2383_2476 : Positive bank38 2383 2476 := by
  decide +kernel

private theorem bank38_2477_2499 : Positive bank38 2477 2499 := by
  decide +kernel

theorem bank38_cover : ∃ ends, Cover bank38 firstHeight ends := by
  exact ⟨[2334, 2347, 2382, 2476, 2499],
    ⟨(by decide), (by decide), bank38_2330_2334,
      (by decide), (by decide), bank38_2335_2347,
      (by decide), (by decide), bank38_2348_2382,
      (by decide), (by decide), bank38_2383_2476,
      (by decide), (by decide), bank38_2477_2499, rfl⟩⟩
#print axioms bank38_cover

end Research6966.HelperWindowCatalogue
