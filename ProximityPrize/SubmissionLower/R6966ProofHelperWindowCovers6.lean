import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def bank30 : Witness :=
  ⟨3, true, 256, 310, 2800, 3898, 828, 22088, 649967151087616, 6245211525094⟩

theorem bank30_nodes : P1_7_1.nodeRows bank30.shape = bank30.nodes :=
  node_check bank30 (by decide) (by decide) (by decide)

private theorem bank30_2330_2330 : Positive bank30 2330 2330 := by
  decide +kernel

private theorem bank30_2331_2332 : Positive bank30 2331 2332 := by
  decide +kernel

private theorem bank30_2333_2338 : Positive bank30 2333 2338 := by
  decide +kernel

private theorem bank30_2339_2354 : Positive bank30 2339 2354 := by
  decide +kernel

private theorem bank30_2355_2397 : Positive bank30 2355 2397 := by
  decide +kernel

private theorem bank30_2398_2499 : Positive bank30 2398 2499 := by
  decide +kernel

theorem bank30_cover : ∃ ends, Cover bank30 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2354, 2397, 2499],
    ⟨(by decide), (by decide), bank30_2330_2330,
      (by decide), (by decide), bank30_2331_2332,
      (by decide), (by decide), bank30_2333_2338,
      (by decide), (by decide), bank30_2339_2354,
      (by decide), (by decide), bank30_2355_2397,
      (by decide), (by decide), bank30_2398_2499, rfl⟩⟩
#print axioms bank30_cover

def bank31 : Witness :=
  ⟨3, true, 1024, 450, 3600, 5010, 1065, 38678, 1381313797160960, 17044071339464⟩

theorem bank31_nodes : P1_7_1.nodeRows bank31.shape = bank31.nodes :=
  node_check bank31 (by decide) (by decide) (by decide)

private theorem bank31_2330_2336 : Positive bank31 2330 2336 := by
  decide +kernel

private theorem bank31_2337_2355 : Positive bank31 2337 2355 := by
  decide +kernel

private theorem bank31_2356_2405 : Positive bank31 2356 2405 := by
  decide +kernel

private theorem bank31_2406_2499 : Positive bank31 2406 2499 := by
  decide +kernel

theorem bank31_cover : ∃ ends, Cover bank31 firstHeight ends := by
  exact ⟨[2336, 2355, 2405, 2499],
    ⟨(by decide), (by decide), bank31_2330_2336,
      (by decide), (by decide), bank31_2337_2355,
      (by decide), (by decide), bank31_2356_2405,
      (by decide), (by decide), bank31_2406_2499, rfl⟩⟩
#print axioms bank31_cover

def bank32 : Witness :=
  ⟨3, true, 512, 450, 3850, 5359, 1116, 38678, 1663250706202624, 21954199792060⟩

theorem bank32_nodes : P1_7_1.nodeRows bank32.shape = bank32.nodes :=
  node_check bank32 (by decide) (by decide) (by decide)

private theorem bank32_2330_2336 : Positive bank32 2330 2336 := by
  decide +kernel

private theorem bank32_2337_2355 : Positive bank32 2337 2355 := by
  decide +kernel

private theorem bank32_2356_2407 : Positive bank32 2356 2407 := by
  decide +kernel

private theorem bank32_2408_2499 : Positive bank32 2408 2499 := by
  decide +kernel

theorem bank32_cover : ∃ ends, Cover bank32 firstHeight ends := by
  exact ⟨[2336, 2355, 2407, 2499],
    ⟨(by decide), (by decide), bank32_2330_2336,
      (by decide), (by decide), bank32_2337_2355,
      (by decide), (by decide), bank32_2356_2407,
      (by decide), (by decide), bank32_2408_2499, rfl⟩⟩
#print axioms bank32_cover

def bank33 : Witness :=
  ⟨3, false, 24, 60, 3200, 4466, 992, 45124, 1005466041712640, 11139389359148⟩

theorem bank33_nodes : P1_7_1.nodeRows bank33.shape = bank33.nodes :=
  node_check bank33 (by decide) (by decide) (by decide)

private theorem bank33_2330_2333 : Positive bank33 2330 2333 := by
  decide +kernel

private theorem bank33_2334_2344 : Positive bank33 2334 2344 := by
  decide +kernel

private theorem bank33_2345_2372 : Positive bank33 2345 2372 := by
  decide +kernel

private theorem bank33_2373_2445 : Positive bank33 2373 2445 := by
  decide +kernel

private theorem bank33_2446_2499 : Positive bank33 2446 2499 := by
  decide +kernel

theorem bank33_cover : ∃ ends, Cover bank33 firstHeight ends := by
  exact ⟨[2333, 2344, 2372, 2445, 2499],
    ⟨(by decide), (by decide), bank33_2330_2333,
      (by decide), (by decide), bank33_2334_2344,
      (by decide), (by decide), bank33_2345_2372,
      (by decide), (by decide), bank33_2373_2445,
      (by decide), (by decide), bank33_2446_2499, rfl⟩⟩
#print axioms bank33_cover

def bank34 : Witness :=
  ⟨4, true, 1, 80, 3600, 5024, 1116, 30422, 1431377948442624, 17836593186390⟩

theorem bank34_nodes : P1_7_1.nodeRows bank34.shape = bank34.nodes :=
  node_check bank34 (by decide) (by decide) (by decide)

private theorem bank34_2330_2330 : Positive bank34 2330 2330 := by
  decide +kernel

private theorem bank34_2331_2333 : Positive bank34 2331 2333 := by
  decide +kernel

private theorem bank34_2334_2341 : Positive bank34 2334 2341 := by
  decide +kernel

private theorem bank34_2342_2361 : Positive bank34 2342 2361 := by
  decide +kernel

private theorem bank34_2362_2413 : Positive bank34 2362 2413 := by
  decide +kernel

private theorem bank34_2414_2499 : Positive bank34 2414 2499 := by
  decide +kernel

theorem bank34_cover : ∃ ends, Cover bank34 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2361, 2413, 2499],
    ⟨(by decide), (by decide), bank34_2330_2330,
      (by decide), (by decide), bank34_2331_2333,
      (by decide), (by decide), bank34_2334_2341,
      (by decide), (by decide), bank34_2342_2361,
      (by decide), (by decide), bank34_2362_2413,
      (by decide), (by decide), bank34_2414_2499, rfl⟩⟩
#print axioms bank34_cover

end Research6966.HelperWindowCatalogue
