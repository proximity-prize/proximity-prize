import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def bank0 : Witness :=
  ⟨1, true, 15, 80, 3600, 5024, 1116, 7807, 1431377948442624, 17836593186390⟩

theorem bank0_nodes : P1_7_1.nodeRows bank0.shape = bank0.nodes :=
  node_check bank0 (by decide) (by decide) (by decide)

private theorem bank0_2330_2350 : Positive bank0 2330 2350 := by
  decide +kernel

private theorem bank0_2351_2405 : Positive bank0 2351 2405 := by
  decide +kernel

private theorem bank0_2406_2499 : Positive bank0 2406 2499 := by
  decide +kernel

theorem bank0_cover : ∃ ends, Cover bank0 firstHeight ends := by
  exact ⟨[2350, 2405, 2499],
    ⟨(by decide), (by decide), bank0_2330_2350,
      (by decide), (by decide), bank0_2351_2405,
      (by decide), (by decide), bank0_2406_2499, rfl⟩⟩

def bank1 : Witness :=
  ⟨1, true, 19, 100, 2800, 3906, 868, 7207, 673724585476096, 6522029371619⟩

theorem bank1_nodes : P1_7_1.nodeRows bank1.shape = bank1.nodes :=
  node_check bank1 (by decide) (by decide) (by decide)

private theorem bank1_2330_2336 : Positive bank1 2330 2336 := by
  decide +kernel

private theorem bank1_2337_2354 : Positive bank1 2337 2354 := by
  decide +kernel

private theorem bank1_2355_2401 : Positive bank1 2355 2401 := by
  decide +kernel

private theorem bank1_2402_2499 : Positive bank1 2402 2499 := by
  decide +kernel

theorem bank1_cover : ∃ ends, Cover bank1 firstHeight ends := by
  exact ⟨[2336, 2354, 2401, 2499],
    ⟨(by decide), (by decide), bank1_2330_2336,
      (by decide), (by decide), bank1_2337_2354,
      (by decide), (by decide), bank1_2355_2401,
      (by decide), (by decide), bank1_2402_2499, rfl⟩⟩

def bank2 : Witness :=
  ⟨1, true, 24, 150, 3200, 4462, 992, 8457, 1005466041712640, 11107288021896⟩

theorem bank2_nodes : P1_7_1.nodeRows bank2.shape = bank2.nodes :=
  node_check bank2 (by decide) (by decide) (by decide)

private theorem bank2_2330_2331 : Positive bank2 2330 2331 := by
  decide +kernel

private theorem bank2_2332_2336 : Positive bank2 2332 2336 := by
  decide +kernel

private theorem bank2_2337_2349 : Positive bank2 2337 2349 := by
  decide +kernel

private theorem bank2_2350_2383 : Positive bank2 2350 2383 := by
  decide +kernel

private theorem bank2_2384_2472 : Positive bank2 2384 2472 := by
  decide +kernel

private theorem bank2_2473_2499 : Positive bank2 2473 2499 := by
  decide +kernel

theorem bank2_cover : ∃ ends, Cover bank2 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2472, 2499],
    ⟨(by decide), (by decide), bank2_2330_2331,
      (by decide), (by decide), bank2_2332_2336,
      (by decide), (by decide), bank2_2337_2349,
      (by decide), (by decide), bank2_2350_2383,
      (by decide), (by decide), bank2_2384_2472,
      (by decide), (by decide), bank2_2473_2499, rfl⟩⟩

def bank3 : Witness :=
  ⟨1, true, 48, 180, 2450, 3414, 759, 8457, 451225494487040, 3808811463031⟩

theorem bank3_nodes : P1_7_1.nodeRows bank3.shape = bank3.nodes :=
  node_check bank3 (by decide) (by decide) (by decide)

private theorem bank3_2330_2330 : Positive bank3 2330 2330 := by
  decide +kernel

private theorem bank3_2331_2332 : Positive bank3 2331 2332 := by
  decide +kernel

private theorem bank3_2333_2338 : Positive bank3 2333 2338 := by
  decide +kernel

private theorem bank3_2339_2353 : Positive bank3 2339 2353 := by
  decide +kernel

private theorem bank3_2354_2393 : Positive bank3 2354 2393 := by
  decide +kernel

private theorem bank3_2394_2498 : Positive bank3 2394 2498 := by
  decide +kernel

private theorem bank3_2499_2499 : Positive bank3 2499 2499 := by
  decide +kernel

theorem bank3_cover : ∃ ends, Cover bank3 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2353, 2393, 2498, 2499],
    ⟨(by decide), (by decide), bank3_2330_2330,
      (by decide), (by decide), bank3_2331_2332,
      (by decide), (by decide), bank3_2333_2338,
      (by decide), (by decide), bank3_2339_2353,
      (by decide), (by decide), bank3_2354_2393,
      (by decide), (by decide), bank3_2394_2498,
      (by decide), (by decide), bank3_2499_2499, rfl⟩⟩

def bank4 : Witness :=
  ⟨1, true, 32, 220, 3850, 5368, 1162, 10751, 1715401077555200, 22781291138451⟩

theorem bank4_nodes : P1_7_1.nodeRows bank4.shape = bank4.nodes :=
  node_check bank4 (by decide) (by decide) (by decide)

private theorem bank4_2330_2331 : Positive bank4 2330 2331 := by
  decide +kernel

private theorem bank4_2332_2336 : Positive bank4 2332 2336 := by
  decide +kernel

private theorem bank4_2337_2349 : Positive bank4 2337 2349 := by
  decide +kernel

private theorem bank4_2350_2383 : Positive bank4 2350 2383 := by
  decide +kernel

private theorem bank4_2384_2472 : Positive bank4 2384 2472 := by
  decide +kernel

private theorem bank4_2473_2499 : Positive bank4 2473 2499 := by
  decide +kernel

theorem bank4_cover : ∃ ends, Cover bank4 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2472, 2499],
    ⟨(by decide), (by decide), bank4_2330_2331,
      (by decide), (by decide), bank4_2332_2336,
      (by decide), (by decide), bank4_2337_2349,
      (by decide), (by decide), bank4_2350_2383,
      (by decide), (by decide), bank4_2384_2472,
      (by decide), (by decide), bank4_2473_2499, rfl⟩⟩

end Research6966.HelperWindowCatalogue
