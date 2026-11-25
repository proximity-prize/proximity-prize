import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def bank15 : Witness :=
  ⟨2, true, 19, 150, 3850, 5370, 1193, 10751, 1750065639325696, 23281141439067⟩

theorem bank15_nodes : P1_7_1.nodeRows bank15.shape = bank15.nodes :=
  node_check bank15 (by decide) (by decide) (by decide)

private theorem bank15_2330_2336 : Positive bank15 2330 2336 := by
  decide +kernel

private theorem bank15_2337_2354 : Positive bank15 2337 2354 := by
  decide +kernel

private theorem bank15_2355_2401 : Positive bank15 2355 2401 := by
  decide +kernel

private theorem bank15_2402_2499 : Positive bank15 2402 2499 := by
  decide +kernel

theorem bank15_cover : ∃ ends, Cover bank15 firstHeight ends := by
  exact ⟨[2336, 2354, 2401, 2499],
    ⟨(by decide), (by decide), bank15_2330_2336,
      (by decide), (by decide), bank15_2337_2354,
      (by decide), (by decide), bank15_2355_2401,
      (by decide), (by decide), bank15_2402_2499, rfl⟩⟩
#print axioms bank15_cover

def bank16 : Witness :=
  ⟨2, true, 24, 180, 3850, 5369, 1193, 9161, 1750065639325696, 23267180540138⟩

theorem bank16_nodes : P1_7_1.nodeRows bank16.shape = bank16.nodes :=
  node_check bank16 (by decide) (by decide) (by decide)

private theorem bank16_2330_2330 : Positive bank16 2330 2330 := by
  decide +kernel

private theorem bank16_2331_2333 : Positive bank16 2331 2333 := by
  decide +kernel

private theorem bank16_2334_2340 : Positive bank16 2334 2340 := by
  decide +kernel

private theorem bank16_2341_2358 : Positive bank16 2341 2358 := by
  decide +kernel

private theorem bank16_2359_2405 : Positive bank16 2359 2405 := by
  decide +kernel

private theorem bank16_2406_2499 : Positive bank16 2406 2499 := by
  decide +kernel

theorem bank16_cover : ∃ ends, Cover bank16 firstHeight ends := by
  exact ⟨[2330, 2333, 2340, 2358, 2405, 2499],
    ⟨(by decide), (by decide), bank16_2330_2330,
      (by decide), (by decide), bank16_2331_2333,
      (by decide), (by decide), bank16_2334_2340,
      (by decide), (by decide), bank16_2341_2358,
      (by decide), (by decide), bank16_2359_2405,
      (by decide), (by decide), bank16_2406_2499, rfl⟩⟩
#print axioms bank16_cover

def bank17 : Witness :=
  ⟨2, true, 32, 220, 3600, 5018, 1116, 11646, 1431377948442624, 17768074724188⟩

theorem bank17_nodes : P1_7_1.nodeRows bank17.shape = bank17.nodes :=
  node_check bank17 (by decide) (by decide) (by decide)

private theorem bank17_2330_2333 : Positive bank17 2330 2333 := by
  decide +kernel

private theorem bank17_2334_2344 : Positive bank17 2334 2344 := by
  decide +kernel

private theorem bank17_2345_2372 : Positive bank17 2345 2372 := by
  decide +kernel

private theorem bank17_2373_2445 : Positive bank17 2373 2445 := by
  decide +kernel

private theorem bank17_2446_2499 : Positive bank17 2446 2499 := by
  decide +kernel

theorem bank17_cover : ∃ ends, Cover bank17 firstHeight ends := by
  exact ⟨[2333, 2344, 2372, 2445, 2499],
    ⟨(by decide), (by decide), bank17_2330_2333,
      (by decide), (by decide), bank17_2334_2344,
      (by decide), (by decide), bank17_2345_2372,
      (by decide), (by decide), bank17_2373_2445,
      (by decide), (by decide), bank17_2446_2499, rfl⟩⟩
#print axioms bank17_cover

def bank18 : Witness :=
  ⟨2, true, 256, 310, 2800, 3898, 828, 23928, 649967151087616, 6245211525094⟩

theorem bank18_nodes : P1_7_1.nodeRows bank18.shape = bank18.nodes :=
  node_check bank18 (by decide) (by decide) (by decide)

private theorem bank18_2330_2331 : Positive bank18 2330 2331 := by
  decide +kernel

private theorem bank18_2332_2336 : Positive bank18 2332 2336 := by
  decide +kernel

private theorem bank18_2337_2349 : Positive bank18 2337 2349 := by
  decide +kernel

private theorem bank18_2350_2384 : Positive bank18 2350 2384 := by
  decide +kernel

private theorem bank18_2385_2478 : Positive bank18 2385 2478 := by
  decide +kernel

private theorem bank18_2479_2499 : Positive bank18 2479 2499 := by
  decide +kernel

theorem bank18_cover : ∃ ends, Cover bank18 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2384, 2478, 2499],
    ⟨(by decide), (by decide), bank18_2330_2331,
      (by decide), (by decide), bank18_2332_2336,
      (by decide), (by decide), bank18_2337_2349,
      (by decide), (by decide), bank18_2350_2384,
      (by decide), (by decide), bank18_2385_2478,
      (by decide), (by decide), bank18_2479_2499, rfl⟩⟩
#print axioms bank18_cover

def bank19 : Witness :=
  ⟨2, true, 1024, 450, 3600, 5010, 1065, 38678, 1381313797160960, 17044071339464⟩

theorem bank19_nodes : P1_7_1.nodeRows bank19.shape = bank19.nodes :=
  node_check bank19 (by decide) (by decide) (by decide)

private theorem bank19_2330_2336 : Positive bank19 2330 2336 := by
  decide +kernel

private theorem bank19_2337_2354 : Positive bank19 2337 2354 := by
  decide +kernel

private theorem bank19_2355_2402 : Positive bank19 2355 2402 := by
  decide +kernel

private theorem bank19_2403_2499 : Positive bank19 2403 2499 := by
  decide +kernel

theorem bank19_cover : ∃ ends, Cover bank19 firstHeight ends := by
  exact ⟨[2336, 2354, 2402, 2499],
    ⟨(by decide), (by decide), bank19_2330_2336,
      (by decide), (by decide), bank19_2337_2354,
      (by decide), (by decide), bank19_2355_2402,
      (by decide), (by decide), bank19_2403_2499, rfl⟩⟩
#print axioms bank19_cover

end Research6966.HelperWindowCatalogue
