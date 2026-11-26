import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def bank10 : Witness :=
  ⟨2, true, 5, 30, 3850, 5374, 1139, 57710, 1689434820444160, 22509079559467⟩

theorem bank10_nodes : P1_7_1.nodeRows bank10.shape = bank10.nodes :=
  node_check bank10 (by decide) (by decide) (by decide)

private theorem bank10_2330_2330 : Positive bank10 2330 2330 := by
  decide +kernel

private theorem bank10_2331_2332 : Positive bank10 2331 2332 := by
  decide +kernel

private theorem bank10_2333_2338 : Positive bank10 2333 2338 := by
  decide +kernel

private theorem bank10_2339_2353 : Positive bank10 2339 2353 := by
  decide +kernel

private theorem bank10_2354_2393 : Positive bank10 2354 2393 := by
  decide +kernel

private theorem bank10_2394_2498 : Positive bank10 2394 2498 := by
  decide +kernel

private theorem bank10_2499_2499 : Positive bank10 2499 2499 := by
  decide +kernel

theorem bank10_cover : ∃ ends, Cover bank10 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2353, 2393, 2498, 2499],
    ⟨(by decide), (by decide), bank10_2330_2330,
      (by decide), (by decide), bank10_2331_2332,
      (by decide), (by decide), bank10_2333_2338,
      (by decide), (by decide), bank10_2339_2353,
      (by decide), (by decide), bank10_2354_2393,
      (by decide), (by decide), bank10_2394_2498,
      (by decide), (by decide), bank10_2499_2499, rfl⟩⟩

def bank11 : Witness :=
  ⟨2, true, 4, 30, 3850, 5374, 1139, 67728, 1689434820444160, 22509079559467⟩

theorem bank11_nodes : P1_7_1.nodeRows bank11.shape = bank11.nodes :=
  node_check bank11 (by decide) (by decide) (by decide)

private theorem bank11_2330_2331 : Positive bank11 2330 2331 := by
  decide +kernel

private theorem bank11_2332_2336 : Positive bank11 2332 2336 := by
  decide +kernel

private theorem bank11_2337_2349 : Positive bank11 2337 2349 := by
  decide +kernel

private theorem bank11_2350_2383 : Positive bank11 2350 2383 := by
  decide +kernel

private theorem bank11_2384_2473 : Positive bank11 2384 2473 := by
  decide +kernel

private theorem bank11_2474_2499 : Positive bank11 2474 2499 := by
  decide +kernel

theorem bank11_cover : ∃ ends, Cover bank11 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2473, 2499],
    ⟨(by decide), (by decide), bank11_2330_2331,
      (by decide), (by decide), bank11_2332_2336,
      (by decide), (by decide), bank11_2337_2349,
      (by decide), (by decide), bank11_2350_2383,
      (by decide), (by decide), bank11_2384_2473,
      (by decide), (by decide), bank11_2474_2499, rfl⟩⟩

def bank12 : Witness :=
  ⟨2, true, 8, 30, 3850, 5374, 1162, 30422, 1715401077555200, 22863342836494⟩

theorem bank12_nodes : P1_7_1.nodeRows bank12.shape = bank12.nodes :=
  node_check bank12 (by decide) (by decide) (by decide)

private theorem bank12_2330_2335 : Positive bank12 2330 2335 := by
  decide +kernel

private theorem bank12_2336_2350 : Positive bank12 2336 2350 := by
  decide +kernel

private theorem bank12_2351_2389 : Positive bank12 2351 2389 := by
  decide +kernel

private theorem bank12_2390_2491 : Positive bank12 2390 2491 := by
  decide +kernel

private theorem bank12_2492_2499 : Positive bank12 2492 2499 := by
  decide +kernel

theorem bank12_cover : ∃ ends, Cover bank12 firstHeight ends := by
  exact ⟨[2335, 2350, 2389, 2491, 2499],
    ⟨(by decide), (by decide), bank12_2330_2335,
      (by decide), (by decide), bank12_2336_2350,
      (by decide), (by decide), bank12_2351_2389,
      (by decide), (by decide), bank12_2390_2491,
      (by decide), (by decide), bank12_2492_2499, rfl⟩⟩

def bank13 : Witness :=
  ⟨2, true, 12, 60, 3600, 5024, 1116, 9161, 1431377948442624, 17836593186390⟩

theorem bank13_nodes : P1_7_1.nodeRows bank13.shape = bank13.nodes :=
  node_check bank13 (by decide) (by decide) (by decide)

private theorem bank13_2330_2336 : Positive bank13 2330 2336 := by
  decide +kernel

private theorem bank13_2337_2354 : Positive bank13 2337 2354 := by
  decide +kernel

private theorem bank13_2355_2401 : Positive bank13 2355 2401 := by
  decide +kernel

private theorem bank13_2402_2499 : Positive bank13 2402 2499 := by
  decide +kernel

theorem bank13_cover : ∃ ends, Cover bank13 firstHeight ends := by
  exact ⟨[2336, 2354, 2401, 2499],
    ⟨(by decide), (by decide), bank13_2330_2336,
      (by decide), (by decide), bank13_2337_2354,
      (by decide), (by decide), bank13_2355_2401,
      (by decide), (by decide), bank13_2402_2499, rfl⟩⟩

def bank14 : Witness :=
  ⟨2, true, 15, 100, 3600, 5023, 1116, 9161, 1431377948442624, 17825160975108⟩

theorem bank14_nodes : P1_7_1.nodeRows bank14.shape = bank14.nodes :=
  node_check bank14 (by decide) (by decide) (by decide)

private theorem bank14_2330_2331 : Positive bank14 2330 2331 := by
  decide +kernel

private theorem bank14_2332_2336 : Positive bank14 2332 2336 := by
  decide +kernel

private theorem bank14_2337_2349 : Positive bank14 2337 2349 := by
  decide +kernel

private theorem bank14_2350_2382 : Positive bank14 2350 2382 := by
  decide +kernel

private theorem bank14_2383_2468 : Positive bank14 2383 2468 := by
  decide +kernel

private theorem bank14_2469_2499 : Positive bank14 2469 2499 := by
  decide +kernel

theorem bank14_cover : ∃ ends, Cover bank14 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2382, 2468, 2499],
    ⟨(by decide), (by decide), bank14_2330_2331,
      (by decide), (by decide), bank14_2332_2336,
      (by decide), (by decide), bank14_2337_2349,
      (by decide), (by decide), bank14_2350_2382,
      (by decide), (by decide), bank14_2383_2468,
      (by decide), (by decide), bank14_2469_2499, rfl⟩⟩

end Research6966.HelperWindowCatalogue
