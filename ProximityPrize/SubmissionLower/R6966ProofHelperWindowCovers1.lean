import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def bank5 : Witness :=
  ⟨1, true, 96, 260, 2800, 3900, 845, 13667, 660120691015680, 6355562702121⟩

theorem bank5_nodes : P1_7_1.nodeRows bank5.shape = bank5.nodes :=
  node_check bank5 (by decide) (by decide) (by decide)

private theorem bank5_2330_2331 : Positive bank5 2330 2331 := by
  decide +kernel

private theorem bank5_2332_2336 : Positive bank5 2332 2336 := by
  decide +kernel

private theorem bank5_2337_2349 : Positive bank5 2337 2349 := by
  decide +kernel

private theorem bank5_2350_2383 : Positive bank5 2350 2383 := by
  decide +kernel

private theorem bank5_2384_2473 : Positive bank5 2384 2473 := by
  decide +kernel

private theorem bank5_2474_2499 : Positive bank5 2474 2499 := by
  decide +kernel

theorem bank5_cover : ∃ ends, Cover bank5 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2473, 2499],
    ⟨(by decide), (by decide), bank5_2330_2331,
      (by decide), (by decide), bank5_2332_2336,
      (by decide), (by decide), bank5_2337_2349,
      (by decide), (by decide), bank5_2350_2383,
      (by decide), (by decide), bank5_2384_2473,
      (by decide), (by decide), bank5_2474_2499, rfl⟩⟩
#print axioms bank5_cover

def bank6 : Witness :=
  ⟨1, true, 256, 310, 2800, 3898, 845, 17374, 660120691015680, 6345079729296⟩

theorem bank6_nodes : P1_7_1.nodeRows bank6.shape = bank6.nodes :=
  node_check bank6 (by decide) (by decide) (by decide)

private theorem bank6_2330_2335 : Positive bank6 2330 2335 := by
  decide +kernel

private theorem bank6_2336_2351 : Positive bank6 2336 2351 := by
  decide +kernel

private theorem bank6_2352_2393 : Positive bank6 2352 2393 := by
  decide +kernel

private theorem bank6_2394_2499 : Positive bank6 2394 2499 := by
  decide +kernel

theorem bank6_cover : ∃ ends, Cover bank6 firstHeight ends := by
  exact ⟨[2335, 2351, 2393, 2499],
    ⟨(by decide), (by decide), bank6_2330_2335,
      (by decide), (by decide), bank6_2336_2351,
      (by decide), (by decide), bank6_2352_2393,
      (by decide), (by decide), bank6_2394_2499, rfl⟩⟩
#print axioms bank6_cover

def bank7 : Witness :=
  ⟨1, false, 64, 180, 3850, 5369, 1193, 35655, 1750065639325696, 23267180540138⟩

theorem bank7_nodes : P1_7_1.nodeRows bank7.shape = bank7.nodes :=
  node_check bank7 (by decide) (by decide) (by decide)

private theorem bank7_2330_2331 : Positive bank7 2330 2331 := by
  decide +kernel

private theorem bank7_2332_2336 : Positive bank7 2332 2336 := by
  decide +kernel

private theorem bank7_2337_2349 : Positive bank7 2337 2349 := by
  decide +kernel

private theorem bank7_2350_2382 : Positive bank7 2350 2382 := by
  decide +kernel

private theorem bank7_2383_2468 : Positive bank7 2383 2468 := by
  decide +kernel

private theorem bank7_2469_2499 : Positive bank7 2469 2499 := by
  decide +kernel

theorem bank7_cover : ∃ ends, Cover bank7 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2382, 2468, 2499],
    ⟨(by decide), (by decide), bank7_2330_2331,
      (by decide), (by decide), bank7_2332_2336,
      (by decide), (by decide), bank7_2337_2349,
      (by decide), (by decide), bank7_2350_2382,
      (by decide), (by decide), bank7_2383_2468,
      (by decide), (by decide), bank7_2469_2499, rfl⟩⟩
#print axioms bank7_cover

def bank8 : Witness :=
  ⟨2, true, 2, 20, 3200, 4467, 947, 57710, 970564165959680, 10751150642307⟩

theorem bank8_nodes : P1_7_1.nodeRows bank8.shape = bank8.nodes :=
  node_check bank8 (by decide) (by decide) (by decide)

private theorem bank8_2330_2331 : Positive bank8 2330 2331 := by
  decide +kernel

private theorem bank8_2332_2336 : Positive bank8 2332 2336 := by
  decide +kernel

private theorem bank8_2337_2350 : Positive bank8 2337 2350 := by
  decide +kernel

private theorem bank8_2351_2386 : Positive bank8 2351 2386 := by
  decide +kernel

private theorem bank8_2387_2482 : Positive bank8 2387 2482 := by
  decide +kernel

private theorem bank8_2483_2499 : Positive bank8 2483 2499 := by
  decide +kernel

theorem bank8_cover : ∃ ends, Cover bank8 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2386, 2482, 2499],
    ⟨(by decide), (by decide), bank8_2330_2331,
      (by decide), (by decide), bank8_2332_2336,
      (by decide), (by decide), bank8_2337_2350,
      (by decide), (by decide), bank8_2351_2386,
      (by decide), (by decide), bank8_2387_2482,
      (by decide), (by decide), bank8_2483_2499, rfl⟩⟩
#print axioms bank8_cover

def bank9 : Witness :=
  ⟨2, true, 1, 20, 3600, 5026, 1065, 62519, 1381313797160960, 17219766768880⟩

theorem bank9_nodes : P1_7_1.nodeRows bank9.shape = bank9.nodes :=
  node_check bank9 (by decide) (by decide) (by decide)

private theorem bank9_2330_2331 : Positive bank9 2330 2331 := by
  decide +kernel

private theorem bank9_2332_2336 : Positive bank9 2332 2336 := by
  decide +kernel

private theorem bank9_2337_2349 : Positive bank9 2337 2349 := by
  decide +kernel

private theorem bank9_2350_2383 : Positive bank9 2350 2383 := by
  decide +kernel

private theorem bank9_2384_2473 : Positive bank9 2384 2473 := by
  decide +kernel

private theorem bank9_2474_2499 : Positive bank9 2474 2499 := by
  decide +kernel

theorem bank9_cover : ∃ ends, Cover bank9 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2473, 2499],
    ⟨(by decide), (by decide), bank9_2330_2331,
      (by decide), (by decide), bank9_2332_2336,
      (by decide), (by decide), bank9_2337_2349,
      (by decide), (by decide), bank9_2350_2383,
      (by decide), (by decide), bank9_2384_2473,
      (by decide), (by decide), bank9_2474_2499, rfl⟩⟩
#print axioms bank9_cover

end Research6966.HelperWindowCatalogue
