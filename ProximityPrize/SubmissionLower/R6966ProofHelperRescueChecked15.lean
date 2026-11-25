import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step512 : Request :=
  ⟨⟨⟨2000, 2789, 604, 22261⟩, 240862397726720, 1663046410409⟩, 76, 5, 41, 642859⟩

theorem step512_nodes : P1_7_1.nodeRows step512.bank.shape = step512.bank.nodeRows :=
  node_check step512.bank (by decide) (by decide) (by decide)

private theorem step512_2330_2342 : Positive step512 2330 2342 := by decide +kernel

private theorem step512_2343_2377 : Positive step512 2343 2377 := by decide +kernel

private theorem step512_2378_2470 : Positive step512 2378 2470 := by decide +kernel

private theorem step512_2471_2499 : Positive step512 2471 2499 := by decide +kernel

theorem step512_cover : ∃ ends, Cover step512 firstHeight ends := by
  exact ⟨[2342, 2377, 2470, 2499],
    ⟨(by decide), (by decide), step512_2330_2342,
      (by decide), (by decide), step512_2343_2377,
      (by decide), (by decide), step512_2378_2470,
      (by decide), (by decide), step512_2471_2499, rfl⟩⟩

theorem step512_verified : Checked step512 :=
  ⟨step512_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step512_cover⟩

def step513 : Request :=
  ⟨⟨⟨2500, 3487, 775, 28173⟩, 479640131993600, 4144013596741⟩, 103, 5, 41, 642859⟩

theorem step513_nodes : P1_7_1.nodeRows step513.bank.shape = step513.bank.nodeRows :=
  node_check step513.bank (by decide) (by decide) (by decide)

private theorem step513_2330_2334 : Positive step513 2330 2334 := by decide +kernel

private theorem step513_2335_2347 : Positive step513 2335 2347 := by decide +kernel

private theorem step513_2348_2381 : Positive step513 2348 2381 := by decide +kernel

private theorem step513_2382_2470 : Positive step513 2382 2470 := by decide +kernel

private theorem step513_2471_2499 : Positive step513 2471 2499 := by decide +kernel

theorem step513_cover : ∃ ends, Cover step513 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2470, 2499],
    ⟨(by decide), (by decide), step513_2330_2334,
      (by decide), (by decide), step513_2335_2347,
      (by decide), (by decide), step513_2348_2381,
      (by decide), (by decide), step513_2382_2470,
      (by decide), (by decide), step513_2471_2499, rfl⟩⟩

theorem step513_verified : Checked step513 :=
  ⟨step513_nodes, Research6966.HelperWindowCatalogue.moment3487_775,
    (by decide), (by decide), (by decide), step513_cover⟩

def step514 : Request :=
  ⟨⟨⟨210, 293, 65, 2113⟩, 289785774080, 211692234⟩, 0, 5, 51, 642859⟩

theorem step514_nodes : P1_7_1.nodeRows step514.bank.shape = step514.bank.nodeRows :=
  node_check step514.bank (by decide) (by decide) (by decide)

private theorem step514_2330_2341 : Positive step514 2330 2341 := by decide +kernel

private theorem step514_2342_2387 : Positive step514 2342 2387 := by decide +kernel

private theorem step514_2388_2499 : Positive step514 2388 2499 := by decide +kernel

theorem step514_cover : ∃ ends, Cover step514 firstHeight ends := by
  exact ⟨[2341, 2387, 2499],
    ⟨(by decide), (by decide), step514_2330_2341,
      (by decide), (by decide), step514_2342_2387,
      (by decide), (by decide), step514_2388_2499, rfl⟩⟩

theorem step514_verified : Checked step514 :=
  ⟨step514_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step514_cover⟩

def step515 : Request :=
  ⟨⟨⟨250, 349, 76, 2377⟩, 480667500544, 418199213⟩, 1, 5, 51, 642859⟩

theorem step515_nodes : P1_7_1.nodeRows step515.bank.shape = step515.bank.nodeRows :=
  node_check step515.bank (by decide) (by decide) (by decide)

private theorem step515_2330_2374 : Positive step515 2330 2374 := by decide +kernel

private theorem step515_2375_2499 : Positive step515 2375 2499 := by decide +kernel

theorem step515_cover : ∃ ends, Cover step515 firstHeight ends := by
  exact ⟨[2374, 2499],
    ⟨(by decide), (by decide), step515_2330_2374,
      (by decide), (by decide), step515_2375_2499, rfl⟩⟩

theorem step515_verified : Checked step515 :=
  ⟨step515_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step515_cover⟩

def step516 : Request :=
  ⟨⟨⟨294, 410, 91, 2377⟩, 790165454848, 805457011⟩, 2, 5, 51, 642859⟩

theorem step516_nodes : P1_7_1.nodeRows step516.bank.shape = step516.bank.nodeRows :=
  node_check step516.bank (by decide) (by decide) (by decide)

private theorem step516_2330_2346 : Positive step516 2330 2346 := by decide +kernel

private theorem step516_2347_2404 : Positive step516 2347 2404 := by decide +kernel

private theorem step516_2405_2499 : Positive step516 2405 2499 := by decide +kernel

theorem step516_cover : ∃ ends, Cover step516 firstHeight ends := by
  exact ⟨[2346, 2404, 2499],
    ⟨(by decide), (by decide), step516_2330_2346,
      (by decide), (by decide), step516_2347_2404,
      (by decide), (by decide), step516_2405_2499, rfl⟩⟩

theorem step516_verified : Checked step516 :=
  ⟨step516_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step516_cover⟩

def step517 : Request :=
  ⟨⟨⟨294, 410, 89, 2674⟩, 777085255680, 791788817⟩, 3, 5, 51, 642859⟩

theorem step517_nodes : P1_7_1.nodeRows step517.bank.shape = step517.bank.nodeRows :=
  node_check step517.bank (by decide) (by decide) (by decide)

private theorem step517_2330_2341 : Positive step517 2330 2341 := by decide +kernel

private theorem step517_2342_2382 : Positive step517 2342 2382 := by decide +kernel

private theorem step517_2383_2499 : Positive step517 2383 2499 := by decide +kernel

theorem step517_cover : ∃ ends, Cover step517 firstHeight ends := by
  exact ⟨[2341, 2382, 2499],
    ⟨(by decide), (by decide), step517_2330_2341,
      (by decide), (by decide), step517_2342_2382,
      (by decide), (by decide), step517_2383_2499, rfl⟩⟩

theorem step517_verified : Checked step517 :=
  ⟨step517_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step517_cover⟩

def step518 : Request :=
  ⟨⟨⟨294, 410, 89, 3008⟩, 777085255680, 791788817⟩, 4, 5, 51, 642859⟩

theorem step518_nodes : P1_7_1.nodeRows step518.bank.shape = step518.bank.nodeRows :=
  node_check step518.bank (by decide) (by decide) (by decide)

private theorem step518_2330_2338 : Positive step518 2330 2338 := by decide +kernel

private theorem step518_2339_2368 : Positive step518 2339 2368 := by decide +kernel

private theorem step518_2369_2470 : Positive step518 2369 2470 := by decide +kernel

private theorem step518_2471_2499 : Positive step518 2471 2499 := by decide +kernel

theorem step518_cover : ∃ ends, Cover step518 firstHeight ends := by
  exact ⟨[2338, 2368, 2470, 2499],
    ⟨(by decide), (by decide), step518_2330_2338,
      (by decide), (by decide), step518_2339_2368,
      (by decide), (by decide), step518_2369_2470,
      (by decide), (by decide), step518_2471_2499, rfl⟩⟩

theorem step518_verified : Checked step518 :=
  ⟨step518_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step518_cover⟩

def step519 : Request :=
  ⟨⟨⟨350, 488, 106, 3008⟩, 1308168290304, 1584729438⟩, 5, 5, 51, 642859⟩

theorem step519_nodes : P1_7_1.nodeRows step519.bank.shape = step519.bank.nodeRows :=
  node_check step519.bank (by decide) (by decide) (by decide)

private theorem step519_2330_2334 : Positive step519 2330 2334 := by decide +kernel

private theorem step519_2335_2350 : Positive step519 2335 2350 := by decide +kernel

private theorem step519_2351_2401 : Positive step519 2351 2401 := by decide +kernel

private theorem step519_2402_2499 : Positive step519 2402 2499 := by decide +kernel

theorem step519_cover : ∃ ends, Cover step519 firstHeight ends := by
  exact ⟨[2334, 2350, 2401, 2499],
    ⟨(by decide), (by decide), step519_2330_2334,
      (by decide), (by decide), step519_2335_2350,
      (by decide), (by decide), step519_2351_2401,
      (by decide), (by decide), step519_2402_2499, rfl⟩⟩

theorem step519_verified : Checked step519 :=
  ⟨step519_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step519_cover⟩

def step520 : Request :=
  ⟨⟨⟨420, 586, 130, 3384⟩, 2292767784960, 3339653140⟩, 7, 5, 51, 642859⟩

theorem step520_nodes : P1_7_1.nodeRows step520.bank.shape = step520.bank.nodeRows :=
  node_check step520.bank (by decide) (by decide) (by decide)

private theorem step520_2330_2353 : Positive step520 2330 2353 := by decide +kernel

private theorem step520_2354_2427 : Positive step520 2354 2427 := by decide +kernel

private theorem step520_2428_2499 : Positive step520 2428 2499 := by decide +kernel

theorem step520_cover : ∃ ends, Cover step520 firstHeight ends := by
  exact ⟨[2353, 2427, 2499],
    ⟨(by decide), (by decide), step520_2330_2353,
      (by decide), (by decide), step520_2354_2427,
      (by decide), (by decide), step520_2428_2499, rfl⟩⟩

theorem step520_verified : Checked step520 :=
  ⟨step520_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step520_cover⟩

def step521 : Request :=
  ⟨⟨⟨420, 586, 127, 4282⟩, 2252760678400, 3279920952⟩, 10, 5, 51, 642859⟩

theorem step521_nodes : P1_7_1.nodeRows step521.bank.shape = step521.bank.nodeRows :=
  node_check step521.bank (by decide) (by decide) (by decide)

private theorem step521_2330_2336 : Positive step521 2330 2336 := by decide +kernel

private theorem step521_2337_2358 : Positive step521 2337 2358 := by decide +kernel

private theorem step521_2359_2426 : Positive step521 2359 2426 := by decide +kernel

private theorem step521_2427_2499 : Positive step521 2427 2499 := by decide +kernel

theorem step521_cover : ∃ ends, Cover step521 firstHeight ends := by
  exact ⟨[2336, 2358, 2426, 2499],
    ⟨(by decide), (by decide), step521_2330_2336,
      (by decide), (by decide), step521_2337_2358,
      (by decide), (by decide), step521_2359_2426,
      (by decide), (by decide), step521_2427_2499, rfl⟩⟩

theorem step521_verified : Checked step521 :=
  ⟨step521_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step521_cover⟩

def step522 : Request :=
  ⟨⟨⟨630, 879, 190, 5419⟩, 7559493713920, 16491913877⟩, 16, 5, 51, 642859⟩

theorem step522_nodes : P1_7_1.nodeRows step522.bank.shape = step522.bank.nodeRows :=
  node_check step522.bank (by decide) (by decide) (by decide)

private theorem step522_2330_2358 : Positive step522 2330 2358 := by decide +kernel

private theorem step522_2359_2443 : Positive step522 2359 2443 := by decide +kernel

private theorem step522_2444_2499 : Positive step522 2444 2499 := by decide +kernel

theorem step522_cover : ∃ ends, Cover step522 firstHeight ends := by
  exact ⟨[2358, 2443, 2499],
    ⟨(by decide), (by decide), step522_2330_2358,
      (by decide), (by decide), step522_2359_2443,
      (by decide), (by decide), step522_2444_2499, rfl⟩⟩

theorem step522_verified : Checked step522 :=
  ⟨step522_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step522_cover⟩

def step523 : Request :=
  ⟨⟨⟨630, 878, 195, 6096⟩, 7709474160640, 16765904450⟩, 20, 5, 51, 642859⟩

theorem step523_nodes : P1_7_1.nodeRows step523.bank.shape = step523.bank.nodeRows :=
  node_check step523.bank (by decide) (by decide) (by decide)

private theorem step523_2330_2341 : Positive step523 2330 2341 := by decide +kernel

private theorem step523_2342_2376 : Positive step523 2342 2376 := by decide +kernel

private theorem step523_2377_2477 : Positive step523 2377 2477 := by decide +kernel

private theorem step523_2478_2499 : Positive step523 2478 2499 := by decide +kernel

theorem step523_cover : ∃ ends, Cover step523 firstHeight ends := by
  exact ⟨[2341, 2376, 2477, 2499],
    ⟨(by decide), (by decide), step523_2330_2341,
      (by decide), (by decide), step523_2342_2376,
      (by decide), (by decide), step523_2377_2477,
      (by decide), (by decide), step523_2478_2499, rfl⟩⟩

theorem step523_verified : Checked step523 :=
  ⟨step523_nodes, Research6966.HelperWindowCatalogue.moment878_195,
    (by decide), (by decide), (by decide), step523_cover⟩

def step524 : Request :=
  ⟨⟨⟨900, 1255, 272, 8679⟩, 22024701870080, 68477558806⟩, 31, 5, 51, 642859⟩

theorem step524_nodes : P1_7_1.nodeRows step524.bank.shape = step524.bank.nodeRows :=
  node_check step524.bank (by decide) (by decide) (by decide)

private theorem step524_2330_2352 : Positive step524 2330 2352 := by decide +kernel

private theorem step524_2353_2417 : Positive step524 2353 2417 := by decide +kernel

private theorem step524_2418_2499 : Positive step524 2418 2499 := by decide +kernel

theorem step524_cover : ∃ ends, Cover step524 firstHeight ends := by
  exact ⟨[2352, 2417, 2499],
    ⟨(by decide), (by decide), step524_2330_2352,
      (by decide), (by decide), step524_2353_2417,
      (by decide), (by decide), step524_2418_2499, rfl⟩⟩

theorem step524_verified : Checked step524 :=
  ⟨step524_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step524_cover⟩

def step525 : Request :=
  ⟨⟨⟨900, 1255, 272, 8679⟩, 22024701870080, 68477558806⟩, 32, 5, 51, 642859⟩

theorem step525_nodes : P1_7_1.nodeRows step525.bank.shape = step525.bank.nodeRows :=
  node_check step525.bank (by decide) (by decide) (by decide)

private theorem step525_2330_2333 : Positive step525 2330 2333 := by decide +kernel

private theorem step525_2334_2344 : Positive step525 2334 2344 := by decide +kernel

private theorem step525_2345_2375 : Positive step525 2345 2375 := by decide +kernel

private theorem step525_2376_2461 : Positive step525 2376 2461 := by decide +kernel

private theorem step525_2462_2499 : Positive step525 2462 2499 := by decide +kernel

theorem step525_cover : ∃ ends, Cover step525 firstHeight ends := by
  exact ⟨[2333, 2344, 2375, 2461, 2499],
    ⟨(by decide), (by decide), step525_2330_2333,
      (by decide), (by decide), step525_2334_2344,
      (by decide), (by decide), step525_2345_2375,
      (by decide), (by decide), step525_2376_2461,
      (by decide), (by decide), step525_2462_2499, rfl⟩⟩

theorem step525_verified : Checked step525 :=
  ⟨step525_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step525_cover⟩

def step526 : Request :=
  ⟨⟨⟨1100, 1534, 341, 10983⟩, 40955142733824, 155702293064⟩, 44, 5, 51, 642859⟩

theorem step526_nodes : P1_7_1.nodeRows step526.bank.shape = step526.bank.nodeRows :=
  node_check step526.bank (by decide) (by decide) (by decide)

private theorem step526_2330_2333 : Positive step526 2330 2333 := by decide +kernel

private theorem step526_2334_2343 : Positive step526 2334 2343 := by decide +kernel

private theorem step526_2344_2371 : Positive step526 2344 2371 := by decide +kernel

private theorem step526_2372_2447 : Positive step526 2372 2447 := by decide +kernel

private theorem step526_2448_2499 : Positive step526 2448 2499 := by decide +kernel

theorem step526_cover : ∃ ends, Cover step526 firstHeight ends := by
  exact ⟨[2333, 2343, 2371, 2447, 2499],
    ⟨(by decide), (by decide), step526_2330_2333,
      (by decide), (by decide), step526_2334_2343,
      (by decide), (by decide), step526_2344_2371,
      (by decide), (by decide), step526_2372_2447,
      (by decide), (by decide), step526_2448_2499, rfl⟩⟩

theorem step526_verified : Checked step526 :=
  ⟨step526_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step526_cover⟩

def step527 : Request :=
  ⟨⟨⟨1650, 2301, 512, 17590⟩, 138129879859200, 787417379725⟩, 73, 5, 51, 642859⟩

theorem step527_nodes : P1_7_1.nodeRows step527.bank.shape = step527.bank.nodeRows :=
  node_check step527.bank (by decide) (by decide) (by decide)

private theorem step527_2330_2340 : Positive step527 2330 2340 := by decide +kernel

private theorem step527_2341_2369 : Positive step527 2341 2369 := by decide +kernel

private theorem step527_2370_2446 : Positive step527 2370 2446 := by decide +kernel

private theorem step527_2447_2499 : Positive step527 2447 2499 := by decide +kernel

theorem step527_cover : ∃ ends, Cover step527 firstHeight ends := by
  exact ⟨[2340, 2369, 2446, 2499],
    ⟨(by decide), (by decide), step527_2330_2340,
      (by decide), (by decide), step527_2341_2369,
      (by decide), (by decide), step527_2370_2446,
      (by decide), (by decide), step527_2447_2499, rfl⟩⟩

theorem step527_verified : Checked step527 :=
  ⟨step527_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step527_cover⟩

def step528 : Request :=
  ⟨⟨⟨2000, 2789, 604, 17590⟩, 240862397726720, 1663046410409⟩, 76, 5, 51, 642859⟩

theorem step528_nodes : P1_7_1.nodeRows step528.bank.shape = step528.bank.nodeRows :=
  node_check step528.bank (by decide) (by decide) (by decide)

private theorem step528_2330_2348 : Positive step528 2330 2348 := by decide +kernel

private theorem step528_2349_2399 : Positive step528 2349 2399 := by decide +kernel

private theorem step528_2400_2499 : Positive step528 2400 2499 := by decide +kernel

theorem step528_cover : ∃ ends, Cover step528 firstHeight ends := by
  exact ⟨[2348, 2399, 2499],
    ⟨(by decide), (by decide), step528_2330_2348,
      (by decide), (by decide), step528_2349_2399,
      (by decide), (by decide), step528_2400_2499, rfl⟩⟩

theorem step528_verified : Checked step528 :=
  ⟨step528_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step528_cover⟩

def step529 : Request :=
  ⟨⟨⟨2500, 3487, 775, 22261⟩, 479640131993600, 4144013596741⟩, 103, 5, 51, 642859⟩

theorem step529_nodes : P1_7_1.nodeRows step529.bank.shape = step529.bank.nodeRows :=
  node_check step529.bank (by decide) (by decide) (by decide)

private theorem step529_2330_2344 : Positive step529 2330 2344 := by decide +kernel

private theorem step529_2345_2384 : Positive step529 2345 2384 := by decide +kernel

private theorem step529_2385_2490 : Positive step529 2385 2490 := by decide +kernel

private theorem step529_2491_2499 : Positive step529 2491 2499 := by decide +kernel

theorem step529_cover : ∃ ends, Cover step529 firstHeight ends := by
  exact ⟨[2344, 2384, 2490, 2499],
    ⟨(by decide), (by decide), step529_2330_2344,
      (by decide), (by decide), step529_2345_2384,
      (by decide), (by decide), step529_2385_2490,
      (by decide), (by decide), step529_2491_2499, rfl⟩⟩

theorem step529_verified : Checked step529 :=
  ⟨step529_nodes, Research6966.HelperWindowCatalogue.moment3487_775,
    (by decide), (by decide), (by decide), step529_cover⟩

def step530 : Request :=
  ⟨⟨⟨210, 293, 63, 1671⟩, 283090354176, 206678784⟩, 0, 5, 71, 642859⟩

theorem step530_nodes : P1_7_1.nodeRows step530.bank.shape = step530.bank.nodeRows :=
  node_check step530.bank (by decide) (by decide) (by decide)

private theorem step530_2330_2331 : Positive step530 2330 2331 := by decide +kernel

private theorem step530_2332_2339 : Positive step530 2332 2339 := by decide +kernel

private theorem step530_2340_2370 : Positive step530 2340 2370 := by decide +kernel

private theorem step530_2371_2491 : Positive step530 2371 2491 := by decide +kernel

private theorem step530_2492_2499 : Positive step530 2492 2499 := by decide +kernel

theorem step530_cover : ∃ ends, Cover step530 firstHeight ends := by
  exact ⟨[2331, 2339, 2370, 2491, 2499],
    ⟨(by decide), (by decide), step530_2330_2331,
      (by decide), (by decide), step530_2332_2339,
      (by decide), (by decide), step530_2340_2370,
      (by decide), (by decide), step530_2371_2491,
      (by decide), (by decide), step530_2492_2499, rfl⟩⟩

theorem step530_verified : Checked step530 :=
  ⟨step530_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step530_cover⟩

def step531 : Request :=
  ⟨⟨⟨210, 293, 63, 1879⟩, 283090354176, 206678784⟩, 1, 5, 71, 642859⟩

theorem step531_nodes : P1_7_1.nodeRows step531.bank.shape = step531.bank.nodeRows :=
  node_check step531.bank (by decide) (by decide) (by decide)

private theorem step531_2330_2332 : Positive step531 2330 2332 := by decide +kernel

private theorem step531_2333_2343 : Positive step531 2333 2343 := by decide +kernel

private theorem step531_2344_2386 : Positive step531 2344 2386 := by decide +kernel

private theorem step531_2387_2499 : Positive step531 2387 2499 := by decide +kernel

theorem step531_cover : ∃ ends, Cover step531 firstHeight ends := by
  exact ⟨[2332, 2343, 2386, 2499],
    ⟨(by decide), (by decide), step531_2330_2332,
      (by decide), (by decide), step531_2333_2343,
      (by decide), (by decide), step531_2344_2386,
      (by decide), (by decide), step531_2387_2499, rfl⟩⟩

theorem step531_verified : Checked step531 :=
  ⟨step531_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step531_cover⟩

def step532 : Request :=
  ⟨⟨⟨210, 293, 65, 2113⟩, 289785774080, 211692234⟩, 2, 5, 71, 642859⟩

theorem step532_nodes : P1_7_1.nodeRows step532.bank.shape = step532.bank.nodeRows :=
  node_check step532.bank (by decide) (by decide) (by decide)

private theorem step532_2330_2345 : Positive step532 2330 2345 := by decide +kernel

private theorem step532_2346_2406 : Positive step532 2346 2406 := by decide +kernel

private theorem step532_2407_2499 : Positive step532 2407 2499 := by decide +kernel

theorem step532_cover : ∃ ends, Cover step532 firstHeight ends := by
  exact ⟨[2345, 2406, 2499],
    ⟨(by decide), (by decide), step532_2330_2345,
      (by decide), (by decide), step532_2346_2406,
      (by decide), (by decide), step532_2407_2499, rfl⟩⟩

theorem step532_verified : Checked step532 :=
  ⟨step532_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step532_cover⟩

def step533 : Request :=
  ⟨⟨⟨250, 348, 78, 2113⟩, 490108092416, 422716393⟩, 3, 5, 71, 642859⟩

theorem step533_nodes : P1_7_1.nodeRows step533.bank.shape = step533.bank.nodeRows :=
  node_check step533.bank (by decide) (by decide) (by decide)

private theorem step533_2330_2346 : Positive step533 2330 2346 := by decide +kernel

private theorem step533_2347_2407 : Positive step533 2347 2407 := by decide +kernel

private theorem step533_2408_2499 : Positive step533 2408 2499 := by decide +kernel

theorem step533_cover : ∃ ends, Cover step533 firstHeight ends := by
  exact ⟨[2346, 2407, 2499],
    ⟨(by decide), (by decide), step533_2330_2346,
      (by decide), (by decide), step533_2347_2407,
      (by decide), (by decide), step533_2408_2499, rfl⟩⟩

theorem step533_verified : Checked step533 :=
  ⟨step533_nodes, Research6966.HelperWindowCatalogue.moment348_78,
    (by decide), (by decide), (by decide), step533_cover⟩

def step534 : Request :=
  ⟨⟨⟨250, 348, 76, 2377⟩, 480667500544, 414368386⟩, 4, 5, 71, 642859⟩

theorem step534_nodes : P1_7_1.nodeRows step534.bank.shape = step534.bank.nodeRows :=
  node_check step534.bank (by decide) (by decide) (by decide)

private theorem step534_2330_2331 : Positive step534 2330 2331 := by decide +kernel

private theorem step534_2332_2338 : Positive step534 2332 2338 := by decide +kernel

private theorem step534_2339_2363 : Positive step534 2339 2363 := by decide +kernel

private theorem step534_2364_2453 : Positive step534 2364 2453 := by decide +kernel

private theorem step534_2454_2499 : Positive step534 2454 2499 := by decide +kernel

theorem step534_cover : ∃ ends, Cover step534 firstHeight ends := by
  exact ⟨[2331, 2338, 2363, 2453, 2499],
    ⟨(by decide), (by decide), step534_2330_2331,
      (by decide), (by decide), step534_2332_2338,
      (by decide), (by decide), step534_2339_2363,
      (by decide), (by decide), step534_2364_2453,
      (by decide), (by decide), step534_2454_2499, rfl⟩⟩

theorem step534_verified : Checked step534 :=
  ⟨step534_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step534_cover⟩

def step535 : Request :=
  ⟨⟨⟨250, 348, 78, 2674⟩, 490108092416, 422716393⟩, 5, 5, 71, 642859⟩

theorem step535_nodes : P1_7_1.nodeRows step535.bank.shape = step535.bank.nodeRows :=
  node_check step535.bank (by decide) (by decide) (by decide)

private theorem step535_2330_2331 : Positive step535 2330 2331 := by decide +kernel

private theorem step535_2332_2339 : Positive step535 2332 2339 := by decide +kernel

private theorem step535_2340_2367 : Positive step535 2340 2367 := by decide +kernel

private theorem step535_2368_2467 : Positive step535 2368 2467 := by decide +kernel

private theorem step535_2468_2499 : Positive step535 2468 2499 := by decide +kernel

theorem step535_cover : ∃ ends, Cover step535 firstHeight ends := by
  exact ⟨[2331, 2339, 2367, 2467, 2499],
    ⟨(by decide), (by decide), step535_2330_2331,
      (by decide), (by decide), step535_2332_2339,
      (by decide), (by decide), step535_2340_2367,
      (by decide), (by decide), step535_2368_2467,
      (by decide), (by decide), step535_2468_2499, rfl⟩⟩

theorem step535_verified : Checked step535 :=
  ⟨step535_nodes, Research6966.HelperWindowCatalogue.moment348_78,
    (by decide), (by decide), (by decide), step535_cover⟩

def step536 : Request :=
  ⟨⟨⟨294, 410, 91, 3008⟩, 790165454848, 805457011⟩, 7, 5, 71, 642859⟩

theorem step536_nodes : P1_7_1.nodeRows step536.bank.shape = step536.bank.nodeRows :=
  node_check step536.bank (by decide) (by decide) (by decide)

private theorem step536_2330_2348 : Positive step536 2330 2348 := by decide +kernel

private theorem step536_2349_2412 : Positive step536 2349 2412 := by decide +kernel

private theorem step536_2413_2499 : Positive step536 2413 2499 := by decide +kernel

theorem step536_cover : ∃ ends, Cover step536 firstHeight ends := by
  exact ⟨[2348, 2412, 2499],
    ⟨(by decide), (by decide), step536_2330_2348,
      (by decide), (by decide), step536_2349_2412,
      (by decide), (by decide), step536_2413_2499, rfl⟩⟩

theorem step536_verified : Checked step536 :=
  ⟨step536_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step536_cover⟩

def step537 : Request :=
  ⟨⟨⟨350, 488, 108, 3384⟩, 1326705278976, 1607754763⟩, 10, 5, 71, 642859⟩

theorem step537_nodes : P1_7_1.nodeRows step537.bank.shape = step537.bank.nodeRows :=
  node_check step537.bank (by decide) (by decide) (by decide)

private theorem step537_2330_2332 : Positive step537 2330 2332 := by decide +kernel

private theorem step537_2333_2341 : Positive step537 2333 2341 := by decide +kernel

private theorem step537_2342_2370 : Positive step537 2342 2370 := by decide +kernel

private theorem step537_2371_2463 : Positive step537 2371 2463 := by decide +kernel

private theorem step537_2464_2499 : Positive step537 2464 2499 := by decide +kernel

theorem step537_cover : ∃ ends, Cover step537 firstHeight ends := by
  exact ⟨[2332, 2341, 2370, 2463, 2499],
    ⟨(by decide), (by decide), step537_2330_2332,
      (by decide), (by decide), step537_2333_2341,
      (by decide), (by decide), step537_2342_2370,
      (by decide), (by decide), step537_2371_2463,
      (by decide), (by decide), step537_2464_2499, rfl⟩⟩

theorem step537_verified : Checked step537 :=
  ⟨step537_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step537_cover⟩

def step538 : Request :=
  ⟨⟨⟨520, 725, 157, 4282⟩, 4261264752640, 7658911630⟩, 16, 5, 71, 642859⟩

theorem step538_nodes : P1_7_1.nodeRows step538.bank.shape = step538.bank.nodeRows :=
  node_check step538.bank (by decide) (by decide) (by decide)

private theorem step538_2330_2337 : Positive step538 2330 2337 := by decide +kernel

private theorem step538_2338_2361 : Positive step538 2338 2361 := by decide +kernel

private theorem step538_2362_2432 : Positive step538 2362 2432 := by decide +kernel

private theorem step538_2433_2499 : Positive step538 2433 2499 := by decide +kernel

theorem step538_cover : ∃ ends, Cover step538 firstHeight ends := by
  exact ⟨[2337, 2361, 2432, 2499],
    ⟨(by decide), (by decide), step538_2330_2337,
      (by decide), (by decide), step538_2338_2361,
      (by decide), (by decide), step538_2362_2432,
      (by decide), (by decide), step538_2433_2499, rfl⟩⟩

theorem step538_verified : Checked step538 :=
  ⟨step538_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step538_cover⟩

def step539 : Request :=
  ⟨⟨⟨630, 878, 195, 4817⟩, 7709474160640, 16765904450⟩, 20, 5, 71, 642859⟩

theorem step539_nodes : P1_7_1.nodeRows step539.bank.shape = step539.bank.nodeRows :=
  node_check step539.bank (by decide) (by decide) (by decide)

private theorem step539_2330_2350 : Positive step539 2330 2350 := by decide +kernel

private theorem step539_2351_2410 : Positive step539 2351 2410 := by decide +kernel

private theorem step539_2411_2499 : Positive step539 2411 2499 := by decide +kernel

theorem step539_cover : ∃ ends, Cover step539 firstHeight ends := by
  exact ⟨[2350, 2410, 2499],
    ⟨(by decide), (by decide), step539_2330_2350,
      (by decide), (by decide), step539_2351_2410,
      (by decide), (by decide), step539_2411_2499, rfl⟩⟩

theorem step539_verified : Checked step539 :=
  ⟨step539_nodes, Research6966.HelperWindowCatalogue.moment878_195,
    (by decide), (by decide), (by decide), step539_cover⟩

def step540 : Request :=
  ⟨⟨⟨750, 1046, 232, 6858⟩, 12985818152960, 33687112323⟩, 31, 5, 71, 642859⟩

theorem step540_nodes : P1_7_1.nodeRows step540.bank.shape = step540.bank.nodeRows :=
  node_check step540.bank (by decide) (by decide) (by decide)

private theorem step540_2330_2352 : Positive step540 2330 2352 := by decide +kernel

private theorem step540_2353_2417 : Positive step540 2353 2417 := by decide +kernel

private theorem step540_2418_2499 : Positive step540 2418 2499 := by decide +kernel

theorem step540_cover : ∃ ends, Cover step540 firstHeight ends := by
  exact ⟨[2352, 2417, 2499],
    ⟨(by decide), (by decide), step540_2330_2352,
      (by decide), (by decide), step540_2353_2417,
      (by decide), (by decide), step540_2418_2499, rfl⟩⟩

theorem step540_verified : Checked step540 :=
  ⟨step540_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step540_cover⟩

def step541 : Request :=
  ⟨⟨⟨900, 1255, 272, 6858⟩, 22024701870080, 68477558806⟩, 32, 5, 71, 642859⟩

theorem step541_nodes : P1_7_1.nodeRows step541.bank.shape = step541.bank.nodeRows :=
  node_check step541.bank (by decide) (by decide) (by decide)

private theorem step541_2330_2337 : Positive step541 2330 2337 := by decide +kernel

private theorem step541_2338_2359 : Positive step541 2338 2359 := by decide +kernel

private theorem step541_2360_2421 : Positive step541 2360 2421 := by decide +kernel

private theorem step541_2422_2499 : Positive step541 2422 2499 := by decide +kernel

theorem step541_cover : ∃ ends, Cover step541 firstHeight ends := by
  exact ⟨[2337, 2359, 2421, 2499],
    ⟨(by decide), (by decide), step541_2330_2337,
      (by decide), (by decide), step541_2338_2359,
      (by decide), (by decide), step541_2360_2421,
      (by decide), (by decide), step541_2422_2499, rfl⟩⟩

theorem step541_verified : Checked step541 :=
  ⟨step541_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step541_cover⟩

def step542 : Request :=
  ⟨⟨⟨1100, 1534, 341, 8679⟩, 40955142733824, 155702293064⟩, 44, 5, 71, 642859⟩

theorem step542_nodes : P1_7_1.nodeRows step542.bank.shape = step542.bank.nodeRows :=
  node_check step542.bank (by decide) (by decide) (by decide)

private theorem step542_2330_2351 : Positive step542 2330 2351 := by decide +kernel

private theorem step542_2352_2411 : Positive step542 2352 2411 := by decide +kernel

private theorem step542_2412_2499 : Positive step542 2412 2499 := by decide +kernel

theorem step542_cover : ∃ ends, Cover step542 firstHeight ends := by
  exact ⟨[2351, 2411, 2499],
    ⟨(by decide), (by decide), step542_2330_2351,
      (by decide), (by decide), step542_2352_2411,
      (by decide), (by decide), step542_2412_2499, rfl⟩⟩

theorem step542_verified : Checked step542 :=
  ⟨step542_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step542_cover⟩

def step543 : Request :=
  ⟨⟨⟨1650, 2301, 498, 13899⟩, 135254251667456, 770619519922⟩, 73, 5, 71, 642859⟩

theorem step543_nodes : P1_7_1.nodeRows step543.bank.shape = step543.bank.nodeRows :=
  node_check step543.bank (by decide) (by decide) (by decide)

private theorem step543_2330_2350 : Positive step543 2330 2350 := by decide +kernel

private theorem step543_2351_2407 : Positive step543 2351 2407 := by decide +kernel

private theorem step543_2408_2499 : Positive step543 2408 2499 := by decide +kernel

theorem step543_cover : ∃ ends, Cover step543 firstHeight ends := by
  exact ⟨[2350, 2407, 2499],
    ⟨(by decide), (by decide), step543_2330_2350,
      (by decide), (by decide), step543_2351_2407,
      (by decide), (by decide), step543_2408_2499, rfl⟩⟩

theorem step543_verified : Checked step543 :=
  ⟨step543_nodes, Research6966.HelperWindowCatalogue.moment2301_498,
    (by decide), (by decide), (by decide), step543_cover⟩

def step544 : Request :=
  ⟨⟨⟨1650, 2301, 512, 13899⟩, 138129879859200, 787417379725⟩, 76, 5, 71, 642859⟩

theorem step544_nodes : P1_7_1.nodeRows step544.bank.shape = step544.bank.nodeRows :=
  node_check step544.bank (by decide) (by decide) (by decide)

private theorem step544_2330_2349 : Positive step544 2330 2349 := by decide +kernel

private theorem step544_2350_2402 : Positive step544 2350 2402 := by decide +kernel

private theorem step544_2403_2499 : Positive step544 2403 2499 := by decide +kernel

theorem step544_cover : ∃ ends, Cover step544 firstHeight ends := by
  exact ⟨[2349, 2402, 2499],
    ⟨(by decide), (by decide), step544_2330_2349,
      (by decide), (by decide), step544_2350_2402,
      (by decide), (by decide), step544_2403_2499, rfl⟩⟩

theorem step544_verified : Checked step544 :=
  ⟨step544_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step544_cover⟩

def step545 : Request :=
  ⟨⟨⟨2000, 2788, 604, 19788⟩, 240862397726720, 1661128510194⟩, 103, 5, 71, 642859⟩

theorem step545_nodes : P1_7_1.nodeRows step545.bank.shape = step545.bank.nodeRows :=
  node_check step545.bank (by decide) (by decide) (by decide)

private theorem step545_2330_2341 : Positive step545 2330 2341 := by decide +kernel

private theorem step545_2342_2373 : Positive step545 2342 2373 := by decide +kernel

private theorem step545_2374_2459 : Positive step545 2374 2459 := by decide +kernel

private theorem step545_2460_2499 : Positive step545 2460 2499 := by decide +kernel

theorem step545_cover : ∃ ends, Cover step545 firstHeight ends := by
  exact ⟨[2341, 2373, 2459, 2499],
    ⟨(by decide), (by decide), step545_2330_2341,
      (by decide), (by decide), step545_2342_2373,
      (by decide), (by decide), step545_2374_2459,
      (by decide), (by decide), step545_2460_2499, rfl⟩⟩

theorem step545_verified : Checked step545 :=
  ⟨step545_nodes, Research6966.HelperWindowCatalogue.moment2788_604,
    (by decide), (by decide), (by decide), step545_cover⟩

def step546 : Request :=
  ⟨⟨⟨294, 410, 89, 5419⟩, 777085255680, 791788817⟩, 0, 6, 1, 771431⟩

theorem step546_nodes : P1_7_1.nodeRows step546.bank.shape = step546.bank.nodeRows :=
  node_check step546.bank (by decide) (by decide) (by decide)

private theorem step546_2330_2341 : Positive step546 2330 2341 := by decide +kernel

private theorem step546_2342_2382 : Positive step546 2342 2382 := by decide +kernel

private theorem step546_2383_2499 : Positive step546 2383 2499 := by decide +kernel

theorem step546_cover : ∃ ends, Cover step546 firstHeight ends := by
  exact ⟨[2341, 2382, 2499],
    ⟨(by decide), (by decide), step546_2330_2341,
      (by decide), (by decide), step546_2342_2382,
      (by decide), (by decide), step546_2383_2499, rfl⟩⟩

theorem step546_verified : Checked step546 :=
  ⟨step546_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step546_cover⟩

def step547 : Request :=
  ⟨⟨⟨294, 410, 89, 6096⟩, 777085255680, 791788817⟩, 1, 6, 1, 771431⟩

theorem step547_nodes : P1_7_1.nodeRows step547.bank.shape = step547.bank.nodeRows :=
  node_check step547.bank (by decide) (by decide) (by decide)

private theorem step547_2330_2339 : Positive step547 2330 2339 := by decide +kernel

private theorem step547_2340_2373 : Positive step547 2340 2373 := by decide +kernel

private theorem step547_2374_2487 : Positive step547 2374 2487 := by decide +kernel

private theorem step547_2488_2499 : Positive step547 2488 2499 := by decide +kernel

theorem step547_cover : ∃ ends, Cover step547 firstHeight ends := by
  exact ⟨[2339, 2373, 2487, 2499],
    ⟨(by decide), (by decide), step547_2330_2339,
      (by decide), (by decide), step547_2340_2373,
      (by decide), (by decide), step547_2374_2487,
      (by decide), (by decide), step547_2488_2499, rfl⟩⟩

theorem step547_verified : Checked step547 :=
  ⟨step547_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step547_cover⟩

def step548 : Request :=
  ⟨⟨⟨294, 410, 91, 6858⟩, 790165454848, 805457011⟩, 2, 6, 1, 771431⟩

theorem step548_nodes : P1_7_1.nodeRows step548.bank.shape = step548.bank.nodeRows :=
  node_check step548.bank (by decide) (by decide) (by decide)

private theorem step548_2330_2342 : Positive step548 2330 2342 := by decide +kernel

private theorem step548_2343_2385 : Positive step548 2343 2385 := by decide +kernel

private theorem step548_2386_2499 : Positive step548 2386 2499 := by decide +kernel

theorem step548_cover : ∃ ends, Cover step548 firstHeight ends := by
  exact ⟨[2342, 2385, 2499],
    ⟨(by decide), (by decide), step548_2330_2342,
      (by decide), (by decide), step548_2343_2385,
      (by decide), (by decide), step548_2386_2499, rfl⟩⟩

theorem step548_verified : Checked step548 :=
  ⟨step548_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step548_cover⟩

def step549 : Request :=
  ⟨⟨⟨350, 488, 108, 6858⟩, 1326705278976, 1607754763⟩, 3, 6, 1, 771431⟩

theorem step549_nodes : P1_7_1.nodeRows step549.bank.shape = step549.bank.nodeRows :=
  node_check step549.bank (by decide) (by decide) (by decide)

private theorem step549_2330_2330 : Positive step549 2330 2330 := by decide +kernel

private theorem step549_2331_2333 : Positive step549 2331 2333 := by decide +kernel

private theorem step549_2334_2342 : Positive step549 2334 2342 := by decide +kernel

private theorem step549_2343_2371 : Positive step549 2343 2371 := by decide +kernel

private theorem step549_2372_2463 : Positive step549 2372 2463 := by decide +kernel

private theorem step549_2464_2499 : Positive step549 2464 2499 := by decide +kernel

theorem step549_cover : ∃ ends, Cover step549 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2371, 2463, 2499],
    ⟨(by decide), (by decide), step549_2330_2330,
      (by decide), (by decide), step549_2331_2333,
      (by decide), (by decide), step549_2334_2342,
      (by decide), (by decide), step549_2343_2371,
      (by decide), (by decide), step549_2372_2463,
      (by decide), (by decide), step549_2464_2499, rfl⟩⟩

theorem step549_verified : Checked step549 :=
  ⟨step549_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step549_cover⟩

def step550 : Request :=
  ⟨⟨⟨350, 488, 108, 7715⟩, 1326705278976, 1607754763⟩, 4, 6, 1, 771431⟩

theorem step550_nodes : P1_7_1.nodeRows step550.bank.shape = step550.bank.nodeRows :=
  node_check step550.bank (by decide) (by decide) (by decide)

private theorem step550_2330_2334 : Positive step550 2330 2334 := by decide +kernel

private theorem step550_2335_2350 : Positive step550 2335 2350 := by decide +kernel

private theorem step550_2351_2401 : Positive step550 2351 2401 := by decide +kernel

private theorem step550_2402_2499 : Positive step550 2402 2499 := by decide +kernel

theorem step550_cover : ∃ ends, Cover step550 firstHeight ends := by
  exact ⟨[2334, 2350, 2401, 2499],
    ⟨(by decide), (by decide), step550_2330_2334,
      (by decide), (by decide), step550_2335_2350,
      (by decide), (by decide), step550_2351_2401,
      (by decide), (by decide), step550_2402_2499, rfl⟩⟩

theorem step550_verified : Checked step550 :=
  ⟨step550_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step550_cover⟩

def step551 : Request :=
  ⟨⟨⟨350, 488, 108, 8679⟩, 1326705278976, 1607754763⟩, 5, 6, 1, 771431⟩

theorem step551_nodes : P1_7_1.nodeRows step551.bank.shape = step551.bank.nodeRows :=
  node_check step551.bank (by decide) (by decide) (by decide)

private theorem step551_2330_2332 : Positive step551 2330 2332 := by decide +kernel

private theorem step551_2333_2342 : Positive step551 2333 2342 := by decide +kernel

private theorem step551_2343_2373 : Positive step551 2343 2373 := by decide +kernel

private theorem step551_2374_2472 : Positive step551 2374 2472 := by decide +kernel

private theorem step551_2473_2499 : Positive step551 2473 2499 := by decide +kernel

theorem step551_cover : ∃ ends, Cover step551 firstHeight ends := by
  exact ⟨[2332, 2342, 2373, 2472, 2499],
    ⟨(by decide), (by decide), step551_2330_2332,
      (by decide), (by decide), step551_2333_2342,
      (by decide), (by decide), step551_2343_2373,
      (by decide), (by decide), step551_2374_2472,
      (by decide), (by decide), step551_2473_2499, rfl⟩⟩

theorem step551_verified : Checked step551 :=
  ⟨step551_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step551_cover⟩

def step552 : Request :=
  ⟨⟨⟨420, 586, 127, 9763⟩, 2252760678400, 3279920952⟩, 7, 6, 1, 771431⟩

theorem step552_nodes : P1_7_1.nodeRows step552.bank.shape = step552.bank.nodeRows :=
  node_check step552.bank (by decide) (by decide) (by decide)

private theorem step552_2330_2337 : Positive step552 2330 2337 := by decide +kernel

private theorem step552_2338_2361 : Positive step552 2338 2361 := by decide +kernel

private theorem step552_2362_2435 : Positive step552 2362 2435 := by decide +kernel

private theorem step552_2436_2499 : Positive step552 2436 2499 := by decide +kernel

theorem step552_cover : ∃ ends, Cover step552 firstHeight ends := by
  exact ⟨[2337, 2361, 2435, 2499],
    ⟨(by decide), (by decide), step552_2330_2337,
      (by decide), (by decide), step552_2338_2361,
      (by decide), (by decide), step552_2362_2435,
      (by decide), (by decide), step552_2436_2499, rfl⟩⟩

theorem step552_verified : Checked step552 :=
  ⟨step552_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step552_cover⟩

def step553 : Request :=
  ⟨⟨⟨520, 725, 157, 10983⟩, 4261264752640, 7658911630⟩, 10, 6, 1, 771431⟩

theorem step553_nodes : P1_7_1.nodeRows step553.bank.shape = step553.bank.nodeRows :=
  node_check step553.bank (by decide) (by decide) (by decide)

private theorem step553_2330_2332 : Positive step553 2330 2332 := by decide +kernel

private theorem step553_2333_2341 : Positive step553 2333 2341 := by decide +kernel

private theorem step553_2342_2367 : Positive step553 2342 2367 := by decide +kernel

private theorem step553_2368_2444 : Positive step553 2368 2444 := by decide +kernel

private theorem step553_2445_2499 : Positive step553 2445 2499 := by decide +kernel

theorem step553_cover : ∃ ends, Cover step553 firstHeight ends := by
  exact ⟨[2332, 2341, 2367, 2444, 2499],
    ⟨(by decide), (by decide), step553_2330_2332,
      (by decide), (by decide), step553_2333_2341,
      (by decide), (by decide), step553_2342_2367,
      (by decide), (by decide), step553_2368_2444,
      (by decide), (by decide), step553_2445_2499, rfl⟩⟩

theorem step553_verified : Checked step553 :=
  ⟨step553_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step553_cover⟩

def step554 : Request :=
  ⟨⟨⟨750, 1046, 226, 13899⟩, 12730741817344, 33009058589⟩, 16, 6, 1, 771431⟩

theorem step554_nodes : P1_7_1.nodeRows step554.bank.shape = step554.bank.nodeRows :=
  node_check step554.bank (by decide) (by decide) (by decide)

private theorem step554_2330_2335 : Positive step554 2330 2335 := by decide +kernel

private theorem step554_2336_2352 : Positive step554 2336 2352 := by decide +kernel

private theorem step554_2353_2400 : Positive step554 2353 2400 := by decide +kernel

private theorem step554_2401_2499 : Positive step554 2401 2499 := by decide +kernel

theorem step554_cover : ∃ ends, Cover step554 firstHeight ends := by
  exact ⟨[2335, 2352, 2400, 2499],
    ⟨(by decide), (by decide), step554_2330_2335,
      (by decide), (by decide), step554_2336_2352,
      (by decide), (by decide), step554_2353_2400,
      (by decide), (by decide), step554_2401_2499, rfl⟩⟩

theorem step554_verified : Checked step554 :=
  ⟨step554_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step554_cover⟩

def step555 : Request :=
  ⟨⟨⟨900, 1256, 279, 15636⟩, 22452680785920, 70021105933⟩, 20, 6, 1, 771431⟩

theorem step555_nodes : P1_7_1.nodeRows step555.bank.shape = step555.bank.nodeRows :=
  node_check step555.bank (by decide) (by decide) (by decide)

private theorem step555_2330_2344 : Positive step555 2330 2344 := by decide +kernel

private theorem step555_2345_2386 : Positive step555 2345 2386 := by decide +kernel

private theorem step555_2387_2499 : Positive step555 2387 2499 := by decide +kernel

theorem step555_cover : ∃ ends, Cover step555 firstHeight ends := by
  exact ⟨[2344, 2386, 2499],
    ⟨(by decide), (by decide), step555_2330_2344,
      (by decide), (by decide), step555_2345_2386,
      (by decide), (by decide), step555_2387_2499, rfl⟩⟩

theorem step555_verified : Checked step555 :=
  ⟨step555_nodes, Research6966.HelperWindowCatalogue.moment1256_279,
    (by decide), (by decide), (by decide), step555_cover⟩

def step556 : Request :=
  ⟨⟨⟨900, 1255, 279, 25043⟩, 22452680785920, 69841856233⟩, 31, 6, 1, 771431⟩

theorem step556_nodes : P1_7_1.nodeRows step556.bank.shape = step556.bank.nodeRows :=
  node_check step556.bank (by decide) (by decide) (by decide)

private theorem step556_2330_2338 : Positive step556 2330 2338 := by decide +kernel

private theorem step556_2339_2362 : Positive step556 2339 2362 := by decide +kernel

private theorem step556_2363_2429 : Positive step556 2363 2429 := by decide +kernel

private theorem step556_2430_2499 : Positive step556 2430 2499 := by decide +kernel

theorem step556_cover : ∃ ends, Cover step556 firstHeight ends := by
  exact ⟨[2338, 2362, 2429, 2499],
    ⟨(by decide), (by decide), step556_2330_2338,
      (by decide), (by decide), step556_2339_2362,
      (by decide), (by decide), step556_2363_2429,
      (by decide), (by decide), step556_2430_2499, rfl⟩⟩

theorem step556_verified : Checked step556 :=
  ⟨step556_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step556_cover⟩

def step557 : Request :=
  ⟨⟨⟨1100, 1534, 341, 22261⟩, 40955142733824, 155702293064⟩, 32, 6, 1, 771431⟩

theorem step557_nodes : P1_7_1.nodeRows step557.bank.shape = step557.bank.nodeRows :=
  node_check step557.bank (by decide) (by decide) (by decide)

private theorem step557_2330_2340 : Positive step557 2330 2340 := by decide +kernel

private theorem step557_2341_2369 : Positive step557 2341 2369 := by decide +kernel

private theorem step557_2370_2448 : Positive step557 2370 2448 := by decide +kernel

private theorem step557_2449_2499 : Positive step557 2449 2499 := by decide +kernel

theorem step557_cover : ∃ ends, Cover step557 firstHeight ends := by
  exact ⟨[2340, 2369, 2448, 2499],
    ⟨(by decide), (by decide), step557_2330_2340,
      (by decide), (by decide), step557_2341_2369,
      (by decide), (by decide), step557_2370_2448,
      (by decide), (by decide), step557_2449_2499, rfl⟩⟩

theorem step557_verified : Checked step557 :=
  ⟨step557_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step557_cover⟩

def step558 : Request :=
  ⟨⟨⟨1350, 1883, 408, 31694⟩, 74202776600576, 346190054868⟩, 44, 6, 1, 771431⟩

theorem step558_nodes : P1_7_1.nodeRows step558.bank.shape = step558.bank.nodeRows :=
  node_check step558.bank (by decide) (by decide) (by decide)

private theorem step558_2330_2354 : Positive step558 2330 2354 := by decide +kernel

private theorem step558_2355_2422 : Positive step558 2355 2422 := by decide +kernel

private theorem step558_2423_2499 : Positive step558 2423 2499 := by decide +kernel

theorem step558_cover : ∃ ends, Cover step558 firstHeight ends := by
  exact ⟨[2354, 2422, 2499],
    ⟨(by decide), (by decide), step558_2330_2354,
      (by decide), (by decide), step558_2355_2422,
      (by decide), (by decide), step558_2423_2499, rfl⟩⟩

theorem step558_verified : Checked step558 :=
  ⟨step558_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step558_cover⟩

def step559 : Request :=
  ⟨⟨⟨2000, 2790, 620, 45124⟩, 245690786119680, 1699185179819⟩, 73, 6, 1, 771431⟩

theorem step559_nodes : P1_7_1.nodeRows step559.bank.shape = step559.bank.nodeRows :=
  node_check step559.bank (by decide) (by decide) (by decide)

private theorem step559_2330_2333 : Positive step559 2330 2333 := by decide +kernel

private theorem step559_2334_2343 : Positive step559 2334 2343 := by decide +kernel

private theorem step559_2344_2369 : Positive step559 2344 2369 := by decide +kernel

private theorem step559_2370_2438 : Positive step559 2370 2438 := by decide +kernel

private theorem step559_2439_2499 : Positive step559 2439 2499 := by decide +kernel

theorem step559_cover : ∃ ends, Cover step559 firstHeight ends := by
  exact ⟨[2333, 2343, 2369, 2438, 2499],
    ⟨(by decide), (by decide), step559_2330_2333,
      (by decide), (by decide), step559_2334_2343,
      (by decide), (by decide), step559_2344_2369,
      (by decide), (by decide), step559_2370_2438,
      (by decide), (by decide), step559_2439_2499, rfl⟩⟩

theorem step559_verified : Checked step559 :=
  ⟨step559_nodes, Research6966.HelperWindowCatalogue.moment2790_620,
    (by decide), (by decide), (by decide), step559_cover⟩

def step560 : Request :=
  ⟨⟨⟨2000, 2789, 604, 50764⟩, 240862397726720, 1663046410409⟩, 76, 6, 1, 771431⟩

theorem step560_nodes : P1_7_1.nodeRows step560.bank.shape = step560.bank.nodeRows :=
  node_check step560.bank (by decide) (by decide) (by decide)

private theorem step560_2330_2334 : Positive step560 2330 2334 := by decide +kernel

private theorem step560_2335_2347 : Positive step560 2335 2347 := by decide +kernel

private theorem step560_2348_2382 : Positive step560 2348 2382 := by decide +kernel

private theorem step560_2383_2475 : Positive step560 2383 2475 := by decide +kernel

private theorem step560_2476_2499 : Positive step560 2476 2499 := by decide +kernel

theorem step560_cover : ∃ ends, Cover step560 firstHeight ends := by
  exact ⟨[2334, 2347, 2382, 2475, 2499],
    ⟨(by decide), (by decide), step560_2330_2334,
      (by decide), (by decide), step560_2335_2347,
      (by decide), (by decide), step560_2348_2382,
      (by decide), (by decide), step560_2383_2475,
      (by decide), (by decide), step560_2476_2499, rfl⟩⟩

theorem step560_verified : Checked step560 :=
  ⟨step560_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step560_cover⟩

def step561 : Request :=
  ⟨⟨⟨3500, 4883, 1085, 57109⟩, 1315428062986240, 15921388386716⟩, 103, 6, 1, 771431⟩

theorem step561_nodes : P1_7_1.nodeRows step561.bank.shape = step561.bank.nodeRows :=
  node_check step561.bank (by decide) (by decide) (by decide)

private theorem step561_2330_2334 : Positive step561 2330 2334 := by decide +kernel

private theorem step561_2335_2347 : Positive step561 2335 2347 := by decide +kernel

private theorem step561_2348_2380 : Positive step561 2348 2380 := by decide +kernel

private theorem step561_2381_2466 : Positive step561 2381 2466 := by decide +kernel

private theorem step561_2467_2499 : Positive step561 2467 2499 := by decide +kernel

theorem step561_cover : ∃ ends, Cover step561 firstHeight ends := by
  exact ⟨[2334, 2347, 2380, 2466, 2499],
    ⟨(by decide), (by decide), step561_2330_2334,
      (by decide), (by decide), step561_2335_2347,
      (by decide), (by decide), step561_2348_2380,
      (by decide), (by decide), step561_2381_2466,
      (by decide), (by decide), step561_2467_2499, rfl⟩⟩

theorem step561_verified : Checked step561 :=
  ⟨step561_nodes, Research6966.HelperWindowCatalogue.moment4883_1085,
    (by decide), (by decide), (by decide), step561_cover⟩

def step562 : Request :=
  ⟨⟨⟨294, 410, 89, 5419⟩, 777085255680, 791788817⟩, 0, 6, 2, 771431⟩

theorem step562_nodes : P1_7_1.nodeRows step562.bank.shape = step562.bank.nodeRows :=
  node_check step562.bank (by decide) (by decide) (by decide)

private theorem step562_2330_2353 : Positive step562 2330 2353 := by decide +kernel

private theorem step562_2354_2434 : Positive step562 2354 2434 := by decide +kernel

private theorem step562_2435_2499 : Positive step562 2435 2499 := by decide +kernel

theorem step562_cover : ∃ ends, Cover step562 firstHeight ends := by
  exact ⟨[2353, 2434, 2499],
    ⟨(by decide), (by decide), step562_2330_2353,
      (by decide), (by decide), step562_2354_2434,
      (by decide), (by decide), step562_2435_2499, rfl⟩⟩

theorem step562_verified : Checked step562 :=
  ⟨step562_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step562_cover⟩

def step563 : Request :=
  ⟨⟨⟨294, 410, 89, 6096⟩, 777085255680, 791788817⟩, 1, 6, 2, 771431⟩

theorem step563_nodes : P1_7_1.nodeRows step563.bank.shape = step563.bank.nodeRows :=
  node_check step563.bank (by decide) (by decide) (by decide)

private theorem step563_2330_2349 : Positive step563 2330 2349 := by decide +kernel

private theorem step563_2350_2417 : Positive step563 2350 2417 := by decide +kernel

private theorem step563_2418_2499 : Positive step563 2418 2499 := by decide +kernel

theorem step563_cover : ∃ ends, Cover step563 firstHeight ends := by
  exact ⟨[2349, 2417, 2499],
    ⟨(by decide), (by decide), step563_2330_2349,
      (by decide), (by decide), step563_2350_2417,
      (by decide), (by decide), step563_2418_2499, rfl⟩⟩

theorem step563_verified : Checked step563 :=
  ⟨step563_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step563_cover⟩

def step564 : Request :=
  ⟨⟨⟨350, 488, 108, 6096⟩, 1326705278976, 1607754763⟩, 2, 6, 2, 771431⟩

theorem step564_nodes : P1_7_1.nodeRows step564.bank.shape = step564.bank.nodeRows :=
  node_check step564.bank (by decide) (by decide) (by decide)

private theorem step564_2330_2330 : Positive step564 2330 2330 := by decide +kernel

private theorem step564_2331_2333 : Positive step564 2331 2333 := by decide +kernel

private theorem step564_2334_2342 : Positive step564 2334 2342 := by decide +kernel

private theorem step564_2343_2371 : Positive step564 2343 2371 := by decide +kernel

private theorem step564_2372_2463 : Positive step564 2372 2463 := by decide +kernel

private theorem step564_2464_2499 : Positive step564 2464 2499 := by decide +kernel

theorem step564_cover : ∃ ends, Cover step564 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2371, 2463, 2499],
    ⟨(by decide), (by decide), step564_2330_2330,
      (by decide), (by decide), step564_2331_2333,
      (by decide), (by decide), step564_2334_2342,
      (by decide), (by decide), step564_2343_2371,
      (by decide), (by decide), step564_2372_2463,
      (by decide), (by decide), step564_2464_2499, rfl⟩⟩

theorem step564_verified : Checked step564 :=
  ⟨step564_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step564_cover⟩

def step565 : Request :=
  ⟨⟨⟨350, 488, 108, 6858⟩, 1326705278976, 1607754763⟩, 3, 6, 2, 771431⟩

theorem step565_nodes : P1_7_1.nodeRows step565.bank.shape = step565.bank.nodeRows :=
  node_check step565.bank (by decide) (by decide) (by decide)

private theorem step565_2330_2340 : Positive step565 2330 2340 := by decide +kernel

private theorem step565_2341_2375 : Positive step565 2341 2375 := by decide +kernel

private theorem step565_2376_2487 : Positive step565 2376 2487 := by decide +kernel

private theorem step565_2488_2499 : Positive step565 2488 2499 := by decide +kernel

theorem step565_cover : ∃ ends, Cover step565 firstHeight ends := by
  exact ⟨[2340, 2375, 2487, 2499],
    ⟨(by decide), (by decide), step565_2330_2340,
      (by decide), (by decide), step565_2341_2375,
      (by decide), (by decide), step565_2376_2487,
      (by decide), (by decide), step565_2488_2499, rfl⟩⟩

theorem step565_verified : Checked step565 :=
  ⟨step565_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step565_cover⟩

def step566 : Request :=
  ⟨⟨⟨350, 488, 106, 7715⟩, 1308168290304, 1584729438⟩, 4, 6, 2, 771431⟩

theorem step566_nodes : P1_7_1.nodeRows step566.bank.shape = step566.bank.nodeRows :=
  node_check step566.bank (by decide) (by decide) (by decide)

private theorem step566_2330_2331 : Positive step566 2330 2331 := by decide +kernel

private theorem step566_2332_2338 : Positive step566 2332 2338 := by decide +kernel

private theorem step566_2339_2360 : Positive step566 2339 2360 := by decide +kernel

private theorem step566_2361_2430 : Positive step566 2361 2430 := by decide +kernel

private theorem step566_2431_2499 : Positive step566 2431 2499 := by decide +kernel

theorem step566_cover : ∃ ends, Cover step566 firstHeight ends := by
  exact ⟨[2331, 2338, 2360, 2430, 2499],
    ⟨(by decide), (by decide), step566_2330_2331,
      (by decide), (by decide), step566_2332_2338,
      (by decide), (by decide), step566_2339_2360,
      (by decide), (by decide), step566_2361_2430,
      (by decide), (by decide), step566_2431_2499, rfl⟩⟩

theorem step566_verified : Checked step566 :=
  ⟨step566_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step566_cover⟩

def step567 : Request :=
  ⟨⟨⟨420, 586, 130, 7715⟩, 2292767784960, 3339653140⟩, 5, 6, 2, 771431⟩

theorem step567_nodes : P1_7_1.nodeRows step567.bank.shape = step567.bank.nodeRows :=
  node_check step567.bank (by decide) (by decide) (by decide)

private theorem step567_2330_2335 : Positive step567 2330 2335 := by decide +kernel

private theorem step567_2336_2354 : Positive step567 2336 2354 := by decide +kernel

private theorem step567_2355_2411 : Positive step567 2355 2411 := by decide +kernel

private theorem step567_2412_2499 : Positive step567 2412 2499 := by decide +kernel

theorem step567_cover : ∃ ends, Cover step567 firstHeight ends := by
  exact ⟨[2335, 2354, 2411, 2499],
    ⟨(by decide), (by decide), step567_2330_2335,
      (by decide), (by decide), step567_2336_2354,
      (by decide), (by decide), step567_2355_2411,
      (by decide), (by decide), step567_2412_2499, rfl⟩⟩

theorem step567_verified : Checked step567 :=
  ⟨step567_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step567_cover⟩

def step568 : Request :=
  ⟨⟨⟨420, 586, 127, 9763⟩, 2252760678400, 3279920952⟩, 7, 6, 2, 771431⟩

theorem step568_nodes : P1_7_1.nodeRows step568.bank.shape = step568.bank.nodeRows :=
  node_check step568.bank (by decide) (by decide) (by decide)

private theorem step568_2330_2345 : Positive step568 2330 2345 := by decide +kernel

private theorem step568_2346_2395 : Positive step568 2346 2395 := by decide +kernel

private theorem step568_2396_2499 : Positive step568 2396 2499 := by decide +kernel

theorem step568_cover : ∃ ends, Cover step568 firstHeight ends := by
  exact ⟨[2345, 2395, 2499],
    ⟨(by decide), (by decide), step568_2330_2345,
      (by decide), (by decide), step568_2346_2395,
      (by decide), (by decide), step568_2396_2499, rfl⟩⟩

theorem step568_verified : Checked step568 :=
  ⟨step568_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step568_cover⟩

def step569 : Request :=
  ⟨⟨⟨520, 725, 157, 10983⟩, 4261264752640, 7658911630⟩, 10, 6, 2, 771431⟩

theorem step569_nodes : P1_7_1.nodeRows step569.bank.shape = step569.bank.nodeRows :=
  node_check step569.bank (by decide) (by decide) (by decide)

private theorem step569_2330_2341 : Positive step569 2330 2341 := by decide +kernel

private theorem step569_2342_2376 : Positive step569 2342 2376 := by decide +kernel

private theorem step569_2377_2481 : Positive step569 2377 2481 := by decide +kernel

private theorem step569_2482_2499 : Positive step569 2482 2499 := by decide +kernel

theorem step569_cover : ∃ ends, Cover step569 firstHeight ends := by
  exact ⟨[2341, 2376, 2481, 2499],
    ⟨(by decide), (by decide), step569_2330_2341,
      (by decide), (by decide), step569_2342_2376,
      (by decide), (by decide), step569_2377_2481,
      (by decide), (by decide), step569_2482_2499, rfl⟩⟩

theorem step569_verified : Checked step569 :=
  ⟨step569_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step569_cover⟩

def step570 : Request :=
  ⟨⟨⟨750, 1046, 226, 13899⟩, 12730741817344, 33009058589⟩, 16, 6, 2, 771431⟩

theorem step570_nodes : P1_7_1.nodeRows step570.bank.shape = step570.bank.nodeRows :=
  node_check step570.bank (by decide) (by decide) (by decide)

private theorem step570_2330_2344 : Positive step570 2330 2344 := by decide +kernel

private theorem step570_2345_2387 : Positive step570 2345 2387 := by decide +kernel

private theorem step570_2388_2499 : Positive step570 2388 2499 := by decide +kernel

theorem step570_cover : ∃ ends, Cover step570 firstHeight ends := by
  exact ⟨[2344, 2387, 2499],
    ⟨(by decide), (by decide), step570_2330_2344,
      (by decide), (by decide), step570_2345_2387,
      (by decide), (by decide), step570_2388_2499, rfl⟩⟩

theorem step570_verified : Checked step570 :=
  ⟨step570_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step570_cover⟩

def step571 : Request :=
  ⟨⟨⟨900, 1256, 272, 15636⟩, 22024701870080, 68653176066⟩, 20, 6, 2, 771431⟩

theorem step571_nodes : P1_7_1.nodeRows step571.bank.shape = step571.bank.nodeRows :=
  node_check step571.bank (by decide) (by decide) (by decide)

private theorem step571_2330_2338 : Positive step571 2330 2338 := by decide +kernel

private theorem step571_2339_2362 : Positive step571 2339 2362 := by decide +kernel

private theorem step571_2363_2429 : Positive step571 2363 2429 := by decide +kernel

private theorem step571_2430_2499 : Positive step571 2430 2499 := by decide +kernel

theorem step571_cover : ∃ ends, Cover step571 firstHeight ends := by
  exact ⟨[2338, 2362, 2429, 2499],
    ⟨(by decide), (by decide), step571_2330_2338,
      (by decide), (by decide), step571_2339_2362,
      (by decide), (by decide), step571_2363_2429,
      (by decide), (by decide), step571_2430_2499, rfl⟩⟩

theorem step571_verified : Checked step571 :=
  ⟨step571_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step571_cover⟩

def step572 : Request :=
  ⟨⟨⟨900, 1255, 279, 25043⟩, 22452680785920, 69841856233⟩, 31, 6, 2, 771431⟩

theorem step572_nodes : P1_7_1.nodeRows step572.bank.shape = step572.bank.nodeRows :=
  node_check step572.bank (by decide) (by decide) (by decide)

private theorem step572_2330_2344 : Positive step572 2330 2344 := by decide +kernel

private theorem step572_2345_2385 : Positive step572 2345 2385 := by decide +kernel

private theorem step572_2386_2499 : Positive step572 2386 2499 := by decide +kernel

theorem step572_cover : ∃ ends, Cover step572 firstHeight ends := by
  exact ⟨[2344, 2385, 2499],
    ⟨(by decide), (by decide), step572_2330_2344,
      (by decide), (by decide), step572_2345_2385,
      (by decide), (by decide), step572_2386_2499, rfl⟩⟩

theorem step572_verified : Checked step572 :=
  ⟨step572_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step572_cover⟩

def step573 : Request :=
  ⟨⟨⟨1100, 1534, 332, 22261⟩, 40133103452160, 152499774767⟩, 32, 6, 2, 771431⟩

theorem step573_nodes : P1_7_1.nodeRows step573.bank.shape = step573.bank.nodeRows :=
  node_check step573.bank (by decide) (by decide) (by decide)

private theorem step573_2330_2330 : Positive step573 2330 2330 := by decide +kernel

private theorem step573_2331_2333 : Positive step573 2331 2333 := by decide +kernel

private theorem step573_2334_2341 : Positive step573 2334 2341 := by decide +kernel

private theorem step573_2342_2363 : Positive step573 2342 2363 := by decide +kernel

private theorem step573_2364_2423 : Positive step573 2364 2423 := by decide +kernel

private theorem step573_2424_2499 : Positive step573 2424 2499 := by decide +kernel

theorem step573_cover : ∃ ends, Cover step573 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2423, 2499],
    ⟨(by decide), (by decide), step573_2330_2330,
      (by decide), (by decide), step573_2331_2333,
      (by decide), (by decide), step573_2334_2341,
      (by decide), (by decide), step573_2342_2363,
      (by decide), (by decide), step573_2364_2423,
      (by decide), (by decide), step573_2424_2499, rfl⟩⟩

theorem step573_verified : Checked step573 :=
  ⟨step573_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step573_cover⟩

def step574 : Request :=
  ⟨⟨⟨1350, 1883, 418, 28173⟩, 75578221264896, 352769102024⟩, 44, 6, 2, 771431⟩

theorem step574_nodes : P1_7_1.nodeRows step574.bank.shape = step574.bank.nodeRows :=
  node_check step574.bank (by decide) (by decide) (by decide)

private theorem step574_2330_2332 : Positive step574 2330 2332 := by decide +kernel

private theorem step574_2333_2340 : Positive step574 2333 2340 := by decide +kernel

private theorem step574_2341_2361 : Positive step574 2341 2361 := by decide +kernel

private theorem step574_2362_2418 : Positive step574 2362 2418 := by decide +kernel

private theorem step574_2419_2499 : Positive step574 2419 2499 := by decide +kernel

theorem step574_cover : ∃ ends, Cover step574 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2418, 2499],
    ⟨(by decide), (by decide), step574_2330_2332,
      (by decide), (by decide), step574_2333_2340,
      (by decide), (by decide), step574_2341_2361,
      (by decide), (by decide), step574_2362_2418,
      (by decide), (by decide), step574_2419_2499, rfl⟩⟩

theorem step574_verified : Checked step574 :=
  ⟨step574_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step574_cover⟩

def step575 : Request :=
  ⟨⟨⟨2000, 2790, 620, 45124⟩, 245690786119680, 1699185179819⟩, 73, 6, 2, 771431⟩

theorem step575_nodes : P1_7_1.nodeRows step575.bank.shape = step575.bank.nodeRows :=
  node_check step575.bank (by decide) (by decide) (by decide)

private theorem step575_2330_2340 : Positive step575 2330 2340 := by decide +kernel

private theorem step575_2341_2369 : Positive step575 2341 2369 := by decide +kernel

private theorem step575_2370_2446 : Positive step575 2370 2446 := by decide +kernel

private theorem step575_2447_2499 : Positive step575 2447 2499 := by decide +kernel

theorem step575_cover : ∃ ends, Cover step575 firstHeight ends := by
  exact ⟨[2340, 2369, 2446, 2499],
    ⟨(by decide), (by decide), step575_2330_2340,
      (by decide), (by decide), step575_2341_2369,
      (by decide), (by decide), step575_2370_2446,
      (by decide), (by decide), step575_2447_2499, rfl⟩⟩

theorem step575_verified : Checked step575 :=
  ⟨step575_nodes, Research6966.HelperWindowCatalogue.moment2790_620,
    (by decide), (by decide), (by decide), step575_cover⟩

def step576 : Request :=
  ⟨⟨⟨2000, 2789, 604, 50764⟩, 240862397726720, 1663046410409⟩, 76, 6, 2, 771431⟩

theorem step576_nodes : P1_7_1.nodeRows step576.bank.shape = step576.bank.nodeRows :=
  node_check step576.bank (by decide) (by decide) (by decide)

private theorem step576_2330_2341 : Positive step576 2330 2341 := by decide +kernel

private theorem step576_2342_2373 : Positive step576 2342 2373 := by decide +kernel

private theorem step576_2374_2458 : Positive step576 2374 2458 := by decide +kernel

private theorem step576_2459_2499 : Positive step576 2459 2499 := by decide +kernel

theorem step576_cover : ∃ ends, Cover step576 firstHeight ends := by
  exact ⟨[2341, 2373, 2458, 2499],
    ⟨(by decide), (by decide), step576_2330_2341,
      (by decide), (by decide), step576_2342_2373,
      (by decide), (by decide), step576_2374_2458,
      (by decide), (by decide), step576_2459_2499, rfl⟩⟩

theorem step576_verified : Checked step576 :=
  ⟨step576_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step576_cover⟩

end Research6966.HelperRescueCatalogue
