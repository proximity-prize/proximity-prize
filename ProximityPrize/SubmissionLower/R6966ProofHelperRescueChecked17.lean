import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step626 : Request :=
  ⟨⟨⟨210, 293, 65, 3807⟩, 289785774080, 211692234⟩, 0, 6, 26, 771431⟩

theorem step626_nodes : P1_7_1.nodeRows step626.bank.shape = step626.bank.nodeRows :=
  node_check step626.bank (by decide) (by decide) (by decide)

private theorem step626_2330_2340 : Positive step626 2330 2340 := by decide +kernel

private theorem step626_2341_2382 : Positive step626 2341 2382 := by decide +kernel

private theorem step626_2383_2499 : Positive step626 2383 2499 := by decide +kernel

theorem step626_cover : ∃ ends, Cover step626 firstHeight ends := by
  exact ⟨[2340, 2382, 2499],
    ⟨(by decide), (by decide), step626_2330_2340,
      (by decide), (by decide), step626_2341_2382,
      (by decide), (by decide), step626_2383_2499, rfl⟩⟩

theorem step626_verified : Checked step626 :=
  ⟨step626_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step626_cover⟩

def step627 : Request :=
  ⟨⟨⟨250, 349, 76, 3807⟩, 480667500544, 418199213⟩, 1, 6, 26, 771431⟩

theorem step627_nodes : P1_7_1.nodeRows step627.bank.shape = step627.bank.nodeRows :=
  node_check step627.bank (by decide) (by decide) (by decide)

private theorem step627_2330_2338 : Positive step627 2330 2338 := by decide +kernel

private theorem step627_2339_2370 : Positive step627 2339 2370 := by decide +kernel

private theorem step627_2371_2483 : Positive step627 2371 2483 := by decide +kernel

private theorem step627_2484_2499 : Positive step627 2484 2499 := by decide +kernel

theorem step627_cover : ∃ ends, Cover step627 firstHeight ends := by
  exact ⟨[2338, 2370, 2483, 2499],
    ⟨(by decide), (by decide), step627_2330_2338,
      (by decide), (by decide), step627_2339_2370,
      (by decide), (by decide), step627_2371_2483,
      (by decide), (by decide), step627_2484_2499, rfl⟩⟩

theorem step627_verified : Checked step627 :=
  ⟨step627_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step627_cover⟩

def step628 : Request :=
  ⟨⟨⟨294, 410, 91, 3807⟩, 790165454848, 805457011⟩, 2, 6, 26, 771431⟩

theorem step628_nodes : P1_7_1.nodeRows step628.bank.shape = step628.bank.nodeRows :=
  node_check step628.bank (by decide) (by decide) (by decide)

private theorem step628_2330_2342 : Positive step628 2330 2342 := by decide +kernel

private theorem step628_2343_2386 : Positive step628 2343 2386 := by decide +kernel

private theorem step628_2387_2499 : Positive step628 2387 2499 := by decide +kernel

theorem step628_cover : ∃ ends, Cover step628 firstHeight ends := by
  exact ⟨[2342, 2386, 2499],
    ⟨(by decide), (by decide), step628_2330_2342,
      (by decide), (by decide), step628_2343_2386,
      (by decide), (by decide), step628_2387_2499, rfl⟩⟩

theorem step628_verified : Checked step628 :=
  ⟨step628_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step628_cover⟩

def step629 : Request :=
  ⟨⟨⟨294, 410, 91, 4282⟩, 790165454848, 805457011⟩, 3, 6, 26, 771431⟩

theorem step629_nodes : P1_7_1.nodeRows step629.bank.shape = step629.bank.nodeRows :=
  node_check step629.bank (by decide) (by decide) (by decide)

private theorem step629_2330_2330 : Positive step629 2330 2330 := by decide +kernel

private theorem step629_2331_2334 : Positive step629 2331 2334 := by decide +kernel

private theorem step629_2335_2347 : Positive step629 2335 2347 := by decide +kernel

private theorem step629_2348_2390 : Positive step629 2348 2390 := by decide +kernel

private theorem step629_2391_2499 : Positive step629 2391 2499 := by decide +kernel

theorem step629_cover : ∃ ends, Cover step629 firstHeight ends := by
  exact ⟨[2330, 2334, 2347, 2390, 2499],
    ⟨(by decide), (by decide), step629_2330_2330,
      (by decide), (by decide), step629_2331_2334,
      (by decide), (by decide), step629_2335_2347,
      (by decide), (by decide), step629_2348_2390,
      (by decide), (by decide), step629_2391_2499, rfl⟩⟩

theorem step629_verified : Checked step629 :=
  ⟨step629_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step629_cover⟩

def step630 : Request :=
  ⟨⟨⟨350, 488, 108, 4282⟩, 1326705278976, 1607754763⟩, 4, 6, 26, 771431⟩

theorem step630_nodes : P1_7_1.nodeRows step630.bank.shape = step630.bank.nodeRows :=
  node_check step630.bank (by decide) (by decide) (by decide)

private theorem step630_2330_2331 : Positive step630 2330 2331 := by decide +kernel

private theorem step630_2332_2338 : Positive step630 2332 2338 := by decide +kernel

private theorem step630_2339_2360 : Positive step630 2339 2360 := by decide +kernel

private theorem step630_2361_2430 : Positive step630 2361 2430 := by decide +kernel

private theorem step630_2431_2499 : Positive step630 2431 2499 := by decide +kernel

theorem step630_cover : ∃ ends, Cover step630 firstHeight ends := by
  exact ⟨[2331, 2338, 2360, 2430, 2499],
    ⟨(by decide), (by decide), step630_2330_2331,
      (by decide), (by decide), step630_2332_2338,
      (by decide), (by decide), step630_2339_2360,
      (by decide), (by decide), step630_2361_2430,
      (by decide), (by decide), step630_2431_2499, rfl⟩⟩

theorem step630_verified : Checked step630 :=
  ⟨step630_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step630_cover⟩

def step631 : Request :=
  ⟨⟨⟨350, 488, 108, 4817⟩, 1326705278976, 1607754763⟩, 5, 6, 26, 771431⟩

theorem step631_nodes : P1_7_1.nodeRows step631.bank.shape = step631.bank.nodeRows :=
  node_check step631.bank (by decide) (by decide) (by decide)

private theorem step631_2330_2334 : Positive step631 2330 2334 := by decide +kernel

private theorem step631_2335_2350 : Positive step631 2335 2350 := by decide +kernel

private theorem step631_2351_2401 : Positive step631 2351 2401 := by decide +kernel

private theorem step631_2402_2499 : Positive step631 2402 2499 := by decide +kernel

theorem step631_cover : ∃ ends, Cover step631 firstHeight ends := by
  exact ⟨[2334, 2350, 2401, 2499],
    ⟨(by decide), (by decide), step631_2330_2334,
      (by decide), (by decide), step631_2335_2350,
      (by decide), (by decide), step631_2351_2401,
      (by decide), (by decide), step631_2402_2499, rfl⟩⟩

theorem step631_verified : Checked step631 :=
  ⟨step631_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step631_cover⟩

def step632 : Request :=
  ⟨⟨⟨420, 586, 127, 5419⟩, 2252760678400, 3279920952⟩, 7, 6, 26, 771431⟩

theorem step632_nodes : P1_7_1.nodeRows step632.bank.shape = step632.bank.nodeRows :=
  node_check step632.bank (by decide) (by decide) (by decide)

private theorem step632_2330_2332 : Positive step632 2330 2332 := by decide +kernel

private theorem step632_2333_2341 : Positive step632 2333 2341 := by decide +kernel

private theorem step632_2342_2369 : Positive step632 2342 2369 := by decide +kernel

private theorem step632_2370_2455 : Positive step632 2370 2455 := by decide +kernel

private theorem step632_2456_2499 : Positive step632 2456 2499 := by decide +kernel

theorem step632_cover : ∃ ends, Cover step632 firstHeight ends := by
  exact ⟨[2332, 2341, 2369, 2455, 2499],
    ⟨(by decide), (by decide), step632_2330_2332,
      (by decide), (by decide), step632_2333_2341,
      (by decide), (by decide), step632_2342_2369,
      (by decide), (by decide), step632_2370_2455,
      (by decide), (by decide), step632_2456_2499, rfl⟩⟩

theorem step632_verified : Checked step632 :=
  ⟨step632_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step632_cover⟩

def step633 : Request :=
  ⟨⟨⟨520, 725, 161, 6096⟩, 4343013310464, 7809559934⟩, 10, 6, 26, 771431⟩

theorem step633_nodes : P1_7_1.nodeRows step633.bank.shape = step633.bank.nodeRows :=
  node_check step633.bank (by decide) (by decide) (by decide)

private theorem step633_2330_2345 : Positive step633 2330 2345 := by decide +kernel

private theorem step633_2346_2392 : Positive step633 2346 2392 := by decide +kernel

private theorem step633_2393_2499 : Positive step633 2393 2499 := by decide +kernel

theorem step633_cover : ∃ ends, Cover step633 firstHeight ends := by
  exact ⟨[2345, 2392, 2499],
    ⟨(by decide), (by decide), step633_2330_2345,
      (by decide), (by decide), step633_2346_2392,
      (by decide), (by decide), step633_2393_2499, rfl⟩⟩

theorem step633_verified : Checked step633 :=
  ⟨step633_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step633_cover⟩

def step634 : Request :=
  ⟨⟨⟨630, 879, 190, 8679⟩, 7559493713920, 16491913877⟩, 16, 6, 26, 771431⟩

theorem step634_nodes : P1_7_1.nodeRows step634.bank.shape = step634.bank.nodeRows :=
  node_check step634.bank (by decide) (by decide) (by decide)

private theorem step634_2330_2347 : Positive step634 2330 2347 := by decide +kernel

private theorem step634_2348_2399 : Positive step634 2348 2399 := by decide +kernel

private theorem step634_2400_2499 : Positive step634 2400 2499 := by decide +kernel

theorem step634_cover : ∃ ends, Cover step634 firstHeight ends := by
  exact ⟨[2347, 2399, 2499],
    ⟨(by decide), (by decide), step634_2330_2347,
      (by decide), (by decide), step634_2348_2399,
      (by decide), (by decide), step634_2400_2499, rfl⟩⟩

theorem step634_verified : Checked step634 :=
  ⟨step634_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step634_cover⟩

def step635 : Request :=
  ⟨⟨⟨630, 878, 195, 10983⟩, 7709474160640, 16765904450⟩, 20, 6, 26, 771431⟩

theorem step635_nodes : P1_7_1.nodeRows step635.bank.shape = step635.bank.nodeRows :=
  node_check step635.bank (by decide) (by decide) (by decide)

private theorem step635_2330_2345 : Positive step635 2330 2345 := by decide +kernel

private theorem step635_2346_2392 : Positive step635 2346 2392 := by decide +kernel

private theorem step635_2393_2499 : Positive step635 2393 2499 := by decide +kernel

theorem step635_cover : ∃ ends, Cover step635 firstHeight ends := by
  exact ⟨[2345, 2392, 2499],
    ⟨(by decide), (by decide), step635_2330_2345,
      (by decide), (by decide), step635_2346_2392,
      (by decide), (by decide), step635_2393_2499, rfl⟩⟩

theorem step635_verified : Checked step635 :=
  ⟨step635_nodes, Research6966.HelperWindowCatalogue.moment878_195,
    (by decide), (by decide), (by decide), step635_cover⟩

def step636 : Request :=
  ⟨⟨⟨900, 1255, 279, 13899⟩, 22452680785920, 69841856233⟩, 31, 6, 26, 771431⟩

theorem step636_nodes : P1_7_1.nodeRows step636.bank.shape = step636.bank.nodeRows :=
  node_check step636.bank (by decide) (by decide) (by decide)

private theorem step636_2330_2342 : Positive step636 2330 2342 := by decide +kernel

private theorem step636_2343_2378 : Positive step636 2343 2378 := by decide +kernel

private theorem step636_2379_2478 : Positive step636 2379 2478 := by decide +kernel

private theorem step636_2479_2499 : Positive step636 2479 2499 := by decide +kernel

theorem step636_cover : ∃ ends, Cover step636 firstHeight ends := by
  exact ⟨[2342, 2378, 2478, 2499],
    ⟨(by decide), (by decide), step636_2330_2342,
      (by decide), (by decide), step636_2343_2378,
      (by decide), (by decide), step636_2379_2478,
      (by decide), (by decide), step636_2479_2499, rfl⟩⟩

theorem step636_verified : Checked step636 :=
  ⟨step636_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step636_cover⟩

def step637 : Request :=
  ⟨⟨⟨1100, 1534, 341, 12355⟩, 40955142733824, 155702293064⟩, 32, 6, 26, 771431⟩

theorem step637_nodes : P1_7_1.nodeRows step637.bank.shape = step637.bank.nodeRows :=
  node_check step637.bank (by decide) (by decide) (by decide)

private theorem step637_2330_2333 : Positive step637 2330 2333 := by decide +kernel

private theorem step637_2334_2344 : Positive step637 2334 2344 := by decide +kernel

private theorem step637_2345_2374 : Positive step637 2345 2374 := by decide +kernel

private theorem step637_2375_2456 : Positive step637 2375 2456 := by decide +kernel

private theorem step637_2457_2499 : Positive step637 2457 2499 := by decide +kernel

theorem step637_cover : ∃ ends, Cover step637 firstHeight ends := by
  exact ⟨[2333, 2344, 2374, 2456, 2499],
    ⟨(by decide), (by decide), step637_2330_2333,
      (by decide), (by decide), step637_2334_2344,
      (by decide), (by decide), step637_2345_2374,
      (by decide), (by decide), step637_2375_2456,
      (by decide), (by decide), step637_2457_2499, rfl⟩⟩

theorem step637_verified : Checked step637 :=
  ⟨step637_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step637_cover⟩

def step638 : Request :=
  ⟨⟨⟨1100, 1534, 341, 19788⟩, 40955142733824, 155702293064⟩, 44, 6, 26, 771431⟩

theorem step638_nodes : P1_7_1.nodeRows step638.bank.shape = step638.bank.nodeRows :=
  node_check step638.bank (by decide) (by decide) (by decide)

private theorem step638_2330_2333 : Positive step638 2330 2333 := by decide +kernel

private theorem step638_2334_2344 : Positive step638 2334 2344 := by decide +kernel

private theorem step638_2345_2374 : Positive step638 2345 2374 := by decide +kernel

private theorem step638_2375_2455 : Positive step638 2375 2455 := by decide +kernel

private theorem step638_2456_2499 : Positive step638 2456 2499 := by decide +kernel

theorem step638_cover : ∃ ends, Cover step638 firstHeight ends := by
  exact ⟨[2333, 2344, 2374, 2455, 2499],
    ⟨(by decide), (by decide), step638_2330_2333,
      (by decide), (by decide), step638_2334_2344,
      (by decide), (by decide), step638_2345_2374,
      (by decide), (by decide), step638_2375_2455,
      (by decide), (by decide), step638_2456_2499, rfl⟩⟩

theorem step638_verified : Checked step638 :=
  ⟨step638_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step638_cover⟩

def step639 : Request :=
  ⟨⟨⟨2000, 2790, 620, 25043⟩, 245690786119680, 1699185179819⟩, 73, 6, 26, 771431⟩

theorem step639_nodes : P1_7_1.nodeRows step639.bank.shape = step639.bank.nodeRows :=
  node_check step639.bank (by decide) (by decide) (by decide)

private theorem step639_2330_2331 : Positive step639 2330 2331 := by decide +kernel

private theorem step639_2332_2336 : Positive step639 2332 2336 := by decide +kernel

private theorem step639_2337_2349 : Positive step639 2337 2349 := by decide +kernel

private theorem step639_2350_2383 : Positive step639 2350 2383 := by decide +kernel

private theorem step639_2384_2473 : Positive step639 2384 2473 := by decide +kernel

private theorem step639_2474_2499 : Positive step639 2474 2499 := by decide +kernel

theorem step639_cover : ∃ ends, Cover step639 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2473, 2499],
    ⟨(by decide), (by decide), step639_2330_2331,
      (by decide), (by decide), step639_2332_2336,
      (by decide), (by decide), step639_2337_2349,
      (by decide), (by decide), step639_2350_2383,
      (by decide), (by decide), step639_2384_2473,
      (by decide), (by decide), step639_2474_2499, rfl⟩⟩

theorem step639_verified : Checked step639 :=
  ⟨step639_nodes, Research6966.HelperWindowCatalogue.moment2790_620,
    (by decide), (by decide), (by decide), step639_cover⟩

def step640 : Request :=
  ⟨⟨⟨2000, 2789, 604, 28173⟩, 240862397726720, 1663046410409⟩, 76, 6, 26, 771431⟩

theorem step640_nodes : P1_7_1.nodeRows step640.bank.shape = step640.bank.nodeRows :=
  node_check step640.bank (by decide) (by decide) (by decide)

private theorem step640_2330_2333 : Positive step640 2330 2333 := by decide +kernel

private theorem step640_2334_2343 : Positive step640 2334 2343 := by decide +kernel

private theorem step640_2344_2370 : Positive step640 2344 2370 := by decide +kernel

private theorem step640_2371_2442 : Positive step640 2371 2442 := by decide +kernel

private theorem step640_2443_2499 : Positive step640 2443 2499 := by decide +kernel

theorem step640_cover : ∃ ends, Cover step640 firstHeight ends := by
  exact ⟨[2333, 2343, 2370, 2442, 2499],
    ⟨(by decide), (by decide), step640_2330_2333,
      (by decide), (by decide), step640_2334_2343,
      (by decide), (by decide), step640_2344_2370,
      (by decide), (by decide), step640_2371_2442,
      (by decide), (by decide), step640_2443_2499, rfl⟩⟩

theorem step640_verified : Checked step640 :=
  ⟨step640_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step640_cover⟩

def step641 : Request :=
  ⟨⟨⟨2500, 3487, 755, 40111⟩, 470210689105920, 4060530796561⟩, 103, 6, 26, 771431⟩

theorem step641_nodes : P1_7_1.nodeRows step641.bank.shape = step641.bank.nodeRows :=
  node_check step641.bank (by decide) (by decide) (by decide)

private theorem step641_2330_2342 : Positive step641 2330 2342 := by decide +kernel

private theorem step641_2343_2377 : Positive step641 2343 2377 := by decide +kernel

private theorem step641_2378_2470 : Positive step641 2378 2470 := by decide +kernel

private theorem step641_2471_2499 : Positive step641 2471 2499 := by decide +kernel

theorem step641_cover : ∃ ends, Cover step641 firstHeight ends := by
  exact ⟨[2342, 2377, 2470, 2499],
    ⟨(by decide), (by decide), step641_2330_2342,
      (by decide), (by decide), step641_2343_2377,
      (by decide), (by decide), step641_2378_2470,
      (by decide), (by decide), step641_2471_2499, rfl⟩⟩

theorem step641_verified : Checked step641 :=
  ⟨step641_nodes, Research6966.HelperWindowCatalogue.moment3487_755,
    (by decide), (by decide), (by decide), step641_cover⟩

def step642 : Request :=
  ⟨⟨⟨210, 293, 63, 2674⟩, 283090354176, 206678784⟩, 0, 6, 41, 771431⟩

theorem step642_nodes : P1_7_1.nodeRows step642.bank.shape = step642.bank.nodeRows :=
  node_check step642.bank (by decide) (by decide) (by decide)

private theorem step642_2330_2352 : Positive step642 2330 2352 := by decide +kernel

private theorem step642_2353_2442 : Positive step642 2353 2442 := by decide +kernel

private theorem step642_2443_2499 : Positive step642 2443 2499 := by decide +kernel

theorem step642_cover : ∃ ends, Cover step642 firstHeight ends := by
  exact ⟨[2352, 2442, 2499],
    ⟨(by decide), (by decide), step642_2330_2352,
      (by decide), (by decide), step642_2353_2442,
      (by decide), (by decide), step642_2443_2499, rfl⟩⟩

theorem step642_verified : Checked step642 :=
  ⟨step642_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step642_cover⟩

def step643 : Request :=
  ⟨⟨⟨250, 349, 76, 2674⟩, 480667500544, 418199213⟩, 1, 6, 41, 771431⟩

theorem step643_nodes : P1_7_1.nodeRows step643.bank.shape = step643.bank.nodeRows :=
  node_check step643.bank (by decide) (by decide) (by decide)

private theorem step643_2330_2360 : Positive step643 2330 2360 := by decide +kernel

private theorem step643_2361_2471 : Positive step643 2361 2471 := by decide +kernel

private theorem step643_2472_2499 : Positive step643 2472 2499 := by decide +kernel

theorem step643_cover : ∃ ends, Cover step643 firstHeight ends := by
  exact ⟨[2360, 2471, 2499],
    ⟨(by decide), (by decide), step643_2330_2360,
      (by decide), (by decide), step643_2361_2471,
      (by decide), (by decide), step643_2472_2499, rfl⟩⟩

theorem step643_verified : Checked step643 :=
  ⟨step643_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step643_cover⟩

def step644 : Request :=
  ⟨⟨⟨250, 349, 76, 3008⟩, 480667500544, 418199213⟩, 2, 6, 41, 771431⟩

theorem step644_nodes : P1_7_1.nodeRows step644.bank.shape = step644.bank.nodeRows :=
  node_check step644.bank (by decide) (by decide) (by decide)

private theorem step644_2330_2336 : Positive step644 2330 2336 := by decide +kernel

private theorem step644_2337_2360 : Positive step644 2337 2360 := by decide +kernel

private theorem step644_2361_2445 : Positive step644 2361 2445 := by decide +kernel

private theorem step644_2446_2499 : Positive step644 2446 2499 := by decide +kernel

theorem step644_cover : ∃ ends, Cover step644 firstHeight ends := by
  exact ⟨[2336, 2360, 2445, 2499],
    ⟨(by decide), (by decide), step644_2330_2336,
      (by decide), (by decide), step644_2337_2360,
      (by decide), (by decide), step644_2361_2445,
      (by decide), (by decide), step644_2446_2499, rfl⟩⟩

theorem step644_verified : Checked step644 :=
  ⟨step644_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step644_cover⟩

def step645 : Request :=
  ⟨⟨⟨294, 410, 89, 3008⟩, 777085255680, 791788817⟩, 3, 6, 41, 771431⟩

theorem step645_nodes : P1_7_1.nodeRows step645.bank.shape = step645.bank.nodeRows :=
  node_check step645.bank (by decide) (by decide) (by decide)

private theorem step645_2330_2330 : Positive step645 2330 2330 := by decide +kernel

private theorem step645_2331_2333 : Positive step645 2331 2333 := by decide +kernel

private theorem step645_2334_2343 : Positive step645 2334 2343 := by decide +kernel

private theorem step645_2344_2377 : Positive step645 2344 2377 := by decide +kernel

private theorem step645_2378_2492 : Positive step645 2378 2492 := by decide +kernel

private theorem step645_2493_2499 : Positive step645 2493 2499 := by decide +kernel

theorem step645_cover : ∃ ends, Cover step645 firstHeight ends := by
  exact ⟨[2330, 2333, 2343, 2377, 2492, 2499],
    ⟨(by decide), (by decide), step645_2330_2330,
      (by decide), (by decide), step645_2331_2333,
      (by decide), (by decide), step645_2334_2343,
      (by decide), (by decide), step645_2344_2377,
      (by decide), (by decide), step645_2378_2492,
      (by decide), (by decide), step645_2493_2499, rfl⟩⟩

theorem step645_verified : Checked step645 :=
  ⟨step645_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step645_cover⟩

def step646 : Request :=
  ⟨⟨⟨294, 410, 91, 3384⟩, 790165454848, 805457011⟩, 4, 6, 41, 771431⟩

theorem step646_nodes : P1_7_1.nodeRows step646.bank.shape = step646.bank.nodeRows :=
  node_check step646.bank (by decide) (by decide) (by decide)

private theorem step646_2330_2342 : Positive step646 2330 2342 := by decide +kernel

private theorem step646_2343_2386 : Positive step646 2343 2386 := by decide +kernel

private theorem step646_2387_2499 : Positive step646 2387 2499 := by decide +kernel

theorem step646_cover : ∃ ends, Cover step646 firstHeight ends := by
  exact ⟨[2342, 2386, 2499],
    ⟨(by decide), (by decide), step646_2330_2342,
      (by decide), (by decide), step646_2343_2386,
      (by decide), (by decide), step646_2387_2499, rfl⟩⟩

theorem step646_verified : Checked step646 :=
  ⟨step646_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step646_cover⟩

def step647 : Request :=
  ⟨⟨⟨350, 488, 108, 3384⟩, 1326705278976, 1607754763⟩, 5, 6, 41, 771431⟩

theorem step647_nodes : P1_7_1.nodeRows step647.bank.shape = step647.bank.nodeRows :=
  node_check step647.bank (by decide) (by decide) (by decide)

private theorem step647_2330_2345 : Positive step647 2330 2345 := by decide +kernel

private theorem step647_2346_2396 : Positive step647 2346 2396 := by decide +kernel

private theorem step647_2397_2499 : Positive step647 2397 2499 := by decide +kernel

theorem step647_cover : ∃ ends, Cover step647 firstHeight ends := by
  exact ⟨[2345, 2396, 2499],
    ⟨(by decide), (by decide), step647_2330_2345,
      (by decide), (by decide), step647_2346_2396,
      (by decide), (by decide), step647_2397_2499, rfl⟩⟩

theorem step647_verified : Checked step647 :=
  ⟨step647_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step647_cover⟩

def step648 : Request :=
  ⟨⟨⟨350, 488, 106, 4282⟩, 1308168290304, 1584729438⟩, 7, 6, 41, 771431⟩

theorem step648_nodes : P1_7_1.nodeRows step648.bank.shape = step648.bank.nodeRows :=
  node_check step648.bank (by decide) (by decide) (by decide)

private theorem step648_2330_2335 : Positive step648 2330 2335 := by decide +kernel

private theorem step648_2336_2354 : Positive step648 2336 2354 := by decide +kernel

private theorem step648_2355_2415 : Positive step648 2355 2415 := by decide +kernel

private theorem step648_2416_2499 : Positive step648 2416 2499 := by decide +kernel

theorem step648_cover : ∃ ends, Cover step648 firstHeight ends := by
  exact ⟨[2335, 2354, 2415, 2499],
    ⟨(by decide), (by decide), step648_2330_2335,
      (by decide), (by decide), step648_2336_2354,
      (by decide), (by decide), step648_2355_2415,
      (by decide), (by decide), step648_2416_2499, rfl⟩⟩

theorem step648_verified : Checked step648 :=
  ⟨step648_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step648_cover⟩

def step649 : Request :=
  ⟨⟨⟨420, 586, 130, 4817⟩, 2292767784960, 3339653140⟩, 10, 6, 41, 771431⟩

theorem step649_nodes : P1_7_1.nodeRows step649.bank.shape = step649.bank.nodeRows :=
  node_check step649.bank (by decide) (by decide) (by decide)

private theorem step649_2330_2344 : Positive step649 2330 2344 := by decide +kernel

private theorem step649_2345_2390 : Positive step649 2345 2390 := by decide +kernel

private theorem step649_2391_2499 : Positive step649 2391 2499 := by decide +kernel

theorem step649_cover : ∃ ends, Cover step649 firstHeight ends := by
  exact ⟨[2344, 2390, 2499],
    ⟨(by decide), (by decide), step649_2330_2344,
      (by decide), (by decide), step649_2345_2390,
      (by decide), (by decide), step649_2391_2499, rfl⟩⟩

theorem step649_verified : Checked step649 :=
  ⟨step649_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step649_cover⟩

def step650 : Request :=
  ⟨⟨⟨520, 725, 157, 6858⟩, 4261264752640, 7658911630⟩, 16, 6, 41, 771431⟩

theorem step650_nodes : P1_7_1.nodeRows step650.bank.shape = step650.bank.nodeRows :=
  node_check step650.bank (by decide) (by decide) (by decide)

private theorem step650_2330_2336 : Positive step650 2330 2336 := by decide +kernel

private theorem step650_2337_2357 : Positive step650 2337 2357 := by decide +kernel

private theorem step650_2358_2419 : Positive step650 2358 2419 := by decide +kernel

private theorem step650_2420_2499 : Positive step650 2420 2499 := by decide +kernel

theorem step650_cover : ∃ ends, Cover step650 firstHeight ends := by
  exact ⟨[2336, 2357, 2419, 2499],
    ⟨(by decide), (by decide), step650_2330_2336,
      (by decide), (by decide), step650_2337_2357,
      (by decide), (by decide), step650_2358_2419,
      (by decide), (by decide), step650_2420_2499, rfl⟩⟩

theorem step650_verified : Checked step650 :=
  ⟨step650_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step650_cover⟩

def step651 : Request :=
  ⟨⟨⟨630, 878, 190, 7715⟩, 7559493713920, 16431687757⟩, 20, 6, 41, 771431⟩

theorem step651_nodes : P1_7_1.nodeRows step651.bank.shape = step651.bank.nodeRows :=
  node_check step651.bank (by decide) (by decide) (by decide)

private theorem step651_2330_2352 : Positive step651 2330 2352 := by decide +kernel

private theorem step651_2353_2419 : Positive step651 2353 2419 := by decide +kernel

private theorem step651_2420_2499 : Positive step651 2420 2499 := by decide +kernel

theorem step651_cover : ∃ ends, Cover step651 firstHeight ends := by
  exact ⟨[2352, 2419, 2499],
    ⟨(by decide), (by decide), step651_2330_2352,
      (by decide), (by decide), step651_2353_2419,
      (by decide), (by decide), step651_2420_2499, rfl⟩⟩

theorem step651_verified : Checked step651 :=
  ⟨step651_nodes, Research6966.HelperWindowCatalogue.moment878_190,
    (by decide), (by decide), (by decide), step651_cover⟩

def step652 : Request :=
  ⟨⟨⟨900, 1255, 272, 9763⟩, 22024701870080, 68477558806⟩, 31, 6, 41, 771431⟩

theorem step652_nodes : P1_7_1.nodeRows step652.bank.shape = step652.bank.nodeRows :=
  node_check step652.bank (by decide) (by decide) (by decide)

private theorem step652_2330_2341 : Positive step652 2330 2341 := by decide +kernel

private theorem step652_2342_2374 : Positive step652 2342 2374 := by decide +kernel

private theorem step652_2375_2467 : Positive step652 2375 2467 := by decide +kernel

private theorem step652_2468_2499 : Positive step652 2468 2499 := by decide +kernel

theorem step652_cover : ∃ ends, Cover step652 firstHeight ends := by
  exact ⟨[2341, 2374, 2467, 2499],
    ⟨(by decide), (by decide), step652_2330_2341,
      (by decide), (by decide), step652_2342_2374,
      (by decide), (by decide), step652_2375_2467,
      (by decide), (by decide), step652_2468_2499, rfl⟩⟩

theorem step652_verified : Checked step652 :=
  ⟨step652_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step652_cover⟩

def step653 : Request :=
  ⟨⟨⟨900, 1255, 279, 9763⟩, 22452680785920, 69841856233⟩, 32, 6, 41, 771431⟩

theorem step653_nodes : P1_7_1.nodeRows step653.bank.shape = step653.bank.nodeRows :=
  node_check step653.bank (by decide) (by decide) (by decide)

private theorem step653_2330_2345 : Positive step653 2330 2345 := by decide +kernel

private theorem step653_2346_2389 : Positive step653 2346 2389 := by decide +kernel

private theorem step653_2390_2499 : Positive step653 2390 2499 := by decide +kernel

theorem step653_cover : ∃ ends, Cover step653 firstHeight ends := by
  exact ⟨[2345, 2389, 2499],
    ⟨(by decide), (by decide), step653_2330_2345,
      (by decide), (by decide), step653_2346_2389,
      (by decide), (by decide), step653_2390_2499, rfl⟩⟩

theorem step653_verified : Checked step653 :=
  ⟨step653_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step653_cover⟩

def step654 : Request :=
  ⟨⟨⟨1100, 1534, 332, 13899⟩, 40133103452160, 152499774767⟩, 44, 6, 41, 771431⟩

theorem step654_nodes : P1_7_1.nodeRows step654.bank.shape = step654.bank.nodeRows :=
  node_check step654.bank (by decide) (by decide) (by decide)

private theorem step654_2330_2339 : Positive step654 2330 2339 := by decide +kernel

private theorem step654_2340_2366 : Positive step654 2340 2366 := by decide +kernel

private theorem step654_2367_2441 : Positive step654 2367 2441 := by decide +kernel

private theorem step654_2442_2499 : Positive step654 2442 2499 := by decide +kernel

theorem step654_cover : ∃ ends, Cover step654 firstHeight ends := by
  exact ⟨[2339, 2366, 2441, 2499],
    ⟨(by decide), (by decide), step654_2330_2339,
      (by decide), (by decide), step654_2340_2366,
      (by decide), (by decide), step654_2367_2441,
      (by decide), (by decide), step654_2442_2499, rfl⟩⟩

theorem step654_verified : Checked step654 :=
  ⟨step654_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step654_cover⟩

def step655 : Request :=
  ⟨⟨⟨1650, 2301, 498, 22261⟩, 135254251667456, 770619519922⟩, 73, 6, 41, 771431⟩

theorem step655_nodes : P1_7_1.nodeRows step655.bank.shape = step655.bank.nodeRows :=
  node_check step655.bank (by decide) (by decide) (by decide)

private theorem step655_2330_2341 : Positive step655 2330 2341 := by decide +kernel

private theorem step655_2342_2373 : Positive step655 2342 2373 := by decide +kernel

private theorem step655_2374_2459 : Positive step655 2374 2459 := by decide +kernel

private theorem step655_2460_2499 : Positive step655 2460 2499 := by decide +kernel

theorem step655_cover : ∃ ends, Cover step655 firstHeight ends := by
  exact ⟨[2341, 2373, 2459, 2499],
    ⟨(by decide), (by decide), step655_2330_2341,
      (by decide), (by decide), step655_2342_2373,
      (by decide), (by decide), step655_2374_2459,
      (by decide), (by decide), step655_2460_2499, rfl⟩⟩

theorem step655_verified : Checked step655 :=
  ⟨step655_nodes, Research6966.HelperWindowCatalogue.moment2301_498,
    (by decide), (by decide), (by decide), step655_cover⟩

def step656 : Request :=
  ⟨⟨⟨1650, 2301, 512, 22261⟩, 138129879859200, 787417379725⟩, 76, 6, 41, 771431⟩

theorem step656_nodes : P1_7_1.nodeRows step656.bank.shape = step656.bank.nodeRows :=
  node_check step656.bank (by decide) (by decide) (by decide)

private theorem step656_2330_2336 : Positive step656 2330 2336 := by decide +kernel

private theorem step656_2337_2354 : Positive step656 2337 2354 := by decide +kernel

private theorem step656_2355_2402 : Positive step656 2355 2402 := by decide +kernel

private theorem step656_2403_2499 : Positive step656 2403 2499 := by decide +kernel

theorem step656_cover : ∃ ends, Cover step656 firstHeight ends := by
  exact ⟨[2336, 2354, 2402, 2499],
    ⟨(by decide), (by decide), step656_2330_2336,
      (by decide), (by decide), step656_2337_2354,
      (by decide), (by decide), step656_2355_2402,
      (by decide), (by decide), step656_2403_2499, rfl⟩⟩

theorem step656_verified : Checked step656 :=
  ⟨step656_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step656_cover⟩

def step657 : Request :=
  ⟨⟨⟨2500, 3487, 775, 25043⟩, 479640131993600, 4144013596741⟩, 103, 6, 41, 771431⟩

theorem step657_nodes : P1_7_1.nodeRows step657.bank.shape = step657.bank.nodeRows :=
  node_check step657.bank (by decide) (by decide) (by decide)

private theorem step657_2330_2336 : Positive step657 2330 2336 := by decide +kernel

private theorem step657_2337_2354 : Positive step657 2337 2354 := by decide +kernel

private theorem step657_2355_2402 : Positive step657 2355 2402 := by decide +kernel

private theorem step657_2403_2499 : Positive step657 2403 2499 := by decide +kernel

theorem step657_cover : ∃ ends, Cover step657 firstHeight ends := by
  exact ⟨[2336, 2354, 2402, 2499],
    ⟨(by decide), (by decide), step657_2330_2336,
      (by decide), (by decide), step657_2337_2354,
      (by decide), (by decide), step657_2355_2402,
      (by decide), (by decide), step657_2403_2499, rfl⟩⟩

theorem step657_verified : Checked step657 :=
  ⟨step657_nodes, Research6966.HelperWindowCatalogue.moment3487_775,
    (by decide), (by decide), (by decide), step657_cover⟩

def step658 : Request :=
  ⟨⟨⟨210, 293, 63, 2113⟩, 283090354176, 206678784⟩, 0, 6, 51, 771431⟩

theorem step658_nodes : P1_7_1.nodeRows step658.bank.shape = step658.bank.nodeRows :=
  node_check step658.bank (by decide) (by decide) (by decide)

private theorem step658_2330_2352 : Positive step658 2330 2352 := by decide +kernel

private theorem step658_2353_2442 : Positive step658 2353 2442 := by decide +kernel

private theorem step658_2443_2499 : Positive step658 2443 2499 := by decide +kernel

theorem step658_cover : ∃ ends, Cover step658 firstHeight ends := by
  exact ⟨[2352, 2442, 2499],
    ⟨(by decide), (by decide), step658_2330_2352,
      (by decide), (by decide), step658_2353_2442,
      (by decide), (by decide), step658_2443_2499, rfl⟩⟩

theorem step658_verified : Checked step658 :=
  ⟨step658_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step658_cover⟩

def step659 : Request :=
  ⟨⟨⟨210, 293, 65, 2377⟩, 289785774080, 211692234⟩, 1, 6, 51, 771431⟩

theorem step659_nodes : P1_7_1.nodeRows step659.bank.shape = step659.bank.nodeRows :=
  node_check step659.bank (by decide) (by decide) (by decide)

private theorem step659_2330_2345 : Positive step659 2330 2345 := by decide +kernel

private theorem step659_2346_2406 : Positive step659 2346 2406 := by decide +kernel

private theorem step659_2407_2499 : Positive step659 2407 2499 := by decide +kernel

theorem step659_cover : ∃ ends, Cover step659 firstHeight ends := by
  exact ⟨[2345, 2406, 2499],
    ⟨(by decide), (by decide), step659_2330_2345,
      (by decide), (by decide), step659_2346_2406,
      (by decide), (by decide), step659_2407_2499, rfl⟩⟩

theorem step659_verified : Checked step659 :=
  ⟨step659_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step659_cover⟩

def step660 : Request :=
  ⟨⟨⟨250, 349, 78, 2377⟩, 490108092416, 426627288⟩, 2, 6, 51, 771431⟩

theorem step660_nodes : P1_7_1.nodeRows step660.bank.shape = step660.bank.nodeRows :=
  node_check step660.bank (by decide) (by decide) (by decide)

private theorem step660_2330_2343 : Positive step660 2330 2343 := by decide +kernel

private theorem step660_2344_2392 : Positive step660 2344 2392 := by decide +kernel

private theorem step660_2393_2499 : Positive step660 2393 2499 := by decide +kernel

theorem step660_cover : ∃ ends, Cover step660 firstHeight ends := by
  exact ⟨[2343, 2392, 2499],
    ⟨(by decide), (by decide), step660_2330_2343,
      (by decide), (by decide), step660_2344_2392,
      (by decide), (by decide), step660_2393_2499, rfl⟩⟩

theorem step660_verified : Checked step660 :=
  ⟨step660_nodes, Research6966.HelperWindowCatalogue.moment349_78,
    (by decide), (by decide), (by decide), step660_cover⟩

def step661 : Request :=
  ⟨⟨⟨250, 348, 78, 2674⟩, 490108092416, 422716393⟩, 3, 6, 51, 771431⟩

theorem step661_nodes : P1_7_1.nodeRows step661.bank.shape = step661.bank.nodeRows :=
  node_check step661.bank (by decide) (by decide) (by decide)

private theorem step661_2330_2338 : Positive step661 2330 2338 := by decide +kernel

private theorem step661_2339_2370 : Positive step661 2339 2370 := by decide +kernel

private theorem step661_2371_2485 : Positive step661 2371 2485 := by decide +kernel

private theorem step661_2486_2499 : Positive step661 2486 2499 := by decide +kernel

theorem step661_cover : ∃ ends, Cover step661 firstHeight ends := by
  exact ⟨[2338, 2370, 2485, 2499],
    ⟨(by decide), (by decide), step661_2330_2338,
      (by decide), (by decide), step661_2339_2370,
      (by decide), (by decide), step661_2371_2485,
      (by decide), (by decide), step661_2486_2499, rfl⟩⟩

theorem step661_verified : Checked step661 :=
  ⟨step661_nodes, Research6966.HelperWindowCatalogue.moment348_78,
    (by decide), (by decide), (by decide), step661_cover⟩

def step662 : Request :=
  ⟨⟨⟨250, 348, 76, 3384⟩, 480667500544, 414368386⟩, 4, 6, 51, 771431⟩

theorem step662_nodes : P1_7_1.nodeRows step662.bank.shape = step662.bank.nodeRows :=
  node_check step662.bank (by decide) (by decide) (by decide)

private theorem step662_2330_2336 : Positive step662 2330 2336 := by decide +kernel

private theorem step662_2337_2361 : Positive step662 2337 2361 := by decide +kernel

private theorem step662_2362_2451 : Positive step662 2362 2451 := by decide +kernel

private theorem step662_2452_2499 : Positive step662 2452 2499 := by decide +kernel

theorem step662_cover : ∃ ends, Cover step662 firstHeight ends := by
  exact ⟨[2336, 2361, 2451, 2499],
    ⟨(by decide), (by decide), step662_2330_2336,
      (by decide), (by decide), step662_2337_2361,
      (by decide), (by decide), step662_2362_2451,
      (by decide), (by decide), step662_2452_2499, rfl⟩⟩

theorem step662_verified : Checked step662 :=
  ⟨step662_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step662_cover⟩

def step663 : Request :=
  ⟨⟨⟨294, 410, 91, 3008⟩, 790165454848, 805457011⟩, 5, 6, 51, 771431⟩

theorem step663_nodes : P1_7_1.nodeRows step663.bank.shape = step663.bank.nodeRows :=
  node_check step663.bank (by decide) (by decide) (by decide)

private theorem step663_2330_2330 : Positive step663 2330 2330 := by decide +kernel

private theorem step663_2331_2333 : Positive step663 2331 2333 := by decide +kernel

private theorem step663_2334_2343 : Positive step663 2334 2343 := by decide +kernel

private theorem step663_2344_2377 : Positive step663 2344 2377 := by decide +kernel

private theorem step663_2378_2491 : Positive step663 2378 2491 := by decide +kernel

private theorem step663_2492_2499 : Positive step663 2492 2499 := by decide +kernel

theorem step663_cover : ∃ ends, Cover step663 firstHeight ends := by
  exact ⟨[2330, 2333, 2343, 2377, 2491, 2499],
    ⟨(by decide), (by decide), step663_2330_2330,
      (by decide), (by decide), step663_2331_2333,
      (by decide), (by decide), step663_2334_2343,
      (by decide), (by decide), step663_2344_2377,
      (by decide), (by decide), step663_2378_2491,
      (by decide), (by decide), step663_2492_2499, rfl⟩⟩

theorem step663_verified : Checked step663 :=
  ⟨step663_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step663_cover⟩

def step664 : Request :=
  ⟨⟨⟨350, 488, 108, 3384⟩, 1326705278976, 1607754763⟩, 7, 6, 51, 771431⟩

theorem step664_nodes : P1_7_1.nodeRows step664.bank.shape = step664.bank.nodeRows :=
  node_check step664.bank (by decide) (by decide) (by decide)

private theorem step664_2330_2348 : Positive step664 2330 2348 := by decide +kernel

private theorem step664_2349_2409 : Positive step664 2349 2409 := by decide +kernel

private theorem step664_2410_2499 : Positive step664 2410 2499 := by decide +kernel

theorem step664_cover : ∃ ends, Cover step664 firstHeight ends := by
  exact ⟨[2348, 2409, 2499],
    ⟨(by decide), (by decide), step664_2330_2348,
      (by decide), (by decide), step664_2349_2409,
      (by decide), (by decide), step664_2410_2499, rfl⟩⟩

theorem step664_verified : Checked step664 :=
  ⟨step664_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step664_cover⟩

def step665 : Request :=
  ⟨⟨⟨350, 488, 108, 4817⟩, 1326705278976, 1607754763⟩, 10, 6, 51, 771431⟩

theorem step665_nodes : P1_7_1.nodeRows step665.bank.shape = step665.bank.nodeRows :=
  node_check step665.bank (by decide) (by decide) (by decide)

private theorem step665_2330_2331 : Positive step665 2330 2331 := by decide +kernel

private theorem step665_2332_2338 : Positive step665 2332 2338 := by decide +kernel

private theorem step665_2339_2360 : Positive step665 2339 2360 := by decide +kernel

private theorem step665_2361_2430 : Positive step665 2361 2430 := by decide +kernel

private theorem step665_2431_2499 : Positive step665 2431 2499 := by decide +kernel

theorem step665_cover : ∃ ends, Cover step665 firstHeight ends := by
  exact ⟨[2331, 2338, 2360, 2430, 2499],
    ⟨(by decide), (by decide), step665_2330_2331,
      (by decide), (by decide), step665_2332_2338,
      (by decide), (by decide), step665_2339_2360,
      (by decide), (by decide), step665_2361_2430,
      (by decide), (by decide), step665_2431_2499, rfl⟩⟩

theorem step665_verified : Checked step665 :=
  ⟨step665_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step665_cover⟩

def step666 : Request :=
  ⟨⟨⟨520, 725, 157, 5419⟩, 4261264752640, 7658911630⟩, 16, 6, 51, 771431⟩

theorem step666_nodes : P1_7_1.nodeRows step666.bank.shape = step666.bank.nodeRows :=
  node_check step666.bank (by decide) (by decide) (by decide)

private theorem step666_2330_2341 : Positive step666 2330 2341 := by decide +kernel

private theorem step666_2342_2377 : Positive step666 2342 2377 := by decide +kernel

private theorem step666_2378_2485 : Positive step666 2378 2485 := by decide +kernel

private theorem step666_2486_2499 : Positive step666 2486 2499 := by decide +kernel

theorem step666_cover : ∃ ends, Cover step666 firstHeight ends := by
  exact ⟨[2341, 2377, 2485, 2499],
    ⟨(by decide), (by decide), step666_2330_2341,
      (by decide), (by decide), step666_2342_2377,
      (by decide), (by decide), step666_2378_2485,
      (by decide), (by decide), step666_2486_2499, rfl⟩⟩

theorem step666_verified : Checked step666 :=
  ⟨step666_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step666_cover⟩

def step667 : Request :=
  ⟨⟨⟨630, 878, 190, 6096⟩, 7559493713920, 16431687757⟩, 20, 6, 51, 771431⟩

theorem step667_nodes : P1_7_1.nodeRows step667.bank.shape = step667.bank.nodeRows :=
  node_check step667.bank (by decide) (by decide) (by decide)

private theorem step667_2330_2347 : Positive step667 2330 2347 := by decide +kernel

private theorem step667_2348_2399 : Positive step667 2348 2399 := by decide +kernel

private theorem step667_2400_2499 : Positive step667 2400 2499 := by decide +kernel

theorem step667_cover : ∃ ends, Cover step667 firstHeight ends := by
  exact ⟨[2347, 2399, 2499],
    ⟨(by decide), (by decide), step667_2330_2347,
      (by decide), (by decide), step667_2348_2399,
      (by decide), (by decide), step667_2400_2499, rfl⟩⟩

theorem step667_verified : Checked step667 :=
  ⟨step667_nodes, Research6966.HelperWindowCatalogue.moment878_190,
    (by decide), (by decide), (by decide), step667_cover⟩

def step668 : Request :=
  ⟨⟨⟨900, 1255, 279, 7715⟩, 22452680785920, 69841856233⟩, 31, 6, 51, 771431⟩

theorem step668_nodes : P1_7_1.nodeRows step668.bank.shape = step668.bank.nodeRows :=
  node_check step668.bank (by decide) (by decide) (by decide)

private theorem step668_2330_2339 : Positive step668 2330 2339 := by decide +kernel

private theorem step668_2340_2367 : Positive step668 2340 2367 := by decide +kernel

private theorem step668_2368_2445 : Positive step668 2368 2445 := by decide +kernel

private theorem step668_2446_2499 : Positive step668 2446 2499 := by decide +kernel

theorem step668_cover : ∃ ends, Cover step668 firstHeight ends := by
  exact ⟨[2339, 2367, 2445, 2499],
    ⟨(by decide), (by decide), step668_2330_2339,
      (by decide), (by decide), step668_2340_2367,
      (by decide), (by decide), step668_2368_2445,
      (by decide), (by decide), step668_2446_2499, rfl⟩⟩

theorem step668_verified : Checked step668 :=
  ⟨step668_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step668_cover⟩

def step669 : Request :=
  ⟨⟨⟨750, 1046, 232, 9763⟩, 12985818152960, 33687112323⟩, 32, 6, 51, 771431⟩

theorem step669_nodes : P1_7_1.nodeRows step669.bank.shape = step669.bank.nodeRows :=
  node_check step669.bank (by decide) (by decide) (by decide)

private theorem step669_2330_2344 : Positive step669 2330 2344 := by decide +kernel

private theorem step669_2345_2386 : Positive step669 2345 2386 := by decide +kernel

private theorem step669_2387_2499 : Positive step669 2387 2499 := by decide +kernel

theorem step669_cover : ∃ ends, Cover step669 firstHeight ends := by
  exact ⟨[2344, 2386, 2499],
    ⟨(by decide), (by decide), step669_2330_2344,
      (by decide), (by decide), step669_2345_2386,
      (by decide), (by decide), step669_2387_2499, rfl⟩⟩

theorem step669_verified : Checked step669 :=
  ⟨step669_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step669_cover⟩

def step670 : Request :=
  ⟨⟨⟨1100, 1534, 332, 10983⟩, 40133103452160, 152499774767⟩, 44, 6, 51, 771431⟩

theorem step670_nodes : P1_7_1.nodeRows step670.bank.shape = step670.bank.nodeRows :=
  node_check step670.bank (by decide) (by decide) (by decide)

private theorem step670_2330_2338 : Positive step670 2330 2338 := by decide +kernel

private theorem step670_2339_2363 : Positive step670 2339 2363 := by decide +kernel

private theorem step670_2364_2432 : Positive step670 2364 2432 := by decide +kernel

private theorem step670_2433_2499 : Positive step670 2433 2499 := by decide +kernel

theorem step670_cover : ∃ ends, Cover step670 firstHeight ends := by
  exact ⟨[2338, 2363, 2432, 2499],
    ⟨(by decide), (by decide), step670_2330_2338,
      (by decide), (by decide), step670_2339_2363,
      (by decide), (by decide), step670_2364_2432,
      (by decide), (by decide), step670_2433_2499, rfl⟩⟩

theorem step670_verified : Checked step670 :=
  ⟨step670_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step670_cover⟩

def step671 : Request :=
  ⟨⟨⟨1650, 2301, 498, 17590⟩, 135254251667456, 770619519922⟩, 73, 6, 51, 771431⟩

theorem step671_nodes : P1_7_1.nodeRows step671.bank.shape = step671.bank.nodeRows :=
  node_check step671.bank (by decide) (by decide) (by decide)

private theorem step671_2330_2348 : Positive step671 2330 2348 := by decide +kernel

private theorem step671_2349_2400 : Positive step671 2349 2400 := by decide +kernel

private theorem step671_2401_2499 : Positive step671 2401 2499 := by decide +kernel

theorem step671_cover : ∃ ends, Cover step671 firstHeight ends := by
  exact ⟨[2348, 2400, 2499],
    ⟨(by decide), (by decide), step671_2330_2348,
      (by decide), (by decide), step671_2349_2400,
      (by decide), (by decide), step671_2401_2499, rfl⟩⟩

theorem step671_verified : Checked step671 :=
  ⟨step671_nodes, Research6966.HelperWindowCatalogue.moment2301_498,
    (by decide), (by decide), (by decide), step671_cover⟩

def step672 : Request :=
  ⟨⟨⟨1650, 2301, 512, 17590⟩, 138129879859200, 787417379725⟩, 76, 6, 51, 771431⟩

theorem step672_nodes : P1_7_1.nodeRows step672.bank.shape = step672.bank.nodeRows :=
  node_check step672.bank (by decide) (by decide) (by decide)

private theorem step672_2330_2345 : Positive step672 2330 2345 := by decide +kernel

private theorem step672_2346_2388 : Positive step672 2346 2388 := by decide +kernel

private theorem step672_2389_2499 : Positive step672 2389 2499 := by decide +kernel

theorem step672_cover : ∃ ends, Cover step672 firstHeight ends := by
  exact ⟨[2345, 2388, 2499],
    ⟨(by decide), (by decide), step672_2330_2345,
      (by decide), (by decide), step672_2346_2388,
      (by decide), (by decide), step672_2389_2499, rfl⟩⟩

theorem step672_verified : Checked step672 :=
  ⟨step672_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step672_cover⟩

def step673 : Request :=
  ⟨⟨⟨2000, 2788, 620, 25043⟩, 245690786119680, 1695265997069⟩, 103, 6, 51, 771431⟩

theorem step673_nodes : P1_7_1.nodeRows step673.bank.shape = step673.bank.nodeRows :=
  node_check step673.bank (by decide) (by decide) (by decide)

private theorem step673_2330_2331 : Positive step673 2330 2331 := by decide +kernel

private theorem step673_2332_2336 : Positive step673 2332 2336 := by decide +kernel

private theorem step673_2337_2349 : Positive step673 2337 2349 := by decide +kernel

private theorem step673_2350_2383 : Positive step673 2350 2383 := by decide +kernel

private theorem step673_2384_2473 : Positive step673 2384 2473 := by decide +kernel

private theorem step673_2474_2499 : Positive step673 2474 2499 := by decide +kernel

theorem step673_cover : ∃ ends, Cover step673 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2473, 2499],
    ⟨(by decide), (by decide), step673_2330_2331,
      (by decide), (by decide), step673_2332_2336,
      (by decide), (by decide), step673_2337_2349,
      (by decide), (by decide), step673_2350_2383,
      (by decide), (by decide), step673_2384_2473,
      (by decide), (by decide), step673_2474_2499, rfl⟩⟩

theorem step673_verified : Checked step673 :=
  ⟨step673_nodes, Research6966.HelperWindowCatalogue.moment2788_620,
    (by decide), (by decide), (by decide), step673_cover⟩

def step674 : Request :=
  ⟨⟨⟨170, 237, 51, 1879⟩, 150975545344, 89126689⟩, 0, 6, 71, 771431⟩

theorem step674_nodes : P1_7_1.nodeRows step674.bank.shape = step674.bank.nodeRows :=
  node_check step674.bank (by decide) (by decide) (by decide)

private theorem step674_2330_2358 : Positive step674 2330 2358 := by decide +kernel

private theorem step674_2359_2488 : Positive step674 2359 2488 := by decide +kernel

private theorem step674_2489_2499 : Positive step674 2489 2499 := by decide +kernel

theorem step674_cover : ∃ ends, Cover step674 firstHeight ends := by
  exact ⟨[2358, 2488, 2499],
    ⟨(by decide), (by decide), step674_2330_2358,
      (by decide), (by decide), step674_2359_2488,
      (by decide), (by decide), step674_2489_2499, rfl⟩⟩

theorem step674_verified : Checked step674 :=
  ⟨step674_nodes, Research6966.HelperWindowCatalogue.moment237_51,
    (by decide), (by decide), (by decide), step674_cover⟩

def step675 : Request :=
  ⟨⟨⟨210, 293, 63, 1879⟩, 283090354176, 206678784⟩, 1, 6, 71, 771431⟩

theorem step675_nodes : P1_7_1.nodeRows step675.bank.shape = step675.bank.nodeRows :=
  node_check step675.bank (by decide) (by decide) (by decide)

private theorem step675_2330_2352 : Positive step675 2330 2352 := by decide +kernel

private theorem step675_2353_2443 : Positive step675 2353 2443 := by decide +kernel

private theorem step675_2444_2499 : Positive step675 2444 2499 := by decide +kernel

theorem step675_cover : ∃ ends, Cover step675 firstHeight ends := by
  exact ⟨[2352, 2443, 2499],
    ⟨(by decide), (by decide), step675_2330_2352,
      (by decide), (by decide), step675_2353_2443,
      (by decide), (by decide), step675_2444_2499, rfl⟩⟩

theorem step675_verified : Checked step675 :=
  ⟨step675_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step675_cover⟩

def step676 : Request :=
  ⟨⟨⟨210, 293, 63, 2113⟩, 283090354176, 206678784⟩, 2, 6, 71, 771431⟩

theorem step676_nodes : P1_7_1.nodeRows step676.bank.shape = step676.bank.nodeRows :=
  node_check step676.bank (by decide) (by decide) (by decide)

private theorem step676_2330_2334 : Positive step676 2330 2334 := by decide +kernel

private theorem step676_2335_2353 : Positive step676 2335 2353 := by decide +kernel

private theorem step676_2354_2427 : Positive step676 2354 2427 := by decide +kernel

private theorem step676_2428_2499 : Positive step676 2428 2499 := by decide +kernel

theorem step676_cover : ∃ ends, Cover step676 firstHeight ends := by
  exact ⟨[2334, 2353, 2427, 2499],
    ⟨(by decide), (by decide), step676_2330_2334,
      (by decide), (by decide), step676_2335_2353,
      (by decide), (by decide), step676_2354_2427,
      (by decide), (by decide), step676_2428_2499, rfl⟩⟩

theorem step676_verified : Checked step676 :=
  ⟨step676_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step676_cover⟩

def step677 : Request :=
  ⟨⟨⟨210, 293, 65, 2377⟩, 289785774080, 211692234⟩, 3, 6, 71, 771431⟩

theorem step677_nodes : P1_7_1.nodeRows step677.bank.shape = step677.bank.nodeRows :=
  node_check step677.bank (by decide) (by decide) (by decide)

private theorem step677_2330_2331 : Positive step677 2330 2331 := by decide +kernel

private theorem step677_2332_2339 : Positive step677 2332 2339 := by decide +kernel

private theorem step677_2340_2369 : Positive step677 2340 2369 := by decide +kernel

private theorem step677_2370_2484 : Positive step677 2370 2484 := by decide +kernel

private theorem step677_2485_2499 : Positive step677 2485 2499 := by decide +kernel

theorem step677_cover : ∃ ends, Cover step677 firstHeight ends := by
  exact ⟨[2331, 2339, 2369, 2484, 2499],
    ⟨(by decide), (by decide), step677_2330_2331,
      (by decide), (by decide), step677_2332_2339,
      (by decide), (by decide), step677_2340_2369,
      (by decide), (by decide), step677_2370_2484,
      (by decide), (by decide), step677_2485_2499, rfl⟩⟩

theorem step677_verified : Checked step677 :=
  ⟨step677_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step677_cover⟩

def step678 : Request :=
  ⟨⟨⟨250, 348, 76, 2377⟩, 480667500544, 414368386⟩, 4, 6, 71, 771431⟩

theorem step678_nodes : P1_7_1.nodeRows step678.bank.shape = step678.bank.nodeRows :=
  node_check step678.bank (by decide) (by decide) (by decide)

private theorem step678_2330_2353 : Positive step678 2330 2353 := by decide +kernel

private theorem step678_2354_2439 : Positive step678 2354 2439 := by decide +kernel

private theorem step678_2440_2499 : Positive step678 2440 2499 := by decide +kernel

theorem step678_cover : ∃ ends, Cover step678 firstHeight ends := by
  exact ⟨[2353, 2439, 2499],
    ⟨(by decide), (by decide), step678_2330_2353,
      (by decide), (by decide), step678_2354_2439,
      (by decide), (by decide), step678_2440_2499, rfl⟩⟩

theorem step678_verified : Checked step678 :=
  ⟨step678_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step678_cover⟩

def step679 : Request :=
  ⟨⟨⟨250, 348, 76, 2674⟩, 480667500544, 414368386⟩, 5, 6, 71, 771431⟩

theorem step679_nodes : P1_7_1.nodeRows step679.bank.shape = step679.bank.nodeRows :=
  node_check step679.bank (by decide) (by decide) (by decide)

private theorem step679_2330_2340 : Positive step679 2330 2340 := by decide +kernel

private theorem step679_2341_2380 : Positive step679 2341 2380 := by decide +kernel

private theorem step679_2381_2499 : Positive step679 2381 2499 := by decide +kernel

theorem step679_cover : ∃ ends, Cover step679 firstHeight ends := by
  exact ⟨[2340, 2380, 2499],
    ⟨(by decide), (by decide), step679_2330_2340,
      (by decide), (by decide), step679_2341_2380,
      (by decide), (by decide), step679_2381_2499, rfl⟩⟩

theorem step679_verified : Checked step679 :=
  ⟨step679_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step679_cover⟩

def step680 : Request :=
  ⟨⟨⟨294, 410, 89, 3008⟩, 777085255680, 791788817⟩, 7, 6, 71, 771431⟩

theorem step680_nodes : P1_7_1.nodeRows step680.bank.shape = step680.bank.nodeRows :=
  node_check step680.bank (by decide) (by decide) (by decide)

private theorem step680_2330_2350 : Positive step680 2330 2350 := by decide +kernel

private theorem step680_2351_2421 : Positive step680 2351 2421 := by decide +kernel

private theorem step680_2422_2499 : Positive step680 2422 2499 := by decide +kernel

theorem step680_cover : ∃ ends, Cover step680 firstHeight ends := by
  exact ⟨[2350, 2421, 2499],
    ⟨(by decide), (by decide), step680_2330_2350,
      (by decide), (by decide), step680_2351_2421,
      (by decide), (by decide), step680_2422_2499, rfl⟩⟩

theorem step680_verified : Checked step680 :=
  ⟨step680_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step680_cover⟩

def step681 : Request :=
  ⟨⟨⟨350, 488, 106, 3384⟩, 1308168290304, 1584729438⟩, 10, 6, 71, 771431⟩

theorem step681_nodes : P1_7_1.nodeRows step681.bank.shape = step681.bank.nodeRows :=
  node_check step681.bank (by decide) (by decide) (by decide)

private theorem step681_2330_2332 : Positive step681 2330 2332 := by decide +kernel

private theorem step681_2333_2342 : Positive step681 2333 2342 := by decide +kernel

private theorem step681_2343_2374 : Positive step681 2343 2374 := by decide +kernel

private theorem step681_2375_2477 : Positive step681 2375 2477 := by decide +kernel

private theorem step681_2478_2499 : Positive step681 2478 2499 := by decide +kernel

theorem step681_cover : ∃ ends, Cover step681 firstHeight ends := by
  exact ⟨[2332, 2342, 2374, 2477, 2499],
    ⟨(by decide), (by decide), step681_2330_2332,
      (by decide), (by decide), step681_2333_2342,
      (by decide), (by decide), step681_2343_2374,
      (by decide), (by decide), step681_2375_2477,
      (by decide), (by decide), step681_2478_2499, rfl⟩⟩

theorem step681_verified : Checked step681 :=
  ⟨step681_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step681_cover⟩

def step682 : Request :=
  ⟨⟨⟨420, 585, 127, 4817⟩, 2252760678400, 3261978232⟩, 16, 6, 71, 771431⟩

theorem step682_nodes : P1_7_1.nodeRows step682.bank.shape = step682.bank.nodeRows :=
  node_check step682.bank (by decide) (by decide) (by decide)

private theorem step682_2330_2331 : Positive step682 2330 2331 := by decide +kernel

private theorem step682_2332_2337 : Positive step682 2332 2337 := by decide +kernel

private theorem step682_2338_2356 : Positive step682 2338 2356 := by decide +kernel

private theorem step682_2357_2415 : Positive step682 2357 2415 := by decide +kernel

private theorem step682_2416_2499 : Positive step682 2416 2499 := by decide +kernel

theorem step682_cover : ∃ ends, Cover step682 firstHeight ends := by
  exact ⟨[2331, 2337, 2356, 2415, 2499],
    ⟨(by decide), (by decide), step682_2330_2331,
      (by decide), (by decide), step682_2332_2337,
      (by decide), (by decide), step682_2338_2356,
      (by decide), (by decide), step682_2357_2415,
      (by decide), (by decide), step682_2416_2499, rfl⟩⟩

theorem step682_verified : Checked step682 :=
  ⟨step682_nodes, Research6966.HelperWindowCatalogue.moment585_127,
    (by decide), (by decide), (by decide), step682_cover⟩

def step683 : Request :=
  ⟨⟨⟨520, 725, 157, 5419⟩, 4261264752640, 7658911630⟩, 20, 6, 71, 771431⟩

theorem step683_nodes : P1_7_1.nodeRows step683.bank.shape = step683.bank.nodeRows :=
  node_check step683.bank (by decide) (by decide) (by decide)

private theorem step683_2330_2361 : Positive step683 2330 2361 := by decide +kernel

private theorem step683_2362_2458 : Positive step683 2362 2458 := by decide +kernel

private theorem step683_2459_2499 : Positive step683 2459 2499 := by decide +kernel

theorem step683_cover : ∃ ends, Cover step683 firstHeight ends := by
  exact ⟨[2361, 2458, 2499],
    ⟨(by decide), (by decide), step683_2330_2361,
      (by decide), (by decide), step683_2362_2458,
      (by decide), (by decide), step683_2459_2499, rfl⟩⟩

theorem step683_verified : Checked step683 :=
  ⟨step683_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step683_cover⟩

def step684 : Request :=
  ⟨⟨⟨750, 1046, 226, 6858⟩, 12730741817344, 33009058589⟩, 31, 6, 71, 771431⟩

theorem step684_nodes : P1_7_1.nodeRows step684.bank.shape = step684.bank.nodeRows :=
  node_check step684.bank (by decide) (by decide) (by decide)

private theorem step684_2330_2339 : Positive step684 2330 2339 := by decide +kernel

private theorem step684_2340_2367 : Positive step684 2340 2367 := by decide +kernel

private theorem step684_2368_2447 : Positive step684 2368 2447 := by decide +kernel

private theorem step684_2448_2499 : Positive step684 2448 2499 := by decide +kernel

theorem step684_cover : ∃ ends, Cover step684 firstHeight ends := by
  exact ⟨[2339, 2367, 2447, 2499],
    ⟨(by decide), (by decide), step684_2330_2339,
      (by decide), (by decide), step684_2340_2367,
      (by decide), (by decide), step684_2368_2447,
      (by decide), (by decide), step684_2448_2499, rfl⟩⟩

theorem step684_verified : Checked step684 :=
  ⟨step684_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step684_cover⟩

def step685 : Request :=
  ⟨⟨⟨750, 1046, 232, 6858⟩, 12985818152960, 33687112323⟩, 32, 6, 71, 771431⟩

theorem step685_nodes : P1_7_1.nodeRows step685.bank.shape = step685.bank.nodeRows :=
  node_check step685.bank (by decide) (by decide) (by decide)

private theorem step685_2330_2345 : Positive step685 2330 2345 := by decide +kernel

private theorem step685_2346_2390 : Positive step685 2346 2390 := by decide +kernel

private theorem step685_2391_2499 : Positive step685 2391 2499 := by decide +kernel

theorem step685_cover : ∃ ends, Cover step685 firstHeight ends := by
  exact ⟨[2345, 2390, 2499],
    ⟨(by decide), (by decide), step685_2330_2345,
      (by decide), (by decide), step685_2346_2390,
      (by decide), (by decide), step685_2391_2499, rfl⟩⟩

theorem step685_verified : Checked step685 :=
  ⟨step685_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step685_cover⟩

def step686 : Request :=
  ⟨⟨⟨900, 1255, 272, 9763⟩, 22024701870080, 68477558806⟩, 44, 6, 71, 771431⟩

theorem step686_nodes : P1_7_1.nodeRows step686.bank.shape = step686.bank.nodeRows :=
  node_check step686.bank (by decide) (by decide) (by decide)

private theorem step686_2330_2342 : Positive step686 2330 2342 := by decide +kernel

private theorem step686_2343_2378 : Positive step686 2343 2378 := by decide +kernel

private theorem step686_2379_2479 : Positive step686 2379 2479 := by decide +kernel

private theorem step686_2480_2499 : Positive step686 2480 2499 := by decide +kernel

theorem step686_cover : ∃ ends, Cover step686 firstHeight ends := by
  exact ⟨[2342, 2378, 2479, 2499],
    ⟨(by decide), (by decide), step686_2330_2342,
      (by decide), (by decide), step686_2343_2378,
      (by decide), (by decide), step686_2379_2479,
      (by decide), (by decide), step686_2480_2499, rfl⟩⟩

theorem step686_verified : Checked step686 :=
  ⟨step686_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step686_cover⟩

def step687 : Request :=
  ⟨⟨⟨1350, 1882, 408, 15636⟩, 74202776600576, 345598963978⟩, 73, 6, 71, 771431⟩

theorem step687_nodes : P1_7_1.nodeRows step687.bank.shape = step687.bank.nodeRows :=
  node_check step687.bank (by decide) (by decide) (by decide)

private theorem step687_2330_2344 : Positive step687 2330 2344 := by decide +kernel

private theorem step687_2345_2385 : Positive step687 2345 2385 := by decide +kernel

private theorem step687_2386_2496 : Positive step687 2386 2496 := by decide +kernel

private theorem step687_2497_2499 : Positive step687 2497 2499 := by decide +kernel

theorem step687_cover : ∃ ends, Cover step687 firstHeight ends := by
  exact ⟨[2344, 2385, 2496, 2499],
    ⟨(by decide), (by decide), step687_2330_2344,
      (by decide), (by decide), step687_2345_2385,
      (by decide), (by decide), step687_2386_2496,
      (by decide), (by decide), step687_2497_2499, rfl⟩⟩

theorem step687_verified : Checked step687 :=
  ⟨step687_nodes, Research6966.HelperWindowCatalogue.moment1882_408,
    (by decide), (by decide), (by decide), step687_cover⟩

def step688 : Request :=
  ⟨⟨⟨1350, 1882, 418, 15636⟩, 75578221264896, 352166349574⟩, 76, 6, 71, 771431⟩

theorem step688_nodes : P1_7_1.nodeRows step688.bank.shape = step688.bank.nodeRows :=
  node_check step688.bank (by decide) (by decide) (by decide)

private theorem step688_2330_2331 : Positive step688 2330 2331 := by decide +kernel

private theorem step688_2332_2337 : Positive step688 2332 2337 := by decide +kernel

private theorem step688_2338_2353 : Positive step688 2338 2353 := by decide +kernel

private theorem step688_2354_2396 : Positive step688 2354 2396 := by decide +kernel

private theorem step688_2397_2499 : Positive step688 2397 2499 := by decide +kernel

theorem step688_cover : ∃ ends, Cover step688 firstHeight ends := by
  exact ⟨[2331, 2337, 2353, 2396, 2499],
    ⟨(by decide), (by decide), step688_2330_2331,
      (by decide), (by decide), step688_2332_2337,
      (by decide), (by decide), step688_2338_2353,
      (by decide), (by decide), step688_2354_2396,
      (by decide), (by decide), step688_2397_2499, rfl⟩⟩

theorem step688_verified : Checked step688 :=
  ⟨step688_nodes, Research6966.HelperWindowCatalogue.moment1882_418,
    (by decide), (by decide), (by decide), step688_cover⟩

def step689 : Request :=
  ⟨⟨⟨2000, 2788, 604, 19788⟩, 240862397726720, 1661128510194⟩, 103, 6, 71, 771431⟩

theorem step689_nodes : P1_7_1.nodeRows step689.bank.shape = step689.bank.nodeRows :=
  node_check step689.bank (by decide) (by decide) (by decide)

private theorem step689_2330_2359 : Positive step689 2330 2359 := by decide +kernel

private theorem step689_2360_2440 : Positive step689 2360 2440 := by decide +kernel

private theorem step689_2441_2499 : Positive step689 2441 2499 := by decide +kernel

theorem step689_cover : ∃ ends, Cover step689 firstHeight ends := by
  exact ⟨[2359, 2440, 2499],
    ⟨(by decide), (by decide), step689_2330_2359,
      (by decide), (by decide), step689_2360_2440,
      (by decide), (by decide), step689_2441_2499, rfl⟩⟩

theorem step689_verified : Checked step689 :=
  ⟨step689_nodes, Research6966.HelperWindowCatalogue.moment2788_604,
    (by decide), (by decide), (by decide), step689_cover⟩

def step690 : Request :=
  ⟨⟨⟨250, 349, 76, 4282⟩, 480667500544, 418199213⟩, 0, 7, 1, 900003⟩

theorem step690_nodes : P1_7_1.nodeRows step690.bank.shape = step690.bank.nodeRows :=
  node_check step690.bank (by decide) (by decide) (by decide)

private theorem step690_2330_2364 : Positive step690 2330 2364 := by decide +kernel

private theorem step690_2365_2490 : Positive step690 2365 2490 := by decide +kernel

private theorem step690_2491_2499 : Positive step690 2491 2499 := by decide +kernel

theorem step690_cover : ∃ ends, Cover step690 firstHeight ends := by
  exact ⟨[2364, 2490, 2499],
    ⟨(by decide), (by decide), step690_2330_2364,
      (by decide), (by decide), step690_2365_2490,
      (by decide), (by decide), step690_2491_2499, rfl⟩⟩

theorem step690_verified : Checked step690 :=
  ⟨step690_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step690_cover⟩

def step691 : Request :=
  ⟨⟨⟨250, 349, 76, 4817⟩, 480667500544, 418199213⟩, 1, 7, 1, 900003⟩

theorem step691_nodes : P1_7_1.nodeRows step691.bank.shape = step691.bank.nodeRows :=
  node_check step691.bank (by decide) (by decide) (by decide)

private theorem step691_2330_2355 : Positive step691 2330 2355 := by decide +kernel

private theorem step691_2356_2447 : Positive step691 2356 2447 := by decide +kernel

private theorem step691_2448_2499 : Positive step691 2448 2499 := by decide +kernel

theorem step691_cover : ∃ ends, Cover step691 firstHeight ends := by
  exact ⟨[2355, 2447, 2499],
    ⟨(by decide), (by decide), step691_2330_2355,
      (by decide), (by decide), step691_2356_2447,
      (by decide), (by decide), step691_2448_2499, rfl⟩⟩

theorem step691_verified : Checked step691 :=
  ⟨step691_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step691_cover⟩

def step692 : Request :=
  ⟨⟨⟨294, 410, 91, 4817⟩, 790165454848, 805457011⟩, 2, 7, 1, 900003⟩

theorem step692_nodes : P1_7_1.nodeRows step692.bank.shape = step692.bank.nodeRows :=
  node_check step692.bank (by decide) (by decide) (by decide)

private theorem step692_2330_2333 : Positive step692 2330 2333 := by decide +kernel

private theorem step692_2334_2346 : Positive step692 2334 2346 := by decide +kernel

private theorem step692_2347_2390 : Positive step692 2347 2390 := by decide +kernel

private theorem step692_2391_2499 : Positive step692 2391 2499 := by decide +kernel

theorem step692_cover : ∃ ends, Cover step692 firstHeight ends := by
  exact ⟨[2333, 2346, 2390, 2499],
    ⟨(by decide), (by decide), step692_2330_2333,
      (by decide), (by decide), step692_2334_2346,
      (by decide), (by decide), step692_2347_2390,
      (by decide), (by decide), step692_2391_2499, rfl⟩⟩

theorem step692_verified : Checked step692 :=
  ⟨step692_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step692_cover⟩

def step693 : Request :=
  ⟨⟨⟨294, 410, 91, 5419⟩, 790165454848, 805457011⟩, 3, 7, 1, 900003⟩

theorem step693_nodes : P1_7_1.nodeRows step693.bank.shape = step693.bank.nodeRows :=
  node_check step693.bank (by decide) (by decide) (by decide)

private theorem step693_2330_2339 : Positive step693 2330 2339 := by decide +kernel

private theorem step693_2340_2373 : Positive step693 2340 2373 := by decide +kernel

private theorem step693_2374_2487 : Positive step693 2374 2487 := by decide +kernel

private theorem step693_2488_2499 : Positive step693 2488 2499 := by decide +kernel

theorem step693_cover : ∃ ends, Cover step693 firstHeight ends := by
  exact ⟨[2339, 2373, 2487, 2499],
    ⟨(by decide), (by decide), step693_2330_2339,
      (by decide), (by decide), step693_2340_2373,
      (by decide), (by decide), step693_2374_2487,
      (by decide), (by decide), step693_2488_2499, rfl⟩⟩

theorem step693_verified : Checked step693 :=
  ⟨step693_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step693_cover⟩

def step694 : Request :=
  ⟨⟨⟨294, 410, 91, 6096⟩, 790165454848, 805457011⟩, 4, 7, 1, 900003⟩

theorem step694_nodes : P1_7_1.nodeRows step694.bank.shape = step694.bank.nodeRows :=
  node_check step694.bank (by decide) (by decide) (by decide)

private theorem step694_2330_2337 : Positive step694 2330 2337 := by decide +kernel

private theorem step694_2338_2364 : Positive step694 2338 2364 := by decide +kernel

private theorem step694_2365_2454 : Positive step694 2365 2454 := by decide +kernel

private theorem step694_2455_2499 : Positive step694 2455 2499 := by decide +kernel

theorem step694_cover : ∃ ends, Cover step694 firstHeight ends := by
  exact ⟨[2337, 2364, 2454, 2499],
    ⟨(by decide), (by decide), step694_2330_2337,
      (by decide), (by decide), step694_2338_2364,
      (by decide), (by decide), step694_2365_2454,
      (by decide), (by decide), step694_2455_2499, rfl⟩⟩

theorem step694_verified : Checked step694 :=
  ⟨step694_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step694_cover⟩

def step695 : Request :=
  ⟨⟨⟨350, 488, 108, 6096⟩, 1326705278976, 1607754763⟩, 5, 7, 1, 900003⟩

theorem step695_nodes : P1_7_1.nodeRows step695.bank.shape = step695.bank.nodeRows :=
  node_check step695.bank (by decide) (by decide) (by decide)

private theorem step695_2330_2335 : Positive step695 2330 2335 := by decide +kernel

private theorem step695_2336_2354 : Positive step695 2336 2354 := by decide +kernel

private theorem step695_2355_2414 : Positive step695 2355 2414 := by decide +kernel

private theorem step695_2415_2499 : Positive step695 2415 2499 := by decide +kernel

theorem step695_cover : ∃ ends, Cover step695 firstHeight ends := by
  exact ⟨[2335, 2354, 2414, 2499],
    ⟨(by decide), (by decide), step695_2330_2335,
      (by decide), (by decide), step695_2336_2354,
      (by decide), (by decide), step695_2355_2414,
      (by decide), (by decide), step695_2415_2499, rfl⟩⟩

theorem step695_verified : Checked step695 :=
  ⟨step695_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step695_cover⟩

def step696 : Request :=
  ⟨⟨⟨420, 586, 130, 6858⟩, 2292767784960, 3339653140⟩, 7, 7, 1, 900003⟩

theorem step696_nodes : P1_7_1.nodeRows step696.bank.shape = step696.bank.nodeRows :=
  node_check step696.bank (by decide) (by decide) (by decide)

private theorem step696_2330_2342 : Positive step696 2330 2342 := by decide +kernel

private theorem step696_2343_2382 : Positive step696 2343 2382 := by decide +kernel

private theorem step696_2383_2499 : Positive step696 2383 2499 := by decide +kernel

theorem step696_cover : ∃ ends, Cover step696 firstHeight ends := by
  exact ⟨[2342, 2382, 2499],
    ⟨(by decide), (by decide), step696_2330_2342,
      (by decide), (by decide), step696_2343_2382,
      (by decide), (by decide), step696_2383_2499, rfl⟩⟩

theorem step696_verified : Checked step696 :=
  ⟨step696_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step696_cover⟩

def step697 : Request :=
  ⟨⟨⟨420, 586, 130, 8679⟩, 2292767784960, 3339653140⟩, 10, 7, 1, 900003⟩

theorem step697_nodes : P1_7_1.nodeRows step697.bank.shape = step697.bank.nodeRows :=
  node_check step697.bank (by decide) (by decide) (by decide)

private theorem step697_2330_2340 : Positive step697 2330 2340 := by decide +kernel

private theorem step697_2341_2374 : Positive step697 2341 2374 := by decide +kernel

private theorem step697_2375_2478 : Positive step697 2375 2478 := by decide +kernel

private theorem step697_2479_2499 : Positive step697 2479 2499 := by decide +kernel

theorem step697_cover : ∃ ends, Cover step697 firstHeight ends := by
  exact ⟨[2340, 2374, 2478, 2499],
    ⟨(by decide), (by decide), step697_2330_2340,
      (by decide), (by decide), step697_2341_2374,
      (by decide), (by decide), step697_2375_2478,
      (by decide), (by decide), step697_2479_2499, rfl⟩⟩

theorem step697_verified : Checked step697 :=
  ⟨step697_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step697_cover⟩

def step698 : Request :=
  ⟨⟨⟨630, 879, 190, 10983⟩, 7559493713920, 16491913877⟩, 16, 7, 1, 900003⟩

theorem step698_nodes : P1_7_1.nodeRows step698.bank.shape = step698.bank.nodeRows :=
  node_check step698.bank (by decide) (by decide) (by decide)

private theorem step698_2330_2348 : Positive step698 2330 2348 := by decide +kernel

private theorem step698_2349_2403 : Positive step698 2349 2403 := by decide +kernel

private theorem step698_2404_2499 : Positive step698 2404 2499 := by decide +kernel

theorem step698_cover : ∃ ends, Cover step698 firstHeight ends := by
  exact ⟨[2348, 2403, 2499],
    ⟨(by decide), (by decide), step698_2330_2348,
      (by decide), (by decide), step698_2349_2403,
      (by decide), (by decide), step698_2404_2499, rfl⟩⟩

theorem step698_verified : Checked step698 :=
  ⟨step698_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step698_cover⟩

def step699 : Request :=
  ⟨⟨⟨750, 1046, 226, 12355⟩, 12730741817344, 33009058589⟩, 20, 7, 1, 900003⟩

theorem step699_nodes : P1_7_1.nodeRows step699.bank.shape = step699.bank.nodeRows :=
  node_check step699.bank (by decide) (by decide) (by decide)

private theorem step699_2330_2338 : Positive step699 2330 2338 := by decide +kernel

private theorem step699_2339_2364 : Positive step699 2339 2364 := by decide +kernel

private theorem step699_2365_2438 : Positive step699 2365 2438 := by decide +kernel

private theorem step699_2439_2499 : Positive step699 2439 2499 := by decide +kernel

theorem step699_cover : ∃ ends, Cover step699 firstHeight ends := by
  exact ⟨[2338, 2364, 2438, 2499],
    ⟨(by decide), (by decide), step699_2330_2338,
      (by decide), (by decide), step699_2339_2364,
      (by decide), (by decide), step699_2365_2438,
      (by decide), (by decide), step699_2439_2499, rfl⟩⟩

theorem step699_verified : Checked step699 :=
  ⟨step699_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step699_cover⟩

def step700 : Request :=
  ⟨⟨⟨900, 1255, 272, 17590⟩, 22024701870080, 68477558806⟩, 31, 7, 1, 900003⟩

theorem step700_nodes : P1_7_1.nodeRows step700.bank.shape = step700.bank.nodeRows :=
  node_check step700.bank (by decide) (by decide) (by decide)

private theorem step700_2330_2337 : Positive step700 2330 2337 := by decide +kernel

private theorem step700_2338_2360 : Positive step700 2338 2360 := by decide +kernel

private theorem step700_2361_2424 : Positive step700 2361 2424 := by decide +kernel

private theorem step700_2425_2499 : Positive step700 2425 2499 := by decide +kernel

theorem step700_cover : ∃ ends, Cover step700 firstHeight ends := by
  exact ⟨[2337, 2360, 2424, 2499],
    ⟨(by decide), (by decide), step700_2330_2337,
      (by decide), (by decide), step700_2338_2360,
      (by decide), (by decide), step700_2361_2424,
      (by decide), (by decide), step700_2425_2499, rfl⟩⟩

theorem step700_verified : Checked step700 :=
  ⟨step700_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step700_cover⟩

def step701 : Request :=
  ⟨⟨⟨900, 1255, 279, 17590⟩, 22452680785920, 69841856233⟩, 32, 7, 1, 900003⟩

theorem step701_nodes : P1_7_1.nodeRows step701.bank.shape = step701.bank.nodeRows :=
  node_check step701.bank (by decide) (by decide) (by decide)

private theorem step701_2330_2339 : Positive step701 2330 2339 := by decide +kernel

private theorem step701_2340_2366 : Positive step701 2340 2366 := by decide +kernel

private theorem step701_2367_2441 : Positive step701 2367 2441 := by decide +kernel

private theorem step701_2442_2499 : Positive step701 2442 2499 := by decide +kernel

theorem step701_cover : ∃ ends, Cover step701 firstHeight ends := by
  exact ⟨[2339, 2366, 2441, 2499],
    ⟨(by decide), (by decide), step701_2330_2339,
      (by decide), (by decide), step701_2340_2366,
      (by decide), (by decide), step701_2367_2441,
      (by decide), (by decide), step701_2442_2499, rfl⟩⟩

theorem step701_verified : Checked step701 :=
  ⟨step701_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step701_cover⟩

def step702 : Request :=
  ⟨⟨⟨1100, 1534, 332, 25043⟩, 40133103452160, 152499774767⟩, 44, 7, 1, 900003⟩

theorem step702_nodes : P1_7_1.nodeRows step702.bank.shape = step702.bank.nodeRows :=
  node_check step702.bank (by decide) (by decide) (by decide)

private theorem step702_2330_2343 : Positive step702 2330 2343 := by decide +kernel

private theorem step702_2344_2382 : Positive step702 2344 2382 := by decide +kernel

private theorem step702_2383_2489 : Positive step702 2383 2489 := by decide +kernel

private theorem step702_2490_2499 : Positive step702 2490 2499 := by decide +kernel

theorem step702_cover : ∃ ends, Cover step702 firstHeight ends := by
  exact ⟨[2343, 2382, 2489, 2499],
    ⟨(by decide), (by decide), step702_2330_2343,
      (by decide), (by decide), step702_2344_2382,
      (by decide), (by decide), step702_2383_2489,
      (by decide), (by decide), step702_2490_2499, rfl⟩⟩

theorem step702_verified : Checked step702 :=
  ⟨step702_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step702_cover⟩

def step703 : Request :=
  ⟨⟨⟨2000, 2790, 604, 35655⟩, 240862397726720, 1664965815864⟩, 73, 7, 1, 900003⟩

theorem step703_nodes : P1_7_1.nodeRows step703.bank.shape = step703.bank.nodeRows :=
  node_check step703.bank (by decide) (by decide) (by decide)

private theorem step703_2330_2360 : Positive step703 2330 2360 := by decide +kernel

private theorem step703_2361_2443 : Positive step703 2361 2443 := by decide +kernel

private theorem step703_2444_2499 : Positive step703 2444 2499 := by decide +kernel

theorem step703_cover : ∃ ends, Cover step703 firstHeight ends := by
  exact ⟨[2360, 2443, 2499],
    ⟨(by decide), (by decide), step703_2330_2360,
      (by decide), (by decide), step703_2361_2443,
      (by decide), (by decide), step703_2444_2499, rfl⟩⟩

theorem step703_verified : Checked step703 :=
  ⟨step703_nodes, Research6966.HelperWindowCatalogue.moment2790_604,
    (by decide), (by decide), (by decide), step703_cover⟩

def step704 : Request :=
  ⟨⟨⟨2000, 2789, 604, 35655⟩, 240862397726720, 1663046410409⟩, 76, 7, 1, 900003⟩

theorem step704_nodes : P1_7_1.nodeRows step704.bank.shape = step704.bank.nodeRows :=
  node_check step704.bank (by decide) (by decide) (by decide)

private theorem step704_2330_2336 : Positive step704 2330 2336 := by decide +kernel

private theorem step704_2337_2355 : Positive step704 2337 2355 := by decide +kernel

private theorem step704_2356_2405 : Positive step704 2356 2405 := by decide +kernel

private theorem step704_2406_2499 : Positive step704 2406 2499 := by decide +kernel

theorem step704_cover : ∃ ends, Cover step704 firstHeight ends := by
  exact ⟨[2336, 2355, 2405, 2499],
    ⟨(by decide), (by decide), step704_2330_2336,
      (by decide), (by decide), step704_2337_2355,
      (by decide), (by decide), step704_2356_2405,
      (by decide), (by decide), step704_2406_2499, rfl⟩⟩

theorem step704_verified : Checked step704 :=
  ⟨step704_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step704_cover⟩

end Research6966.HelperRescueCatalogue
