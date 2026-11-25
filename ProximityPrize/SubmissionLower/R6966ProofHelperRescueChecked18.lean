import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step705 : Request :=
  ⟨⟨⟨3000, 4185, 906, 45124⟩, 812266433019904, 8420412037186⟩, 103, 7, 1, 900003⟩

theorem step705_nodes : P1_7_1.nodeRows step705.bank.shape = step705.bank.nodeRows :=
  node_check step705.bank (by decide) (by decide) (by decide)

private theorem step705_2330_2331 : Positive step705 2330 2331 := by decide +kernel

private theorem step705_2332_2336 : Positive step705 2332 2336 := by decide +kernel

private theorem step705_2337_2349 : Positive step705 2337 2349 := by decide +kernel

private theorem step705_2350_2383 : Positive step705 2350 2383 := by decide +kernel

private theorem step705_2384_2472 : Positive step705 2384 2472 := by decide +kernel

private theorem step705_2473_2499 : Positive step705 2473 2499 := by decide +kernel

theorem step705_cover : ∃ ends, Cover step705 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2472, 2499],
    ⟨(by decide), (by decide), step705_2330_2331,
      (by decide), (by decide), step705_2332_2336,
      (by decide), (by decide), step705_2337_2349,
      (by decide), (by decide), step705_2350_2383,
      (by decide), (by decide), step705_2384_2472,
      (by decide), (by decide), step705_2473_2499, rfl⟩⟩

theorem step705_verified : Checked step705 :=
  ⟨step705_nodes, Research6966.HelperWindowCatalogue.moment4185_906,
    (by decide), (by decide), (by decide), step705_cover⟩

def step706 : Request :=
  ⟨⟨⟨250, 349, 74, 4282⟩, 471125196800, 409695834⟩, 0, 7, 2, 900003⟩

theorem step706_nodes : P1_7_1.nodeRows step706.bank.shape = step706.bank.nodeRows :=
  node_check step706.bank (by decide) (by decide) (by decide)

private theorem step706_2330_2332 : Positive step706 2330 2332 := by decide +kernel

private theorem step706_2333_2343 : Positive step706 2333 2343 := by decide +kernel

private theorem step706_2344_2383 : Positive step706 2344 2383 := by decide +kernel

private theorem step706_2384_2499 : Positive step706 2384 2499 := by decide +kernel

theorem step706_cover : ∃ ends, Cover step706 firstHeight ends := by
  exact ⟨[2332, 2343, 2383, 2499],
    ⟨(by decide), (by decide), step706_2330_2332,
      (by decide), (by decide), step706_2333_2343,
      (by decide), (by decide), step706_2344_2383,
      (by decide), (by decide), step706_2384_2499, rfl⟩⟩

theorem step706_verified : Checked step706 :=
  ⟨step706_nodes, Research6966.HelperWindowCatalogue.moment349_74,
    (by decide), (by decide), (by decide), step706_cover⟩

def step707 : Request :=
  ⟨⟨⟨250, 349, 76, 4817⟩, 480667500544, 418199213⟩, 1, 7, 2, 900003⟩

theorem step707_nodes : P1_7_1.nodeRows step707.bank.shape = step707.bank.nodeRows :=
  node_check step707.bank (by decide) (by decide) (by decide)

private theorem step707_2330_2364 : Positive step707 2330 2364 := by decide +kernel

private theorem step707_2365_2490 : Positive step707 2365 2490 := by decide +kernel

private theorem step707_2491_2499 : Positive step707 2491 2499 := by decide +kernel

theorem step707_cover : ∃ ends, Cover step707 firstHeight ends := by
  exact ⟨[2364, 2490, 2499],
    ⟨(by decide), (by decide), step707_2330_2364,
      (by decide), (by decide), step707_2365_2490,
      (by decide), (by decide), step707_2491_2499, rfl⟩⟩

theorem step707_verified : Checked step707 :=
  ⟨step707_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step707_cover⟩

def step708 : Request :=
  ⟨⟨⟨294, 410, 91, 4817⟩, 790165454848, 805457011⟩, 2, 7, 2, 900003⟩

theorem step708_nodes : P1_7_1.nodeRows step708.bank.shape = step708.bank.nodeRows :=
  node_check step708.bank (by decide) (by decide) (by decide)

private theorem step708_2330_2343 : Positive step708 2330 2343 := by decide +kernel

private theorem step708_2344_2390 : Positive step708 2344 2390 := by decide +kernel

private theorem step708_2391_2499 : Positive step708 2391 2499 := by decide +kernel

theorem step708_cover : ∃ ends, Cover step708 firstHeight ends := by
  exact ⟨[2343, 2390, 2499],
    ⟨(by decide), (by decide), step708_2330_2343,
      (by decide), (by decide), step708_2344_2390,
      (by decide), (by decide), step708_2391_2499, rfl⟩⟩

theorem step708_verified : Checked step708 :=
  ⟨step708_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step708_cover⟩

def step709 : Request :=
  ⟨⟨⟨294, 410, 89, 5419⟩, 777085255680, 791788817⟩, 3, 7, 2, 900003⟩

theorem step709_nodes : P1_7_1.nodeRows step709.bank.shape = step709.bank.nodeRows :=
  node_check step709.bank (by decide) (by decide) (by decide)

private theorem step709_2330_2332 : Positive step709 2330 2332 := by decide +kernel

private theorem step709_2333_2342 : Positive step709 2333 2342 := by decide +kernel

private theorem step709_2343_2376 : Positive step709 2343 2376 := by decide +kernel

private theorem step709_2377_2490 : Positive step709 2377 2490 := by decide +kernel

private theorem step709_2491_2499 : Positive step709 2491 2499 := by decide +kernel

theorem step709_cover : ∃ ends, Cover step709 firstHeight ends := by
  exact ⟨[2332, 2342, 2376, 2490, 2499],
    ⟨(by decide), (by decide), step709_2330_2332,
      (by decide), (by decide), step709_2333_2342,
      (by decide), (by decide), step709_2343_2376,
      (by decide), (by decide), step709_2377_2490,
      (by decide), (by decide), step709_2491_2499, rfl⟩⟩

theorem step709_verified : Checked step709 :=
  ⟨step709_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step709_cover⟩

def step710 : Request :=
  ⟨⟨⟨294, 410, 91, 6096⟩, 790165454848, 805457011⟩, 4, 7, 2, 900003⟩

theorem step710_nodes : P1_7_1.nodeRows step710.bank.shape = step710.bank.nodeRows :=
  node_check step710.bank (by decide) (by decide) (by decide)

private theorem step710_2330_2345 : Positive step710 2330 2345 := by decide +kernel

private theorem step710_2346_2399 : Positive step710 2346 2399 := by decide +kernel

private theorem step710_2400_2499 : Positive step710 2400 2499 := by decide +kernel

theorem step710_cover : ∃ ends, Cover step710 firstHeight ends := by
  exact ⟨[2345, 2399, 2499],
    ⟨(by decide), (by decide), step710_2330_2345,
      (by decide), (by decide), step710_2346_2399,
      (by decide), (by decide), step710_2400_2499, rfl⟩⟩

theorem step710_verified : Checked step710 :=
  ⟨step710_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step710_cover⟩

def step711 : Request :=
  ⟨⟨⟨350, 488, 108, 6096⟩, 1326705278976, 1607754763⟩, 5, 7, 2, 900003⟩

theorem step711_nodes : P1_7_1.nodeRows step711.bank.shape = step711.bank.nodeRows :=
  node_check step711.bank (by decide) (by decide) (by decide)

private theorem step711_2330_2344 : Positive step711 2330 2344 := by decide +kernel

private theorem step711_2345_2392 : Positive step711 2345 2392 := by decide +kernel

private theorem step711_2393_2499 : Positive step711 2393 2499 := by decide +kernel

theorem step711_cover : ∃ ends, Cover step711 firstHeight ends := by
  exact ⟨[2344, 2392, 2499],
    ⟨(by decide), (by decide), step711_2330_2344,
      (by decide), (by decide), step711_2345_2392,
      (by decide), (by decide), step711_2393_2499, rfl⟩⟩

theorem step711_verified : Checked step711 :=
  ⟨step711_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step711_cover⟩

def step712 : Request :=
  ⟨⟨⟨420, 586, 127, 6858⟩, 2252760678400, 3279920952⟩, 7, 7, 2, 900003⟩

theorem step712_nodes : P1_7_1.nodeRows step712.bank.shape = step712.bank.nodeRows :=
  node_check step712.bank (by decide) (by decide) (by decide)

private theorem step712_2330_2333 : Positive step712 2330 2333 := by decide +kernel

private theorem step712_2334_2346 : Positive step712 2334 2346 := by decide +kernel

private theorem step712_2347_2386 : Positive step712 2347 2386 := by decide +kernel

private theorem step712_2387_2499 : Positive step712 2387 2499 := by decide +kernel

theorem step712_cover : ∃ ends, Cover step712 firstHeight ends := by
  exact ⟨[2333, 2346, 2386, 2499],
    ⟨(by decide), (by decide), step712_2330_2333,
      (by decide), (by decide), step712_2334_2346,
      (by decide), (by decide), step712_2347_2386,
      (by decide), (by decide), step712_2387_2499, rfl⟩⟩

theorem step712_verified : Checked step712 :=
  ⟨step712_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step712_cover⟩

def step713 : Request :=
  ⟨⟨⟨520, 725, 161, 7715⟩, 4343013310464, 7809559934⟩, 10, 7, 2, 900003⟩

theorem step713_nodes : P1_7_1.nodeRows step713.bank.shape = step713.bank.nodeRows :=
  node_check step713.bank (by decide) (by decide) (by decide)

private theorem step713_2330_2332 : Positive step713 2330 2332 := by decide +kernel

private theorem step713_2333_2341 : Positive step713 2333 2341 := by decide +kernel

private theorem step713_2342_2368 : Positive step713 2342 2368 := by decide +kernel

private theorem step713_2369_2447 : Positive step713 2369 2447 := by decide +kernel

private theorem step713_2448_2499 : Positive step713 2448 2499 := by decide +kernel

theorem step713_cover : ∃ ends, Cover step713 firstHeight ends := by
  exact ⟨[2332, 2341, 2368, 2447, 2499],
    ⟨(by decide), (by decide), step713_2330_2332,
      (by decide), (by decide), step713_2333_2341,
      (by decide), (by decide), step713_2342_2368,
      (by decide), (by decide), step713_2369_2447,
      (by decide), (by decide), step713_2448_2499, rfl⟩⟩

theorem step713_verified : Checked step713 :=
  ⟨step713_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step713_cover⟩

def step714 : Request :=
  ⟨⟨⟨630, 879, 190, 10983⟩, 7559493713920, 16491913877⟩, 16, 7, 2, 900003⟩

theorem step714_nodes : P1_7_1.nodeRows step714.bank.shape = step714.bank.nodeRows :=
  node_check step714.bank (by decide) (by decide) (by decide)

private theorem step714_2330_2356 : Positive step714 2330 2356 := by decide +kernel

private theorem step714_2357_2435 : Positive step714 2357 2435 := by decide +kernel

private theorem step714_2436_2499 : Positive step714 2436 2499 := by decide +kernel

theorem step714_cover : ∃ ends, Cover step714 firstHeight ends := by
  exact ⟨[2356, 2435, 2499],
    ⟨(by decide), (by decide), step714_2330_2356,
      (by decide), (by decide), step714_2357_2435,
      (by decide), (by decide), step714_2436_2499, rfl⟩⟩

theorem step714_verified : Checked step714 :=
  ⟨step714_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step714_cover⟩

def step715 : Request :=
  ⟨⟨⟨750, 1046, 226, 12355⟩, 12730741817344, 33009058589⟩, 20, 7, 2, 900003⟩

theorem step715_nodes : P1_7_1.nodeRows step715.bank.shape = step715.bank.nodeRows :=
  node_check step715.bank (by decide) (by decide) (by decide)

private theorem step715_2330_2347 : Positive step715 2330 2347 := by decide +kernel

private theorem step715_2348_2398 : Positive step715 2348 2398 := by decide +kernel

private theorem step715_2399_2499 : Positive step715 2399 2499 := by decide +kernel

theorem step715_cover : ∃ ends, Cover step715 firstHeight ends := by
  exact ⟨[2347, 2398, 2499],
    ⟨(by decide), (by decide), step715_2330_2347,
      (by decide), (by decide), step715_2348_2398,
      (by decide), (by decide), step715_2399_2499, rfl⟩⟩

theorem step715_verified : Checked step715 :=
  ⟨step715_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step715_cover⟩

def step716 : Request :=
  ⟨⟨⟨1100, 1534, 341, 15636⟩, 40955142733824, 155702293064⟩, 31, 7, 2, 900003⟩

theorem step716_nodes : P1_7_1.nodeRows step716.bank.shape = step716.bank.nodeRows :=
  node_check step716.bank (by decide) (by decide) (by decide)

private theorem step716_2330_2332 : Positive step716 2330 2332 := by decide +kernel

private theorem step716_2333_2340 : Positive step716 2333 2340 := by decide +kernel

private theorem step716_2341_2362 : Positive step716 2341 2362 := by decide +kernel

private theorem step716_2363_2421 : Positive step716 2363 2421 := by decide +kernel

private theorem step716_2422_2499 : Positive step716 2422 2499 := by decide +kernel

theorem step716_cover : ∃ ends, Cover step716 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2421, 2499],
    ⟨(by decide), (by decide), step716_2330_2332,
      (by decide), (by decide), step716_2333_2340,
      (by decide), (by decide), step716_2341_2362,
      (by decide), (by decide), step716_2363_2421,
      (by decide), (by decide), step716_2422_2499, rfl⟩⟩

theorem step716_verified : Checked step716 :=
  ⟨step716_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step716_cover⟩

def step717 : Request :=
  ⟨⟨⟨900, 1255, 279, 17590⟩, 22452680785920, 69841856233⟩, 32, 7, 2, 900003⟩

theorem step717_nodes : P1_7_1.nodeRows step717.bank.shape = step717.bank.nodeRows :=
  node_check step717.bank (by decide) (by decide) (by decide)

private theorem step717_2330_2346 : Positive step717 2330 2346 := by decide +kernel

private theorem step717_2347_2393 : Positive step717 2347 2393 := by decide +kernel

private theorem step717_2394_2499 : Positive step717 2394 2499 := by decide +kernel

theorem step717_cover : ∃ ends, Cover step717 firstHeight ends := by
  exact ⟨[2346, 2393, 2499],
    ⟨(by decide), (by decide), step717_2330_2346,
      (by decide), (by decide), step717_2347_2393,
      (by decide), (by decide), step717_2394_2499, rfl⟩⟩

theorem step717_verified : Checked step717 :=
  ⟨step717_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step717_cover⟩

def step718 : Request :=
  ⟨⟨⟨1350, 1883, 408, 22261⟩, 74202776600576, 346190054868⟩, 44, 7, 2, 900003⟩

theorem step718_nodes : P1_7_1.nodeRows step718.bank.shape = step718.bank.nodeRows :=
  node_check step718.bank (by decide) (by decide) (by decide)

private theorem step718_2330_2353 : Positive step718 2330 2353 := by decide +kernel

private theorem step718_2354_2418 : Positive step718 2354 2418 := by decide +kernel

private theorem step718_2419_2499 : Positive step718 2419 2499 := by decide +kernel

theorem step718_cover : ∃ ends, Cover step718 firstHeight ends := by
  exact ⟨[2353, 2418, 2499],
    ⟨(by decide), (by decide), step718_2330_2353,
      (by decide), (by decide), step718_2354_2418,
      (by decide), (by decide), step718_2419_2499, rfl⟩⟩

theorem step718_verified : Checked step718 :=
  ⟨step718_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step718_cover⟩

def step719 : Request :=
  ⟨⟨⟨1650, 2301, 512, 35655⟩, 138129879859200, 787417379725⟩, 73, 7, 2, 900003⟩

theorem step719_nodes : P1_7_1.nodeRows step719.bank.shape = step719.bank.nodeRows :=
  node_check step719.bank (by decide) (by decide) (by decide)

private theorem step719_2330_2332 : Positive step719 2330 2332 := by decide +kernel

private theorem step719_2333_2340 : Positive step719 2333 2340 := by decide +kernel

private theorem step719_2341_2361 : Positive step719 2341 2361 := by decide +kernel

private theorem step719_2362_2417 : Positive step719 2362 2417 := by decide +kernel

private theorem step719_2418_2499 : Positive step719 2418 2499 := by decide +kernel

theorem step719_cover : ∃ ends, Cover step719 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2417, 2499],
    ⟨(by decide), (by decide), step719_2330_2332,
      (by decide), (by decide), step719_2333_2340,
      (by decide), (by decide), step719_2341_2361,
      (by decide), (by decide), step719_2362_2417,
      (by decide), (by decide), step719_2418_2499, rfl⟩⟩

theorem step719_verified : Checked step719 :=
  ⟨step719_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step719_cover⟩

def step720 : Request :=
  ⟨⟨⟨2000, 2789, 604, 35655⟩, 240862397726720, 1663046410409⟩, 76, 7, 2, 900003⟩

theorem step720_nodes : P1_7_1.nodeRows step720.bank.shape = step720.bank.nodeRows :=
  node_check step720.bank (by decide) (by decide) (by decide)

private theorem step720_2330_2344 : Positive step720 2330 2344 := by decide +kernel

private theorem step720_2345_2384 : Positive step720 2345 2384 := by decide +kernel

private theorem step720_2385_2491 : Positive step720 2385 2491 := by decide +kernel

private theorem step720_2492_2499 : Positive step720 2492 2499 := by decide +kernel

theorem step720_cover : ∃ ends, Cover step720 firstHeight ends := by
  exact ⟨[2344, 2384, 2491, 2499],
    ⟨(by decide), (by decide), step720_2330_2344,
      (by decide), (by decide), step720_2345_2384,
      (by decide), (by decide), step720_2385_2491,
      (by decide), (by decide), step720_2492_2499, rfl⟩⟩

theorem step720_verified : Checked step720 :=
  ⟨step720_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step720_cover⟩

def step721 : Request :=
  ⟨⟨⟨2500, 3487, 775, 45124⟩, 479640131993600, 4144013596741⟩, 103, 7, 2, 900003⟩

theorem step721_nodes : P1_7_1.nodeRows step721.bank.shape = step721.bank.nodeRows :=
  node_check step721.bank (by decide) (by decide) (by decide)

private theorem step721_2330_2336 : Positive step721 2330 2336 := by decide +kernel

private theorem step721_2337_2354 : Positive step721 2337 2354 := by decide +kernel

private theorem step721_2355_2401 : Positive step721 2355 2401 := by decide +kernel

private theorem step721_2402_2499 : Positive step721 2402 2499 := by decide +kernel

theorem step721_cover : ∃ ends, Cover step721 firstHeight ends := by
  exact ⟨[2336, 2354, 2401, 2499],
    ⟨(by decide), (by decide), step721_2330_2336,
      (by decide), (by decide), step721_2337_2354,
      (by decide), (by decide), step721_2355_2401,
      (by decide), (by decide), step721_2402_2499, rfl⟩⟩

theorem step721_verified : Checked step721 :=
  ⟨step721_nodes, Research6966.HelperWindowCatalogue.moment3487_775,
    (by decide), (by decide), (by decide), step721_cover⟩

def step722 : Request :=
  ⟨⟨⟨210, 293, 65, 4282⟩, 289785774080, 211692234⟩, 0, 7, 4, 900003⟩

theorem step722_nodes : P1_7_1.nodeRows step722.bank.shape = step722.bank.nodeRows :=
  node_check step722.bank (by decide) (by decide) (by decide)

private theorem step722_2330_2346 : Positive step722 2330 2346 := by decide +kernel

private theorem step722_2347_2411 : Positive step722 2347 2411 := by decide +kernel

private theorem step722_2412_2499 : Positive step722 2412 2499 := by decide +kernel

theorem step722_cover : ∃ ends, Cover step722 firstHeight ends := by
  exact ⟨[2346, 2411, 2499],
    ⟨(by decide), (by decide), step722_2330_2346,
      (by decide), (by decide), step722_2347_2411,
      (by decide), (by decide), step722_2412_2499, rfl⟩⟩

theorem step722_verified : Checked step722 :=
  ⟨step722_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step722_cover⟩

def step723 : Request :=
  ⟨⟨⟨210, 293, 63, 5419⟩, 283090354176, 206678784⟩, 1, 7, 4, 900003⟩

theorem step723_nodes : P1_7_1.nodeRows step723.bank.shape = step723.bank.nodeRows :=
  node_check step723.bank (by decide) (by decide) (by decide)

private theorem step723_2330_2333 : Positive step723 2330 2333 := by decide +kernel

private theorem step723_2334_2348 : Positive step723 2334 2348 := by decide +kernel

private theorem step723_2349_2406 : Positive step723 2349 2406 := by decide +kernel

private theorem step723_2407_2499 : Positive step723 2407 2499 := by decide +kernel

theorem step723_cover : ∃ ends, Cover step723 firstHeight ends := by
  exact ⟨[2333, 2348, 2406, 2499],
    ⟨(by decide), (by decide), step723_2330_2333,
      (by decide), (by decide), step723_2334_2348,
      (by decide), (by decide), step723_2349_2406,
      (by decide), (by decide), step723_2407_2499, rfl⟩⟩

theorem step723_verified : Checked step723 :=
  ⟨step723_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step723_cover⟩

def step724 : Request :=
  ⟨⟨⟨250, 349, 76, 5419⟩, 480667500544, 418199213⟩, 2, 7, 4, 900003⟩

theorem step724_nodes : P1_7_1.nodeRows step724.bank.shape = step724.bank.nodeRows :=
  node_check step724.bank (by decide) (by decide) (by decide)

private theorem step724_2330_2362 : Positive step724 2330 2362 := by decide +kernel

private theorem step724_2363_2480 : Positive step724 2363 2480 := by decide +kernel

private theorem step724_2481_2499 : Positive step724 2481 2499 := by decide +kernel

theorem step724_cover : ∃ ends, Cover step724 firstHeight ends := by
  exact ⟨[2362, 2480, 2499],
    ⟨(by decide), (by decide), step724_2330_2362,
      (by decide), (by decide), step724_2363_2480,
      (by decide), (by decide), step724_2481_2499, rfl⟩⟩

theorem step724_verified : Checked step724 :=
  ⟨step724_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step724_cover⟩

def step725 : Request :=
  ⟨⟨⟨250, 348, 76, 6096⟩, 480667500544, 414368386⟩, 3, 7, 4, 900003⟩

theorem step725_nodes : P1_7_1.nodeRows step725.bank.shape = step725.bank.nodeRows :=
  node_check step725.bank (by decide) (by decide) (by decide)

private theorem step725_2330_2339 : Positive step725 2330 2339 := by decide +kernel

private theorem step725_2340_2375 : Positive step725 2340 2375 := by decide +kernel

private theorem step725_2376_2499 : Positive step725 2376 2499 := by decide +kernel

theorem step725_cover : ∃ ends, Cover step725 firstHeight ends := by
  exact ⟨[2339, 2375, 2499],
    ⟨(by decide), (by decide), step725_2330_2339,
      (by decide), (by decide), step725_2340_2375,
      (by decide), (by decide), step725_2376_2499, rfl⟩⟩

theorem step725_verified : Checked step725 :=
  ⟨step725_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step725_cover⟩

def step726 : Request :=
  ⟨⟨⟨294, 410, 89, 6096⟩, 777085255680, 791788817⟩, 4, 7, 4, 900003⟩

theorem step726_nodes : P1_7_1.nodeRows step726.bank.shape = step726.bank.nodeRows :=
  node_check step726.bank (by decide) (by decide) (by decide)

private theorem step726_2330_2346 : Positive step726 2330 2346 := by decide +kernel

private theorem step726_2347_2403 : Positive step726 2347 2403 := by decide +kernel

private theorem step726_2404_2499 : Positive step726 2404 2499 := by decide +kernel

theorem step726_cover : ∃ ends, Cover step726 firstHeight ends := by
  exact ⟨[2346, 2403, 2499],
    ⟨(by decide), (by decide), step726_2330_2346,
      (by decide), (by decide), step726_2347_2403,
      (by decide), (by decide), step726_2404_2499, rfl⟩⟩

theorem step726_verified : Checked step726 :=
  ⟨step726_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step726_cover⟩

def step727 : Request :=
  ⟨⟨⟨294, 410, 89, 6858⟩, 777085255680, 791788817⟩, 5, 7, 4, 900003⟩

theorem step727_nodes : P1_7_1.nodeRows step727.bank.shape = step727.bank.nodeRows :=
  node_check step727.bank (by decide) (by decide) (by decide)

private theorem step727_2330_2333 : Positive step727 2330 2333 := by decide +kernel

private theorem step727_2334_2347 : Positive step727 2334 2347 := by decide +kernel

private theorem step727_2348_2394 : Positive step727 2348 2394 := by decide +kernel

private theorem step727_2395_2499 : Positive step727 2395 2499 := by decide +kernel

theorem step727_cover : ∃ ends, Cover step727 firstHeight ends := by
  exact ⟨[2333, 2347, 2394, 2499],
    ⟨(by decide), (by decide), step727_2330_2333,
      (by decide), (by decide), step727_2334_2347,
      (by decide), (by decide), step727_2348_2394,
      (by decide), (by decide), step727_2395_2499, rfl⟩⟩

theorem step727_verified : Checked step727 :=
  ⟨step727_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step727_cover⟩

def step728 : Request :=
  ⟨⟨⟨350, 488, 104, 7715⟩, 1289487646720, 1561556019⟩, 7, 7, 4, 900003⟩

theorem step728_nodes : P1_7_1.nodeRows step728.bank.shape = step728.bank.nodeRows :=
  node_check step728.bank (by decide) (by decide) (by decide)

private theorem step728_2330_2330 : Positive step728 2330 2330 := by decide +kernel

private theorem step728_2331_2333 : Positive step728 2331 2333 := by decide +kernel

private theorem step728_2334_2342 : Positive step728 2334 2342 := by decide +kernel

private theorem step728_2343_2372 : Positive step728 2343 2372 := by decide +kernel

private theorem step728_2373_2469 : Positive step728 2373 2469 := by decide +kernel

private theorem step728_2470_2499 : Positive step728 2470 2499 := by decide +kernel

theorem step728_cover : ∃ ends, Cover step728 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2372, 2469, 2499],
    ⟨(by decide), (by decide), step728_2330_2330,
      (by decide), (by decide), step728_2331_2333,
      (by decide), (by decide), step728_2334_2342,
      (by decide), (by decide), step728_2343_2372,
      (by decide), (by decide), step728_2373_2469,
      (by decide), (by decide), step728_2470_2499, rfl⟩⟩

theorem step728_verified : Checked step728 :=
  ⟨step728_nodes, Research6966.HelperWindowCatalogue.moment488_104,
    (by decide), (by decide), (by decide), step728_cover⟩

def step729 : Request :=
  ⟨⟨⟨420, 586, 127, 8679⟩, 2252760678400, 3279920952⟩, 10, 7, 4, 900003⟩

theorem step729_nodes : P1_7_1.nodeRows step729.bank.shape = step729.bank.nodeRows :=
  node_check step729.bank (by decide) (by decide) (by decide)

private theorem step729_2330_2345 : Positive step729 2330 2345 := by decide +kernel

private theorem step729_2346_2394 : Positive step729 2346 2394 := by decide +kernel

private theorem step729_2395_2499 : Positive step729 2395 2499 := by decide +kernel

theorem step729_cover : ∃ ends, Cover step729 firstHeight ends := by
  exact ⟨[2345, 2394, 2499],
    ⟨(by decide), (by decide), step729_2330_2345,
      (by decide), (by decide), step729_2346_2394,
      (by decide), (by decide), step729_2395_2499, rfl⟩⟩

theorem step729_verified : Checked step729 :=
  ⟨step729_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step729_cover⟩

def step730 : Request :=
  ⟨⟨⟨520, 725, 161, 10983⟩, 4343013310464, 7809559934⟩, 16, 7, 4, 900003⟩

theorem step730_nodes : P1_7_1.nodeRows step730.bank.shape = step730.bank.nodeRows :=
  node_check step730.bank (by decide) (by decide) (by decide)

private theorem step730_2330_2333 : Positive step730 2330 2333 := by decide +kernel

private theorem step730_2334_2345 : Positive step730 2334 2345 := by decide +kernel

private theorem step730_2346_2380 : Positive step730 2346 2380 := by decide +kernel

private theorem step730_2381_2483 : Positive step730 2381 2483 := by decide +kernel

private theorem step730_2484_2499 : Positive step730 2484 2499 := by decide +kernel

theorem step730_cover : ∃ ends, Cover step730 firstHeight ends := by
  exact ⟨[2333, 2345, 2380, 2483, 2499],
    ⟨(by decide), (by decide), step730_2330_2333,
      (by decide), (by decide), step730_2334_2345,
      (by decide), (by decide), step730_2346_2380,
      (by decide), (by decide), step730_2381_2483,
      (by decide), (by decide), step730_2484_2499, rfl⟩⟩

theorem step730_verified : Checked step730 :=
  ⟨step730_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step730_cover⟩

def step731 : Request :=
  ⟨⟨⟨630, 878, 195, 12355⟩, 7709474160640, 16765904450⟩, 20, 7, 4, 900003⟩

theorem step731_nodes : P1_7_1.nodeRows step731.bank.shape = step731.bank.nodeRows :=
  node_check step731.bank (by decide) (by decide) (by decide)

private theorem step731_2330_2344 : Positive step731 2330 2344 := by decide +kernel

private theorem step731_2345_2387 : Positive step731 2345 2387 := by decide +kernel

private theorem step731_2388_2499 : Positive step731 2388 2499 := by decide +kernel

theorem step731_cover : ∃ ends, Cover step731 firstHeight ends := by
  exact ⟨[2344, 2387, 2499],
    ⟨(by decide), (by decide), step731_2330_2344,
      (by decide), (by decide), step731_2345_2387,
      (by decide), (by decide), step731_2388_2499, rfl⟩⟩

theorem step731_verified : Checked step731 :=
  ⟨step731_nodes, Research6966.HelperWindowCatalogue.moment878_195,
    (by decide), (by decide), (by decide), step731_cover⟩

def step732 : Request :=
  ⟨⟨⟨750, 1046, 232, 19788⟩, 12985818152960, 33687112323⟩, 31, 7, 4, 900003⟩

theorem step732_nodes : P1_7_1.nodeRows step732.bank.shape = step732.bank.nodeRows :=
  node_check step732.bank (by decide) (by decide) (by decide)

private theorem step732_2330_2340 : Positive step732 2330 2340 := by decide +kernel

private theorem step732_2341_2370 : Positive step732 2341 2370 := by decide +kernel

private theorem step732_2371_2455 : Positive step732 2371 2455 := by decide +kernel

private theorem step732_2456_2499 : Positive step732 2456 2499 := by decide +kernel

theorem step732_cover : ∃ ends, Cover step732 firstHeight ends := by
  exact ⟨[2340, 2370, 2455, 2499],
    ⟨(by decide), (by decide), step732_2330_2340,
      (by decide), (by decide), step732_2341_2370,
      (by decide), (by decide), step732_2371_2455,
      (by decide), (by decide), step732_2456_2499, rfl⟩⟩

theorem step732_verified : Checked step732 :=
  ⟨step732_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step732_cover⟩

def step733 : Request :=
  ⟨⟨⟨900, 1255, 272, 17590⟩, 22024701870080, 68477558806⟩, 32, 7, 4, 900003⟩

theorem step733_nodes : P1_7_1.nodeRows step733.bank.shape = step733.bank.nodeRows :=
  node_check step733.bank (by decide) (by decide) (by decide)

private theorem step733_2330_2340 : Positive step733 2330 2340 := by decide +kernel

private theorem step733_2341_2371 : Positive step733 2341 2371 := by decide +kernel

private theorem step733_2372_2457 : Positive step733 2372 2457 := by decide +kernel

private theorem step733_2458_2499 : Positive step733 2458 2499 := by decide +kernel

theorem step733_cover : ∃ ends, Cover step733 firstHeight ends := by
  exact ⟨[2340, 2371, 2457, 2499],
    ⟨(by decide), (by decide), step733_2330_2340,
      (by decide), (by decide), step733_2341_2371,
      (by decide), (by decide), step733_2372_2457,
      (by decide), (by decide), step733_2458_2499, rfl⟩⟩

theorem step733_verified : Checked step733 :=
  ⟨step733_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step733_cover⟩

def step734 : Request :=
  ⟨⟨⟨1100, 1534, 341, 22261⟩, 40955142733824, 155702293064⟩, 44, 7, 4, 900003⟩

theorem step734_nodes : P1_7_1.nodeRows step734.bank.shape = step734.bank.nodeRows :=
  node_check step734.bank (by decide) (by decide) (by decide)

private theorem step734_2330_2336 : Positive step734 2330 2336 := by decide +kernel

private theorem step734_2337_2355 : Positive step734 2337 2355 := by decide +kernel

private theorem step734_2356_2406 : Positive step734 2356 2406 := by decide +kernel

private theorem step734_2407_2499 : Positive step734 2407 2499 := by decide +kernel

theorem step734_cover : ∃ ends, Cover step734 firstHeight ends := by
  exact ⟨[2336, 2355, 2406, 2499],
    ⟨(by decide), (by decide), step734_2330_2336,
      (by decide), (by decide), step734_2337_2355,
      (by decide), (by decide), step734_2356_2406,
      (by decide), (by decide), step734_2407_2499, rfl⟩⟩

theorem step734_verified : Checked step734 :=
  ⟨step734_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step734_cover⟩

def step735 : Request :=
  ⟨⟨⟨1650, 2301, 512, 35655⟩, 138129879859200, 787417379725⟩, 73, 7, 4, 900003⟩

theorem step735_nodes : P1_7_1.nodeRows step735.bank.shape = step735.bank.nodeRows :=
  node_check step735.bank (by decide) (by decide) (by decide)

private theorem step735_2330_2344 : Positive step735 2330 2344 := by decide +kernel

private theorem step735_2345_2384 : Positive step735 2345 2384 := by decide +kernel

private theorem step735_2385_2491 : Positive step735 2385 2491 := by decide +kernel

private theorem step735_2492_2499 : Positive step735 2492 2499 := by decide +kernel

theorem step735_cover : ∃ ends, Cover step735 firstHeight ends := by
  exact ⟨[2344, 2384, 2491, 2499],
    ⟨(by decide), (by decide), step735_2330_2344,
      (by decide), (by decide), step735_2345_2384,
      (by decide), (by decide), step735_2385_2491,
      (by decide), (by decide), step735_2492_2499, rfl⟩⟩

theorem step735_verified : Checked step735 :=
  ⟨step735_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step735_cover⟩

def step736 : Request :=
  ⟨⟨⟨1650, 2301, 498, 40111⟩, 135254251667456, 770619519922⟩, 76, 7, 4, 900003⟩

theorem step736_nodes : P1_7_1.nodeRows step736.bank.shape = step736.bank.nodeRows :=
  node_check step736.bank (by decide) (by decide) (by decide)

private theorem step736_2330_2336 : Positive step736 2330 2336 := by decide +kernel

private theorem step736_2337_2355 : Positive step736 2337 2355 := by decide +kernel

private theorem step736_2356_2406 : Positive step736 2356 2406 := by decide +kernel

private theorem step736_2407_2499 : Positive step736 2407 2499 := by decide +kernel

theorem step736_cover : ∃ ends, Cover step736 firstHeight ends := by
  exact ⟨[2336, 2355, 2406, 2499],
    ⟨(by decide), (by decide), step736_2330_2336,
      (by decide), (by decide), step736_2337_2355,
      (by decide), (by decide), step736_2356_2406,
      (by decide), (by decide), step736_2407_2499, rfl⟩⟩

theorem step736_verified : Checked step736 :=
  ⟨step736_nodes, Research6966.HelperWindowCatalogue.moment2301_498,
    (by decide), (by decide), (by decide), step736_cover⟩

def step737 : Request :=
  ⟨⟨⟨2500, 3487, 775, 45124⟩, 479640131993600, 4144013596741⟩, 103, 7, 4, 900003⟩

theorem step737_nodes : P1_7_1.nodeRows step737.bank.shape = step737.bank.nodeRows :=
  node_check step737.bank (by decide) (by decide) (by decide)

private theorem step737_2330_2350 : Positive step737 2330 2350 := by decide +kernel

private theorem step737_2351_2406 : Positive step737 2351 2406 := by decide +kernel

private theorem step737_2407_2499 : Positive step737 2407 2499 := by decide +kernel

theorem step737_cover : ∃ ends, Cover step737 firstHeight ends := by
  exact ⟨[2350, 2406, 2499],
    ⟨(by decide), (by decide), step737_2330_2350,
      (by decide), (by decide), step737_2351_2406,
      (by decide), (by decide), step737_2407_2499, rfl⟩⟩

theorem step737_verified : Checked step737 :=
  ⟨step737_nodes, Research6966.HelperWindowCatalogue.moment3487_775,
    (by decide), (by decide), (by decide), step737_cover⟩

def step738 : Request :=
  ⟨⟨⟨250, 349, 76, 3807⟩, 480667500544, 418199213⟩, 0, 7, 9, 900003⟩

theorem step738_nodes : P1_7_1.nodeRows step738.bank.shape = step738.bank.nodeRows :=
  node_check step738.bank (by decide) (by decide) (by decide)

private theorem step738_2330_2370 : Positive step738 2330 2370 := by decide +kernel

private theorem step738_2371_2499 : Positive step738 2371 2499 := by decide +kernel

theorem step738_cover : ∃ ends, Cover step738 firstHeight ends := by
  exact ⟨[2370, 2499],
    ⟨(by decide), (by decide), step738_2330_2370,
      (by decide), (by decide), step738_2371_2499, rfl⟩⟩

theorem step738_verified : Checked step738 :=
  ⟨step738_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step738_cover⟩

def step739 : Request :=
  ⟨⟨⟨250, 349, 76, 4282⟩, 480667500544, 418199213⟩, 1, 7, 9, 900003⟩

theorem step739_nodes : P1_7_1.nodeRows step739.bank.shape = step739.bank.nodeRows :=
  node_check step739.bank (by decide) (by decide) (by decide)

private theorem step739_2330_2361 : Positive step739 2330 2361 := by decide +kernel

private theorem step739_2362_2475 : Positive step739 2362 2475 := by decide +kernel

private theorem step739_2476_2499 : Positive step739 2476 2499 := by decide +kernel

theorem step739_cover : ∃ ends, Cover step739 firstHeight ends := by
  exact ⟨[2361, 2475, 2499],
    ⟨(by decide), (by decide), step739_2330_2361,
      (by decide), (by decide), step739_2362_2475,
      (by decide), (by decide), step739_2476_2499, rfl⟩⟩

theorem step739_verified : Checked step739 :=
  ⟨step739_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step739_cover⟩

def step740 : Request :=
  ⟨⟨⟨294, 410, 91, 4282⟩, 790165454848, 805457011⟩, 2, 7, 9, 900003⟩

theorem step740_nodes : P1_7_1.nodeRows step740.bank.shape = step740.bank.nodeRows :=
  node_check step740.bank (by decide) (by decide) (by decide)

private theorem step740_2330_2340 : Positive step740 2330 2340 := by decide +kernel

private theorem step740_2341_2376 : Positive step740 2341 2376 := by decide +kernel

private theorem step740_2377_2497 : Positive step740 2377 2497 := by decide +kernel

private theorem step740_2498_2499 : Positive step740 2498 2499 := by decide +kernel

theorem step740_cover : ∃ ends, Cover step740 firstHeight ends := by
  exact ⟨[2340, 2376, 2497, 2499],
    ⟨(by decide), (by decide), step740_2330_2340,
      (by decide), (by decide), step740_2341_2376,
      (by decide), (by decide), step740_2377_2497,
      (by decide), (by decide), step740_2498_2499, rfl⟩⟩

theorem step740_verified : Checked step740 :=
  ⟨step740_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step740_cover⟩

def step741 : Request :=
  ⟨⟨⟨294, 410, 91, 4817⟩, 790165454848, 805457011⟩, 3, 7, 9, 900003⟩

theorem step741_nodes : P1_7_1.nodeRows step741.bank.shape = step741.bank.nodeRows :=
  node_check step741.bank (by decide) (by decide) (by decide)

private theorem step741_2330_2345 : Positive step741 2330 2345 := by decide +kernel

private theorem step741_2346_2399 : Positive step741 2346 2399 := by decide +kernel

private theorem step741_2400_2499 : Positive step741 2400 2499 := by decide +kernel

theorem step741_cover : ∃ ends, Cover step741 firstHeight ends := by
  exact ⟨[2345, 2399, 2499],
    ⟨(by decide), (by decide), step741_2330_2345,
      (by decide), (by decide), step741_2346_2399,
      (by decide), (by decide), step741_2400_2499, rfl⟩⟩

theorem step741_verified : Checked step741 :=
  ⟨step741_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step741_cover⟩

def step742 : Request :=
  ⟨⟨⟨294, 410, 91, 5419⟩, 790165454848, 805457011⟩, 4, 7, 9, 900003⟩

theorem step742_nodes : P1_7_1.nodeRows step742.bank.shape = step742.bank.nodeRows :=
  node_check step742.bank (by decide) (by decide) (by decide)

private theorem step742_2330_2343 : Positive step742 2330 2343 := by decide +kernel

private theorem step742_2344_2390 : Positive step742 2344 2390 := by decide +kernel

private theorem step742_2391_2499 : Positive step742 2391 2499 := by decide +kernel

theorem step742_cover : ∃ ends, Cover step742 firstHeight ends := by
  exact ⟨[2343, 2390, 2499],
    ⟨(by decide), (by decide), step742_2330_2343,
      (by decide), (by decide), step742_2344_2390,
      (by decide), (by decide), step742_2391_2499, rfl⟩⟩

theorem step742_verified : Checked step742 :=
  ⟨step742_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step742_cover⟩

def step743 : Request :=
  ⟨⟨⟨350, 488, 108, 5419⟩, 1326705278976, 1607754763⟩, 5, 7, 9, 900003⟩

theorem step743_nodes : P1_7_1.nodeRows step743.bank.shape = step743.bank.nodeRows :=
  node_check step743.bank (by decide) (by decide) (by decide)

private theorem step743_2330_2341 : Positive step743 2330 2341 := by decide +kernel

private theorem step743_2342_2379 : Positive step743 2342 2379 := by decide +kernel

private theorem step743_2380_2499 : Positive step743 2380 2499 := by decide +kernel

theorem step743_cover : ∃ ends, Cover step743 firstHeight ends := by
  exact ⟨[2341, 2379, 2499],
    ⟨(by decide), (by decide), step743_2330_2341,
      (by decide), (by decide), step743_2342_2379,
      (by decide), (by decide), step743_2380_2499, rfl⟩⟩

theorem step743_verified : Checked step743 :=
  ⟨step743_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step743_cover⟩

def step744 : Request :=
  ⟨⟨⟨420, 586, 130, 6096⟩, 2292767784960, 3339653140⟩, 7, 7, 9, 900003⟩

theorem step744_nodes : P1_7_1.nodeRows step744.bank.shape = step744.bank.nodeRows :=
  node_check step744.bank (by decide) (by decide) (by decide)

private theorem step744_2330_2348 : Positive step744 2330 2348 := by decide +kernel

private theorem step744_2349_2406 : Positive step744 2349 2406 := by decide +kernel

private theorem step744_2407_2499 : Positive step744 2407 2499 := by decide +kernel

theorem step744_cover : ∃ ends, Cover step744 firstHeight ends := by
  exact ⟨[2348, 2406, 2499],
    ⟨(by decide), (by decide), step744_2330_2348,
      (by decide), (by decide), step744_2349_2406,
      (by decide), (by decide), step744_2407_2499, rfl⟩⟩

theorem step744_verified : Checked step744 :=
  ⟨step744_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step744_cover⟩

def step745 : Request :=
  ⟨⟨⟨420, 586, 130, 7715⟩, 2292767784960, 3339653140⟩, 10, 7, 9, 900003⟩

theorem step745_nodes : P1_7_1.nodeRows step745.bank.shape = step745.bank.nodeRows :=
  node_check step745.bank (by decide) (by decide) (by decide)

private theorem step745_2330_2345 : Positive step745 2330 2345 := by decide +kernel

private theorem step745_2346_2394 : Positive step745 2346 2394 := by decide +kernel

private theorem step745_2395_2499 : Positive step745 2395 2499 := by decide +kernel

theorem step745_cover : ∃ ends, Cover step745 firstHeight ends := by
  exact ⟨[2345, 2394, 2499],
    ⟨(by decide), (by decide), step745_2330_2345,
      (by decide), (by decide), step745_2346_2394,
      (by decide), (by decide), step745_2395_2499, rfl⟩⟩

theorem step745_verified : Checked step745 :=
  ⟨step745_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step745_cover⟩

def step746 : Request :=
  ⟨⟨⟨630, 879, 190, 9763⟩, 7559493713920, 16491913877⟩, 16, 7, 9, 900003⟩

theorem step746_nodes : P1_7_1.nodeRows step746.bank.shape = step746.bank.nodeRows :=
  node_check step746.bank (by decide) (by decide) (by decide)

private theorem step746_2330_2352 : Positive step746 2330 2352 := by decide +kernel

private theorem step746_2353_2419 : Positive step746 2353 2419 := by decide +kernel

private theorem step746_2420_2499 : Positive step746 2420 2499 := by decide +kernel

theorem step746_cover : ∃ ends, Cover step746 firstHeight ends := by
  exact ⟨[2352, 2419, 2499],
    ⟨(by decide), (by decide), step746_2330_2352,
      (by decide), (by decide), step746_2353_2419,
      (by decide), (by decide), step746_2420_2499, rfl⟩⟩

theorem step746_verified : Checked step746 :=
  ⟨step746_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step746_cover⟩

def step747 : Request :=
  ⟨⟨⟨750, 1046, 226, 10983⟩, 12730741817344, 33009058589⟩, 20, 7, 9, 900003⟩

theorem step747_nodes : P1_7_1.nodeRows step747.bank.shape = step747.bank.nodeRows :=
  node_check step747.bank (by decide) (by decide) (by decide)

private theorem step747_2330_2343 : Positive step747 2330 2343 := by decide +kernel

private theorem step747_2344_2383 : Positive step747 2344 2383 := by decide +kernel

private theorem step747_2384_2497 : Positive step747 2384 2497 := by decide +kernel

private theorem step747_2498_2499 : Positive step747 2498 2499 := by decide +kernel

theorem step747_cover : ∃ ends, Cover step747 firstHeight ends := by
  exact ⟨[2343, 2383, 2497, 2499],
    ⟨(by decide), (by decide), step747_2330_2343,
      (by decide), (by decide), step747_2344_2383,
      (by decide), (by decide), step747_2384_2497,
      (by decide), (by decide), step747_2498_2499, rfl⟩⟩

theorem step747_verified : Checked step747 :=
  ⟨step747_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step747_cover⟩

def step748 : Request :=
  ⟨⟨⟨900, 1255, 272, 15636⟩, 22024701870080, 68477558806⟩, 31, 7, 9, 900003⟩

theorem step748_nodes : P1_7_1.nodeRows step748.bank.shape = step748.bank.nodeRows :=
  node_check step748.bank (by decide) (by decide) (by decide)

private theorem step748_2330_2342 : Positive step748 2330 2342 := by decide +kernel

private theorem step748_2343_2378 : Positive step748 2343 2378 := by decide +kernel

private theorem step748_2379_2478 : Positive step748 2379 2478 := by decide +kernel

private theorem step748_2479_2499 : Positive step748 2479 2499 := by decide +kernel

theorem step748_cover : ∃ ends, Cover step748 firstHeight ends := by
  exact ⟨[2342, 2378, 2478, 2499],
    ⟨(by decide), (by decide), step748_2330_2342,
      (by decide), (by decide), step748_2343_2378,
      (by decide), (by decide), step748_2379_2478,
      (by decide), (by decide), step748_2479_2499, rfl⟩⟩

theorem step748_verified : Checked step748 :=
  ⟨step748_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step748_cover⟩

def step749 : Request :=
  ⟨⟨⟨900, 1255, 279, 15636⟩, 22452680785920, 69841856233⟩, 32, 7, 9, 900003⟩

theorem step749_nodes : P1_7_1.nodeRows step749.bank.shape = step749.bank.nodeRows :=
  node_check step749.bank (by decide) (by decide) (by decide)

private theorem step749_2330_2343 : Positive step749 2330 2343 := by decide +kernel

private theorem step749_2344_2382 : Positive step749 2344 2382 := by decide +kernel

private theorem step749_2383_2490 : Positive step749 2383 2490 := by decide +kernel

private theorem step749_2491_2499 : Positive step749 2491 2499 := by decide +kernel

theorem step749_cover : ∃ ends, Cover step749 firstHeight ends := by
  exact ⟨[2343, 2382, 2490, 2499],
    ⟨(by decide), (by decide), step749_2330_2343,
      (by decide), (by decide), step749_2344_2382,
      (by decide), (by decide), step749_2383_2490,
      (by decide), (by decide), step749_2491_2499, rfl⟩⟩

theorem step749_verified : Checked step749 :=
  ⟨step749_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step749_cover⟩

def step750 : Request :=
  ⟨⟨⟨1350, 1883, 408, 19788⟩, 74202776600576, 346190054868⟩, 44, 7, 9, 900003⟩

theorem step750_nodes : P1_7_1.nodeRows step750.bank.shape = step750.bank.nodeRows :=
  node_check step750.bank (by decide) (by decide) (by decide)

private theorem step750_2330_2349 : Positive step750 2330 2349 := by decide +kernel

private theorem step750_2350_2403 : Positive step750 2350 2403 := by decide +kernel

private theorem step750_2404_2499 : Positive step750 2404 2499 := by decide +kernel

theorem step750_cover : ∃ ends, Cover step750 firstHeight ends := by
  exact ⟨[2349, 2403, 2499],
    ⟨(by decide), (by decide), step750_2330_2349,
      (by decide), (by decide), step750_2350_2403,
      (by decide), (by decide), step750_2404_2499, rfl⟩⟩

theorem step750_verified : Checked step750 :=
  ⟨step750_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step750_cover⟩

def step751 : Request :=
  ⟨⟨⟨1650, 2301, 512, 31694⟩, 138129879859200, 787417379725⟩, 73, 7, 9, 900003⟩

theorem step751_nodes : P1_7_1.nodeRows step751.bank.shape = step751.bank.nodeRows :=
  node_check step751.bank (by decide) (by decide) (by decide)

private theorem step751_2330_2330 : Positive step751 2330 2330 := by decide +kernel

private theorem step751_2331_2333 : Positive step751 2331 2333 := by decide +kernel

private theorem step751_2334_2341 : Positive step751 2334 2341 := by decide +kernel

private theorem step751_2342_2362 : Positive step751 2342 2362 := by decide +kernel

private theorem step751_2363_2418 : Positive step751 2363 2418 := by decide +kernel

private theorem step751_2419_2499 : Positive step751 2419 2499 := by decide +kernel

theorem step751_cover : ∃ ends, Cover step751 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2418, 2499],
    ⟨(by decide), (by decide), step751_2330_2330,
      (by decide), (by decide), step751_2331_2333,
      (by decide), (by decide), step751_2334_2341,
      (by decide), (by decide), step751_2342_2362,
      (by decide), (by decide), step751_2363_2418,
      (by decide), (by decide), step751_2419_2499, rfl⟩⟩

theorem step751_verified : Checked step751 :=
  ⟨step751_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step751_cover⟩

def step752 : Request :=
  ⟨⟨⟨2000, 2789, 604, 31694⟩, 240862397726720, 1663046410409⟩, 76, 7, 9, 900003⟩

theorem step752_nodes : P1_7_1.nodeRows step752.bank.shape = step752.bank.nodeRows :=
  node_check step752.bank (by decide) (by decide) (by decide)

private theorem step752_2330_2341 : Positive step752 2330 2341 := by decide +kernel

private theorem step752_2342_2373 : Positive step752 2342 2373 := by decide +kernel

private theorem step752_2374_2458 : Positive step752 2374 2458 := by decide +kernel

private theorem step752_2459_2499 : Positive step752 2459 2499 := by decide +kernel

theorem step752_cover : ∃ ends, Cover step752 firstHeight ends := by
  exact ⟨[2341, 2373, 2458, 2499],
    ⟨(by decide), (by decide), step752_2330_2341,
      (by decide), (by decide), step752_2342_2373,
      (by decide), (by decide), step752_2374_2458,
      (by decide), (by decide), step752_2459_2499, rfl⟩⟩

theorem step752_verified : Checked step752 :=
  ⟨step752_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step752_cover⟩

def step753 : Request :=
  ⟨⟨⟨2500, 3487, 775, 40111⟩, 479640131993600, 4144013596741⟩, 103, 7, 9, 900003⟩

theorem step753_nodes : P1_7_1.nodeRows step753.bank.shape = step753.bank.nodeRows :=
  node_check step753.bank (by decide) (by decide) (by decide)

private theorem step753_2330_2333 : Positive step753 2330 2333 := by decide +kernel

private theorem step753_2334_2344 : Positive step753 2334 2344 := by decide +kernel

private theorem step753_2345_2373 : Positive step753 2345 2373 := by decide +kernel

private theorem step753_2374_2448 : Positive step753 2374 2448 := by decide +kernel

private theorem step753_2449_2499 : Positive step753 2449 2499 := by decide +kernel

theorem step753_cover : ∃ ends, Cover step753 firstHeight ends := by
  exact ⟨[2333, 2344, 2373, 2448, 2499],
    ⟨(by decide), (by decide), step753_2330_2333,
      (by decide), (by decide), step753_2334_2344,
      (by decide), (by decide), step753_2345_2373,
      (by decide), (by decide), step753_2374_2448,
      (by decide), (by decide), step753_2449_2499, rfl⟩⟩

theorem step753_verified : Checked step753 :=
  ⟨step753_nodes, Research6966.HelperWindowCatalogue.moment3487_775,
    (by decide), (by decide), (by decide), step753_cover⟩

def step754 : Request :=
  ⟨⟨⟨210, 293, 62, 3807⟩, 279710269440, 204151930⟩, 0, 7, 16, 900003⟩

theorem step754_nodes : P1_7_1.nodeRows step754.bank.shape = step754.bank.nodeRows :=
  node_check step754.bank (by decide) (by decide) (by decide)

private theorem step754_2330_2334 : Positive step754 2330 2334 := by decide +kernel

private theorem step754_2335_2353 : Positive step754 2335 2353 := by decide +kernel

private theorem step754_2354_2427 : Positive step754 2354 2427 := by decide +kernel

private theorem step754_2428_2499 : Positive step754 2428 2499 := by decide +kernel

theorem step754_cover : ∃ ends, Cover step754 firstHeight ends := by
  exact ⟨[2334, 2353, 2427, 2499],
    ⟨(by decide), (by decide), step754_2330_2334,
      (by decide), (by decide), step754_2335_2353,
      (by decide), (by decide), step754_2354_2427,
      (by decide), (by decide), step754_2428_2499, rfl⟩⟩

theorem step754_verified : Checked step754 :=
  ⟨step754_nodes, Research6966.HelperWindowCatalogue.moment293_62,
    (by decide), (by decide), (by decide), step754_cover⟩

def step755 : Request :=
  ⟨⟨⟨210, 293, 65, 4282⟩, 289785774080, 211692234⟩, 1, 7, 16, 900003⟩

theorem step755_nodes : P1_7_1.nodeRows step755.bank.shape = step755.bank.nodeRows :=
  node_check step755.bank (by decide) (by decide) (by decide)

private theorem step755_2330_2346 : Positive step755 2330 2346 := by decide +kernel

private theorem step755_2347_2411 : Positive step755 2347 2411 := by decide +kernel

private theorem step755_2412_2499 : Positive step755 2412 2499 := by decide +kernel

theorem step755_cover : ∃ ends, Cover step755 firstHeight ends := by
  exact ⟨[2346, 2411, 2499],
    ⟨(by decide), (by decide), step755_2330_2346,
      (by decide), (by decide), step755_2347_2411,
      (by decide), (by decide), step755_2412_2499, rfl⟩⟩

theorem step755_verified : Checked step755 :=
  ⟨step755_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step755_cover⟩

def step756 : Request :=
  ⟨⟨⟨250, 349, 76, 4282⟩, 480667500544, 418199213⟩, 2, 7, 16, 900003⟩

theorem step756_nodes : P1_7_1.nodeRows step756.bank.shape = step756.bank.nodeRows :=
  node_check step756.bank (by decide) (by decide) (by decide)

private theorem step756_2330_2344 : Positive step756 2330 2344 := by decide +kernel

private theorem step756_2345_2397 : Positive step756 2345 2397 := by decide +kernel

private theorem step756_2398_2499 : Positive step756 2398 2499 := by decide +kernel

theorem step756_cover : ∃ ends, Cover step756 firstHeight ends := by
  exact ⟨[2344, 2397, 2499],
    ⟨(by decide), (by decide), step756_2330_2344,
      (by decide), (by decide), step756_2345_2397,
      (by decide), (by decide), step756_2398_2499, rfl⟩⟩

theorem step756_verified : Checked step756 :=
  ⟨step756_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step756_cover⟩

def step757 : Request :=
  ⟨⟨⟨250, 348, 78, 4817⟩, 490108092416, 422716393⟩, 3, 7, 16, 900003⟩

theorem step757_nodes : P1_7_1.nodeRows step757.bank.shape = step757.bank.nodeRows :=
  node_check step757.bank (by decide) (by decide) (by decide)

private theorem step757_2330_2337 : Positive step757 2330 2337 := by decide +kernel

private theorem step757_2338_2366 : Positive step757 2338 2366 := by decide +kernel

private theorem step757_2367_2469 : Positive step757 2367 2469 := by decide +kernel

private theorem step757_2470_2499 : Positive step757 2470 2499 := by decide +kernel

theorem step757_cover : ∃ ends, Cover step757 firstHeight ends := by
  exact ⟨[2337, 2366, 2469, 2499],
    ⟨(by decide), (by decide), step757_2330_2337,
      (by decide), (by decide), step757_2338_2366,
      (by decide), (by decide), step757_2367_2469,
      (by decide), (by decide), step757_2470_2499, rfl⟩⟩

theorem step757_verified : Checked step757 :=
  ⟨step757_nodes, Research6966.HelperWindowCatalogue.moment348_78,
    (by decide), (by decide), (by decide), step757_cover⟩

def step758 : Request :=
  ⟨⟨⟨294, 410, 91, 4817⟩, 790165454848, 805457011⟩, 4, 7, 16, 900003⟩

theorem step758_nodes : P1_7_1.nodeRows step758.bank.shape = step758.bank.nodeRows :=
  node_check step758.bank (by decide) (by decide) (by decide)

private theorem step758_2330_2345 : Positive step758 2330 2345 := by decide +kernel

private theorem step758_2346_2399 : Positive step758 2346 2399 := by decide +kernel

private theorem step758_2400_2499 : Positive step758 2400 2499 := by decide +kernel

theorem step758_cover : ∃ ends, Cover step758 firstHeight ends := by
  exact ⟨[2345, 2399, 2499],
    ⟨(by decide), (by decide), step758_2330_2345,
      (by decide), (by decide), step758_2346_2399,
      (by decide), (by decide), step758_2400_2499, rfl⟩⟩

theorem step758_verified : Checked step758 :=
  ⟨step758_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step758_cover⟩

def step759 : Request :=
  ⟨⟨⟨294, 410, 91, 5419⟩, 790165454848, 805457011⟩, 5, 7, 16, 900003⟩

theorem step759_nodes : P1_7_1.nodeRows step759.bank.shape = step759.bank.nodeRows :=
  node_check step759.bank (by decide) (by decide) (by decide)

private theorem step759_2330_2335 : Positive step759 2330 2335 := by decide +kernel

private theorem step759_2336_2355 : Positive step759 2336 2355 := by decide +kernel

private theorem step759_2356_2422 : Positive step759 2356 2422 := by decide +kernel

private theorem step759_2423_2499 : Positive step759 2423 2499 := by decide +kernel

theorem step759_cover : ∃ ends, Cover step759 firstHeight ends := by
  exact ⟨[2335, 2355, 2422, 2499],
    ⟨(by decide), (by decide), step759_2330_2335,
      (by decide), (by decide), step759_2336_2355,
      (by decide), (by decide), step759_2356_2422,
      (by decide), (by decide), step759_2423_2499, rfl⟩⟩

theorem step759_verified : Checked step759 :=
  ⟨step759_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step759_cover⟩

def step760 : Request :=
  ⟨⟨⟨350, 488, 106, 6096⟩, 1308168290304, 1584729438⟩, 7, 7, 16, 900003⟩

theorem step760_nodes : P1_7_1.nodeRows step760.bank.shape = step760.bank.nodeRows :=
  node_check step760.bank (by decide) (by decide) (by decide)

private theorem step760_2330_2343 : Positive step760 2330 2343 := by decide +kernel

private theorem step760_2344_2388 : Positive step760 2344 2388 := by decide +kernel

private theorem step760_2389_2499 : Positive step760 2389 2499 := by decide +kernel

theorem step760_cover : ∃ ends, Cover step760 firstHeight ends := by
  exact ⟨[2343, 2388, 2499],
    ⟨(by decide), (by decide), step760_2330_2343,
      (by decide), (by decide), step760_2344_2388,
      (by decide), (by decide), step760_2389_2499, rfl⟩⟩

theorem step760_verified : Checked step760 :=
  ⟨step760_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step760_cover⟩

def step761 : Request :=
  ⟨⟨⟨420, 586, 130, 6858⟩, 2292767784960, 3339653140⟩, 10, 7, 16, 900003⟩

theorem step761_nodes : P1_7_1.nodeRows step761.bank.shape = step761.bank.nodeRows :=
  node_check step761.bank (by decide) (by decide) (by decide)

private theorem step761_2330_2347 : Positive step761 2330 2347 := by decide +kernel

private theorem step761_2348_2402 : Positive step761 2348 2402 := by decide +kernel

private theorem step761_2403_2499 : Positive step761 2403 2499 := by decide +kernel

theorem step761_cover : ∃ ends, Cover step761 firstHeight ends := by
  exact ⟨[2347, 2402, 2499],
    ⟨(by decide), (by decide), step761_2330_2347,
      (by decide), (by decide), step761_2348_2402,
      (by decide), (by decide), step761_2403_2499, rfl⟩⟩

theorem step761_verified : Checked step761 :=
  ⟨step761_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step761_cover⟩

def step762 : Request :=
  ⟨⟨⟨520, 725, 157, 9763⟩, 4261264752640, 7658911630⟩, 16, 7, 16, 900003⟩

theorem step762_nodes : P1_7_1.nodeRows step762.bank.shape = step762.bank.nodeRows :=
  node_check step762.bank (by decide) (by decide) (by decide)

private theorem step762_2330_2348 : Positive step762 2330 2348 := by decide +kernel

private theorem step762_2349_2405 : Positive step762 2349 2405 := by decide +kernel

private theorem step762_2406_2499 : Positive step762 2406 2499 := by decide +kernel

theorem step762_cover : ∃ ends, Cover step762 firstHeight ends := by
  exact ⟨[2348, 2405, 2499],
    ⟨(by decide), (by decide), step762_2330_2348,
      (by decide), (by decide), step762_2349_2405,
      (by decide), (by decide), step762_2406_2499, rfl⟩⟩

theorem step762_verified : Checked step762 :=
  ⟨step762_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step762_cover⟩

def step763 : Request :=
  ⟨⟨⟨630, 878, 190, 10983⟩, 7559493713920, 16431687757⟩, 20, 7, 16, 900003⟩

theorem step763_nodes : P1_7_1.nodeRows step763.bank.shape = step763.bank.nodeRows :=
  node_check step763.bank (by decide) (by decide) (by decide)

private theorem step763_2330_2359 : Positive step763 2330 2359 := by decide +kernel

private theorem step763_2360_2447 : Positive step763 2360 2447 := by decide +kernel

private theorem step763_2448_2499 : Positive step763 2448 2499 := by decide +kernel

theorem step763_cover : ∃ ends, Cover step763 firstHeight ends := by
  exact ⟨[2359, 2447, 2499],
    ⟨(by decide), (by decide), step763_2330_2359,
      (by decide), (by decide), step763_2360_2447,
      (by decide), (by decide), step763_2448_2499, rfl⟩⟩

theorem step763_verified : Checked step763 :=
  ⟨step763_nodes, Research6966.HelperWindowCatalogue.moment878_190,
    (by decide), (by decide), (by decide), step763_cover⟩

def step764 : Request :=
  ⟨⟨⟨900, 1255, 272, 13899⟩, 22024701870080, 68477558806⟩, 31, 7, 16, 900003⟩

theorem step764_nodes : P1_7_1.nodeRows step764.bank.shape = step764.bank.nodeRows :=
  node_check step764.bank (by decide) (by decide) (by decide)

private theorem step764_2330_2342 : Positive step764 2330 2342 := by decide +kernel

private theorem step764_2343_2379 : Positive step764 2343 2379 := by decide +kernel

private theorem step764_2380_2482 : Positive step764 2380 2482 := by decide +kernel

private theorem step764_2483_2499 : Positive step764 2483 2499 := by decide +kernel

theorem step764_cover : ∃ ends, Cover step764 firstHeight ends := by
  exact ⟨[2342, 2379, 2482, 2499],
    ⟨(by decide), (by decide), step764_2330_2342,
      (by decide), (by decide), step764_2343_2379,
      (by decide), (by decide), step764_2380_2482,
      (by decide), (by decide), step764_2483_2499, rfl⟩⟩

theorem step764_verified : Checked step764 :=
  ⟨step764_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step764_cover⟩

def step765 : Request :=
  ⟨⟨⟨900, 1255, 279, 13899⟩, 22452680785920, 69841856233⟩, 32, 7, 16, 900003⟩

theorem step765_nodes : P1_7_1.nodeRows step765.bank.shape = step765.bank.nodeRows :=
  node_check step765.bank (by decide) (by decide) (by decide)

private theorem step765_2330_2345 : Positive step765 2330 2345 := by decide +kernel

private theorem step765_2346_2389 : Positive step765 2346 2389 := by decide +kernel

private theorem step765_2390_2499 : Positive step765 2390 2499 := by decide +kernel

theorem step765_cover : ∃ ends, Cover step765 firstHeight ends := by
  exact ⟨[2345, 2389, 2499],
    ⟨(by decide), (by decide), step765_2330_2345,
      (by decide), (by decide), step765_2346_2389,
      (by decide), (by decide), step765_2390_2499, rfl⟩⟩

theorem step765_verified : Checked step765 :=
  ⟨step765_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step765_cover⟩

def step766 : Request :=
  ⟨⟨⟨1100, 1534, 332, 19788⟩, 40133103452160, 152499774767⟩, 44, 7, 16, 900003⟩

theorem step766_nodes : P1_7_1.nodeRows step766.bank.shape = step766.bank.nodeRows :=
  node_check step766.bank (by decide) (by decide) (by decide)

private theorem step766_2330_2348 : Positive step766 2330 2348 := by decide +kernel

private theorem step766_2349_2401 : Positive step766 2349 2401 := by decide +kernel

private theorem step766_2402_2499 : Positive step766 2402 2499 := by decide +kernel

theorem step766_cover : ∃ ends, Cover step766 firstHeight ends := by
  exact ⟨[2348, 2401, 2499],
    ⟨(by decide), (by decide), step766_2330_2348,
      (by decide), (by decide), step766_2349_2401,
      (by decide), (by decide), step766_2402_2499, rfl⟩⟩

theorem step766_verified : Checked step766 :=
  ⟨step766_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step766_cover⟩

end Research6966.HelperRescueCatalogue
