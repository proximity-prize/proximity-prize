import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments7
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step465 : Request :=
  ⟨⟨⟨3500, 4883, 1057, 72277⟩, 1289556817346560, 15600507702257⟩, 103, 5, 9, 642859⟩

theorem step465_nodes : P1_7_1.nodeRows step465.bank.shape = step465.bank.nodeRows :=
  node_check step465.bank (by decide) (by decide) (by decide)

private theorem step465_2330_2334 : Positive step465 2330 2334 := by decide +kernel

private theorem step465_2335_2347 : Positive step465 2335 2347 := by decide +kernel

private theorem step465_2348_2381 : Positive step465 2348 2381 := by decide +kernel

private theorem step465_2382_2470 : Positive step465 2382 2470 := by decide +kernel

private theorem step465_2471_2499 : Positive step465 2471 2499 := by decide +kernel

theorem step465_cover : ∃ ends, Cover step465 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2470, 2499],
    ⟨(by decide), (by decide), step465_2330_2334,
      (by decide), (by decide), step465_2335_2347,
      (by decide), (by decide), step465_2348_2381,
      (by decide), (by decide), step465_2382_2470,
      (by decide), (by decide), step465_2471_2499, rfl⟩⟩

theorem step465_verified : Checked step465 :=
  ⟨step465_nodes, Research6966.HelperWindowCatalogue.moment4883_1057,
    (by decide), (by decide), (by decide), step465_cover⟩

def step466 : Request :=
  ⟨⟨⟨294, 410, 89, 5419⟩, 777085255680, 791788817⟩, 0, 5, 16, 642859⟩

theorem step466_nodes : P1_7_1.nodeRows step466.bank.shape = step466.bank.nodeRows :=
  node_check step466.bank (by decide) (by decide) (by decide)

private theorem step466_2330_2333 : Positive step466 2330 2333 := by decide +kernel

private theorem step466_2334_2346 : Positive step466 2334 2346 := by decide +kernel

private theorem step466_2347_2390 : Positive step466 2347 2390 := by decide +kernel

private theorem step466_2391_2499 : Positive step466 2391 2499 := by decide +kernel

theorem step466_cover : ∃ ends, Cover step466 firstHeight ends := by
  exact ⟨[2333, 2346, 2390, 2499],
    ⟨(by decide), (by decide), step466_2330_2333,
      (by decide), (by decide), step466_2334_2346,
      (by decide), (by decide), step466_2347_2390,
      (by decide), (by decide), step466_2391_2499, rfl⟩⟩

theorem step466_verified : Checked step466 :=
  ⟨step466_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step466_cover⟩

def step467 : Request :=
  ⟨⟨⟨420, 586, 130, 5419⟩, 2292767784960, 3339653140⟩, 1, 5, 16, 642859⟩

theorem step467_nodes : P1_7_1.nodeRows step467.bank.shape = step467.bank.nodeRows :=
  node_check step467.bank (by decide) (by decide) (by decide)

private theorem step467_2330_2339 : Positive step467 2330 2339 := by decide +kernel

private theorem step467_2340_2369 : Positive step467 2340 2369 := by decide +kernel

private theorem step467_2370_2461 : Positive step467 2370 2461 := by decide +kernel

private theorem step467_2462_2499 : Positive step467 2462 2499 := by decide +kernel

theorem step467_cover : ∃ ends, Cover step467 firstHeight ends := by
  exact ⟨[2339, 2369, 2461, 2499],
    ⟨(by decide), (by decide), step467_2330_2339,
      (by decide), (by decide), step467_2340_2369,
      (by decide), (by decide), step467_2370_2461,
      (by decide), (by decide), step467_2462_2499, rfl⟩⟩

theorem step467_verified : Checked step467 :=
  ⟨step467_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step467_cover⟩

def step468 : Request :=
  ⟨⟨⟨420, 586, 127, 6096⟩, 2252760678400, 3279920952⟩, 2, 5, 16, 642859⟩

theorem step468_nodes : P1_7_1.nodeRows step468.bank.shape = step468.bank.nodeRows :=
  node_check step468.bank (by decide) (by decide) (by decide)

private theorem step468_2330_2338 : Positive step468 2330 2338 := by decide +kernel

private theorem step468_2339_2366 : Positive step468 2339 2366 := by decide +kernel

private theorem step468_2367_2452 : Positive step468 2367 2452 := by decide +kernel

private theorem step468_2453_2499 : Positive step468 2453 2499 := by decide +kernel

theorem step468_cover : ∃ ends, Cover step468 firstHeight ends := by
  exact ⟨[2338, 2366, 2452, 2499],
    ⟨(by decide), (by decide), step468_2330_2338,
      (by decide), (by decide), step468_2339_2366,
      (by decide), (by decide), step468_2367_2452,
      (by decide), (by decide), step468_2453_2499, rfl⟩⟩

theorem step468_verified : Checked step468 :=
  ⟨step468_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step468_cover⟩

def step469 : Request :=
  ⟨⟨⟨420, 586, 127, 6858⟩, 2252760678400, 3279920952⟩, 3, 5, 16, 642859⟩

theorem step469_nodes : P1_7_1.nodeRows step469.bank.shape = step469.bank.nodeRows :=
  node_check step469.bank (by decide) (by decide) (by decide)

private theorem step469_2330_2346 : Positive step469 2330 2346 := by decide +kernel

private theorem step469_2347_2398 : Positive step469 2347 2398 := by decide +kernel

private theorem step469_2399_2499 : Positive step469 2399 2499 := by decide +kernel

theorem step469_cover : ∃ ends, Cover step469 firstHeight ends := by
  exact ⟨[2346, 2398, 2499],
    ⟨(by decide), (by decide), step469_2330_2346,
      (by decide), (by decide), step469_2347_2398,
      (by decide), (by decide), step469_2399_2499, rfl⟩⟩

theorem step469_verified : Checked step469 :=
  ⟨step469_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step469_cover⟩

def step470 : Request :=
  ⟨⟨⟨520, 725, 161, 6858⟩, 4343013310464, 7809559934⟩, 4, 5, 16, 642859⟩

theorem step470_nodes : P1_7_1.nodeRows step470.bank.shape = step470.bank.nodeRows :=
  node_check step470.bank (by decide) (by decide) (by decide)

private theorem step470_2330_2341 : Positive step470 2330 2341 := by decide +kernel

private theorem step470_2342_2376 : Positive step470 2342 2376 := by decide +kernel

private theorem step470_2377_2480 : Positive step470 2377 2480 := by decide +kernel

private theorem step470_2481_2499 : Positive step470 2481 2499 := by decide +kernel

theorem step470_cover : ∃ ends, Cover step470 firstHeight ends := by
  exact ⟨[2341, 2376, 2480, 2499],
    ⟨(by decide), (by decide), step470_2330_2341,
      (by decide), (by decide), step470_2342_2376,
      (by decide), (by decide), step470_2377_2480,
      (by decide), (by decide), step470_2481_2499, rfl⟩⟩

theorem step470_verified : Checked step470 :=
  ⟨step470_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step470_cover⟩

def step471 : Request :=
  ⟨⟨⟨520, 725, 157, 7715⟩, 4261264752640, 7658911630⟩, 5, 5, 16, 642859⟩

theorem step471_nodes : P1_7_1.nodeRows step471.bank.shape = step471.bank.nodeRows :=
  node_check step471.bank (by decide) (by decide) (by decide)

private theorem step471_2330_2345 : Positive step471 2330 2345 := by decide +kernel

private theorem step471_2346_2393 : Positive step471 2346 2393 := by decide +kernel

private theorem step471_2394_2499 : Positive step471 2394 2499 := by decide +kernel

theorem step471_cover : ∃ ends, Cover step471 firstHeight ends := by
  exact ⟨[2345, 2393, 2499],
    ⟨(by decide), (by decide), step471_2330_2345,
      (by decide), (by decide), step471_2346_2393,
      (by decide), (by decide), step471_2394_2499, rfl⟩⟩

theorem step471_verified : Checked step471 :=
  ⟨step471_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step471_cover⟩

def step472 : Request :=
  ⟨⟨⟨520, 725, 161, 8679⟩, 4343013310464, 7809559934⟩, 7, 5, 16, 642859⟩

theorem step472_nodes : P1_7_1.nodeRows step472.bank.shape = step472.bank.nodeRows :=
  node_check step472.bank (by decide) (by decide) (by decide)

private theorem step472_2330_2339 : Positive step472 2330 2339 := by decide +kernel

private theorem step472_2340_2369 : Positive step472 2340 2369 := by decide +kernel

private theorem step472_2370_2457 : Positive step472 2370 2457 := by decide +kernel

private theorem step472_2458_2499 : Positive step472 2458 2499 := by decide +kernel

theorem step472_cover : ∃ ends, Cover step472 firstHeight ends := by
  exact ⟨[2339, 2369, 2457, 2499],
    ⟨(by decide), (by decide), step472_2330_2339,
      (by decide), (by decide), step472_2340_2369,
      (by decide), (by decide), step472_2370_2457,
      (by decide), (by decide), step472_2458_2499, rfl⟩⟩

theorem step472_verified : Checked step472 :=
  ⟨step472_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step472_cover⟩

def step473 : Request :=
  ⟨⟨⟨750, 1046, 232, 9763⟩, 12985818152960, 33687112323⟩, 10, 5, 16, 642859⟩

theorem step473_nodes : P1_7_1.nodeRows step473.bank.shape = step473.bank.nodeRows :=
  node_check step473.bank (by decide) (by decide) (by decide)

private theorem step473_2330_2342 : Positive step473 2330 2342 := by decide +kernel

private theorem step473_2343_2378 : Positive step473 2343 2378 := by decide +kernel

private theorem step473_2379_2480 : Positive step473 2379 2480 := by decide +kernel

private theorem step473_2481_2499 : Positive step473 2481 2499 := by decide +kernel

theorem step473_cover : ∃ ends, Cover step473 firstHeight ends := by
  exact ⟨[2342, 2378, 2480, 2499],
    ⟨(by decide), (by decide), step473_2330_2342,
      (by decide), (by decide), step473_2343_2378,
      (by decide), (by decide), step473_2379_2480,
      (by decide), (by decide), step473_2481_2499, rfl⟩⟩

theorem step473_verified : Checked step473 :=
  ⟨step473_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step473_cover⟩

def step474 : Request :=
  ⟨⟨⟨750, 1046, 232, 13899⟩, 12985818152960, 33687112323⟩, 16, 5, 16, 642859⟩

theorem step474_nodes : P1_7_1.nodeRows step474.bank.shape = step474.bank.nodeRows :=
  node_check step474.bank (by decide) (by decide) (by decide)

private theorem step474_2330_2344 : Positive step474 2330 2344 := by decide +kernel

private theorem step474_2345_2386 : Positive step474 2345 2386 := by decide +kernel

private theorem step474_2387_2499 : Positive step474 2387 2499 := by decide +kernel

theorem step474_cover : ∃ ends, Cover step474 firstHeight ends := by
  exact ⟨[2344, 2386, 2499],
    ⟨(by decide), (by decide), step474_2330_2344,
      (by decide), (by decide), step474_2345_2386,
      (by decide), (by decide), step474_2387_2499, rfl⟩⟩

theorem step474_verified : Checked step474 :=
  ⟨step474_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step474_cover⟩

def step475 : Request :=
  ⟨⟨⟨900, 1256, 272, 15636⟩, 22024701870080, 68653176066⟩, 20, 5, 16, 642859⟩

theorem step475_nodes : P1_7_1.nodeRows step475.bank.shape = step475.bank.nodeRows :=
  node_check step475.bank (by decide) (by decide) (by decide)

private theorem step475_2330_2331 : Positive step475 2330 2331 := by decide +kernel

private theorem step475_2332_2337 : Positive step475 2332 2337 := by decide +kernel

private theorem step475_2338_2353 : Positive step475 2338 2353 := by decide +kernel

private theorem step475_2354_2398 : Positive step475 2354 2398 := by decide +kernel

private theorem step475_2399_2499 : Positive step475 2399 2499 := by decide +kernel

theorem step475_cover : ∃ ends, Cover step475 firstHeight ends := by
  exact ⟨[2331, 2337, 2353, 2398, 2499],
    ⟨(by decide), (by decide), step475_2330_2331,
      (by decide), (by decide), step475_2332_2337,
      (by decide), (by decide), step475_2338_2353,
      (by decide), (by decide), step475_2354_2398,
      (by decide), (by decide), step475_2399_2499, rfl⟩⟩

theorem step475_verified : Checked step475 :=
  ⟨step475_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step475_cover⟩

def step476 : Request :=
  ⟨⟨⟨1350, 1883, 418, 19788⟩, 75578221264896, 352769102024⟩, 31, 5, 16, 642859⟩

theorem step476_nodes : P1_7_1.nodeRows step476.bank.shape = step476.bank.nodeRows :=
  node_check step476.bank (by decide) (by decide) (by decide)

private theorem step476_2330_2335 : Positive step476 2330 2335 := by decide +kernel

private theorem step476_2336_2351 : Positive step476 2336 2351 := by decide +kernel

private theorem step476_2352_2394 : Positive step476 2352 2394 := by decide +kernel

private theorem step476_2395_2499 : Positive step476 2395 2499 := by decide +kernel

theorem step476_cover : ∃ ends, Cover step476 firstHeight ends := by
  exact ⟨[2335, 2351, 2394, 2499],
    ⟨(by decide), (by decide), step476_2330_2335,
      (by decide), (by decide), step476_2336_2351,
      (by decide), (by decide), step476_2352_2394,
      (by decide), (by decide), step476_2395_2499, rfl⟩⟩

theorem step476_verified : Checked step476 :=
  ⟨step476_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step476_cover⟩

def step477 : Request :=
  ⟨⟨⟨1350, 1883, 408, 22261⟩, 74202776600576, 346190054868⟩, 32, 5, 16, 642859⟩

theorem step477_nodes : P1_7_1.nodeRows step477.bank.shape = step477.bank.nodeRows :=
  node_check step477.bank (by decide) (by decide) (by decide)

private theorem step477_2330_2352 : Positive step477 2330 2352 := by decide +kernel

private theorem step477_2353_2415 : Positive step477 2353 2415 := by decide +kernel

private theorem step477_2416_2499 : Positive step477 2416 2499 := by decide +kernel

theorem step477_cover : ∃ ends, Cover step477 firstHeight ends := by
  exact ⟨[2352, 2415, 2499],
    ⟨(by decide), (by decide), step477_2330_2352,
      (by decide), (by decide), step477_2353_2415,
      (by decide), (by decide), step477_2416_2499, rfl⟩⟩

theorem step477_verified : Checked step477 :=
  ⟨step477_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step477_cover⟩

def step478 : Request :=
  ⟨⟨⟨1650, 2302, 498, 28173⟩, 135254251667456, 771697512616⟩, 44, 5, 16, 642859⟩

theorem step478_nodes : P1_7_1.nodeRows step478.bank.shape = step478.bank.nodeRows :=
  node_check step478.bank (by decide) (by decide) (by decide)

private theorem step478_2330_2336 : Positive step478 2330 2336 := by decide +kernel

private theorem step478_2337_2355 : Positive step478 2337 2355 := by decide +kernel

private theorem step478_2356_2406 : Positive step478 2356 2406 := by decide +kernel

private theorem step478_2407_2499 : Positive step478 2407 2499 := by decide +kernel

theorem step478_cover : ∃ ends, Cover step478 firstHeight ends := by
  exact ⟨[2336, 2355, 2406, 2499],
    ⟨(by decide), (by decide), step478_2330_2336,
      (by decide), (by decide), step478_2337_2355,
      (by decide), (by decide), step478_2356_2406,
      (by decide), (by decide), step478_2407_2499, rfl⟩⟩

theorem step478_verified : Checked step478 :=
  ⟨step478_nodes, Research6966.HelperWindowCatalogue.moment2302_498,
    (by decide), (by decide), (by decide), step478_cover⟩

def step479 : Request :=
  ⟨⟨⟨3000, 4186, 930, 40111⟩, 828559354757120, 8600191575129⟩, 73, 5, 16, 642859⟩

theorem step479_nodes : P1_7_1.nodeRows step479.bank.shape = step479.bank.nodeRows :=
  node_check step479.bank (by decide) (by decide) (by decide)

private theorem step479_2330_2342 : Positive step479 2330 2342 := by decide +kernel

private theorem step479_2343_2376 : Positive step479 2343 2376 := by decide +kernel

private theorem step479_2377_2465 : Positive step479 2377 2465 := by decide +kernel

private theorem step479_2466_2499 : Positive step479 2466 2499 := by decide +kernel

theorem step479_cover : ∃ ends, Cover step479 firstHeight ends := by
  exact ⟨[2342, 2376, 2465, 2499],
    ⟨(by decide), (by decide), step479_2330_2342,
      (by decide), (by decide), step479_2343_2376,
      (by decide), (by decide), step479_2377_2465,
      (by decide), (by decide), step479_2466_2499, rfl⟩⟩

theorem step479_verified : Checked step479 :=
  ⟨step479_nodes, Research6966.HelperWindowCatalogue.moment4186_930,
    (by decide), (by decide), (by decide), step479_cover⟩

def step480 : Request :=
  ⟨⟨⟨2500, 3488, 775, 45124⟩, 479640131993600, 4147842034257⟩, 76, 5, 16, 642859⟩

theorem step480_nodes : P1_7_1.nodeRows step480.bank.shape = step480.bank.nodeRows :=
  node_check step480.bank (by decide) (by decide) (by decide)

private theorem step480_2330_2345 : Positive step480 2330 2345 := by decide +kernel

private theorem step480_2346_2387 : Positive step480 2346 2387 := by decide +kernel

private theorem step480_2388_2497 : Positive step480 2388 2497 := by decide +kernel

private theorem step480_2498_2499 : Positive step480 2498 2499 := by decide +kernel

theorem step480_cover : ∃ ends, Cover step480 firstHeight ends := by
  exact ⟨[2345, 2387, 2497, 2499],
    ⟨(by decide), (by decide), step480_2330_2345,
      (by decide), (by decide), step480_2346_2387,
      (by decide), (by decide), step480_2388_2497,
      (by decide), (by decide), step480_2498_2499, rfl⟩⟩

theorem step480_verified : Checked step480 :=
  ⟨step480_nodes, Research6966.HelperWindowCatalogue.moment3488_775,
    (by decide), (by decide), (by decide), step480_cover⟩

def step481 : Request :=
  ⟨⟨⟨3500, 4883, 1057, 57109⟩, 1289556817346560, 15600507702257⟩, 103, 5, 16, 642859⟩

theorem step481_nodes : P1_7_1.nodeRows step481.bank.shape = step481.bank.nodeRows :=
  node_check step481.bank (by decide) (by decide) (by decide)

private theorem step481_2330_2330 : Positive step481 2330 2330 := by decide +kernel

private theorem step481_2331_2333 : Positive step481 2331 2333 := by decide +kernel

private theorem step481_2334_2340 : Positive step481 2334 2340 := by decide +kernel

private theorem step481_2341_2359 : Positive step481 2341 2359 := by decide +kernel

private theorem step481_2360_2408 : Positive step481 2360 2408 := by decide +kernel

private theorem step481_2409_2499 : Positive step481 2409 2499 := by decide +kernel

theorem step481_cover : ∃ ends, Cover step481 firstHeight ends := by
  exact ⟨[2330, 2333, 2340, 2359, 2408, 2499],
    ⟨(by decide), (by decide), step481_2330_2330,
      (by decide), (by decide), step481_2331_2333,
      (by decide), (by decide), step481_2334_2340,
      (by decide), (by decide), step481_2341_2359,
      (by decide), (by decide), step481_2360_2408,
      (by decide), (by decide), step481_2409_2499, rfl⟩⟩

theorem step481_verified : Checked step481 :=
  ⟨step481_nodes, Research6966.HelperWindowCatalogue.moment4883_1057,
    (by decide), (by decide), (by decide), step481_cover⟩

def step482 : Request :=
  ⟨⟨⟨294, 410, 89, 3807⟩, 777085255680, 791788817⟩, 0, 5, 26, 642859⟩

theorem step482_nodes : P1_7_1.nodeRows step482.bank.shape = step482.bank.nodeRows :=
  node_check step482.bank (by decide) (by decide) (by decide)

private theorem step482_2330_2342 : Positive step482 2330 2342 := by decide +kernel

private theorem step482_2343_2386 : Positive step482 2343 2386 := by decide +kernel

private theorem step482_2387_2499 : Positive step482 2387 2499 := by decide +kernel

theorem step482_cover : ∃ ends, Cover step482 firstHeight ends := by
  exact ⟨[2342, 2386, 2499],
    ⟨(by decide), (by decide), step482_2330_2342,
      (by decide), (by decide), step482_2343_2386,
      (by decide), (by decide), step482_2387_2499, rfl⟩⟩

theorem step482_verified : Checked step482 :=
  ⟨step482_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step482_cover⟩

def step483 : Request :=
  ⟨⟨⟨294, 410, 91, 4282⟩, 790165454848, 805457011⟩, 1, 5, 26, 642859⟩

theorem step483_nodes : P1_7_1.nodeRows step483.bank.shape = step483.bank.nodeRows :=
  node_check step483.bank (by decide) (by decide) (by decide)

private theorem step483_2330_2334 : Positive step483 2330 2334 := by decide +kernel

private theorem step483_2335_2351 : Positive step483 2335 2351 := by decide +kernel

private theorem step483_2352_2408 : Positive step483 2352 2408 := by decide +kernel

private theorem step483_2409_2499 : Positive step483 2409 2499 := by decide +kernel

theorem step483_cover : ∃ ends, Cover step483 firstHeight ends := by
  exact ⟨[2334, 2351, 2408, 2499],
    ⟨(by decide), (by decide), step483_2330_2334,
      (by decide), (by decide), step483_2335_2351,
      (by decide), (by decide), step483_2352_2408,
      (by decide), (by decide), step483_2409_2499, rfl⟩⟩

theorem step483_verified : Checked step483 :=
  ⟨step483_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step483_cover⟩

def step484 : Request :=
  ⟨⟨⟨294, 410, 91, 5419⟩, 790165454848, 805457011⟩, 2, 5, 26, 642859⟩

theorem step484_nodes : P1_7_1.nodeRows step484.bank.shape = step484.bank.nodeRows :=
  node_check step484.bank (by decide) (by decide) (by decide)

private theorem step484_2330_2340 : Positive step484 2330 2340 := by decide +kernel

private theorem step484_2341_2377 : Positive step484 2341 2377 := by decide +kernel

private theorem step484_2378_2499 : Positive step484 2378 2499 := by decide +kernel

theorem step484_cover : ∃ ends, Cover step484 firstHeight ends := by
  exact ⟨[2340, 2377, 2499],
    ⟨(by decide), (by decide), step484_2330_2340,
      (by decide), (by decide), step484_2341_2377,
      (by decide), (by decide), step484_2378_2499, rfl⟩⟩

theorem step484_verified : Checked step484 :=
  ⟨step484_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step484_cover⟩

def step485 : Request :=
  ⟨⟨⟨350, 488, 106, 5419⟩, 1308168290304, 1584729438⟩, 3, 5, 26, 642859⟩

theorem step485_nodes : P1_7_1.nodeRows step485.bank.shape = step485.bank.nodeRows :=
  node_check step485.bank (by decide) (by decide) (by decide)

private theorem step485_2330_2351 : Positive step485 2330 2351 := by decide +kernel

private theorem step485_2352_2422 : Positive step485 2352 2422 := by decide +kernel

private theorem step485_2423_2499 : Positive step485 2423 2499 := by decide +kernel

theorem step485_cover : ∃ ends, Cover step485 firstHeight ends := by
  exact ⟨[2351, 2422, 2499],
    ⟨(by decide), (by decide), step485_2330_2351,
      (by decide), (by decide), step485_2352_2422,
      (by decide), (by decide), step485_2423_2499, rfl⟩⟩

theorem step485_verified : Checked step485 :=
  ⟨step485_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step485_cover⟩

def step486 : Request :=
  ⟨⟨⟨350, 488, 106, 6096⟩, 1308168290304, 1584729438⟩, 4, 5, 26, 642859⟩

theorem step486_nodes : P1_7_1.nodeRows step486.bank.shape = step486.bank.nodeRows :=
  node_check step486.bank (by decide) (by decide) (by decide)

private theorem step486_2330_2331 : Positive step486 2330 2331 := by decide +kernel

private theorem step486_2332_2338 : Positive step486 2332 2338 := by decide +kernel

private theorem step486_2339_2360 : Positive step486 2339 2360 := by decide +kernel

private theorem step486_2361_2431 : Positive step486 2361 2431 := by decide +kernel

private theorem step486_2432_2499 : Positive step486 2432 2499 := by decide +kernel

theorem step486_cover : ∃ ends, Cover step486 firstHeight ends := by
  exact ⟨[2331, 2338, 2360, 2431, 2499],
    ⟨(by decide), (by decide), step486_2330_2331,
      (by decide), (by decide), step486_2332_2338,
      (by decide), (by decide), step486_2339_2360,
      (by decide), (by decide), step486_2361_2431,
      (by decide), (by decide), step486_2432_2499, rfl⟩⟩

theorem step486_verified : Checked step486 :=
  ⟨step486_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step486_cover⟩

def step487 : Request :=
  ⟨⟨⟨420, 586, 127, 6096⟩, 2252760678400, 3279920952⟩, 5, 5, 26, 642859⟩

theorem step487_nodes : P1_7_1.nodeRows step487.bank.shape = step487.bank.nodeRows :=
  node_check step487.bank (by decide) (by decide) (by decide)

private theorem step487_2330_2354 : Positive step487 2330 2354 := by decide +kernel

private theorem step487_2355_2432 : Positive step487 2355 2432 := by decide +kernel

private theorem step487_2433_2499 : Positive step487 2433 2499 := by decide +kernel

theorem step487_cover : ∃ ends, Cover step487 firstHeight ends := by
  exact ⟨[2354, 2432, 2499],
    ⟨(by decide), (by decide), step487_2330_2354,
      (by decide), (by decide), step487_2355_2432,
      (by decide), (by decide), step487_2433_2499, rfl⟩⟩

theorem step487_verified : Checked step487 :=
  ⟨step487_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step487_cover⟩

def step488 : Request :=
  ⟨⟨⟨520, 725, 161, 6096⟩, 4343013310464, 7809559934⟩, 7, 5, 26, 642859⟩

theorem step488_nodes : P1_7_1.nodeRows step488.bank.shape = step488.bank.nodeRows :=
  node_check step488.bank (by decide) (by decide) (by decide)

private theorem step488_2330_2347 : Positive step488 2330 2347 := by decide +kernel

private theorem step488_2348_2400 : Positive step488 2348 2400 := by decide +kernel

private theorem step488_2401_2499 : Positive step488 2401 2499 := by decide +kernel

theorem step488_cover : ∃ ends, Cover step488 firstHeight ends := by
  exact ⟨[2347, 2400, 2499],
    ⟨(by decide), (by decide), step488_2330_2347,
      (by decide), (by decide), step488_2348_2400,
      (by decide), (by decide), step488_2401_2499, rfl⟩⟩

theorem step488_verified : Checked step488 :=
  ⟨step488_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step488_cover⟩

def step489 : Request :=
  ⟨⟨⟨520, 725, 161, 7715⟩, 4343013310464, 7809559934⟩, 10, 5, 26, 642859⟩

theorem step489_nodes : P1_7_1.nodeRows step489.bank.shape = step489.bank.nodeRows :=
  node_check step489.bank (by decide) (by decide) (by decide)

private theorem step489_2330_2331 : Positive step489 2330 2331 := by decide +kernel

private theorem step489_2332_2336 : Positive step489 2332 2336 := by decide +kernel

private theorem step489_2337_2351 : Positive step489 2337 2351 := by decide +kernel

private theorem step489_2352_2395 : Positive step489 2352 2395 := by decide +kernel

private theorem step489_2396_2499 : Positive step489 2396 2499 := by decide +kernel

theorem step489_cover : ∃ ends, Cover step489 firstHeight ends := by
  exact ⟨[2331, 2336, 2351, 2395, 2499],
    ⟨(by decide), (by decide), step489_2330_2331,
      (by decide), (by decide), step489_2332_2336,
      (by decide), (by decide), step489_2337_2351,
      (by decide), (by decide), step489_2352_2395,
      (by decide), (by decide), step489_2396_2499, rfl⟩⟩

theorem step489_verified : Checked step489 :=
  ⟨step489_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step489_cover⟩

def step490 : Request :=
  ⟨⟨⟨750, 1046, 226, 9763⟩, 12730741817344, 33009058589⟩, 16, 5, 26, 642859⟩

theorem step490_nodes : P1_7_1.nodeRows step490.bank.shape = step490.bank.nodeRows :=
  node_check step490.bank (by decide) (by decide) (by decide)

private theorem step490_2330_2334 : Positive step490 2330 2334 := by decide +kernel

private theorem step490_2335_2348 : Positive step490 2335 2348 := by decide +kernel

private theorem step490_2349_2388 : Positive step490 2349 2388 := by decide +kernel

private theorem step490_2389_2499 : Positive step490 2389 2499 := by decide +kernel

theorem step490_cover : ∃ ends, Cover step490 firstHeight ends := by
  exact ⟨[2334, 2348, 2388, 2499],
    ⟨(by decide), (by decide), step490_2330_2334,
      (by decide), (by decide), step490_2335_2348,
      (by decide), (by decide), step490_2349_2388,
      (by decide), (by decide), step490_2389_2499, rfl⟩⟩

theorem step490_verified : Checked step490 :=
  ⟨step490_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step490_cover⟩

def step491 : Request :=
  ⟨⟨⟨750, 1046, 232, 12355⟩, 12985818152960, 33687112323⟩, 20, 5, 26, 642859⟩

theorem step491_nodes : P1_7_1.nodeRows step491.bank.shape = step491.bank.nodeRows :=
  node_check step491.bank (by decide) (by decide) (by decide)

private theorem step491_2330_2336 : Positive step491 2330 2336 := by decide +kernel

private theorem step491_2337_2356 : Positive step491 2337 2356 := by decide +kernel

private theorem step491_2357_2412 : Positive step491 2357 2412 := by decide +kernel

private theorem step491_2413_2499 : Positive step491 2413 2499 := by decide +kernel

theorem step491_cover : ∃ ends, Cover step491 firstHeight ends := by
  exact ⟨[2336, 2356, 2412, 2499],
    ⟨(by decide), (by decide), step491_2330_2336,
      (by decide), (by decide), step491_2337_2356,
      (by decide), (by decide), step491_2357_2412,
      (by decide), (by decide), step491_2413_2499, rfl⟩⟩

theorem step491_verified : Checked step491 :=
  ⟨step491_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step491_cover⟩

def step492 : Request :=
  ⟨⟨⟨1100, 1534, 341, 15636⟩, 40955142733824, 155702293064⟩, 31, 5, 26, 642859⟩

theorem step492_nodes : P1_7_1.nodeRows step492.bank.shape = step492.bank.nodeRows :=
  node_check step492.bank (by decide) (by decide) (by decide)

private theorem step492_2330_2343 : Positive step492 2330 2343 := by decide +kernel

private theorem step492_2344_2381 : Positive step492 2344 2381 := by decide +kernel

private theorem step492_2382_2485 : Positive step492 2382 2485 := by decide +kernel

private theorem step492_2486_2499 : Positive step492 2486 2499 := by decide +kernel

theorem step492_cover : ∃ ends, Cover step492 firstHeight ends := by
  exact ⟨[2343, 2381, 2485, 2499],
    ⟨(by decide), (by decide), step492_2330_2343,
      (by decide), (by decide), step492_2344_2381,
      (by decide), (by decide), step492_2382_2485,
      (by decide), (by decide), step492_2486_2499, rfl⟩⟩

theorem step492_verified : Checked step492 :=
  ⟨step492_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step492_cover⟩

def step493 : Request :=
  ⟨⟨⟨1100, 1534, 332, 17590⟩, 40133103452160, 152499774767⟩, 32, 5, 26, 642859⟩

theorem step493_nodes : P1_7_1.nodeRows step493.bank.shape = step493.bank.nodeRows :=
  node_check step493.bank (by decide) (by decide) (by decide)

private theorem step493_2330_2344 : Positive step493 2330 2344 := by decide +kernel

private theorem step493_2345_2385 : Positive step493 2345 2385 := by decide +kernel

private theorem step493_2386_2498 : Positive step493 2386 2498 := by decide +kernel

private theorem step493_2499_2499 : Positive step493 2499 2499 := by decide +kernel

theorem step493_cover : ∃ ends, Cover step493 firstHeight ends := by
  exact ⟨[2344, 2385, 2498, 2499],
    ⟨(by decide), (by decide), step493_2330_2344,
      (by decide), (by decide), step493_2345_2385,
      (by decide), (by decide), step493_2386_2498,
      (by decide), (by decide), step493_2499_2499, rfl⟩⟩

theorem step493_verified : Checked step493 :=
  ⟨step493_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step493_cover⟩

def step494 : Request :=
  ⟨⟨⟨1350, 1883, 418, 22261⟩, 75578221264896, 352769102024⟩, 44, 5, 26, 642859⟩

theorem step494_nodes : P1_7_1.nodeRows step494.bank.shape = step494.bank.nodeRows :=
  node_check step494.bank (by decide) (by decide) (by decide)

private theorem step494_2330_2340 : Positive step494 2330 2340 := by decide +kernel

private theorem step494_2341_2370 : Positive step494 2341 2370 := by decide +kernel

private theorem step494_2371_2450 : Positive step494 2371 2450 := by decide +kernel

private theorem step494_2451_2499 : Positive step494 2451 2499 := by decide +kernel

theorem step494_cover : ∃ ends, Cover step494 firstHeight ends := by
  exact ⟨[2340, 2370, 2450, 2499],
    ⟨(by decide), (by decide), step494_2330_2340,
      (by decide), (by decide), step494_2341_2370,
      (by decide), (by decide), step494_2371_2450,
      (by decide), (by decide), step494_2451_2499, rfl⟩⟩

theorem step494_verified : Checked step494 :=
  ⟨step494_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step494_cover⟩

def step495 : Request :=
  ⟨⟨⟨2000, 2790, 620, 35655⟩, 245690786119680, 1699185179819⟩, 73, 5, 26, 642859⟩

theorem step495_nodes : P1_7_1.nodeRows step495.bank.shape = step495.bank.nodeRows :=
  node_check step495.bank (by decide) (by decide) (by decide)

private theorem step495_2330_2336 : Positive step495 2330 2336 := by decide +kernel

private theorem step495_2337_2354 : Positive step495 2337 2354 := by decide +kernel

private theorem step495_2355_2402 : Positive step495 2355 2402 := by decide +kernel

private theorem step495_2403_2499 : Positive step495 2403 2499 := by decide +kernel

theorem step495_cover : ∃ ends, Cover step495 firstHeight ends := by
  exact ⟨[2336, 2354, 2402, 2499],
    ⟨(by decide), (by decide), step495_2330_2336,
      (by decide), (by decide), step495_2337_2354,
      (by decide), (by decide), step495_2355_2402,
      (by decide), (by decide), step495_2403_2499, rfl⟩⟩

theorem step495_verified : Checked step495 :=
  ⟨step495_nodes, Research6966.HelperWindowCatalogue.moment2790_620,
    (by decide), (by decide), (by decide), step495_cover⟩

def step496 : Request :=
  ⟨⟨⟨2500, 3488, 755, 31694⟩, 470210689105920, 4064279218567⟩, 76, 5, 26, 642859⟩

theorem step496_nodes : P1_7_1.nodeRows step496.bank.shape = step496.bank.nodeRows :=
  node_check step496.bank (by decide) (by decide) (by decide)

private theorem step496_2330_2334 : Positive step496 2330 2334 := by decide +kernel

private theorem step496_2335_2348 : Positive step496 2335 2348 := by decide +kernel

private theorem step496_2349_2384 : Positive step496 2349 2384 := by decide +kernel

private theorem step496_2385_2480 : Positive step496 2385 2480 := by decide +kernel

private theorem step496_2481_2499 : Positive step496 2481 2499 := by decide +kernel

theorem step496_cover : ∃ ends, Cover step496 firstHeight ends := by
  exact ⟨[2334, 2348, 2384, 2480, 2499],
    ⟨(by decide), (by decide), step496_2330_2334,
      (by decide), (by decide), step496_2335_2348,
      (by decide), (by decide), step496_2349_2384,
      (by decide), (by decide), step496_2385_2480,
      (by decide), (by decide), step496_2481_2499, rfl⟩⟩

theorem step496_verified : Checked step496 :=
  ⟨step496_nodes, Research6966.HelperWindowCatalogue.moment3488_755,
    (by decide), (by decide), (by decide), step496_cover⟩

def step497 : Request :=
  ⟨⟨⟨3000, 4185, 906, 45124⟩, 812266433019904, 8420412037186⟩, 103, 5, 26, 642859⟩

theorem step497_nodes : P1_7_1.nodeRows step497.bank.shape = step497.bank.nodeRows :=
  node_check step497.bank (by decide) (by decide) (by decide)

private theorem step497_2330_2337 : Positive step497 2330 2337 := by decide +kernel

private theorem step497_2338_2358 : Positive step497 2338 2358 := by decide +kernel

private theorem step497_2359_2413 : Positive step497 2359 2413 := by decide +kernel

private theorem step497_2414_2499 : Positive step497 2414 2499 := by decide +kernel

theorem step497_cover : ∃ ends, Cover step497 firstHeight ends := by
  exact ⟨[2337, 2358, 2413, 2499],
    ⟨(by decide), (by decide), step497_2330_2337,
      (by decide), (by decide), step497_2338_2358,
      (by decide), (by decide), step497_2359_2413,
      (by decide), (by decide), step497_2414_2499, rfl⟩⟩

theorem step497_verified : Checked step497 :=
  ⟨step497_nodes, Research6966.HelperWindowCatalogue.moment4185_906,
    (by decide), (by decide), (by decide), step497_cover⟩

def step498 : Request :=
  ⟨⟨⟨250, 349, 78, 2377⟩, 490108092416, 426627288⟩, 0, 5, 41, 642859⟩

theorem step498_nodes : P1_7_1.nodeRows step498.bank.shape = step498.bank.nodeRows :=
  node_check step498.bank (by decide) (by decide) (by decide)

private theorem step498_2330_2333 : Positive step498 2330 2333 := by decide +kernel

private theorem step498_2334_2347 : Positive step498 2334 2347 := by decide +kernel

private theorem step498_2348_2396 : Positive step498 2348 2396 := by decide +kernel

private theorem step498_2397_2499 : Positive step498 2397 2499 := by decide +kernel

theorem step498_cover : ∃ ends, Cover step498 firstHeight ends := by
  exact ⟨[2333, 2347, 2396, 2499],
    ⟨(by decide), (by decide), step498_2330_2333,
      (by decide), (by decide), step498_2334_2347,
      (by decide), (by decide), step498_2348_2396,
      (by decide), (by decide), step498_2397_2499, rfl⟩⟩

theorem step498_verified : Checked step498 :=
  ⟨step498_nodes, Research6966.HelperWindowCatalogue.moment349_78,
    (by decide), (by decide), (by decide), step498_cover⟩

def step499 : Request :=
  ⟨⟨⟨250, 349, 76, 3008⟩, 480667500544, 418199213⟩, 1, 5, 41, 642859⟩

theorem step499_nodes : P1_7_1.nodeRows step499.bank.shape = step499.bank.nodeRows :=
  node_check step499.bank (by decide) (by decide) (by decide)

private theorem step499_2330_2345 : Positive step499 2330 2345 := by decide +kernel

private theorem step499_2346_2402 : Positive step499 2346 2402 := by decide +kernel

private theorem step499_2403_2499 : Positive step499 2403 2499 := by decide +kernel

theorem step499_cover : ∃ ends, Cover step499 firstHeight ends := by
  exact ⟨[2345, 2402, 2499],
    ⟨(by decide), (by decide), step499_2330_2345,
      (by decide), (by decide), step499_2346_2402,
      (by decide), (by decide), step499_2403_2499, rfl⟩⟩

theorem step499_verified : Checked step499 :=
  ⟨step499_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step499_cover⟩

def step500 : Request :=
  ⟨⟨⟨294, 410, 89, 3008⟩, 777085255680, 791788817⟩, 2, 5, 41, 642859⟩

theorem step500_nodes : P1_7_1.nodeRows step500.bank.shape = step500.bank.nodeRows :=
  node_check step500.bank (by decide) (by decide) (by decide)

private theorem step500_2330_2342 : Positive step500 2330 2342 := by decide +kernel

private theorem step500_2343_2386 : Positive step500 2343 2386 := by decide +kernel

private theorem step500_2387_2499 : Positive step500 2387 2499 := by decide +kernel

theorem step500_cover : ∃ ends, Cover step500 firstHeight ends := by
  exact ⟨[2342, 2386, 2499],
    ⟨(by decide), (by decide), step500_2330_2342,
      (by decide), (by decide), step500_2343_2386,
      (by decide), (by decide), step500_2387_2499, rfl⟩⟩

theorem step500_verified : Checked step500 :=
  ⟨step500_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step500_cover⟩

def step501 : Request :=
  ⟨⟨⟨294, 410, 91, 3384⟩, 790165454848, 805457011⟩, 3, 5, 41, 642859⟩

theorem step501_nodes : P1_7_1.nodeRows step501.bank.shape = step501.bank.nodeRows :=
  node_check step501.bank (by decide) (by decide) (by decide)

private theorem step501_2330_2342 : Positive step501 2330 2342 := by decide +kernel

private theorem step501_2343_2386 : Positive step501 2343 2386 := by decide +kernel

private theorem step501_2387_2499 : Positive step501 2387 2499 := by decide +kernel

theorem step501_cover : ∃ ends, Cover step501 firstHeight ends := by
  exact ⟨[2342, 2386, 2499],
    ⟨(by decide), (by decide), step501_2330_2342,
      (by decide), (by decide), step501_2343_2386,
      (by decide), (by decide), step501_2387_2499, rfl⟩⟩

theorem step501_verified : Checked step501 :=
  ⟨step501_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step501_cover⟩

def step502 : Request :=
  ⟨⟨⟨350, 488, 106, 3384⟩, 1308168290304, 1584729438⟩, 4, 5, 41, 642859⟩

theorem step502_nodes : P1_7_1.nodeRows step502.bank.shape = step502.bank.nodeRows :=
  node_check step502.bank (by decide) (by decide) (by decide)

private theorem step502_2330_2333 : Positive step502 2330 2333 := by decide +kernel

private theorem step502_2334_2345 : Positive step502 2334 2345 := by decide +kernel

private theorem step502_2346_2384 : Positive step502 2346 2384 := by decide +kernel

private theorem step502_2385_2499 : Positive step502 2385 2499 := by decide +kernel

theorem step502_cover : ∃ ends, Cover step502 firstHeight ends := by
  exact ⟨[2333, 2345, 2384, 2499],
    ⟨(by decide), (by decide), step502_2330_2333,
      (by decide), (by decide), step502_2334_2345,
      (by decide), (by decide), step502_2346_2384,
      (by decide), (by decide), step502_2385_2499, rfl⟩⟩

theorem step502_verified : Checked step502 :=
  ⟨step502_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step502_cover⟩

def step503 : Request :=
  ⟨⟨⟨350, 488, 106, 3807⟩, 1308168290304, 1584729438⟩, 5, 5, 41, 642859⟩

theorem step503_nodes : P1_7_1.nodeRows step503.bank.shape = step503.bank.nodeRows :=
  node_check step503.bank (by decide) (by decide) (by decide)

private theorem step503_2330_2332 : Positive step503 2330 2332 := by decide +kernel

private theorem step503_2333_2342 : Positive step503 2333 2342 := by decide +kernel

private theorem step503_2343_2374 : Positive step503 2343 2374 := by decide +kernel

private theorem step503_2375_2477 : Positive step503 2375 2477 := by decide +kernel

private theorem step503_2478_2499 : Positive step503 2478 2499 := by decide +kernel

theorem step503_cover : ∃ ends, Cover step503 firstHeight ends := by
  exact ⟨[2332, 2342, 2374, 2477, 2499],
    ⟨(by decide), (by decide), step503_2330_2332,
      (by decide), (by decide), step503_2333_2342,
      (by decide), (by decide), step503_2343_2374,
      (by decide), (by decide), step503_2375_2477,
      (by decide), (by decide), step503_2478_2499, rfl⟩⟩

theorem step503_verified : Checked step503 :=
  ⟨step503_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step503_cover⟩

def step504 : Request :=
  ⟨⟨⟨420, 586, 127, 4282⟩, 2252760678400, 3279920952⟩, 7, 5, 41, 642859⟩

theorem step504_nodes : P1_7_1.nodeRows step504.bank.shape = step504.bank.nodeRows :=
  node_check step504.bank (by decide) (by decide) (by decide)

private theorem step504_2330_2347 : Positive step504 2330 2347 := by decide +kernel

private theorem step504_2348_2402 : Positive step504 2348 2402 := by decide +kernel

private theorem step504_2403_2499 : Positive step504 2403 2499 := by decide +kernel

theorem step504_cover : ∃ ends, Cover step504 firstHeight ends := by
  exact ⟨[2347, 2402, 2499],
    ⟨(by decide), (by decide), step504_2330_2347,
      (by decide), (by decide), step504_2348_2402,
      (by decide), (by decide), step504_2403_2499, rfl⟩⟩

theorem step504_verified : Checked step504 :=
  ⟨step504_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step504_cover⟩

def step505 : Request :=
  ⟨⟨⟨520, 725, 157, 4817⟩, 4261264752640, 7658911630⟩, 10, 5, 41, 642859⟩

theorem step505_nodes : P1_7_1.nodeRows step505.bank.shape = step505.bank.nodeRows :=
  node_check step505.bank (by decide) (by decide) (by decide)

private theorem step505_2330_2338 : Positive step505 2330 2338 := by decide +kernel

private theorem step505_2339_2365 : Positive step505 2339 2365 := by decide +kernel

private theorem step505_2366_2445 : Positive step505 2366 2445 := by decide +kernel

private theorem step505_2446_2499 : Positive step505 2446 2499 := by decide +kernel

theorem step505_cover : ∃ ends, Cover step505 firstHeight ends := by
  exact ⟨[2338, 2365, 2445, 2499],
    ⟨(by decide), (by decide), step505_2330_2338,
      (by decide), (by decide), step505_2339_2365,
      (by decide), (by decide), step505_2366_2445,
      (by decide), (by decide), step505_2446_2499, rfl⟩⟩

theorem step505_verified : Checked step505 :=
  ⟨step505_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step505_cover⟩

def step506 : Request :=
  ⟨⟨⟨630, 879, 195, 6096⟩, 7709474160640, 16827402390⟩, 16, 5, 41, 642859⟩

theorem step506_nodes : P1_7_1.nodeRows step506.bank.shape = step506.bank.nodeRows :=
  node_check step506.bank (by decide) (by decide) (by decide)

private theorem step506_2330_2333 : Positive step506 2330 2333 := by decide +kernel

private theorem step506_2334_2344 : Positive step506 2334 2344 := by decide +kernel

private theorem step506_2345_2376 : Positive step506 2345 2376 := by decide +kernel

private theorem step506_2377_2467 : Positive step506 2377 2467 := by decide +kernel

private theorem step506_2468_2499 : Positive step506 2468 2499 := by decide +kernel

theorem step506_cover : ∃ ends, Cover step506 firstHeight ends := by
  exact ⟨[2333, 2344, 2376, 2467, 2499],
    ⟨(by decide), (by decide), step506_2330_2333,
      (by decide), (by decide), step506_2334_2344,
      (by decide), (by decide), step506_2345_2376,
      (by decide), (by decide), step506_2377_2467,
      (by decide), (by decide), step506_2468_2499, rfl⟩⟩

theorem step506_verified : Checked step506 :=
  ⟨step506_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step506_cover⟩

def step507 : Request :=
  ⟨⟨⟨630, 878, 195, 8679⟩, 7709474160640, 16765904450⟩, 20, 5, 41, 642859⟩

theorem step507_nodes : P1_7_1.nodeRows step507.bank.shape = step507.bank.nodeRows :=
  node_check step507.bank (by decide) (by decide) (by decide)

private theorem step507_2330_2342 : Positive step507 2330 2342 := by decide +kernel

private theorem step507_2343_2379 : Positive step507 2343 2379 := by decide +kernel

private theorem step507_2380_2486 : Positive step507 2380 2486 := by decide +kernel

private theorem step507_2487_2499 : Positive step507 2487 2499 := by decide +kernel

theorem step507_cover : ∃ ends, Cover step507 firstHeight ends := by
  exact ⟨[2342, 2379, 2486, 2499],
    ⟨(by decide), (by decide), step507_2330_2342,
      (by decide), (by decide), step507_2343_2379,
      (by decide), (by decide), step507_2380_2486,
      (by decide), (by decide), step507_2487_2499, rfl⟩⟩

theorem step507_verified : Checked step507 :=
  ⟨step507_nodes, Research6966.HelperWindowCatalogue.moment878_195,
    (by decide), (by decide), (by decide), step507_cover⟩

def step508 : Request :=
  ⟨⟨⟨900, 1255, 279, 10983⟩, 22452680785920, 69841856233⟩, 31, 5, 41, 642859⟩

theorem step508_nodes : P1_7_1.nodeRows step508.bank.shape = step508.bank.nodeRows :=
  node_check step508.bank (by decide) (by decide) (by decide)

private theorem step508_2330_2348 : Positive step508 2330 2348 := by decide +kernel

private theorem step508_2349_2401 : Positive step508 2349 2401 := by decide +kernel

private theorem step508_2402_2499 : Positive step508 2402 2499 := by decide +kernel

theorem step508_cover : ∃ ends, Cover step508 firstHeight ends := by
  exact ⟨[2348, 2401, 2499],
    ⟨(by decide), (by decide), step508_2330_2348,
      (by decide), (by decide), step508_2349_2401,
      (by decide), (by decide), step508_2402_2499, rfl⟩⟩

theorem step508_verified : Checked step508 :=
  ⟨step508_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step508_cover⟩

def step509 : Request :=
  ⟨⟨⟨900, 1255, 279, 10983⟩, 22452680785920, 69841856233⟩, 32, 5, 41, 642859⟩

theorem step509_nodes : P1_7_1.nodeRows step509.bank.shape = step509.bank.nodeRows :=
  node_check step509.bank (by decide) (by decide) (by decide)

private theorem step509_2330_2330 : Positive step509 2330 2330 := by decide +kernel

private theorem step509_2331_2332 : Positive step509 2331 2332 := by decide +kernel

private theorem step509_2333_2338 : Positive step509 2333 2338 := by decide +kernel

private theorem step509_2339_2355 : Positive step509 2339 2355 := by decide +kernel

private theorem step509_2356_2401 : Positive step509 2356 2401 := by decide +kernel

private theorem step509_2402_2499 : Positive step509 2402 2499 := by decide +kernel

theorem step509_cover : ∃ ends, Cover step509 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2355, 2401, 2499],
    ⟨(by decide), (by decide), step509_2330_2330,
      (by decide), (by decide), step509_2331_2332,
      (by decide), (by decide), step509_2333_2338,
      (by decide), (by decide), step509_2339_2355,
      (by decide), (by decide), step509_2356_2401,
      (by decide), (by decide), step509_2402_2499, rfl⟩⟩

theorem step509_verified : Checked step509 :=
  ⟨step509_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step509_cover⟩

def step510 : Request :=
  ⟨⟨⟨1350, 1883, 418, 12355⟩, 75578221264896, 352769102024⟩, 44, 5, 41, 642859⟩

theorem step510_nodes : P1_7_1.nodeRows step510.bank.shape = step510.bank.nodeRows :=
  node_check step510.bank (by decide) (by decide) (by decide)

private theorem step510_2330_2333 : Positive step510 2330 2333 := by decide +kernel

private theorem step510_2334_2344 : Positive step510 2334 2344 := by decide +kernel

private theorem step510_2345_2374 : Positive step510 2345 2374 := by decide +kernel

private theorem step510_2375_2454 : Positive step510 2375 2454 := by decide +kernel

private theorem step510_2455_2499 : Positive step510 2455 2499 := by decide +kernel

theorem step510_cover : ∃ ends, Cover step510 firstHeight ends := by
  exact ⟨[2333, 2344, 2374, 2454, 2499],
    ⟨(by decide), (by decide), step510_2330_2333,
      (by decide), (by decide), step510_2334_2344,
      (by decide), (by decide), step510_2345_2374,
      (by decide), (by decide), step510_2375_2454,
      (by decide), (by decide), step510_2455_2499, rfl⟩⟩

theorem step510_verified : Checked step510 :=
  ⟨step510_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step510_cover⟩

def step511 : Request :=
  ⟨⟨⟨2000, 2790, 620, 19788⟩, 245690786119680, 1699185179819⟩, 73, 5, 41, 642859⟩

theorem step511_nodes : P1_7_1.nodeRows step511.bank.shape = step511.bank.nodeRows :=
  node_check step511.bank (by decide) (by decide) (by decide)

private theorem step511_2330_2345 : Positive step511 2330 2345 := by decide +kernel

private theorem step511_2346_2388 : Positive step511 2346 2388 := by decide +kernel

private theorem step511_2389_2499 : Positive step511 2389 2499 := by decide +kernel

theorem step511_cover : ∃ ends, Cover step511 firstHeight ends := by
  exact ⟨[2345, 2388, 2499],
    ⟨(by decide), (by decide), step511_2330_2345,
      (by decide), (by decide), step511_2346_2388,
      (by decide), (by decide), step511_2389_2499, rfl⟩⟩

theorem step511_verified : Checked step511 :=
  ⟨step511_nodes, Research6966.HelperWindowCatalogue.moment2790_620,
    (by decide), (by decide), (by decide), step511_cover⟩

end Research6966.HelperRescueCatalogue
