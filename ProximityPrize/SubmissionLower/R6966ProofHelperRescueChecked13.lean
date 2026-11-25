import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments7
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step432 : Request :=
  ⟨⟨⟨3000, 4186, 906, 64247⟩, 812266433019904, 8426888829858⟩, 76, 5, 2, 642859⟩

theorem step432_nodes : P1_7_1.nodeRows step432.bank.shape = step432.bank.nodeRows :=
  node_check step432.bank (by decide) (by decide) (by decide)

private theorem step432_2330_2333 : Positive step432 2330 2333 := by decide +kernel

private theorem step432_2334_2344 : Positive step432 2334 2344 := by decide +kernel

private theorem step432_2345_2373 : Positive step432 2345 2373 := by decide +kernel

private theorem step432_2374_2449 : Positive step432 2374 2449 := by decide +kernel

private theorem step432_2450_2499 : Positive step432 2450 2499 := by decide +kernel

theorem step432_cover : ∃ ends, Cover step432 firstHeight ends := by
  exact ⟨[2333, 2344, 2373, 2449, 2499],
    ⟨(by decide), (by decide), step432_2330_2333,
      (by decide), (by decide), step432_2334_2344,
      (by decide), (by decide), step432_2345_2373,
      (by decide), (by decide), step432_2374_2449,
      (by decide), (by decide), step432_2450_2499, rfl⟩⟩

theorem step432_verified : Checked step432 :=
  ⟨step432_nodes, Research6966.HelperWindowCatalogue.moment4186_906,
    (by decide), (by decide), (by decide), step432_cover⟩

def step433 : Request :=
  ⟨⟨⟨3500, 4883, 1057, 91474⟩, 1289556817346560, 15600507702257⟩, 103, 5, 2, 642859⟩

theorem step433_nodes : P1_7_1.nodeRows step433.bank.shape = step433.bank.nodeRows :=
  node_check step433.bank (by decide) (by decide) (by decide)

private theorem step433_2330_2347 : Positive step433 2330 2347 := by decide +kernel

private theorem step433_2348_2394 : Positive step433 2348 2394 := by decide +kernel

private theorem step433_2395_2499 : Positive step433 2395 2499 := by decide +kernel

theorem step433_cover : ∃ ends, Cover step433 firstHeight ends := by
  exact ⟨[2347, 2394, 2499],
    ⟨(by decide), (by decide), step433_2330_2347,
      (by decide), (by decide), step433_2348_2394,
      (by decide), (by decide), step433_2395_2499, rfl⟩⟩

theorem step433_verified : Checked step433 :=
  ⟨step433_nodes, Research6966.HelperWindowCatalogue.moment4883_1057,
    (by decide), (by decide), (by decide), step433_cover⟩

def step434 : Request :=
  ⟨⟨⟨294, 410, 91, 7715⟩, 790165454848, 805457011⟩, 0, 5, 4, 642859⟩

theorem step434_nodes : P1_7_1.nodeRows step434.bank.shape = step434.bank.nodeRows :=
  node_check step434.bank (by decide) (by decide) (by decide)

private theorem step434_2330_2332 : Positive step434 2330 2332 := by decide +kernel

private theorem step434_2333_2342 : Positive step434 2333 2342 := by decide +kernel

private theorem step434_2343_2375 : Positive step434 2343 2375 := by decide +kernel

private theorem step434_2376_2485 : Positive step434 2376 2485 := by decide +kernel

private theorem step434_2486_2499 : Positive step434 2486 2499 := by decide +kernel

theorem step434_cover : ∃ ends, Cover step434 firstHeight ends := by
  exact ⟨[2332, 2342, 2375, 2485, 2499],
    ⟨(by decide), (by decide), step434_2330_2332,
      (by decide), (by decide), step434_2333_2342,
      (by decide), (by decide), step434_2343_2375,
      (by decide), (by decide), step434_2376_2485,
      (by decide), (by decide), step434_2486_2499, rfl⟩⟩

theorem step434_verified : Checked step434 :=
  ⟨step434_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step434_cover⟩

def step435 : Request :=
  ⟨⟨⟨420, 586, 130, 7715⟩, 2292767784960, 3339653140⟩, 1, 5, 4, 642859⟩

theorem step435_nodes : P1_7_1.nodeRows step435.bank.shape = step435.bank.nodeRows :=
  node_check step435.bank (by decide) (by decide) (by decide)

private theorem step435_2330_2331 : Positive step435 2330 2331 := by decide +kernel

private theorem step435_2332_2337 : Positive step435 2332 2337 := by decide +kernel

private theorem step435_2338_2356 : Positive step435 2338 2356 := by decide +kernel

private theorem step435_2357_2413 : Positive step435 2357 2413 := by decide +kernel

private theorem step435_2414_2499 : Positive step435 2414 2499 := by decide +kernel

theorem step435_cover : ∃ ends, Cover step435 firstHeight ends := by
  exact ⟨[2331, 2337, 2356, 2413, 2499],
    ⟨(by decide), (by decide), step435_2330_2331,
      (by decide), (by decide), step435_2332_2337,
      (by decide), (by decide), step435_2338_2356,
      (by decide), (by decide), step435_2357_2413,
      (by decide), (by decide), step435_2414_2499, rfl⟩⟩

theorem step435_verified : Checked step435 :=
  ⟨step435_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step435_cover⟩

def step436 : Request :=
  ⟨⟨⟨420, 586, 127, 8679⟩, 2252760678400, 3279920952⟩, 2, 5, 4, 642859⟩

theorem step436_nodes : P1_7_1.nodeRows step436.bank.shape = step436.bank.nodeRows :=
  node_check step436.bank (by decide) (by decide) (by decide)

private theorem step436_2330_2334 : Positive step436 2330 2334 := by decide +kernel

private theorem step436_2335_2349 : Positive step436 2335 2349 := by decide +kernel

private theorem step436_2350_2395 : Positive step436 2350 2395 := by decide +kernel

private theorem step436_2396_2499 : Positive step436 2396 2499 := by decide +kernel

theorem step436_cover : ∃ ends, Cover step436 firstHeight ends := by
  exact ⟨[2334, 2349, 2395, 2499],
    ⟨(by decide), (by decide), step436_2330_2334,
      (by decide), (by decide), step436_2335_2349,
      (by decide), (by decide), step436_2350_2395,
      (by decide), (by decide), step436_2396_2499, rfl⟩⟩

theorem step436_verified : Checked step436 :=
  ⟨step436_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step436_cover⟩

def step437 : Request :=
  ⟨⟨⟨420, 586, 127, 9763⟩, 2252760678400, 3279920952⟩, 3, 5, 4, 642859⟩

theorem step437_nodes : P1_7_1.nodeRows step437.bank.shape = step437.bank.nodeRows :=
  node_check step437.bank (by decide) (by decide) (by decide)

private theorem step437_2330_2339 : Positive step437 2330 2339 := by decide +kernel

private theorem step437_2340_2370 : Positive step437 2340 2370 := by decide +kernel

private theorem step437_2371_2466 : Positive step437 2371 2466 := by decide +kernel

private theorem step437_2467_2499 : Positive step437 2467 2499 := by decide +kernel

theorem step437_cover : ∃ ends, Cover step437 firstHeight ends := by
  exact ⟨[2339, 2370, 2466, 2499],
    ⟨(by decide), (by decide), step437_2330_2339,
      (by decide), (by decide), step437_2340_2370,
      (by decide), (by decide), step437_2371_2466,
      (by decide), (by decide), step437_2467_2499, rfl⟩⟩

theorem step437_verified : Checked step437 :=
  ⟨step437_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step437_cover⟩

def step438 : Request :=
  ⟨⟨⟨520, 725, 161, 9763⟩, 4343013310464, 7809559934⟩, 4, 5, 4, 642859⟩

theorem step438_nodes : P1_7_1.nodeRows step438.bank.shape = step438.bank.nodeRows :=
  node_check step438.bank (by decide) (by decide) (by decide)

private theorem step438_2330_2333 : Positive step438 2330 2333 := by decide +kernel

private theorem step438_2334_2345 : Positive step438 2334 2345 := by decide +kernel

private theorem step438_2346_2380 : Positive step438 2346 2380 := by decide +kernel

private theorem step438_2381_2483 : Positive step438 2381 2483 := by decide +kernel

private theorem step438_2484_2499 : Positive step438 2484 2499 := by decide +kernel

theorem step438_cover : ∃ ends, Cover step438 firstHeight ends := by
  exact ⟨[2333, 2345, 2380, 2483, 2499],
    ⟨(by decide), (by decide), step438_2330_2333,
      (by decide), (by decide), step438_2334_2345,
      (by decide), (by decide), step438_2346_2380,
      (by decide), (by decide), step438_2381_2483,
      (by decide), (by decide), step438_2484_2499, rfl⟩⟩

theorem step438_verified : Checked step438 :=
  ⟨step438_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step438_cover⟩

def step439 : Request :=
  ⟨⟨⟨520, 725, 157, 10983⟩, 4261264752640, 7658911630⟩, 5, 5, 4, 642859⟩

theorem step439_nodes : P1_7_1.nodeRows step439.bank.shape = step439.bank.nodeRows :=
  node_check step439.bank (by decide) (by decide) (by decide)

private theorem step439_2330_2340 : Positive step439 2330 2340 := by decide +kernel

private theorem step439_2341_2373 : Positive step439 2341 2373 := by decide +kernel

private theorem step439_2374_2471 : Positive step439 2374 2471 := by decide +kernel

private theorem step439_2472_2499 : Positive step439 2472 2499 := by decide +kernel

theorem step439_cover : ∃ ends, Cover step439 firstHeight ends := by
  exact ⟨[2340, 2373, 2471, 2499],
    ⟨(by decide), (by decide), step439_2330_2340,
      (by decide), (by decide), step439_2341_2373,
      (by decide), (by decide), step439_2374_2471,
      (by decide), (by decide), step439_2472_2499, rfl⟩⟩

theorem step439_verified : Checked step439 :=
  ⟨step439_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step439_cover⟩

def step440 : Request :=
  ⟨⟨⟨520, 725, 161, 12355⟩, 4343013310464, 7809559934⟩, 7, 5, 4, 642859⟩

theorem step440_nodes : P1_7_1.nodeRows step440.bank.shape = step440.bank.nodeRows :=
  node_check step440.bank (by decide) (by decide) (by decide)

private theorem step440_2330_2330 : Positive step440 2330 2330 := by decide +kernel

private theorem step440_2331_2333 : Positive step440 2331 2333 := by decide +kernel

private theorem step440_2334_2342 : Positive step440 2334 2342 := by decide +kernel

private theorem step440_2343_2368 : Positive step440 2343 2368 := by decide +kernel

private theorem step440_2369_2444 : Positive step440 2369 2444 := by decide +kernel

private theorem step440_2445_2499 : Positive step440 2445 2499 := by decide +kernel

theorem step440_cover : ∃ ends, Cover step440 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2368, 2444, 2499],
    ⟨(by decide), (by decide), step440_2330_2330,
      (by decide), (by decide), step440_2331_2333,
      (by decide), (by decide), step440_2334_2342,
      (by decide), (by decide), step440_2343_2368,
      (by decide), (by decide), step440_2369_2444,
      (by decide), (by decide), step440_2445_2499, rfl⟩⟩

theorem step440_verified : Checked step440 :=
  ⟨step440_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step440_cover⟩

def step441 : Request :=
  ⟨⟨⟨750, 1046, 232, 13899⟩, 12985818152960, 33687112323⟩, 10, 5, 4, 642859⟩

theorem step441_nodes : P1_7_1.nodeRows step441.bank.shape = step441.bank.nodeRows :=
  node_check step441.bank (by decide) (by decide) (by decide)

private theorem step441_2330_2335 : Positive step441 2330 2335 := by decide +kernel

private theorem step441_2336_2352 : Positive step441 2336 2352 := by decide +kernel

private theorem step441_2353_2399 : Positive step441 2353 2399 := by decide +kernel

private theorem step441_2400_2499 : Positive step441 2400 2499 := by decide +kernel

theorem step441_cover : ∃ ends, Cover step441 firstHeight ends := by
  exact ⟨[2335, 2352, 2399, 2499],
    ⟨(by decide), (by decide), step441_2330_2335,
      (by decide), (by decide), step441_2336_2352,
      (by decide), (by decide), step441_2353_2399,
      (by decide), (by decide), step441_2400_2499, rfl⟩⟩

theorem step441_verified : Checked step441 :=
  ⟨step441_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step441_cover⟩

def step442 : Request :=
  ⟨⟨⟨750, 1046, 232, 19788⟩, 12985818152960, 33687112323⟩, 16, 5, 4, 642859⟩

theorem step442_nodes : P1_7_1.nodeRows step442.bank.shape = step442.bank.nodeRows :=
  node_check step442.bank (by decide) (by decide) (by decide)

private theorem step442_2330_2335 : Positive step442 2330 2335 := by decide +kernel

private theorem step442_2336_2352 : Positive step442 2336 2352 := by decide +kernel

private theorem step442_2353_2400 : Positive step442 2353 2400 := by decide +kernel

private theorem step442_2401_2499 : Positive step442 2401 2499 := by decide +kernel

theorem step442_cover : ∃ ends, Cover step442 firstHeight ends := by
  exact ⟨[2335, 2352, 2400, 2499],
    ⟨(by decide), (by decide), step442_2330_2335,
      (by decide), (by decide), step442_2336_2352,
      (by decide), (by decide), step442_2353_2400,
      (by decide), (by decide), step442_2401_2499, rfl⟩⟩

theorem step442_verified : Checked step442 :=
  ⟨step442_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step442_cover⟩

def step443 : Request :=
  ⟨⟨⟨900, 1256, 279, 22261⟩, 22452680785920, 70021105933⟩, 20, 5, 4, 642859⟩

theorem step443_nodes : P1_7_1.nodeRows step443.bank.shape = step443.bank.nodeRows :=
  node_check step443.bank (by decide) (by decide) (by decide)

private theorem step443_2330_2337 : Positive step443 2330 2337 := by decide +kernel

private theorem step443_2338_2359 : Positive step443 2338 2359 := by decide +kernel

private theorem step443_2360_2420 : Positive step443 2360 2420 := by decide +kernel

private theorem step443_2421_2499 : Positive step443 2421 2499 := by decide +kernel

theorem step443_cover : ∃ ends, Cover step443 firstHeight ends := by
  exact ⟨[2337, 2359, 2420, 2499],
    ⟨(by decide), (by decide), step443_2330_2337,
      (by decide), (by decide), step443_2338_2359,
      (by decide), (by decide), step443_2360_2420,
      (by decide), (by decide), step443_2421_2499, rfl⟩⟩

theorem step443_verified : Checked step443 :=
  ⟨step443_nodes, Research6966.HelperWindowCatalogue.moment1256_279,
    (by decide), (by decide), (by decide), step443_cover⟩

def step444 : Request :=
  ⟨⟨⟨1650, 2302, 512, 28173⟩, 138129879859200, 788519769358⟩, 31, 5, 4, 642859⟩

theorem step444_nodes : P1_7_1.nodeRows step444.bank.shape = step444.bank.nodeRows :=
  node_check step444.bank (by decide) (by decide) (by decide)

private theorem step444_2330_2332 : Positive step444 2330 2332 := by decide +kernel

private theorem step444_2333_2339 : Positive step444 2333 2339 := by decide +kernel

private theorem step444_2340_2358 : Positive step444 2340 2358 := by decide +kernel

private theorem step444_2359_2408 : Positive step444 2359 2408 := by decide +kernel

private theorem step444_2409_2499 : Positive step444 2409 2499 := by decide +kernel

theorem step444_cover : ∃ ends, Cover step444 firstHeight ends := by
  exact ⟨[2332, 2339, 2358, 2408, 2499],
    ⟨(by decide), (by decide), step444_2330_2332,
      (by decide), (by decide), step444_2333_2339,
      (by decide), (by decide), step444_2340_2358,
      (by decide), (by decide), step444_2359_2408,
      (by decide), (by decide), step444_2409_2499, rfl⟩⟩

theorem step444_verified : Checked step444 :=
  ⟨step444_nodes, Research6966.HelperWindowCatalogue.moment2302_512,
    (by decide), (by decide), (by decide), step444_cover⟩

def step445 : Request :=
  ⟨⟨⟨1350, 1883, 408, 31694⟩, 74202776600576, 346190054868⟩, 32, 5, 4, 642859⟩

theorem step445_nodes : P1_7_1.nodeRows step445.bank.shape = step445.bank.nodeRows :=
  node_check step445.bank (by decide) (by decide) (by decide)

private theorem step445_2330_2347 : Positive step445 2330 2347 := by decide +kernel

private theorem step445_2348_2396 : Positive step445 2348 2396 := by decide +kernel

private theorem step445_2397_2499 : Positive step445 2397 2499 := by decide +kernel

theorem step445_cover : ∃ ends, Cover step445 firstHeight ends := by
  exact ⟨[2347, 2396, 2499],
    ⟨(by decide), (by decide), step445_2330_2347,
      (by decide), (by decide), step445_2348_2396,
      (by decide), (by decide), step445_2397_2499, rfl⟩⟩

theorem step445_verified : Checked step445 :=
  ⟨step445_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step445_cover⟩

def step446 : Request :=
  ⟨⟨⟨1650, 2302, 498, 40111⟩, 135254251667456, 771697512616⟩, 44, 5, 4, 642859⟩

theorem step446_nodes : P1_7_1.nodeRows step446.bank.shape = step446.bank.nodeRows :=
  node_check step446.bank (by decide) (by decide) (by decide)

private theorem step446_2330_2332 : Positive step446 2330 2332 := by decide +kernel

private theorem step446_2333_2340 : Positive step446 2333 2340 := by decide +kernel

private theorem step446_2341_2361 : Positive step446 2341 2361 := by decide +kernel

private theorem step446_2362_2417 : Positive step446 2362 2417 := by decide +kernel

private theorem step446_2418_2499 : Positive step446 2418 2499 := by decide +kernel

theorem step446_cover : ∃ ends, Cover step446 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2417, 2499],
    ⟨(by decide), (by decide), step446_2330_2332,
      (by decide), (by decide), step446_2333_2340,
      (by decide), (by decide), step446_2341_2361,
      (by decide), (by decide), step446_2362_2417,
      (by decide), (by decide), step446_2418_2499, rfl⟩⟩

theorem step446_verified : Checked step446 :=
  ⟨step446_nodes, Research6966.HelperWindowCatalogue.moment2302_498,
    (by decide), (by decide), (by decide), step446_cover⟩

def step447 : Request :=
  ⟨⟨⟨3000, 4186, 930, 57109⟩, 828559354757120, 8600191575129⟩, 73, 5, 4, 642859⟩

theorem step447_nodes : P1_7_1.nodeRows step447.bank.shape = step447.bank.nodeRows :=
  node_check step447.bank (by decide) (by decide) (by decide)

private theorem step447_2330_2336 : Positive step447 2330 2336 := by decide +kernel

private theorem step447_2337_2354 : Positive step447 2337 2354 := by decide +kernel

private theorem step447_2355_2401 : Positive step447 2355 2401 := by decide +kernel

private theorem step447_2402_2499 : Positive step447 2402 2499 := by decide +kernel

theorem step447_cover : ∃ ends, Cover step447 firstHeight ends := by
  exact ⟨[2336, 2354, 2401, 2499],
    ⟨(by decide), (by decide), step447_2330_2336,
      (by decide), (by decide), step447_2337_2354,
      (by decide), (by decide), step447_2355_2401,
      (by decide), (by decide), step447_2402_2499, rfl⟩⟩

theorem step447_verified : Checked step447 :=
  ⟨step447_nodes, Research6966.HelperWindowCatalogue.moment4186_930,
    (by decide), (by decide), (by decide), step447_cover⟩

def step448 : Request :=
  ⟨⟨⟨2500, 3488, 775, 64247⟩, 479640131993600, 4147842034257⟩, 76, 5, 4, 642859⟩

theorem step448_nodes : P1_7_1.nodeRows step448.bank.shape = step448.bank.nodeRows :=
  node_check step448.bank (by decide) (by decide) (by decide)

private theorem step448_2330_2337 : Positive step448 2330 2337 := by decide +kernel

private theorem step448_2338_2358 : Positive step448 2338 2358 := by decide +kernel

private theorem step448_2359_2413 : Positive step448 2359 2413 := by decide +kernel

private theorem step448_2414_2499 : Positive step448 2414 2499 := by decide +kernel

theorem step448_cover : ∃ ends, Cover step448 firstHeight ends := by
  exact ⟨[2337, 2358, 2413, 2499],
    ⟨(by decide), (by decide), step448_2330_2337,
      (by decide), (by decide), step448_2338_2358,
      (by decide), (by decide), step448_2359_2413,
      (by decide), (by decide), step448_2414_2499, rfl⟩⟩

theorem step448_verified : Checked step448 :=
  ⟨step448_nodes, Research6966.HelperWindowCatalogue.moment3488_775,
    (by decide), (by decide), (by decide), step448_cover⟩

def step449 : Request :=
  ⟨⟨⟨3500, 4883, 1085, 81311⟩, 1315428062986240, 15921388386716⟩, 103, 5, 4, 642859⟩

theorem step449_nodes : P1_7_1.nodeRows step449.bank.shape = step449.bank.nodeRows :=
  node_check step449.bank (by decide) (by decide) (by decide)

private theorem step449_2330_2338 : Positive step449 2330 2338 := by decide +kernel

private theorem step449_2339_2362 : Positive step449 2339 2362 := by decide +kernel

private theorem step449_2363_2424 : Positive step449 2363 2424 := by decide +kernel

private theorem step449_2425_2499 : Positive step449 2425 2499 := by decide +kernel

theorem step449_cover : ∃ ends, Cover step449 firstHeight ends := by
  exact ⟨[2338, 2362, 2424, 2499],
    ⟨(by decide), (by decide), step449_2330_2338,
      (by decide), (by decide), step449_2339_2362,
      (by decide), (by decide), step449_2363_2424,
      (by decide), (by decide), step449_2425_2499, rfl⟩⟩

theorem step449_verified : Checked step449 :=
  ⟨step449_nodes, Research6966.HelperWindowCatalogue.moment4883_1085,
    (by decide), (by decide), (by decide), step449_cover⟩

def step450 : Request :=
  ⟨⟨⟨294, 410, 89, 6858⟩, 777085255680, 791788817⟩, 0, 5, 9, 642859⟩

theorem step450_nodes : P1_7_1.nodeRows step450.bank.shape = step450.bank.nodeRows :=
  node_check step450.bank (by decide) (by decide) (by decide)

private theorem step450_2330_2335 : Positive step450 2330 2335 := by decide +kernel

private theorem step450_2336_2355 : Positive step450 2336 2355 := by decide +kernel

private theorem step450_2356_2422 : Positive step450 2356 2422 := by decide +kernel

private theorem step450_2423_2499 : Positive step450 2423 2499 := by decide +kernel

theorem step450_cover : ∃ ends, Cover step450 firstHeight ends := by
  exact ⟨[2335, 2355, 2422, 2499],
    ⟨(by decide), (by decide), step450_2330_2335,
      (by decide), (by decide), step450_2336_2355,
      (by decide), (by decide), step450_2356_2422,
      (by decide), (by decide), step450_2423_2499, rfl⟩⟩

theorem step450_verified : Checked step450 :=
  ⟨step450_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step450_cover⟩

def step451 : Request :=
  ⟨⟨⟨420, 586, 127, 6858⟩, 2252760678400, 3279920952⟩, 1, 5, 9, 642859⟩

theorem step451_nodes : P1_7_1.nodeRows step451.bank.shape = step451.bank.nodeRows :=
  node_check step451.bank (by decide) (by decide) (by decide)

private theorem step451_2330_2333 : Positive step451 2330 2333 := by decide +kernel

private theorem step451_2334_2345 : Positive step451 2334 2345 := by decide +kernel

private theorem step451_2346_2382 : Positive step451 2346 2382 := by decide +kernel

private theorem step451_2383_2496 : Positive step451 2383 2496 := by decide +kernel

private theorem step451_2497_2499 : Positive step451 2497 2499 := by decide +kernel

theorem step451_cover : ∃ ends, Cover step451 firstHeight ends := by
  exact ⟨[2333, 2345, 2382, 2496, 2499],
    ⟨(by decide), (by decide), step451_2330_2333,
      (by decide), (by decide), step451_2334_2345,
      (by decide), (by decide), step451_2346_2382,
      (by decide), (by decide), step451_2383_2496,
      (by decide), (by decide), step451_2497_2499, rfl⟩⟩

theorem step451_verified : Checked step451 :=
  ⟨step451_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step451_cover⟩

def step452 : Request :=
  ⟨⟨⟨420, 586, 127, 7715⟩, 2252760678400, 3279920952⟩, 2, 5, 9, 642859⟩

theorem step452_nodes : P1_7_1.nodeRows step452.bank.shape = step452.bank.nodeRows :=
  node_check step452.bank (by decide) (by decide) (by decide)

private theorem step452_2330_2344 : Positive step452 2330 2344 := by decide +kernel

private theorem step452_2345_2391 : Positive step452 2345 2391 := by decide +kernel

private theorem step452_2392_2499 : Positive step452 2392 2499 := by decide +kernel

theorem step452_cover : ∃ ends, Cover step452 firstHeight ends := by
  exact ⟨[2344, 2391, 2499],
    ⟨(by decide), (by decide), step452_2330_2344,
      (by decide), (by decide), step452_2345_2391,
      (by decide), (by decide), step452_2392_2499, rfl⟩⟩

theorem step452_verified : Checked step452 :=
  ⟨step452_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step452_cover⟩

def step453 : Request :=
  ⟨⟨⟨420, 586, 127, 8679⟩, 2252760678400, 3279920952⟩, 3, 5, 9, 642859⟩

theorem step453_nodes : P1_7_1.nodeRows step453.bank.shape = step453.bank.nodeRows :=
  node_check step453.bank (by decide) (by decide) (by decide)

private theorem step453_2330_2350 : Positive step453 2330 2350 := by decide +kernel

private theorem step453_2351_2414 : Positive step453 2351 2414 := by decide +kernel

private theorem step453_2415_2499 : Positive step453 2415 2499 := by decide +kernel

theorem step453_cover : ∃ ends, Cover step453 firstHeight ends := by
  exact ⟨[2350, 2414, 2499],
    ⟨(by decide), (by decide), step453_2330_2350,
      (by decide), (by decide), step453_2351_2414,
      (by decide), (by decide), step453_2415_2499, rfl⟩⟩

theorem step453_verified : Checked step453 :=
  ⟨step453_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step453_cover⟩

def step454 : Request :=
  ⟨⟨⟨420, 586, 127, 9763⟩, 2252760678400, 3279920952⟩, 4, 5, 9, 642859⟩

theorem step454_nodes : P1_7_1.nodeRows step454.bank.shape = step454.bank.nodeRows :=
  node_check step454.bank (by decide) (by decide) (by decide)

private theorem step454_2330_2349 : Positive step454 2330 2349 := by decide +kernel

private theorem step454_2350_2411 : Positive step454 2350 2411 := by decide +kernel

private theorem step454_2412_2499 : Positive step454 2412 2499 := by decide +kernel

theorem step454_cover : ∃ ends, Cover step454 firstHeight ends := by
  exact ⟨[2349, 2411, 2499],
    ⟨(by decide), (by decide), step454_2330_2349,
      (by decide), (by decide), step454_2350_2411,
      (by decide), (by decide), step454_2412_2499, rfl⟩⟩

theorem step454_verified : Checked step454 :=
  ⟨step454_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step454_cover⟩

def step455 : Request :=
  ⟨⟨⟨420, 586, 127, 10983⟩, 2252760678400, 3279920952⟩, 5, 5, 9, 642859⟩

theorem step455_nodes : P1_7_1.nodeRows step455.bank.shape = step455.bank.nodeRows :=
  node_check step455.bank (by decide) (by decide) (by decide)

private theorem step455_2330_2344 : Positive step455 2330 2344 := by decide +kernel

private theorem step455_2345_2390 : Positive step455 2345 2390 := by decide +kernel

private theorem step455_2391_2499 : Positive step455 2391 2499 := by decide +kernel

theorem step455_cover : ∃ ends, Cover step455 firstHeight ends := by
  exact ⟨[2344, 2390, 2499],
    ⟨(by decide), (by decide), step455_2330_2344,
      (by decide), (by decide), step455_2345_2390,
      (by decide), (by decide), step455_2391_2499, rfl⟩⟩

theorem step455_verified : Checked step455 :=
  ⟨step455_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step455_cover⟩

def step456 : Request :=
  ⟨⟨⟨520, 725, 161, 10983⟩, 4343013310464, 7809559934⟩, 7, 5, 9, 642859⟩

theorem step456_nodes : P1_7_1.nodeRows step456.bank.shape = step456.bank.nodeRows :=
  node_check step456.bank (by decide) (by decide) (by decide)

private theorem step456_2330_2340 : Positive step456 2330 2340 := by decide +kernel

private theorem step456_2341_2373 : Positive step456 2341 2373 := by decide +kernel

private theorem step456_2374_2470 : Positive step456 2374 2470 := by decide +kernel

private theorem step456_2471_2499 : Positive step456 2471 2499 := by decide +kernel

theorem step456_cover : ∃ ends, Cover step456 firstHeight ends := by
  exact ⟨[2340, 2373, 2470, 2499],
    ⟨(by decide), (by decide), step456_2330_2340,
      (by decide), (by decide), step456_2341_2373,
      (by decide), (by decide), step456_2374_2470,
      (by decide), (by decide), step456_2471_2499, rfl⟩⟩

theorem step456_verified : Checked step456 :=
  ⟨step456_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step456_cover⟩

def step457 : Request :=
  ⟨⟨⟨630, 879, 195, 12355⟩, 7709474160640, 16827402390⟩, 10, 5, 9, 642859⟩

theorem step457_nodes : P1_7_1.nodeRows step457.bank.shape = step457.bank.nodeRows :=
  node_check step457.bank (by decide) (by decide) (by decide)

private theorem step457_2330_2330 : Positive step457 2330 2330 := by decide +kernel

private theorem step457_2331_2333 : Positive step457 2331 2333 := by decide +kernel

private theorem step457_2334_2342 : Positive step457 2334 2342 := by decide +kernel

private theorem step457_2343_2367 : Positive step457 2343 2367 := by decide +kernel

private theorem step457_2368_2439 : Positive step457 2368 2439 := by decide +kernel

private theorem step457_2440_2499 : Positive step457 2440 2499 := by decide +kernel

theorem step457_cover : ∃ ends, Cover step457 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2367, 2439, 2499],
    ⟨(by decide), (by decide), step457_2330_2330,
      (by decide), (by decide), step457_2331_2333,
      (by decide), (by decide), step457_2334_2342,
      (by decide), (by decide), step457_2343_2367,
      (by decide), (by decide), step457_2368_2439,
      (by decide), (by decide), step457_2440_2499, rfl⟩⟩

theorem step457_verified : Checked step457 :=
  ⟨step457_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step457_cover⟩

def step458 : Request :=
  ⟨⟨⟨900, 1256, 279, 15636⟩, 22452680785920, 70021105933⟩, 16, 5, 9, 642859⟩

theorem step458_nodes : P1_7_1.nodeRows step458.bank.shape = step458.bank.nodeRows :=
  node_check step458.bank (by decide) (by decide) (by decide)

private theorem step458_2330_2333 : Positive step458 2330 2333 := by decide +kernel

private theorem step458_2334_2344 : Positive step458 2334 2344 := by decide +kernel

private theorem step458_2345_2374 : Positive step458 2345 2374 := by decide +kernel

private theorem step458_2375_2457 : Positive step458 2375 2457 := by decide +kernel

private theorem step458_2458_2499 : Positive step458 2458 2499 := by decide +kernel

theorem step458_cover : ∃ ends, Cover step458 firstHeight ends := by
  exact ⟨[2333, 2344, 2374, 2457, 2499],
    ⟨(by decide), (by decide), step458_2330_2333,
      (by decide), (by decide), step458_2334_2344,
      (by decide), (by decide), step458_2345_2374,
      (by decide), (by decide), step458_2375_2457,
      (by decide), (by decide), step458_2458_2499, rfl⟩⟩

theorem step458_verified : Checked step458 :=
  ⟨step458_nodes, Research6966.HelperWindowCatalogue.moment1256_279,
    (by decide), (by decide), (by decide), step458_cover⟩

def step459 : Request :=
  ⟨⟨⟨900, 1256, 272, 19788⟩, 22024701870080, 68653176066⟩, 20, 5, 9, 642859⟩

theorem step459_nodes : P1_7_1.nodeRows step459.bank.shape = step459.bank.nodeRows :=
  node_check step459.bank (by decide) (by decide) (by decide)

private theorem step459_2330_2334 : Positive step459 2330 2334 := by decide +kernel

private theorem step459_2335_2348 : Positive step459 2335 2348 := by decide +kernel

private theorem step459_2349_2387 : Positive step459 2349 2387 := by decide +kernel

private theorem step459_2388_2495 : Positive step459 2388 2495 := by decide +kernel

private theorem step459_2496_2499 : Positive step459 2496 2499 := by decide +kernel

theorem step459_cover : ∃ ends, Cover step459 firstHeight ends := by
  exact ⟨[2334, 2348, 2387, 2495, 2499],
    ⟨(by decide), (by decide), step459_2330_2334,
      (by decide), (by decide), step459_2335_2348,
      (by decide), (by decide), step459_2349_2387,
      (by decide), (by decide), step459_2388_2495,
      (by decide), (by decide), step459_2496_2499, rfl⟩⟩

theorem step459_verified : Checked step459 :=
  ⟨step459_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step459_cover⟩

def step460 : Request :=
  ⟨⟨⟨1100, 1534, 341, 28173⟩, 40955142733824, 155702293064⟩, 31, 5, 9, 642859⟩

theorem step460_nodes : P1_7_1.nodeRows step460.bank.shape = step460.bank.nodeRows :=
  node_check step460.bank (by decide) (by decide) (by decide)

private theorem step460_2330_2330 : Positive step460 2330 2330 := by decide +kernel

private theorem step460_2331_2332 : Positive step460 2331 2332 := by decide +kernel

private theorem step460_2333_2338 : Positive step460 2333 2338 := by decide +kernel

private theorem step460_2339_2354 : Positive step460 2339 2354 := by decide +kernel

private theorem step460_2355_2397 : Positive step460 2355 2397 := by decide +kernel

private theorem step460_2398_2499 : Positive step460 2398 2499 := by decide +kernel

theorem step460_cover : ∃ ends, Cover step460 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2354, 2397, 2499],
    ⟨(by decide), (by decide), step460_2330_2330,
      (by decide), (by decide), step460_2331_2332,
      (by decide), (by decide), step460_2333_2338,
      (by decide), (by decide), step460_2339_2354,
      (by decide), (by decide), step460_2355_2397,
      (by decide), (by decide), step460_2398_2499, rfl⟩⟩

theorem step460_verified : Checked step460 :=
  ⟨step460_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step460_cover⟩

def step461 : Request :=
  ⟨⟨⟨1100, 1534, 332, 31694⟩, 40133103452160, 152499774767⟩, 32, 5, 9, 642859⟩

theorem step461_nodes : P1_7_1.nodeRows step461.bank.shape = step461.bank.nodeRows :=
  node_check step461.bank (by decide) (by decide) (by decide)

private theorem step461_2330_2332 : Positive step461 2330 2332 := by decide +kernel

private theorem step461_2333_2341 : Positive step461 2333 2341 := by decide +kernel

private theorem step461_2342_2365 : Positive step461 2342 2365 := by decide +kernel

private theorem step461_2366_2431 : Positive step461 2366 2431 := by decide +kernel

private theorem step461_2432_2499 : Positive step461 2432 2499 := by decide +kernel

theorem step461_cover : ∃ ends, Cover step461 firstHeight ends := by
  exact ⟨[2332, 2341, 2365, 2431, 2499],
    ⟨(by decide), (by decide), step461_2330_2332,
      (by decide), (by decide), step461_2333_2341,
      (by decide), (by decide), step461_2342_2365,
      (by decide), (by decide), step461_2366_2431,
      (by decide), (by decide), step461_2432_2499, rfl⟩⟩

theorem step461_verified : Checked step461 :=
  ⟨step461_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step461_cover⟩

def step462 : Request :=
  ⟨⟨⟨1650, 2302, 498, 35655⟩, 135254251667456, 771697512616⟩, 44, 5, 9, 642859⟩

theorem step462_nodes : P1_7_1.nodeRows step462.bank.shape = step462.bank.nodeRows :=
  node_check step462.bank (by decide) (by decide) (by decide)

private theorem step462_2330_2340 : Positive step462 2330 2340 := by decide +kernel

private theorem step462_2341_2369 : Positive step462 2341 2369 := by decide +kernel

private theorem step462_2370_2447 : Positive step462 2370 2447 := by decide +kernel

private theorem step462_2448_2499 : Positive step462 2448 2499 := by decide +kernel

theorem step462_cover : ∃ ends, Cover step462 firstHeight ends := by
  exact ⟨[2340, 2369, 2447, 2499],
    ⟨(by decide), (by decide), step462_2330_2340,
      (by decide), (by decide), step462_2341_2369,
      (by decide), (by decide), step462_2370_2447,
      (by decide), (by decide), step462_2448_2499, rfl⟩⟩

theorem step462_verified : Checked step462 :=
  ⟨step462_nodes, Research6966.HelperWindowCatalogue.moment2302_498,
    (by decide), (by decide), (by decide), step462_cover⟩

def step463 : Request :=
  ⟨⟨⟨3000, 4186, 906, 50764⟩, 812266433019904, 8426888829858⟩, 73, 5, 9, 642859⟩

theorem step463_nodes : P1_7_1.nodeRows step463.bank.shape = step463.bank.nodeRows :=
  node_check step463.bank (by decide) (by decide) (by decide)

private theorem step463_2330_2332 : Positive step463 2330 2332 := by decide +kernel

private theorem step463_2333_2340 : Positive step463 2333 2340 := by decide +kernel

private theorem step463_2341_2361 : Positive step463 2341 2361 := by decide +kernel

private theorem step463_2362_2416 : Positive step463 2362 2416 := by decide +kernel

private theorem step463_2417_2499 : Positive step463 2417 2499 := by decide +kernel

theorem step463_cover : ∃ ends, Cover step463 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2416, 2499],
    ⟨(by decide), (by decide), step463_2330_2332,
      (by decide), (by decide), step463_2333_2340,
      (by decide), (by decide), step463_2341_2361,
      (by decide), (by decide), step463_2362_2416,
      (by decide), (by decide), step463_2417_2499, rfl⟩⟩

theorem step463_verified : Checked step463 :=
  ⟨step463_nodes, Research6966.HelperWindowCatalogue.moment4186_906,
    (by decide), (by decide), (by decide), step463_cover⟩

def step464 : Request :=
  ⟨⟨⟨3000, 4186, 930, 50764⟩, 828559354757120, 8600191575129⟩, 76, 5, 9, 642859⟩

theorem step464_nodes : P1_7_1.nodeRows step464.bank.shape = step464.bank.nodeRows :=
  node_check step464.bank (by decide) (by decide) (by decide)

private theorem step464_2330_2331 : Positive step464 2330 2331 := by decide +kernel

private theorem step464_2332_2336 : Positive step464 2332 2336 := by decide +kernel

private theorem step464_2337_2349 : Positive step464 2337 2349 := by decide +kernel

private theorem step464_2350_2383 : Positive step464 2350 2383 := by decide +kernel

private theorem step464_2384_2471 : Positive step464 2384 2471 := by decide +kernel

private theorem step464_2472_2499 : Positive step464 2472 2499 := by decide +kernel

theorem step464_cover : ∃ ends, Cover step464 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2471, 2499],
    ⟨(by decide), (by decide), step464_2330_2331,
      (by decide), (by decide), step464_2332_2336,
      (by decide), (by decide), step464_2337_2349,
      (by decide), (by decide), step464_2350_2383,
      (by decide), (by decide), step464_2384_2471,
      (by decide), (by decide), step464_2472_2499, rfl⟩⟩

theorem step464_verified : Checked step464 :=
  ⟨step464_nodes, Research6966.HelperWindowCatalogue.moment4186_930,
    (by decide), (by decide), (by decide), step464_cover⟩

end Research6966.HelperRescueCatalogue
