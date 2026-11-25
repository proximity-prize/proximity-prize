import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments11
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments12
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments9
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step305 : Request :=
  ⟨⟨⟨4500, 6279, 1332, 146522⟩, 2698317932789760, 41969435185037⟩, 103, 4, 4, 514287⟩

theorem step305_nodes : P1_7_1.nodeRows step305.bank.shape = step305.bank.nodeRows :=
  node_check step305.bank (by decide) (by decide) (by decide)

private theorem step305_2330_2334 : Positive step305 2330 2334 := by decide +kernel

private theorem step305_2335_2347 : Positive step305 2335 2347 := by decide +kernel

private theorem step305_2348_2381 : Positive step305 2348 2381 := by decide +kernel

private theorem step305_2382_2471 : Positive step305 2382 2471 := by decide +kernel

private theorem step305_2472_2499 : Positive step305 2472 2499 := by decide +kernel

theorem step305_cover : ∃ ends, Cover step305 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2471, 2499],
    ⟨(by decide), (by decide), step305_2330_2334,
      (by decide), (by decide), step305_2335_2347,
      (by decide), (by decide), step305_2348_2381,
      (by decide), (by decide), step305_2382_2471,
      (by decide), (by decide), step305_2472_2499, rfl⟩⟩

theorem step305_verified : Checked step305 :=
  ⟨step305_nodes, Research6966.HelperWindowCatalogue.moment6279_1332,
    (by decide), (by decide), (by decide), step305_cover⟩

def step306 : Request :=
  ⟨⟨⟨520, 726, 157, 9763⟩, 4261264752640, 7692905725⟩, 0, 4, 9, 514287⟩

theorem step306_nodes : P1_7_1.nodeRows step306.bank.shape = step306.bank.nodeRows :=
  node_check step306.bank (by decide) (by decide) (by decide)

private theorem step306_2330_2330 : Positive step306 2330 2330 := by decide +kernel

private theorem step306_2331_2333 : Positive step306 2331 2333 := by decide +kernel

private theorem step306_2334_2342 : Positive step306 2334 2342 := by decide +kernel

private theorem step306_2343_2368 : Positive step306 2343 2368 := by decide +kernel

private theorem step306_2369_2445 : Positive step306 2369 2445 := by decide +kernel

private theorem step306_2446_2499 : Positive step306 2446 2499 := by decide +kernel

theorem step306_cover : ∃ ends, Cover step306 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2368, 2445, 2499],
    ⟨(by decide), (by decide), step306_2330_2330,
      (by decide), (by decide), step306_2331_2333,
      (by decide), (by decide), step306_2334_2342,
      (by decide), (by decide), step306_2343_2368,
      (by decide), (by decide), step306_2369_2445,
      (by decide), (by decide), step306_2446_2499, rfl⟩⟩

theorem step306_verified : Checked step306 :=
  ⟨step306_nodes, Research6966.HelperWindowCatalogue.moment726_157,
    (by decide), (by decide), (by decide), step306_cover⟩

def step307 : Request :=
  ⟨⟨⟨520, 726, 157, 10983⟩, 4261264752640, 7692905725⟩, 1, 4, 9, 514287⟩

theorem step307_nodes : P1_7_1.nodeRows step307.bank.shape = step307.bank.nodeRows :=
  node_check step307.bank (by decide) (by decide) (by decide)

private theorem step307_2330_2339 : Positive step307 2330 2339 := by decide +kernel

private theorem step307_2340_2368 : Positive step307 2340 2368 := by decide +kernel

private theorem step307_2369_2454 : Positive step307 2369 2454 := by decide +kernel

private theorem step307_2455_2499 : Positive step307 2455 2499 := by decide +kernel

theorem step307_cover : ∃ ends, Cover step307 firstHeight ends := by
  exact ⟨[2339, 2368, 2454, 2499],
    ⟨(by decide), (by decide), step307_2330_2339,
      (by decide), (by decide), step307_2340_2368,
      (by decide), (by decide), step307_2369_2454,
      (by decide), (by decide), step307_2455_2499, rfl⟩⟩

theorem step307_verified : Checked step307 :=
  ⟨step307_nodes, Research6966.HelperWindowCatalogue.moment726_157,
    (by decide), (by decide), (by decide), step307_cover⟩

def step308 : Request :=
  ⟨⟨⟨520, 726, 157, 12355⟩, 4261264752640, 7692905725⟩, 2, 4, 9, 514287⟩

theorem step308_nodes : P1_7_1.nodeRows step308.bank.shape = step308.bank.nodeRows :=
  node_check step308.bank (by decide) (by decide) (by decide)

private theorem step308_2330_2343 : Positive step308 2330 2343 := by decide +kernel

private theorem step308_2344_2384 : Positive step308 2344 2384 := by decide +kernel

private theorem step308_2385_2499 : Positive step308 2385 2499 := by decide +kernel

theorem step308_cover : ∃ ends, Cover step308 firstHeight ends := by
  exact ⟨[2343, 2384, 2499],
    ⟨(by decide), (by decide), step308_2330_2343,
      (by decide), (by decide), step308_2344_2384,
      (by decide), (by decide), step308_2385_2499, rfl⟩⟩

theorem step308_verified : Checked step308 :=
  ⟨step308_nodes, Research6966.HelperWindowCatalogue.moment726_157,
    (by decide), (by decide), (by decide), step308_cover⟩

def step309 : Request :=
  ⟨⟨⟨520, 725, 157, 13899⟩, 4261264752640, 7658911630⟩, 3, 4, 9, 514287⟩

theorem step309_nodes : P1_7_1.nodeRows step309.bank.shape = step309.bank.nodeRows :=
  node_check step309.bank (by decide) (by decide) (by decide)

private theorem step309_2330_2344 : Positive step309 2330 2344 := by decide +kernel

private theorem step309_2345_2389 : Positive step309 2345 2389 := by decide +kernel

private theorem step309_2390_2499 : Positive step309 2390 2499 := by decide +kernel

theorem step309_cover : ∃ ends, Cover step309 firstHeight ends := by
  exact ⟨[2344, 2389, 2499],
    ⟨(by decide), (by decide), step309_2330_2344,
      (by decide), (by decide), step309_2345_2389,
      (by decide), (by decide), step309_2390_2499, rfl⟩⟩

theorem step309_verified : Checked step309 :=
  ⟨step309_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step309_cover⟩

def step310 : Request :=
  ⟨⟨⟨630, 879, 190, 13899⟩, 7559493713920, 16491913877⟩, 4, 4, 9, 514287⟩

theorem step310_nodes : P1_7_1.nodeRows step310.bank.shape = step310.bank.nodeRows :=
  node_check step310.bank (by decide) (by decide) (by decide)

private theorem step310_2330_2337 : Positive step310 2330 2337 := by decide +kernel

private theorem step310_2338_2360 : Positive step310 2338 2360 := by decide +kernel

private theorem step310_2361_2426 : Positive step310 2361 2426 := by decide +kernel

private theorem step310_2427_2499 : Positive step310 2427 2499 := by decide +kernel

theorem step310_cover : ∃ ends, Cover step310 firstHeight ends := by
  exact ⟨[2337, 2360, 2426, 2499],
    ⟨(by decide), (by decide), step310_2330_2337,
      (by decide), (by decide), step310_2338_2360,
      (by decide), (by decide), step310_2361_2426,
      (by decide), (by decide), step310_2427_2499, rfl⟩⟩

theorem step310_verified : Checked step310 :=
  ⟨step310_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step310_cover⟩

def step311 : Request :=
  ⟨⟨⟨630, 879, 190, 15636⟩, 7559493713920, 16491913877⟩, 5, 4, 9, 514287⟩

theorem step311_nodes : P1_7_1.nodeRows step311.bank.shape = step311.bank.nodeRows :=
  node_check step311.bank (by decide) (by decide) (by decide)

private theorem step311_2330_2345 : Positive step311 2330 2345 := by decide +kernel

private theorem step311_2346_2391 : Positive step311 2346 2391 := by decide +kernel

private theorem step311_2392_2499 : Positive step311 2392 2499 := by decide +kernel

theorem step311_cover : ∃ ends, Cover step311 firstHeight ends := by
  exact ⟨[2345, 2391, 2499],
    ⟨(by decide), (by decide), step311_2330_2345,
      (by decide), (by decide), step311_2346_2391,
      (by decide), (by decide), step311_2392_2499, rfl⟩⟩

theorem step311_verified : Checked step311 :=
  ⟨step311_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step311_cover⟩

def step312 : Request :=
  ⟨⟨⟨750, 1047, 222, 17590⟩, 12559140782080, 32653699308⟩, 7, 4, 9, 514287⟩

theorem step312_nodes : P1_7_1.nodeRows step312.bank.shape = step312.bank.nodeRows :=
  node_check step312.bank (by decide) (by decide) (by decide)

private theorem step312_2330_2331 : Positive step312 2330 2331 := by decide +kernel

private theorem step312_2332_2337 : Positive step312 2332 2337 := by decide +kernel

private theorem step312_2338_2354 : Positive step312 2338 2354 := by decide +kernel

private theorem step312_2355_2402 : Positive step312 2355 2402 := by decide +kernel

private theorem step312_2403_2499 : Positive step312 2403 2499 := by decide +kernel

theorem step312_cover : ∃ ends, Cover step312 firstHeight ends := by
  exact ⟨[2331, 2337, 2354, 2402, 2499],
    ⟨(by decide), (by decide), step312_2330_2331,
      (by decide), (by decide), step312_2332_2337,
      (by decide), (by decide), step312_2338_2354,
      (by decide), (by decide), step312_2355_2402,
      (by decide), (by decide), step312_2403_2499, rfl⟩⟩

theorem step312_verified : Checked step312 :=
  ⟨step312_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_1047_222),
    (by decide), (by decide), (by decide), step312_cover⟩

def step313 : Request :=
  ⟨⟨⟨900, 1256, 272, 19788⟩, 22024701870080, 68653176066⟩, 10, 4, 9, 514287⟩

theorem step313_nodes : P1_7_1.nodeRows step313.bank.shape = step313.bank.nodeRows :=
  node_check step313.bank (by decide) (by decide) (by decide)

private theorem step313_2330_2339 : Positive step313 2330 2339 := by decide +kernel

private theorem step313_2340_2367 : Positive step313 2340 2367 := by decide +kernel

private theorem step313_2368_2444 : Positive step313 2368 2444 := by decide +kernel

private theorem step313_2445_2499 : Positive step313 2445 2499 := by decide +kernel

theorem step313_cover : ∃ ends, Cover step313 firstHeight ends := by
  exact ⟨[2339, 2367, 2444, 2499],
    ⟨(by decide), (by decide), step313_2330_2339,
      (by decide), (by decide), step313_2340_2367,
      (by decide), (by decide), step313_2368_2444,
      (by decide), (by decide), step313_2445_2499, rfl⟩⟩

theorem step313_verified : Checked step313 :=
  ⟨step313_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step313_cover⟩

def step314 : Request :=
  ⟨⟨⟨1100, 1535, 341, 25043⟩, 40955142733824, 156029238110⟩, 16, 4, 9, 514287⟩

theorem step314_nodes : P1_7_1.nodeRows step314.bank.shape = step314.bank.nodeRows :=
  node_check step314.bank (by decide) (by decide) (by decide)

private theorem step314_2330_2331 : Positive step314 2330 2331 := by decide +kernel

private theorem step314_2332_2336 : Positive step314 2332 2336 := by decide +kernel

private theorem step314_2337_2350 : Positive step314 2337 2350 := by decide +kernel

private theorem step314_2351_2388 : Positive step314 2351 2388 := by decide +kernel

private theorem step314_2389_2491 : Positive step314 2389 2491 := by decide +kernel

private theorem step314_2492_2499 : Positive step314 2492 2499 := by decide +kernel

theorem step314_cover : ∃ ends, Cover step314 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2388, 2491, 2499],
    ⟨(by decide), (by decide), step314_2330_2331,
      (by decide), (by decide), step314_2332_2336,
      (by decide), (by decide), step314_2337_2350,
      (by decide), (by decide), step314_2351_2388,
      (by decide), (by decide), step314_2389_2491,
      (by decide), (by decide), step314_2492_2499, rfl⟩⟩

theorem step314_verified : Checked step314 :=
  ⟨step314_nodes, Research6966.HelperWindowCatalogue.moment1535_341,
    (by decide), (by decide), (by decide), step314_cover⟩

def step315 : Request :=
  ⟨⟨⟨1100, 1535, 341, 31694⟩, 40955142733824, 156029238110⟩, 20, 4, 9, 514287⟩

theorem step315_nodes : P1_7_1.nodeRows step315.bank.shape = step315.bank.nodeRows :=
  node_check step315.bank (by decide) (by decide) (by decide)

private theorem step315_2330_2332 : Positive step315 2330 2332 := by decide +kernel

private theorem step315_2333_2340 : Positive step315 2333 2340 := by decide +kernel

private theorem step315_2341_2361 : Positive step315 2341 2361 := by decide +kernel

private theorem step315_2362_2418 : Positive step315 2362 2418 := by decide +kernel

private theorem step315_2419_2499 : Positive step315 2419 2499 := by decide +kernel

theorem step315_cover : ∃ ends, Cover step315 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2418, 2499],
    ⟨(by decide), (by decide), step315_2330_2332,
      (by decide), (by decide), step315_2333_2340,
      (by decide), (by decide), step315_2341_2361,
      (by decide), (by decide), step315_2362_2418,
      (by decide), (by decide), step315_2419_2499, rfl⟩⟩

theorem step315_verified : Checked step315 :=
  ⟨step315_nodes, Research6966.HelperWindowCatalogue.moment1535_341,
    (by decide), (by decide), (by decide), step315_cover⟩

def step316 : Request :=
  ⟨⟨⟨1650, 2302, 512, 40111⟩, 138129879859200, 788519769358⟩, 31, 4, 9, 514287⟩

theorem step316_nodes : P1_7_1.nodeRows step316.bank.shape = step316.bank.nodeRows :=
  node_check step316.bank (by decide) (by decide) (by decide)

private theorem step316_2330_2332 : Positive step316 2330 2332 := by decide +kernel

private theorem step316_2333_2340 : Positive step316 2333 2340 := by decide +kernel

private theorem step316_2341_2361 : Positive step316 2341 2361 := by decide +kernel

private theorem step316_2362_2416 : Positive step316 2362 2416 := by decide +kernel

private theorem step316_2417_2499 : Positive step316 2417 2499 := by decide +kernel

theorem step316_cover : ∃ ends, Cover step316 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2416, 2499],
    ⟨(by decide), (by decide), step316_2330_2332,
      (by decide), (by decide), step316_2333_2340,
      (by decide), (by decide), step316_2341_2361,
      (by decide), (by decide), step316_2362_2416,
      (by decide), (by decide), step316_2417_2499, rfl⟩⟩

theorem step316_verified : Checked step316 :=
  ⟨step316_nodes, Research6966.HelperWindowCatalogue.moment2302_512,
    (by decide), (by decide), (by decide), step316_cover⟩

def step317 : Request :=
  ⟨⟨⟨2000, 2791, 604, 40111⟩, 240862397726720, 1666886727164⟩, 32, 4, 9, 514287⟩

theorem step317_nodes : P1_7_1.nodeRows step317.bank.shape = step317.bank.nodeRows :=
  node_check step317.bank (by decide) (by decide) (by decide)

private theorem step317_2330_2332 : Positive step317 2330 2332 := by decide +kernel

private theorem step317_2333_2340 : Positive step317 2333 2340 := by decide +kernel

private theorem step317_2341_2362 : Positive step317 2341 2362 := by decide +kernel

private theorem step317_2363_2420 : Positive step317 2363 2420 := by decide +kernel

private theorem step317_2421_2499 : Positive step317 2421 2499 := by decide +kernel

theorem step317_cover : ∃ ends, Cover step317 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2420, 2499],
    ⟨(by decide), (by decide), step317_2330_2332,
      (by decide), (by decide), step317_2333_2340,
      (by decide), (by decide), step317_2341_2362,
      (by decide), (by decide), step317_2363_2420,
      (by decide), (by decide), step317_2421_2499, rfl⟩⟩

theorem step317_verified : Checked step317 :=
  ⟨step317_nodes, Research6966.HelperWindowCatalogue.moment2791_604,
    (by decide), (by decide), (by decide), step317_cover⟩

def step318 : Request :=
  ⟨⟨⟨2500, 3489, 775, 50764⟩, 479640131993600, 4151672878537⟩, 44, 4, 9, 514287⟩

theorem step318_nodes : P1_7_1.nodeRows step318.bank.shape = step318.bank.nodeRows :=
  node_check step318.bank (by decide) (by decide) (by decide)

private theorem step318_2330_2333 : Positive step318 2330 2333 := by decide +kernel

private theorem step318_2334_2343 : Positive step318 2334 2343 := by decide +kernel

private theorem step318_2344_2369 : Positive step318 2344 2369 := by decide +kernel

private theorem step318_2370_2437 : Positive step318 2370 2437 := by decide +kernel

private theorem step318_2438_2499 : Positive step318 2438 2499 := by decide +kernel

theorem step318_cover : ∃ ends, Cover step318 firstHeight ends := by
  exact ⟨[2333, 2343, 2369, 2437, 2499],
    ⟨(by decide), (by decide), step318_2330_2333,
      (by decide), (by decide), step318_2334_2343,
      (by decide), (by decide), step318_2344_2369,
      (by decide), (by decide), step318_2370_2437,
      (by decide), (by decide), step318_2438_2499, rfl⟩⟩

theorem step318_verified : Checked step318 :=
  ⟨step318_nodes, Research6966.HelperWindowCatalogue.moment3489_775,
    (by decide), (by decide), (by decide), step318_cover⟩

def step319 : Request :=
  ⟨⟨⟨3500, 4884, 1057, 81311⟩, 1289556817346560, 15610792063730⟩, 73, 4, 9, 514287⟩

theorem step319_nodes : P1_7_1.nodeRows step319.bank.shape = step319.bank.nodeRows :=
  node_check step319.bank (by decide) (by decide) (by decide)

private theorem step319_2330_2335 : Positive step319 2330 2335 := by decide +kernel

private theorem step319_2336_2350 : Positive step319 2336 2350 := by decide +kernel

private theorem step319_2351_2389 : Positive step319 2351 2389 := by decide +kernel

private theorem step319_2390_2491 : Positive step319 2390 2491 := by decide +kernel

private theorem step319_2492_2499 : Positive step319 2492 2499 := by decide +kernel

theorem step319_cover : ∃ ends, Cover step319 firstHeight ends := by
  exact ⟨[2335, 2350, 2389, 2491, 2499],
    ⟨(by decide), (by decide), step319_2330_2335,
      (by decide), (by decide), step319_2336_2350,
      (by decide), (by decide), step319_2351_2389,
      (by decide), (by decide), step319_2390_2491,
      (by decide), (by decide), step319_2492_2499, rfl⟩⟩

theorem step319_verified : Checked step319 :=
  ⟨step319_nodes, Research6966.HelperWindowCatalogue.moment4884_1057,
    (by decide), (by decide), (by decide), step319_cover⟩

def step320 : Request :=
  ⟨⟨⟨4500, 6280, 1395, 81311⟩, 2794932370145280, 43531937415069⟩, 76, 4, 9, 514287⟩

theorem step320_nodes : P1_7_1.nodeRows step320.bank.shape = step320.bank.nodeRows :=
  node_check step320.bank (by decide) (by decide) (by decide)

private theorem step320_2330_2335 : Positive step320 2330 2335 := by decide +kernel

private theorem step320_2336_2350 : Positive step320 2336 2350 := by decide +kernel

private theorem step320_2351_2389 : Positive step320 2351 2389 := by decide +kernel

private theorem step320_2390_2490 : Positive step320 2390 2490 := by decide +kernel

private theorem step320_2491_2499 : Positive step320 2491 2499 := by decide +kernel

theorem step320_cover : ∃ ends, Cover step320 firstHeight ends := by
  exact ⟨[2335, 2350, 2389, 2490, 2499],
    ⟨(by decide), (by decide), step320_2330_2335,
      (by decide), (by decide), step320_2336_2350,
      (by decide), (by decide), step320_2351_2389,
      (by decide), (by decide), step320_2390_2490,
      (by decide), (by decide), step320_2491_2499, rfl⟩⟩

theorem step320_verified : Checked step320 :=
  ⟨step320_nodes, Research6966.HelperWindowCatalogue.moment6280_1395,
    (by decide), (by decide), (by decide), step320_cover⟩

def step321 : Request :=
  ⟨⟨⟨4500, 6279, 1359, 115771⟩, 2739950258749440, 42632508857204⟩, 103, 4, 9, 514287⟩

theorem step321_nodes : P1_7_1.nodeRows step321.bank.shape = step321.bank.nodeRows :=
  node_check step321.bank (by decide) (by decide) (by decide)

private theorem step321_2330_2340 : Positive step321 2330 2340 := by decide +kernel

private theorem step321_2341_2368 : Positive step321 2341 2368 := by decide +kernel

private theorem step321_2369_2441 : Positive step321 2369 2441 := by decide +kernel

private theorem step321_2442_2499 : Positive step321 2442 2499 := by decide +kernel

theorem step321_cover : ∃ ends, Cover step321 firstHeight ends := by
  exact ⟨[2340, 2368, 2441, 2499],
    ⟨(by decide), (by decide), step321_2330_2340,
      (by decide), (by decide), step321_2341_2368,
      (by decide), (by decide), step321_2369_2441,
      (by decide), (by decide), step321_2442_2499, rfl⟩⟩

theorem step321_verified : Checked step321 :=
  ⟨step321_nodes, Research6966.HelperWindowCatalogue.moment6279_1359,
    (by decide), (by decide), (by decide), step321_cover⟩

def step322 : Request :=
  ⟨⟨⟨350, 488, 106, 8679⟩, 1308168290304, 1584729438⟩, 0, 4, 16, 514287⟩

theorem step322_nodes : P1_7_1.nodeRows step322.bank.shape = step322.bank.nodeRows :=
  node_check step322.bank (by decide) (by decide) (by decide)

private theorem step322_2330_2340 : Positive step322 2330 2340 := by decide +kernel

private theorem step322_2341_2375 : Positive step322 2341 2375 := by decide +kernel

private theorem step322_2376_2487 : Positive step322 2376 2487 := by decide +kernel

private theorem step322_2488_2499 : Positive step322 2488 2499 := by decide +kernel

theorem step322_cover : ∃ ends, Cover step322 firstHeight ends := by
  exact ⟨[2340, 2375, 2487, 2499],
    ⟨(by decide), (by decide), step322_2330_2340,
      (by decide), (by decide), step322_2341_2375,
      (by decide), (by decide), step322_2376_2487,
      (by decide), (by decide), step322_2488_2499, rfl⟩⟩

theorem step322_verified : Checked step322 :=
  ⟨step322_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step322_cover⟩

def step323 : Request :=
  ⟨⟨⟨420, 586, 127, 8679⟩, 2252760678400, 3279920952⟩, 1, 4, 16, 514287⟩

theorem step323_nodes : P1_7_1.nodeRows step323.bank.shape = step323.bank.nodeRows :=
  node_check step323.bank (by decide) (by decide) (by decide)

private theorem step323_2330_2339 : Positive step323 2330 2339 := by decide +kernel

private theorem step323_2340_2370 : Positive step323 2340 2370 := by decide +kernel

private theorem step323_2371_2465 : Positive step323 2371 2465 := by decide +kernel

private theorem step323_2466_2499 : Positive step323 2466 2499 := by decide +kernel

theorem step323_cover : ∃ ends, Cover step323 firstHeight ends := by
  exact ⟨[2339, 2370, 2465, 2499],
    ⟨(by decide), (by decide), step323_2330_2339,
      (by decide), (by decide), step323_2340_2370,
      (by decide), (by decide), step323_2371_2465,
      (by decide), (by decide), step323_2466_2499, rfl⟩⟩

theorem step323_verified : Checked step323 :=
  ⟨step323_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step323_cover⟩

def step324 : Request :=
  ⟨⟨⟨520, 726, 157, 8679⟩, 4261264752640, 7692905725⟩, 2, 4, 16, 514287⟩

theorem step324_nodes : P1_7_1.nodeRows step324.bank.shape = step324.bank.nodeRows :=
  node_check step324.bank (by decide) (by decide) (by decide)

private theorem step324_2330_2332 : Positive step324 2330 2332 := by decide +kernel

private theorem step324_2333_2341 : Positive step324 2333 2341 := by decide +kernel

private theorem step324_2342_2367 : Positive step324 2342 2367 := by decide +kernel

private theorem step324_2368_2444 : Positive step324 2368 2444 := by decide +kernel

private theorem step324_2445_2499 : Positive step324 2445 2499 := by decide +kernel

theorem step324_cover : ∃ ends, Cover step324 firstHeight ends := by
  exact ⟨[2332, 2341, 2367, 2444, 2499],
    ⟨(by decide), (by decide), step324_2330_2332,
      (by decide), (by decide), step324_2333_2341,
      (by decide), (by decide), step324_2342_2367,
      (by decide), (by decide), step324_2368_2444,
      (by decide), (by decide), step324_2445_2499, rfl⟩⟩

theorem step324_verified : Checked step324 :=
  ⟨step324_nodes, Research6966.HelperWindowCatalogue.moment726_157,
    (by decide), (by decide), (by decide), step324_cover⟩

def step325 : Request :=
  ⟨⟨⟨520, 725, 157, 9763⟩, 4261264752640, 7658911630⟩, 3, 4, 16, 514287⟩

theorem step325_nodes : P1_7_1.nodeRows step325.bank.shape = step325.bank.nodeRows :=
  node_check step325.bank (by decide) (by decide) (by decide)

private theorem step325_2330_2337 : Positive step325 2330 2337 := by decide +kernel

private theorem step325_2338_2360 : Positive step325 2338 2360 := by decide +kernel

private theorem step325_2361_2429 : Positive step325 2361 2429 := by decide +kernel

private theorem step325_2430_2499 : Positive step325 2430 2499 := by decide +kernel

theorem step325_cover : ∃ ends, Cover step325 firstHeight ends := by
  exact ⟨[2337, 2360, 2429, 2499],
    ⟨(by decide), (by decide), step325_2330_2337,
      (by decide), (by decide), step325_2338_2360,
      (by decide), (by decide), step325_2361_2429,
      (by decide), (by decide), step325_2430_2499, rfl⟩⟩

theorem step325_verified : Checked step325 :=
  ⟨step325_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step325_cover⟩

def step326 : Request :=
  ⟨⟨⟨520, 725, 157, 10983⟩, 4261264752640, 7658911630⟩, 4, 4, 16, 514287⟩

theorem step326_nodes : P1_7_1.nodeRows step326.bank.shape = step326.bank.nodeRows :=
  node_check step326.bank (by decide) (by decide) (by decide)

private theorem step326_2330_2334 : Positive step326 2330 2334 := by decide +kernel

private theorem step326_2335_2349 : Positive step326 2335 2349 := by decide +kernel

private theorem step326_2350_2393 : Positive step326 2350 2393 := by decide +kernel

private theorem step326_2394_2499 : Positive step326 2394 2499 := by decide +kernel

theorem step326_cover : ∃ ends, Cover step326 firstHeight ends := by
  exact ⟨[2334, 2349, 2393, 2499],
    ⟨(by decide), (by decide), step326_2330_2334,
      (by decide), (by decide), step326_2335_2349,
      (by decide), (by decide), step326_2350_2393,
      (by decide), (by decide), step326_2394_2499, rfl⟩⟩

theorem step326_verified : Checked step326 :=
  ⟨step326_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step326_cover⟩

def step327 : Request :=
  ⟨⟨⟨520, 725, 161, 12355⟩, 4343013310464, 7809559934⟩, 5, 4, 16, 514287⟩

theorem step327_nodes : P1_7_1.nodeRows step327.bank.shape = step327.bank.nodeRows :=
  node_check step327.bank (by decide) (by decide) (by decide)

private theorem step327_2330_2333 : Positive step327 2330 2333 := by decide +kernel

private theorem step327_2334_2345 : Positive step327 2334 2345 := by decide +kernel

private theorem step327_2346_2380 : Positive step327 2346 2380 := by decide +kernel

private theorem step327_2381_2483 : Positive step327 2381 2483 := by decide +kernel

private theorem step327_2484_2499 : Positive step327 2484 2499 := by decide +kernel

theorem step327_cover : ∃ ends, Cover step327 firstHeight ends := by
  exact ⟨[2333, 2345, 2380, 2483, 2499],
    ⟨(by decide), (by decide), step327_2330_2333,
      (by decide), (by decide), step327_2334_2345,
      (by decide), (by decide), step327_2346_2380,
      (by decide), (by decide), step327_2381_2483,
      (by decide), (by decide), step327_2484_2499, rfl⟩⟩

theorem step327_verified : Checked step327 :=
  ⟨step327_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step327_cover⟩

def step328 : Request :=
  ⟨⟨⟨630, 879, 190, 13899⟩, 7559493713920, 16491913877⟩, 7, 4, 16, 514287⟩

theorem step328_nodes : P1_7_1.nodeRows step328.bank.shape = step328.bank.nodeRows :=
  node_check step328.bank (by decide) (by decide) (by decide)

private theorem step328_2330_2343 : Positive step328 2330 2343 := by decide +kernel

private theorem step328_2344_2384 : Positive step328 2344 2384 := by decide +kernel

private theorem step328_2385_2499 : Positive step328 2385 2499 := by decide +kernel

theorem step328_cover : ∃ ends, Cover step328 firstHeight ends := by
  exact ⟨[2343, 2384, 2499],
    ⟨(by decide), (by decide), step328_2330_2343,
      (by decide), (by decide), step328_2344_2384,
      (by decide), (by decide), step328_2385_2499, rfl⟩⟩

theorem step328_verified : Checked step328 :=
  ⟨step328_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step328_cover⟩

def step329 : Request :=
  ⟨⟨⟨750, 1046, 226, 15636⟩, 12730741817344, 33009058589⟩, 10, 4, 16, 514287⟩

theorem step329_nodes : P1_7_1.nodeRows step329.bank.shape = step329.bank.nodeRows :=
  node_check step329.bank (by decide) (by decide) (by decide)

private theorem step329_2330_2336 : Positive step329 2330 2336 := by decide +kernel

private theorem step329_2337_2356 : Positive step329 2337 2356 := by decide +kernel

private theorem step329_2357_2413 : Positive step329 2357 2413 := by decide +kernel

private theorem step329_2414_2499 : Positive step329 2414 2499 := by decide +kernel

theorem step329_cover : ∃ ends, Cover step329 firstHeight ends := by
  exact ⟨[2336, 2356, 2413, 2499],
    ⟨(by decide), (by decide), step329_2330_2336,
      (by decide), (by decide), step329_2337_2356,
      (by decide), (by decide), step329_2357_2413,
      (by decide), (by decide), step329_2414_2499, rfl⟩⟩

theorem step329_verified : Checked step329 :=
  ⟨step329_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step329_cover⟩

def step330 : Request :=
  ⟨⟨⟨900, 1256, 272, 22261⟩, 22024701870080, 68653176066⟩, 16, 4, 16, 514287⟩

theorem step330_nodes : P1_7_1.nodeRows step330.bank.shape = step330.bank.nodeRows :=
  node_check step330.bank (by decide) (by decide) (by decide)

private theorem step330_2330_2339 : Positive step330 2330 2339 := by decide +kernel

private theorem step330_2340_2367 : Positive step330 2340 2367 := by decide +kernel

private theorem step330_2368_2445 : Positive step330 2368 2445 := by decide +kernel

private theorem step330_2446_2499 : Positive step330 2446 2499 := by decide +kernel

theorem step330_cover : ∃ ends, Cover step330 firstHeight ends := by
  exact ⟨[2339, 2367, 2445, 2499],
    ⟨(by decide), (by decide), step330_2330_2339,
      (by decide), (by decide), step330_2340_2367,
      (by decide), (by decide), step330_2368_2445,
      (by decide), (by decide), step330_2446_2499, rfl⟩⟩

theorem step330_verified : Checked step330 :=
  ⟨step330_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step330_cover⟩

def step331 : Request :=
  ⟨⟨⟨1100, 1535, 326, 25043⟩, 39579969388544, 150663514795⟩, 20, 4, 16, 514287⟩

theorem step331_nodes : P1_7_1.nodeRows step331.bank.shape = step331.bank.nodeRows :=
  node_check step331.bank (by decide) (by decide) (by decide)

private theorem step331_2330_2331 : Positive step331 2330 2331 := by decide +kernel

private theorem step331_2332_2336 : Positive step331 2332 2336 := by decide +kernel

private theorem step331_2337_2350 : Positive step331 2337 2350 := by decide +kernel

private theorem step331_2351_2389 : Positive step331 2351 2389 := by decide +kernel

private theorem step331_2390_2497 : Positive step331 2390 2497 := by decide +kernel

private theorem step331_2498_2499 : Positive step331 2498 2499 := by decide +kernel

theorem step331_cover : ∃ ends, Cover step331 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2389, 2497, 2499],
    ⟨(by decide), (by decide), step331_2330_2331,
      (by decide), (by decide), step331_2332_2336,
      (by decide), (by decide), step331_2337_2350,
      (by decide), (by decide), step331_2351_2389,
      (by decide), (by decide), step331_2390_2497,
      (by decide), (by decide), step331_2498_2499, rfl⟩⟩

theorem step331_verified : Checked step331 :=
  ⟨step331_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step331_cover⟩

def step332 : Request :=
  ⟨⟨⟨1350, 1883, 408, 35655⟩, 74202776600576, 346190054868⟩, 31, 4, 16, 514287⟩

theorem step332_nodes : P1_7_1.nodeRows step332.bank.shape = step332.bank.nodeRows :=
  node_check step332.bank (by decide) (by decide) (by decide)

private theorem step332_2330_2330 : Positive step332 2330 2330 := by decide +kernel

private theorem step332_2331_2333 : Positive step332 2331 2333 := by decide +kernel

private theorem step332_2334_2341 : Positive step332 2334 2341 := by decide +kernel

private theorem step332_2342_2362 : Positive step332 2342 2362 := by decide +kernel

private theorem step332_2363_2419 : Positive step332 2363 2419 := by decide +kernel

private theorem step332_2420_2499 : Positive step332 2420 2499 := by decide +kernel

theorem step332_cover : ∃ ends, Cover step332 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2419, 2499],
    ⟨(by decide), (by decide), step332_2330_2330,
      (by decide), (by decide), step332_2331_2333,
      (by decide), (by decide), step332_2334_2341,
      (by decide), (by decide), step332_2342_2362,
      (by decide), (by decide), step332_2363_2419,
      (by decide), (by decide), step332_2420_2499, rfl⟩⟩

theorem step332_verified : Checked step332 :=
  ⟨step332_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step332_cover⟩

def step333 : Request :=
  ⟨⟨⟨1650, 2302, 498, 31694⟩, 135254251667456, 771697512616⟩, 32, 4, 16, 514287⟩

theorem step333_nodes : P1_7_1.nodeRows step333.bank.shape = step333.bank.nodeRows :=
  node_check step333.bank (by decide) (by decide) (by decide)

private theorem step333_2330_2340 : Positive step333 2330 2340 := by decide +kernel

private theorem step333_2341_2369 : Positive step333 2341 2369 := by decide +kernel

private theorem step333_2370_2447 : Positive step333 2370 2447 := by decide +kernel

private theorem step333_2448_2499 : Positive step333 2448 2499 := by decide +kernel

theorem step333_cover : ∃ ends, Cover step333 firstHeight ends := by
  exact ⟨[2340, 2369, 2447, 2499],
    ⟨(by decide), (by decide), step333_2330_2340,
      (by decide), (by decide), step333_2341_2369,
      (by decide), (by decide), step333_2370_2447,
      (by decide), (by decide), step333_2448_2499, rfl⟩⟩

theorem step333_verified : Checked step333 :=
  ⟨step333_nodes, Research6966.HelperWindowCatalogue.moment2302_498,
    (by decide), (by decide), (by decide), step333_cover⟩

def step334 : Request :=
  ⟨⟨⟨2000, 2791, 620, 40111⟩, 245690786119680, 1701147081935⟩, 44, 4, 16, 514287⟩

theorem step334_nodes : P1_7_1.nodeRows step334.bank.shape = step334.bank.nodeRows :=
  node_check step334.bank (by decide) (by decide) (by decide)

private theorem step334_2330_2334 : Positive step334 2330 2334 := by decide +kernel

private theorem step334_2335_2347 : Positive step334 2335 2347 := by decide +kernel

private theorem step334_2348_2382 : Positive step334 2348 2382 := by decide +kernel

private theorem step334_2383_2474 : Positive step334 2383 2474 := by decide +kernel

private theorem step334_2475_2499 : Positive step334 2475 2499 := by decide +kernel

theorem step334_cover : ∃ ends, Cover step334 firstHeight ends := by
  exact ⟨[2334, 2347, 2382, 2474, 2499],
    ⟨(by decide), (by decide), step334_2330_2334,
      (by decide), (by decide), step334_2335_2347,
      (by decide), (by decide), step334_2348_2382,
      (by decide), (by decide), step334_2383_2474,
      (by decide), (by decide), step334_2475_2499, rfl⟩⟩

theorem step334_verified : Checked step334 :=
  ⟨step334_nodes, Research6966.HelperWindowCatalogue.moment2791_620,
    (by decide), (by decide), (by decide), step334_cover⟩

end Research6966.HelperRescueCatalogue
