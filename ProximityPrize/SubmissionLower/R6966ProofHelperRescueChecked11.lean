import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments11
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments7
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step335 : Request :=
  ⟨⟨⟨3000, 4186, 906, 64247⟩, 812266433019904, 8426888829858⟩, 73, 4, 16, 514287⟩

theorem step335_nodes : P1_7_1.nodeRows step335.bank.shape = step335.bank.nodeRows :=
  node_check step335.bank (by decide) (by decide) (by decide)

private theorem step335_2330_2332 : Positive step335 2330 2332 := by decide +kernel

private theorem step335_2333_2340 : Positive step335 2333 2340 := by decide +kernel

private theorem step335_2341_2361 : Positive step335 2341 2361 := by decide +kernel

private theorem step335_2362_2416 : Positive step335 2362 2416 := by decide +kernel

private theorem step335_2417_2499 : Positive step335 2417 2499 := by decide +kernel

theorem step335_cover : ∃ ends, Cover step335 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2416, 2499],
    ⟨(by decide), (by decide), step335_2330_2332,
      (by decide), (by decide), step335_2333_2340,
      (by decide), (by decide), step335_2341_2361,
      (by decide), (by decide), step335_2362_2416,
      (by decide), (by decide), step335_2417_2499, rfl⟩⟩

theorem step335_verified : Checked step335 :=
  ⟨step335_nodes, Research6966.HelperWindowCatalogue.moment4186_906,
    (by decide), (by decide), (by decide), step335_cover⟩

def step336 : Request :=
  ⟨⟨⟨3000, 4186, 906, 72277⟩, 812266433019904, 8426888829858⟩, 76, 4, 16, 514287⟩

theorem step336_nodes : P1_7_1.nodeRows step336.bank.shape = step336.bank.nodeRows :=
  node_check step336.bank (by decide) (by decide) (by decide)

private theorem step336_2330_2341 : Positive step336 2330 2341 := by decide +kernel

private theorem step336_2342_2372 : Positive step336 2342 2372 := by decide +kernel

private theorem step336_2373_2454 : Positive step336 2373 2454 := by decide +kernel

private theorem step336_2455_2499 : Positive step336 2455 2499 := by decide +kernel

theorem step336_cover : ∃ ends, Cover step336 firstHeight ends := by
  exact ⟨[2341, 2372, 2454, 2499],
    ⟨(by decide), (by decide), step336_2330_2341,
      (by decide), (by decide), step336_2342_2372,
      (by decide), (by decide), step336_2373_2454,
      (by decide), (by decide), step336_2455_2499, rfl⟩⟩

theorem step336_verified : Checked step336 :=
  ⟨step336_nodes, Research6966.HelperWindowCatalogue.moment4186_906,
    (by decide), (by decide), (by decide), step336_cover⟩

def step337 : Request :=
  ⟨⟨⟨4500, 6279, 1359, 81311⟩, 2739950258749440, 42632508857204⟩, 103, 4, 16, 514287⟩

theorem step337_nodes : P1_7_1.nodeRows step337.bank.shape = step337.bank.nodeRows :=
  node_check step337.bank (by decide) (by decide) (by decide)

private theorem step337_2330_2331 : Positive step337 2330 2331 := by decide +kernel

private theorem step337_2332_2336 : Positive step337 2332 2336 := by decide +kernel

private theorem step337_2337_2349 : Positive step337 2337 2349 := by decide +kernel

private theorem step337_2350_2383 : Positive step337 2350 2383 := by decide +kernel

private theorem step337_2384_2472 : Positive step337 2384 2472 := by decide +kernel

private theorem step337_2473_2499 : Positive step337 2473 2499 := by decide +kernel

theorem step337_cover : ∃ ends, Cover step337 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2472, 2499],
    ⟨(by decide), (by decide), step337_2330_2331,
      (by decide), (by decide), step337_2332_2336,
      (by decide), (by decide), step337_2337_2349,
      (by decide), (by decide), step337_2350_2383,
      (by decide), (by decide), step337_2384_2472,
      (by decide), (by decide), step337_2473_2499, rfl⟩⟩

theorem step337_verified : Checked step337 :=
  ⟨step337_nodes, Research6966.HelperWindowCatalogue.moment6279_1359,
    (by decide), (by decide), (by decide), step337_cover⟩

def step338 : Request :=
  ⟨⟨⟨350, 488, 106, 4817⟩, 1308168290304, 1584729438⟩, 0, 4, 26, 514287⟩

theorem step338_nodes : P1_7_1.nodeRows step338.bank.shape = step338.bank.nodeRows :=
  node_check step338.bank (by decide) (by decide) (by decide)

private theorem step338_2330_2348 : Positive step338 2330 2348 := by decide +kernel

private theorem step338_2349_2410 : Positive step338 2349 2410 := by decide +kernel

private theorem step338_2411_2499 : Positive step338 2411 2499 := by decide +kernel

theorem step338_cover : ∃ ends, Cover step338 firstHeight ends := by
  exact ⟨[2348, 2410, 2499],
    ⟨(by decide), (by decide), step338_2330_2348,
      (by decide), (by decide), step338_2349_2410,
      (by decide), (by decide), step338_2411_2499, rfl⟩⟩

theorem step338_verified : Checked step338 :=
  ⟨step338_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step338_cover⟩

def step339 : Request :=
  ⟨⟨⟨350, 488, 108, 5419⟩, 1326705278976, 1607754763⟩, 1, 4, 26, 514287⟩

theorem step339_nodes : P1_7_1.nodeRows step339.bank.shape = step339.bank.nodeRows :=
  node_check step339.bank (by decide) (by decide) (by decide)

private theorem step339_2330_2333 : Positive step339 2330 2333 := by decide +kernel

private theorem step339_2334_2346 : Positive step339 2334 2346 := by decide +kernel

private theorem step339_2347_2387 : Positive step339 2347 2387 := by decide +kernel

private theorem step339_2388_2499 : Positive step339 2388 2499 := by decide +kernel

theorem step339_cover : ∃ ends, Cover step339 firstHeight ends := by
  exact ⟨[2333, 2346, 2387, 2499],
    ⟨(by decide), (by decide), step339_2330_2333,
      (by decide), (by decide), step339_2334_2346,
      (by decide), (by decide), step339_2347_2387,
      (by decide), (by decide), step339_2388_2499, rfl⟩⟩

theorem step339_verified : Checked step339 :=
  ⟨step339_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step339_cover⟩

def step340 : Request :=
  ⟨⟨⟨420, 586, 130, 5419⟩, 2292767784960, 3339653140⟩, 2, 4, 26, 514287⟩

theorem step340_nodes : P1_7_1.nodeRows step340.bank.shape = step340.bank.nodeRows :=
  node_check step340.bank (by decide) (by decide) (by decide)

private theorem step340_2330_2340 : Positive step340 2330 2340 := by decide +kernel

private theorem step340_2341_2374 : Positive step340 2341 2374 := by decide +kernel

private theorem step340_2375_2478 : Positive step340 2375 2478 := by decide +kernel

private theorem step340_2479_2499 : Positive step340 2479 2499 := by decide +kernel

theorem step340_cover : ∃ ends, Cover step340 firstHeight ends := by
  exact ⟨[2340, 2374, 2478, 2499],
    ⟨(by decide), (by decide), step340_2330_2340,
      (by decide), (by decide), step340_2341_2374,
      (by decide), (by decide), step340_2375_2478,
      (by decide), (by decide), step340_2479_2499, rfl⟩⟩

theorem step340_verified : Checked step340 :=
  ⟨step340_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step340_cover⟩

def step341 : Request :=
  ⟨⟨⟨520, 725, 161, 5419⟩, 4343013310464, 7809559934⟩, 3, 4, 26, 514287⟩

theorem step341_nodes : P1_7_1.nodeRows step341.bank.shape = step341.bank.nodeRows :=
  node_check step341.bank (by decide) (by decide) (by decide)

private theorem step341_2330_2336 : Positive step341 2330 2336 := by decide +kernel

private theorem step341_2337_2356 : Positive step341 2337 2356 := by decide +kernel

private theorem step341_2357_2415 : Positive step341 2357 2415 := by decide +kernel

private theorem step341_2416_2499 : Positive step341 2416 2499 := by decide +kernel

theorem step341_cover : ∃ ends, Cover step341 firstHeight ends := by
  exact ⟨[2336, 2356, 2415, 2499],
    ⟨(by decide), (by decide), step341_2330_2336,
      (by decide), (by decide), step341_2337_2356,
      (by decide), (by decide), step341_2357_2415,
      (by decide), (by decide), step341_2416_2499, rfl⟩⟩

theorem step341_verified : Checked step341 :=
  ⟨step341_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step341_cover⟩

def step342 : Request :=
  ⟨⟨⟨520, 725, 161, 6096⟩, 4343013310464, 7809559934⟩, 4, 4, 26, 514287⟩

theorem step342_nodes : P1_7_1.nodeRows step342.bank.shape = step342.bank.nodeRows :=
  node_check step342.bank (by decide) (by decide) (by decide)

private theorem step342_2330_2345 : Positive step342 2330 2345 := by decide +kernel

private theorem step342_2346_2392 : Positive step342 2346 2392 := by decide +kernel

private theorem step342_2393_2499 : Positive step342 2393 2499 := by decide +kernel

theorem step342_cover : ∃ ends, Cover step342 firstHeight ends := by
  exact ⟨[2345, 2392, 2499],
    ⟨(by decide), (by decide), step342_2330_2345,
      (by decide), (by decide), step342_2346_2392,
      (by decide), (by decide), step342_2393_2499, rfl⟩⟩

theorem step342_verified : Checked step342 :=
  ⟨step342_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step342_cover⟩

def step343 : Request :=
  ⟨⟨⟨520, 725, 157, 6858⟩, 4261264752640, 7658911630⟩, 5, 4, 26, 514287⟩

theorem step343_nodes : P1_7_1.nodeRows step343.bank.shape = step343.bank.nodeRows :=
  node_check step343.bank (by decide) (by decide) (by decide)

private theorem step343_2330_2332 : Positive step343 2330 2332 := by decide +kernel

private theorem step343_2333_2341 : Positive step343 2333 2341 := by decide +kernel

private theorem step343_2342_2367 : Positive step343 2342 2367 := by decide +kernel

private theorem step343_2368_2444 : Positive step343 2368 2444 := by decide +kernel

private theorem step343_2445_2499 : Positive step343 2445 2499 := by decide +kernel

theorem step343_cover : ∃ ends, Cover step343 firstHeight ends := by
  exact ⟨[2332, 2341, 2367, 2444, 2499],
    ⟨(by decide), (by decide), step343_2330_2332,
      (by decide), (by decide), step343_2333_2341,
      (by decide), (by decide), step343_2342_2367,
      (by decide), (by decide), step343_2368_2444,
      (by decide), (by decide), step343_2445_2499, rfl⟩⟩

theorem step343_verified : Checked step343 :=
  ⟨step343_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step343_cover⟩

def step344 : Request :=
  ⟨⟨⟨520, 725, 161, 8679⟩, 4343013310464, 7809559934⟩, 7, 4, 26, 514287⟩

theorem step344_nodes : P1_7_1.nodeRows step344.bank.shape = step344.bank.nodeRows :=
  node_check step344.bank (by decide) (by decide) (by decide)

private theorem step344_2330_2332 : Positive step344 2330 2332 := by decide +kernel

private theorem step344_2333_2341 : Positive step344 2333 2341 := by decide +kernel

private theorem step344_2342_2367 : Positive step344 2342 2367 := by decide +kernel

private theorem step344_2368_2444 : Positive step344 2368 2444 := by decide +kernel

private theorem step344_2445_2499 : Positive step344 2445 2499 := by decide +kernel

theorem step344_cover : ∃ ends, Cover step344 firstHeight ends := by
  exact ⟨[2332, 2341, 2367, 2444, 2499],
    ⟨(by decide), (by decide), step344_2330_2332,
      (by decide), (by decide), step344_2333_2341,
      (by decide), (by decide), step344_2342_2367,
      (by decide), (by decide), step344_2368_2444,
      (by decide), (by decide), step344_2445_2499, rfl⟩⟩

theorem step344_verified : Checked step344 :=
  ⟨step344_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step344_cover⟩

def step345 : Request :=
  ⟨⟨⟨630, 879, 195, 9763⟩, 7709474160640, 16827402390⟩, 10, 4, 26, 514287⟩

theorem step345_nodes : P1_7_1.nodeRows step345.bank.shape = step345.bank.nodeRows :=
  node_check step345.bank (by decide) (by decide) (by decide)

private theorem step345_2330_2335 : Positive step345 2330 2335 := by decide +kernel

private theorem step345_2336_2352 : Positive step345 2336 2352 := by decide +kernel

private theorem step345_2353_2400 : Positive step345 2353 2400 := by decide +kernel

private theorem step345_2401_2499 : Positive step345 2401 2499 := by decide +kernel

theorem step345_cover : ∃ ends, Cover step345 firstHeight ends := by
  exact ⟨[2335, 2352, 2400, 2499],
    ⟨(by decide), (by decide), step345_2330_2335,
      (by decide), (by decide), step345_2336_2352,
      (by decide), (by decide), step345_2353_2400,
      (by decide), (by decide), step345_2401_2499, rfl⟩⟩

theorem step345_verified : Checked step345 :=
  ⟨step345_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step345_cover⟩

def step346 : Request :=
  ⟨⟨⟨900, 1256, 272, 12355⟩, 22024701870080, 68653176066⟩, 16, 4, 26, 514287⟩

theorem step346_nodes : P1_7_1.nodeRows step346.bank.shape = step346.bank.nodeRows :=
  node_check step346.bank (by decide) (by decide) (by decide)

private theorem step346_2330_2344 : Positive step346 2330 2344 := by decide +kernel

private theorem step346_2345_2386 : Positive step346 2345 2386 := by decide +kernel

private theorem step346_2387_2499 : Positive step346 2387 2499 := by decide +kernel

theorem step346_cover : ∃ ends, Cover step346 firstHeight ends := by
  exact ⟨[2344, 2386, 2499],
    ⟨(by decide), (by decide), step346_2330_2344,
      (by decide), (by decide), step346_2345_2386,
      (by decide), (by decide), step346_2387_2499, rfl⟩⟩

theorem step346_verified : Checked step346 :=
  ⟨step346_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step346_cover⟩

def step347 : Request :=
  ⟨⟨⟨900, 1256, 279, 15636⟩, 22452680785920, 70021105933⟩, 20, 4, 26, 514287⟩

theorem step347_nodes : P1_7_1.nodeRows step347.bank.shape = step347.bank.nodeRows :=
  node_check step347.bank (by decide) (by decide) (by decide)

private theorem step347_2330_2332 : Positive step347 2330 2332 := by decide +kernel

private theorem step347_2333_2340 : Positive step347 2333 2340 := by decide +kernel

private theorem step347_2341_2362 : Positive step347 2341 2362 := by decide +kernel

private theorem step347_2363_2423 : Positive step347 2363 2423 := by decide +kernel

private theorem step347_2424_2499 : Positive step347 2424 2499 := by decide +kernel

theorem step347_cover : ∃ ends, Cover step347 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2423, 2499],
    ⟨(by decide), (by decide), step347_2330_2332,
      (by decide), (by decide), step347_2333_2340,
      (by decide), (by decide), step347_2341_2362,
      (by decide), (by decide), step347_2363_2423,
      (by decide), (by decide), step347_2424_2499, rfl⟩⟩

theorem step347_verified : Checked step347 :=
  ⟨step347_nodes, Research6966.HelperWindowCatalogue.moment1256_279,
    (by decide), (by decide), (by decide), step347_cover⟩

def step348 : Request :=
  ⟨⟨⟨1350, 1883, 408, 19788⟩, 74202776600576, 346190054868⟩, 31, 4, 26, 514287⟩

theorem step348_nodes : P1_7_1.nodeRows step348.bank.shape = step348.bank.nodeRows :=
  node_check step348.bank (by decide) (by decide) (by decide)

private theorem step348_2330_2338 : Positive step348 2330 2338 := by decide +kernel

private theorem step348_2339_2362 : Positive step348 2339 2362 := by decide +kernel

private theorem step348_2363_2427 : Positive step348 2363 2427 := by decide +kernel

private theorem step348_2428_2499 : Positive step348 2428 2499 := by decide +kernel

theorem step348_cover : ∃ ends, Cover step348 firstHeight ends := by
  exact ⟨[2338, 2362, 2427, 2499],
    ⟨(by decide), (by decide), step348_2330_2338,
      (by decide), (by decide), step348_2339_2362,
      (by decide), (by decide), step348_2363_2427,
      (by decide), (by decide), step348_2428_2499, rfl⟩⟩

theorem step348_verified : Checked step348 :=
  ⟨step348_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step348_cover⟩

def step349 : Request :=
  ⟨⟨⟨1350, 1883, 418, 19788⟩, 75578221264896, 352769102024⟩, 32, 4, 26, 514287⟩

theorem step349_nodes : P1_7_1.nodeRows step349.bank.shape = step349.bank.nodeRows :=
  node_check step349.bank (by decide) (by decide) (by decide)

private theorem step349_2330_2339 : Positive step349 2330 2339 := by decide +kernel

private theorem step349_2340_2366 : Positive step349 2340 2366 := by decide +kernel

private theorem step349_2367_2439 : Positive step349 2367 2439 := by decide +kernel

private theorem step349_2440_2499 : Positive step349 2440 2499 := by decide +kernel

theorem step349_cover : ∃ ends, Cover step349 firstHeight ends := by
  exact ⟨[2339, 2366, 2439, 2499],
    ⟨(by decide), (by decide), step349_2330_2339,
      (by decide), (by decide), step349_2340_2366,
      (by decide), (by decide), step349_2367_2439,
      (by decide), (by decide), step349_2440_2499, rfl⟩⟩

theorem step349_verified : Checked step349 :=
  ⟨step349_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step349_cover⟩

def step350 : Request :=
  ⟨⟨⟨2000, 2791, 620, 22261⟩, 245690786119680, 1701147081935⟩, 44, 4, 26, 514287⟩

theorem step350_nodes : P1_7_1.nodeRows step350.bank.shape = step350.bank.nodeRows :=
  node_check step350.bank (by decide) (by decide) (by decide)

private theorem step350_2330_2332 : Positive step350 2330 2332 := by decide +kernel

private theorem step350_2333_2340 : Positive step350 2333 2340 := by decide +kernel

private theorem step350_2341_2361 : Positive step350 2341 2361 := by decide +kernel

private theorem step350_2362_2417 : Positive step350 2362 2417 := by decide +kernel

private theorem step350_2418_2499 : Positive step350 2418 2499 := by decide +kernel

theorem step350_cover : ∃ ends, Cover step350 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2417, 2499],
    ⟨(by decide), (by decide), step350_2330_2332,
      (by decide), (by decide), step350_2333_2340,
      (by decide), (by decide), step350_2341_2361,
      (by decide), (by decide), step350_2362_2417,
      (by decide), (by decide), step350_2418_2499, rfl⟩⟩

theorem step350_verified : Checked step350 :=
  ⟨step350_nodes, Research6966.HelperWindowCatalogue.moment2791_620,
    (by decide), (by decide), (by decide), step350_cover⟩

def step351 : Request :=
  ⟨⟨⟨3000, 4186, 930, 35655⟩, 828559354757120, 8600191575129⟩, 73, 4, 26, 514287⟩

theorem step351_nodes : P1_7_1.nodeRows step351.bank.shape = step351.bank.nodeRows :=
  node_check step351.bank (by decide) (by decide) (by decide)

private theorem step351_2330_2343 : Positive step351 2330 2343 := by decide +kernel

private theorem step351_2344_2380 : Positive step351 2344 2380 := by decide +kernel

private theorem step351_2381_2477 : Positive step351 2381 2477 := by decide +kernel

private theorem step351_2478_2499 : Positive step351 2478 2499 := by decide +kernel

theorem step351_cover : ∃ ends, Cover step351 firstHeight ends := by
  exact ⟨[2343, 2380, 2477, 2499],
    ⟨(by decide), (by decide), step351_2330_2343,
      (by decide), (by decide), step351_2344_2380,
      (by decide), (by decide), step351_2381_2477,
      (by decide), (by decide), step351_2478_2499, rfl⟩⟩

theorem step351_verified : Checked step351 :=
  ⟨step351_nodes, Research6966.HelperWindowCatalogue.moment4186_930,
    (by decide), (by decide), (by decide), step351_cover⟩

def step352 : Request :=
  ⟨⟨⟨3000, 4186, 906, 40111⟩, 812266433019904, 8426888829858⟩, 76, 4, 26, 514287⟩

theorem step352_nodes : P1_7_1.nodeRows step352.bank.shape = step352.bank.nodeRows :=
  node_check step352.bank (by decide) (by decide) (by decide)

private theorem step352_2330_2343 : Positive step352 2330 2343 := by decide +kernel

private theorem step352_2344_2380 : Positive step352 2344 2380 := by decide +kernel

private theorem step352_2381_2478 : Positive step352 2381 2478 := by decide +kernel

private theorem step352_2479_2499 : Positive step352 2479 2499 := by decide +kernel

theorem step352_cover : ∃ ends, Cover step352 firstHeight ends := by
  exact ⟨[2343, 2380, 2478, 2499],
    ⟨(by decide), (by decide), step352_2330_2343,
      (by decide), (by decide), step352_2344_2380,
      (by decide), (by decide), step352_2381_2478,
      (by decide), (by decide), step352_2479_2499, rfl⟩⟩

theorem step352_verified : Checked step352 :=
  ⟨step352_nodes, Research6966.HelperWindowCatalogue.moment4186_906,
    (by decide), (by decide), (by decide), step352_cover⟩

def step353 : Request :=
  ⟨⟨⟨3500, 4883, 1057, 57109⟩, 1289556817346560, 15600507702257⟩, 103, 4, 26, 514287⟩

theorem step353_nodes : P1_7_1.nodeRows step353.bank.shape = step353.bank.nodeRows :=
  node_check step353.bank (by decide) (by decide) (by decide)

private theorem step353_2330_2330 : Positive step353 2330 2330 := by decide +kernel

private theorem step353_2331_2333 : Positive step353 2331 2333 := by decide +kernel

private theorem step353_2334_2340 : Positive step353 2334 2340 := by decide +kernel

private theorem step353_2341_2359 : Positive step353 2341 2359 := by decide +kernel

private theorem step353_2360_2408 : Positive step353 2360 2408 := by decide +kernel

private theorem step353_2409_2499 : Positive step353 2409 2499 := by decide +kernel

theorem step353_cover : ∃ ends, Cover step353 firstHeight ends := by
  exact ⟨[2330, 2333, 2340, 2359, 2408, 2499],
    ⟨(by decide), (by decide), step353_2330_2330,
      (by decide), (by decide), step353_2331_2333,
      (by decide), (by decide), step353_2334_2340,
      (by decide), (by decide), step353_2341_2359,
      (by decide), (by decide), step353_2360_2408,
      (by decide), (by decide), step353_2409_2499, rfl⟩⟩

theorem step353_verified : Checked step353 :=
  ⟨step353_nodes, Research6966.HelperWindowCatalogue.moment4883_1057,
    (by decide), (by decide), (by decide), step353_cover⟩

def step354 : Request :=
  ⟨⟨⟨250, 349, 78, 2674⟩, 490108092416, 426627288⟩, 0, 4, 41, 514287⟩

theorem step354_nodes : P1_7_1.nodeRows step354.bank.shape = step354.bank.nodeRows :=
  node_check step354.bank (by decide) (by decide) (by decide)

private theorem step354_2330_2330 : Positive step354 2330 2330 := by decide +kernel

private theorem step354_2331_2333 : Positive step354 2331 2333 := by decide +kernel

private theorem step354_2334_2344 : Positive step354 2334 2344 := by decide +kernel

private theorem step354_2345_2382 : Positive step354 2345 2382 := by decide +kernel

private theorem step354_2383_2499 : Positive step354 2383 2499 := by decide +kernel

theorem step354_cover : ∃ ends, Cover step354 firstHeight ends := by
  exact ⟨[2330, 2333, 2344, 2382, 2499],
    ⟨(by decide), (by decide), step354_2330_2330,
      (by decide), (by decide), step354_2331_2333,
      (by decide), (by decide), step354_2334_2344,
      (by decide), (by decide), step354_2345_2382,
      (by decide), (by decide), step354_2383_2499, rfl⟩⟩

theorem step354_verified : Checked step354 :=
  ⟨step354_nodes, Research6966.HelperWindowCatalogue.moment349_78,
    (by decide), (by decide), (by decide), step354_cover⟩

def step355 : Request :=
  ⟨⟨⟨294, 410, 89, 3008⟩, 777085255680, 791788817⟩, 1, 4, 41, 514287⟩

theorem step355_nodes : P1_7_1.nodeRows step355.bank.shape = step355.bank.nodeRows :=
  node_check step355.bank (by decide) (by decide) (by decide)

private theorem step355_2330_2354 : Positive step355 2330 2354 := by decide +kernel

private theorem step355_2355_2439 : Positive step355 2355 2439 := by decide +kernel

private theorem step355_2440_2499 : Positive step355 2440 2499 := by decide +kernel

theorem step355_cover : ∃ ends, Cover step355 firstHeight ends := by
  exact ⟨[2354, 2439, 2499],
    ⟨(by decide), (by decide), step355_2330_2354,
      (by decide), (by decide), step355_2355_2439,
      (by decide), (by decide), step355_2440_2499, rfl⟩⟩

theorem step355_verified : Checked step355 :=
  ⟨step355_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step355_cover⟩

def step356 : Request :=
  ⟨⟨⟨350, 488, 106, 3008⟩, 1308168290304, 1584729438⟩, 2, 4, 41, 514287⟩

theorem step356_nodes : P1_7_1.nodeRows step356.bank.shape = step356.bank.nodeRows :=
  node_check step356.bank (by decide) (by decide) (by decide)

private theorem step356_2330_2332 : Positive step356 2330 2332 := by decide +kernel

private theorem step356_2333_2342 : Positive step356 2333 2342 := by decide +kernel

private theorem step356_2343_2374 : Positive step356 2343 2374 := by decide +kernel

private theorem step356_2375_2477 : Positive step356 2375 2477 := by decide +kernel

private theorem step356_2478_2499 : Positive step356 2478 2499 := by decide +kernel

theorem step356_cover : ∃ ends, Cover step356 firstHeight ends := by
  exact ⟨[2332, 2342, 2374, 2477, 2499],
    ⟨(by decide), (by decide), step356_2330_2332,
      (by decide), (by decide), step356_2333_2342,
      (by decide), (by decide), step356_2343_2374,
      (by decide), (by decide), step356_2375_2477,
      (by decide), (by decide), step356_2478_2499, rfl⟩⟩

theorem step356_verified : Checked step356 :=
  ⟨step356_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step356_cover⟩

def step357 : Request :=
  ⟨⟨⟨350, 488, 106, 3384⟩, 1308168290304, 1584729438⟩, 3, 4, 41, 514287⟩

theorem step357_nodes : P1_7_1.nodeRows step357.bank.shape = step357.bank.nodeRows :=
  node_check step357.bank (by decide) (by decide) (by decide)

private theorem step357_2330_2338 : Positive step357 2330 2338 := by decide +kernel

private theorem step357_2339_2367 : Positive step357 2339 2367 := by decide +kernel

private theorem step357_2368_2461 : Positive step357 2368 2461 := by decide +kernel

private theorem step357_2462_2499 : Positive step357 2462 2499 := by decide +kernel

theorem step357_cover : ∃ ends, Cover step357 firstHeight ends := by
  exact ⟨[2338, 2367, 2461, 2499],
    ⟨(by decide), (by decide), step357_2330_2338,
      (by decide), (by decide), step357_2339_2367,
      (by decide), (by decide), step357_2368_2461,
      (by decide), (by decide), step357_2462_2499, rfl⟩⟩

theorem step357_verified : Checked step357 :=
  ⟨step357_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step357_cover⟩

def step358 : Request :=
  ⟨⟨⟨350, 488, 108, 3807⟩, 1326705278976, 1607754763⟩, 4, 4, 41, 514287⟩

theorem step358_nodes : P1_7_1.nodeRows step358.bank.shape = step358.bank.nodeRows :=
  node_check step358.bank (by decide) (by decide) (by decide)

private theorem step358_2330_2344 : Positive step358 2330 2344 := by decide +kernel

private theorem step358_2345_2392 : Positive step358 2345 2392 := by decide +kernel

private theorem step358_2393_2499 : Positive step358 2393 2499 := by decide +kernel

theorem step358_cover : ∃ ends, Cover step358 firstHeight ends := by
  exact ⟨[2344, 2392, 2499],
    ⟨(by decide), (by decide), step358_2330_2344,
      (by decide), (by decide), step358_2345_2392,
      (by decide), (by decide), step358_2393_2499, rfl⟩⟩

theorem step358_verified : Checked step358 :=
  ⟨step358_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step358_cover⟩

def step359 : Request :=
  ⟨⟨⟨420, 586, 127, 3807⟩, 2252760678400, 3279920952⟩, 5, 4, 41, 514287⟩

theorem step359_nodes : P1_7_1.nodeRows step359.bank.shape = step359.bank.nodeRows :=
  node_check step359.bank (by decide) (by decide) (by decide)

private theorem step359_2330_2331 : Positive step359 2330 2331 := by decide +kernel

private theorem step359_2332_2338 : Positive step359 2332 2338 := by decide +kernel

private theorem step359_2339_2359 : Positive step359 2339 2359 := by decide +kernel

private theorem step359_2360_2424 : Positive step359 2360 2424 := by decide +kernel

private theorem step359_2425_2499 : Positive step359 2425 2499 := by decide +kernel

theorem step359_cover : ∃ ends, Cover step359 firstHeight ends := by
  exact ⟨[2331, 2338, 2359, 2424, 2499],
    ⟨(by decide), (by decide), step359_2330_2331,
      (by decide), (by decide), step359_2332_2338,
      (by decide), (by decide), step359_2339_2359,
      (by decide), (by decide), step359_2360_2424,
      (by decide), (by decide), step359_2425_2499, rfl⟩⟩

theorem step359_verified : Checked step359 :=
  ⟨step359_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step359_cover⟩

def step360 : Request :=
  ⟨⟨⟨520, 725, 157, 4282⟩, 4261264752640, 7658911630⟩, 7, 4, 41, 514287⟩

theorem step360_nodes : P1_7_1.nodeRows step360.bank.shape = step360.bank.nodeRows :=
  node_check step360.bank (by decide) (by decide) (by decide)

private theorem step360_2330_2336 : Positive step360 2330 2336 := by decide +kernel

private theorem step360_2337_2356 : Positive step360 2337 2356 := by decide +kernel

private theorem step360_2357_2416 : Positive step360 2357 2416 := by decide +kernel

private theorem step360_2417_2499 : Positive step360 2417 2499 := by decide +kernel

theorem step360_cover : ∃ ends, Cover step360 firstHeight ends := by
  exact ⟨[2336, 2356, 2416, 2499],
    ⟨(by decide), (by decide), step360_2330_2336,
      (by decide), (by decide), step360_2337_2356,
      (by decide), (by decide), step360_2357_2416,
      (by decide), (by decide), step360_2417_2499, rfl⟩⟩

theorem step360_verified : Checked step360 :=
  ⟨step360_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step360_cover⟩

def step361 : Request :=
  ⟨⟨⟨520, 725, 157, 5419⟩, 4261264752640, 7658911630⟩, 10, 4, 41, 514287⟩

theorem step361_nodes : P1_7_1.nodeRows step361.bank.shape = step361.bank.nodeRows :=
  node_check step361.bank (by decide) (by decide) (by decide)

private theorem step361_2330_2342 : Positive step361 2330 2342 := by decide +kernel

private theorem step361_2343_2381 : Positive step361 2343 2381 := by decide +kernel

private theorem step361_2382_2497 : Positive step361 2382 2497 := by decide +kernel

private theorem step361_2498_2499 : Positive step361 2498 2499 := by decide +kernel

theorem step361_cover : ∃ ends, Cover step361 firstHeight ends := by
  exact ⟨[2342, 2381, 2497, 2499],
    ⟨(by decide), (by decide), step361_2330_2342,
      (by decide), (by decide), step361_2343_2381,
      (by decide), (by decide), step361_2382_2497,
      (by decide), (by decide), step361_2498_2499, rfl⟩⟩

theorem step361_verified : Checked step361 :=
  ⟨step361_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step361_cover⟩

def step362 : Request :=
  ⟨⟨⟨750, 1046, 226, 6858⟩, 12730741817344, 33009058589⟩, 16, 4, 41, 514287⟩

theorem step362_nodes : P1_7_1.nodeRows step362.bank.shape = step362.bank.nodeRows :=
  node_check step362.bank (by decide) (by decide) (by decide)

private theorem step362_2330_2354 : Positive step362 2330 2354 := by decide +kernel

private theorem step362_2355_2426 : Positive step362 2355 2426 := by decide +kernel

private theorem step362_2427_2499 : Positive step362 2427 2499 := by decide +kernel

theorem step362_cover : ∃ ends, Cover step362 firstHeight ends := by
  exact ⟨[2354, 2426, 2499],
    ⟨(by decide), (by decide), step362_2330_2354,
      (by decide), (by decide), step362_2355_2426,
      (by decide), (by decide), step362_2427_2499, rfl⟩⟩

theorem step362_verified : Checked step362 :=
  ⟨step362_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step362_cover⟩

def step363 : Request :=
  ⟨⟨⟨750, 1046, 232, 7715⟩, 12985818152960, 33687112323⟩, 20, 4, 41, 514287⟩

theorem step363_nodes : P1_7_1.nodeRows step363.bank.shape = step363.bank.nodeRows :=
  node_check step363.bank (by decide) (by decide) (by decide)

private theorem step363_2330_2334 : Positive step363 2330 2334 := by decide +kernel

private theorem step363_2335_2348 : Positive step363 2335 2348 := by decide +kernel

private theorem step363_2349_2388 : Positive step363 2349 2388 := by decide +kernel

private theorem step363_2389_2499 : Positive step363 2389 2499 := by decide +kernel

theorem step363_cover : ∃ ends, Cover step363 firstHeight ends := by
  exact ⟨[2334, 2348, 2388, 2499],
    ⟨(by decide), (by decide), step363_2330_2334,
      (by decide), (by decide), step363_2335_2348,
      (by decide), (by decide), step363_2349_2388,
      (by decide), (by decide), step363_2389_2499, rfl⟩⟩

theorem step363_verified : Checked step363 :=
  ⟨step363_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step363_cover⟩

def step364 : Request :=
  ⟨⟨⟨1100, 1534, 332, 10983⟩, 40133103452160, 152499774767⟩, 31, 4, 41, 514287⟩

theorem step364_nodes : P1_7_1.nodeRows step364.bank.shape = step364.bank.nodeRows :=
  node_check step364.bank (by decide) (by decide) (by decide)

private theorem step364_2330_2349 : Positive step364 2330 2349 := by decide +kernel

private theorem step364_2350_2404 : Positive step364 2350 2404 := by decide +kernel

private theorem step364_2405_2499 : Positive step364 2405 2499 := by decide +kernel

theorem step364_cover : ∃ ends, Cover step364 firstHeight ends := by
  exact ⟨[2349, 2404, 2499],
    ⟨(by decide), (by decide), step364_2330_2349,
      (by decide), (by decide), step364_2350_2404,
      (by decide), (by decide), step364_2405_2499, rfl⟩⟩

theorem step364_verified : Checked step364 :=
  ⟨step364_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step364_cover⟩

def step365 : Request :=
  ⟨⟨⟨1100, 1534, 332, 10983⟩, 40133103452160, 152499774767⟩, 32, 4, 41, 514287⟩

theorem step365_nodes : P1_7_1.nodeRows step365.bank.shape = step365.bank.nodeRows :=
  node_check step365.bank (by decide) (by decide) (by decide)

private theorem step365_2330_2334 : Positive step365 2330 2334 := by decide +kernel

private theorem step365_2335_2348 : Positive step365 2335 2348 := by decide +kernel

private theorem step365_2349_2386 : Positive step365 2349 2386 := by decide +kernel

private theorem step365_2387_2491 : Positive step365 2387 2491 := by decide +kernel

private theorem step365_2492_2499 : Positive step365 2492 2499 := by decide +kernel

theorem step365_cover : ∃ ends, Cover step365 firstHeight ends := by
  exact ⟨[2334, 2348, 2386, 2491, 2499],
    ⟨(by decide), (by decide), step365_2330_2334,
      (by decide), (by decide), step365_2335_2348,
      (by decide), (by decide), step365_2349_2386,
      (by decide), (by decide), step365_2387_2491,
      (by decide), (by decide), step365_2492_2499, rfl⟩⟩

theorem step365_verified : Checked step365 :=
  ⟨step365_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step365_cover⟩

def step366 : Request :=
  ⟨⟨⟨1350, 1883, 418, 13899⟩, 75578221264896, 352769102024⟩, 44, 4, 41, 514287⟩

theorem step366_nodes : P1_7_1.nodeRows step366.bank.shape = step366.bank.nodeRows :=
  node_check step366.bank (by decide) (by decide) (by decide)

private theorem step366_2330_2338 : Positive step366 2330 2338 := by decide +kernel

private theorem step366_2339_2362 : Positive step366 2339 2362 := by decide +kernel

private theorem step366_2363_2427 : Positive step366 2363 2427 := by decide +kernel

private theorem step366_2428_2499 : Positive step366 2428 2499 := by decide +kernel

theorem step366_cover : ∃ ends, Cover step366 firstHeight ends := by
  exact ⟨[2338, 2362, 2427, 2499],
    ⟨(by decide), (by decide), step366_2330_2338,
      (by decide), (by decide), step366_2339_2362,
      (by decide), (by decide), step366_2363_2427,
      (by decide), (by decide), step366_2428_2499, rfl⟩⟩

theorem step366_verified : Checked step366 :=
  ⟨step366_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step366_cover⟩

def step367 : Request :=
  ⟨⟨⟨2500, 3488, 775, 19788⟩, 479640131993600, 4147842034257⟩, 73, 4, 41, 514287⟩

theorem step367_nodes : P1_7_1.nodeRows step367.bank.shape = step367.bank.nodeRows :=
  node_check step367.bank (by decide) (by decide) (by decide)

private theorem step367_2330_2333 : Positive step367 2330 2333 := by decide +kernel

private theorem step367_2334_2344 : Positive step367 2334 2344 := by decide +kernel

private theorem step367_2345_2373 : Positive step367 2345 2373 := by decide +kernel

private theorem step367_2374_2449 : Positive step367 2374 2449 := by decide +kernel

private theorem step367_2450_2499 : Positive step367 2450 2499 := by decide +kernel

theorem step367_cover : ∃ ends, Cover step367 firstHeight ends := by
  exact ⟨[2333, 2344, 2373, 2449, 2499],
    ⟨(by decide), (by decide), step367_2330_2333,
      (by decide), (by decide), step367_2334_2344,
      (by decide), (by decide), step367_2345_2373,
      (by decide), (by decide), step367_2374_2449,
      (by decide), (by decide), step367_2450_2499, rfl⟩⟩

theorem step367_verified : Checked step367 :=
  ⟨step367_nodes, Research6966.HelperWindowCatalogue.moment3488_775,
    (by decide), (by decide), (by decide), step367_cover⟩

def step368 : Request :=
  ⟨⟨⟨2500, 3488, 755, 22261⟩, 470210689105920, 4064279218567⟩, 76, 4, 41, 514287⟩

theorem step368_nodes : P1_7_1.nodeRows step368.bank.shape = step368.bank.nodeRows :=
  node_check step368.bank (by decide) (by decide) (by decide)

private theorem step368_2330_2350 : Positive step368 2330 2350 := by decide +kernel

private theorem step368_2351_2406 : Positive step368 2351 2406 := by decide +kernel

private theorem step368_2407_2499 : Positive step368 2407 2499 := by decide +kernel

theorem step368_cover : ∃ ends, Cover step368 firstHeight ends := by
  exact ⟨[2350, 2406, 2499],
    ⟨(by decide), (by decide), step368_2330_2350,
      (by decide), (by decide), step368_2351_2406,
      (by decide), (by decide), step368_2407_2499, rfl⟩⟩

theorem step368_verified : Checked step368 :=
  ⟨step368_nodes, Research6966.HelperWindowCatalogue.moment3488_755,
    (by decide), (by decide), (by decide), step368_cover⟩

def step369 : Request :=
  ⟨⟨⟨3000, 4185, 930, 28173⟩, 828559354757120, 8593576488693⟩, 103, 4, 41, 514287⟩

theorem step369_nodes : P1_7_1.nodeRows step369.bank.shape = step369.bank.nodeRows :=
  node_check step369.bank (by decide) (by decide) (by decide)

private theorem step369_2330_2345 : Positive step369 2330 2345 := by decide +kernel

private theorem step369_2346_2387 : Positive step369 2346 2387 := by decide +kernel

private theorem step369_2388_2498 : Positive step369 2388 2498 := by decide +kernel

private theorem step369_2499_2499 : Positive step369 2499 2499 := by decide +kernel

theorem step369_cover : ∃ ends, Cover step369 firstHeight ends := by
  exact ⟨[2345, 2387, 2498, 2499],
    ⟨(by decide), (by decide), step369_2330_2345,
      (by decide), (by decide), step369_2346_2387,
      (by decide), (by decide), step369_2388_2498,
      (by decide), (by decide), step369_2499_2499, rfl⟩⟩

theorem step369_verified : Checked step369 :=
  ⟨step369_nodes, Research6966.HelperWindowCatalogue.moment4185_930,
    (by decide), (by decide), (by decide), step369_cover⟩

def step370 : Request :=
  ⟨⟨⟨210, 293, 65, 2377⟩, 289785774080, 211692234⟩, 0, 4, 51, 514287⟩

theorem step370_nodes : P1_7_1.nodeRows step370.bank.shape = step370.bank.nodeRows :=
  node_check step370.bank (by decide) (by decide) (by decide)

private theorem step370_2330_2345 : Positive step370 2330 2345 := by decide +kernel

private theorem step370_2346_2407 : Positive step370 2346 2407 := by decide +kernel

private theorem step370_2408_2499 : Positive step370 2408 2499 := by decide +kernel

theorem step370_cover : ∃ ends, Cover step370 firstHeight ends := by
  exact ⟨[2345, 2407, 2499],
    ⟨(by decide), (by decide), step370_2330_2345,
      (by decide), (by decide), step370_2346_2407,
      (by decide), (by decide), step370_2408_2499, rfl⟩⟩

theorem step370_verified : Checked step370 :=
  ⟨step370_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step370_cover⟩

def step371 : Request :=
  ⟨⟨⟨250, 349, 76, 2377⟩, 480667500544, 418199213⟩, 1, 4, 51, 514287⟩

theorem step371_nodes : P1_7_1.nodeRows step371.bank.shape = step371.bank.nodeRows :=
  node_check step371.bank (by decide) (by decide) (by decide)

private theorem step371_2330_2336 : Positive step371 2330 2336 := by decide +kernel

private theorem step371_2337_2360 : Positive step371 2337 2360 := by decide +kernel

private theorem step371_2361_2446 : Positive step371 2361 2446 := by decide +kernel

private theorem step371_2447_2499 : Positive step371 2447 2499 := by decide +kernel

theorem step371_cover : ∃ ends, Cover step371 firstHeight ends := by
  exact ⟨[2336, 2360, 2446, 2499],
    ⟨(by decide), (by decide), step371_2330_2336,
      (by decide), (by decide), step371_2337_2360,
      (by decide), (by decide), step371_2361_2446,
      (by decide), (by decide), step371_2447_2499, rfl⟩⟩

theorem step371_verified : Checked step371 :=
  ⟨step371_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step371_cover⟩

def step372 : Request :=
  ⟨⟨⟨250, 349, 76, 3008⟩, 480667500544, 418199213⟩, 2, 4, 51, 514287⟩

theorem step372_nodes : P1_7_1.nodeRows step372.bank.shape = step372.bank.nodeRows :=
  node_check step372.bank (by decide) (by decide) (by decide)

private theorem step372_2330_2343 : Positive step372 2330 2343 := by decide +kernel

private theorem step372_2344_2393 : Positive step372 2344 2393 := by decide +kernel

private theorem step372_2394_2499 : Positive step372 2394 2499 := by decide +kernel

theorem step372_cover : ∃ ends, Cover step372 firstHeight ends := by
  exact ⟨[2343, 2393, 2499],
    ⟨(by decide), (by decide), step372_2330_2343,
      (by decide), (by decide), step372_2344_2393,
      (by decide), (by decide), step372_2394_2499, rfl⟩⟩

theorem step372_verified : Checked step372 :=
  ⟨step372_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step372_cover⟩

def step373 : Request :=
  ⟨⟨⟨294, 410, 89, 3008⟩, 777085255680, 791788817⟩, 3, 4, 51, 514287⟩

theorem step373_nodes : P1_7_1.nodeRows step373.bank.shape = step373.bank.nodeRows :=
  node_check step373.bank (by decide) (by decide) (by decide)

private theorem step373_2330_2367 : Positive step373 2330 2367 := by decide +kernel

private theorem step373_2368_2498 : Positive step373 2368 2498 := by decide +kernel

private theorem step373_2499_2499 : Positive step373 2499 2499 := by decide +kernel

theorem step373_cover : ∃ ends, Cover step373 firstHeight ends := by
  exact ⟨[2367, 2498, 2499],
    ⟨(by decide), (by decide), step373_2330_2367,
      (by decide), (by decide), step373_2368_2498,
      (by decide), (by decide), step373_2499_2499, rfl⟩⟩

theorem step373_verified : Checked step373 :=
  ⟨step373_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step373_cover⟩

def step374 : Request :=
  ⟨⟨⟨294, 410, 89, 3384⟩, 777085255680, 791788817⟩, 4, 4, 51, 514287⟩

theorem step374_nodes : P1_7_1.nodeRows step374.bank.shape = step374.bank.nodeRows :=
  node_check step374.bank (by decide) (by decide) (by decide)

private theorem step374_2330_2339 : Positive step374 2330 2339 := by decide +kernel

private theorem step374_2340_2373 : Positive step374 2340 2373 := by decide +kernel

private theorem step374_2374_2488 : Positive step374 2374 2488 := by decide +kernel

private theorem step374_2489_2499 : Positive step374 2489 2499 := by decide +kernel

theorem step374_cover : ∃ ends, Cover step374 firstHeight ends := by
  exact ⟨[2339, 2373, 2488, 2499],
    ⟨(by decide), (by decide), step374_2330_2339,
      (by decide), (by decide), step374_2340_2373,
      (by decide), (by decide), step374_2374_2488,
      (by decide), (by decide), step374_2489_2499, rfl⟩⟩

theorem step374_verified : Checked step374 :=
  ⟨step374_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step374_cover⟩

def step375 : Request :=
  ⟨⟨⟨350, 488, 104, 3384⟩, 1289487646720, 1561556019⟩, 5, 4, 51, 514287⟩

theorem step375_nodes : P1_7_1.nodeRows step375.bank.shape = step375.bank.nodeRows :=
  node_check step375.bank (by decide) (by decide) (by decide)

private theorem step375_2330_2338 : Positive step375 2330 2338 := by decide +kernel

private theorem step375_2339_2367 : Positive step375 2339 2367 := by decide +kernel

private theorem step375_2368_2462 : Positive step375 2368 2462 := by decide +kernel

private theorem step375_2463_2499 : Positive step375 2463 2499 := by decide +kernel

theorem step375_cover : ∃ ends, Cover step375 firstHeight ends := by
  exact ⟨[2338, 2367, 2462, 2499],
    ⟨(by decide), (by decide), step375_2330_2338,
      (by decide), (by decide), step375_2339_2367,
      (by decide), (by decide), step375_2368_2462,
      (by decide), (by decide), step375_2463_2499, rfl⟩⟩

theorem step375_verified : Checked step375 :=
  ⟨step375_nodes, Research6966.HelperWindowCatalogue.moment488_104,
    (by decide), (by decide), (by decide), step375_cover⟩

def step376 : Request :=
  ⟨⟨⟨350, 488, 106, 4282⟩, 1308168290304, 1584729438⟩, 7, 4, 51, 514287⟩

theorem step376_nodes : P1_7_1.nodeRows step376.bank.shape = step376.bank.nodeRows :=
  node_check step376.bank (by decide) (by decide) (by decide)

private theorem step376_2330_2338 : Positive step376 2330 2338 := by decide +kernel

private theorem step376_2339_2367 : Positive step376 2339 2367 := by decide +kernel

private theorem step376_2368_2461 : Positive step376 2368 2461 := by decide +kernel

private theorem step376_2462_2499 : Positive step376 2462 2499 := by decide +kernel

theorem step376_cover : ∃ ends, Cover step376 firstHeight ends := by
  exact ⟨[2338, 2367, 2461, 2499],
    ⟨(by decide), (by decide), step376_2330_2338,
      (by decide), (by decide), step376_2339_2367,
      (by decide), (by decide), step376_2368_2461,
      (by decide), (by decide), step376_2462_2499, rfl⟩⟩

theorem step376_verified : Checked step376 :=
  ⟨step376_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step376_cover⟩

def step377 : Request :=
  ⟨⟨⟨420, 586, 127, 4817⟩, 2252760678400, 3279920952⟩, 10, 4, 51, 514287⟩

theorem step377_nodes : P1_7_1.nodeRows step377.bank.shape = step377.bank.nodeRows :=
  node_check step377.bank (by decide) (by decide) (by decide)

private theorem step377_2330_2338 : Positive step377 2330 2338 := by decide +kernel

private theorem step377_2339_2366 : Positive step377 2339 2366 := by decide +kernel

private theorem step377_2367_2453 : Positive step377 2367 2453 := by decide +kernel

private theorem step377_2454_2499 : Positive step377 2454 2499 := by decide +kernel

theorem step377_cover : ∃ ends, Cover step377 firstHeight ends := by
  exact ⟨[2338, 2366, 2453, 2499],
    ⟨(by decide), (by decide), step377_2330_2338,
      (by decide), (by decide), step377_2339_2366,
      (by decide), (by decide), step377_2367_2453,
      (by decide), (by decide), step377_2454_2499, rfl⟩⟩

theorem step377_verified : Checked step377 :=
  ⟨step377_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step377_cover⟩

end Research6966.HelperRescueCatalogue
