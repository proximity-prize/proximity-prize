import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
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

def step378 : Request :=
  ⟨⟨⟨630, 879, 190, 5419⟩, 7559493713920, 16491913877⟩, 16, 4, 51, 514287⟩

theorem step378_nodes : P1_7_1.nodeRows step378.bank.shape = step378.bank.nodeRows :=
  node_check step378.bank (by decide) (by decide) (by decide)

private theorem step378_2330_2332 : Positive step378 2330 2332 := by decide +kernel

private theorem step378_2333_2341 : Positive step378 2333 2341 := by decide +kernel

private theorem step378_2342_2367 : Positive step378 2342 2367 := by decide +kernel

private theorem step378_2368_2442 : Positive step378 2368 2442 := by decide +kernel

private theorem step378_2443_2499 : Positive step378 2443 2499 := by decide +kernel

theorem step378_cover : ∃ ends, Cover step378 firstHeight ends := by
  exact ⟨[2332, 2341, 2367, 2442, 2499],
    ⟨(by decide), (by decide), step378_2330_2332,
      (by decide), (by decide), step378_2333_2341,
      (by decide), (by decide), step378_2342_2367,
      (by decide), (by decide), step378_2368_2442,
      (by decide), (by decide), step378_2443_2499, rfl⟩⟩

theorem step378_verified : Checked step378 :=
  ⟨step378_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step378_cover⟩

def step379 : Request :=
  ⟨⟨⟨630, 878, 195, 6858⟩, 7709474160640, 16765904450⟩, 20, 4, 51, 514287⟩

theorem step379_nodes : P1_7_1.nodeRows step379.bank.shape = step379.bank.nodeRows :=
  node_check step379.bank (by decide) (by decide) (by decide)

private theorem step379_2330_2351 : Positive step379 2330 2351 := by decide +kernel

private theorem step379_2352_2415 : Positive step379 2352 2415 := by decide +kernel

private theorem step379_2416_2499 : Positive step379 2416 2499 := by decide +kernel

theorem step379_cover : ∃ ends, Cover step379 firstHeight ends := by
  exact ⟨[2351, 2415, 2499],
    ⟨(by decide), (by decide), step379_2330_2351,
      (by decide), (by decide), step379_2352_2415,
      (by decide), (by decide), step379_2416_2499, rfl⟩⟩

theorem step379_verified : Checked step379 :=
  ⟨step379_nodes, Research6966.HelperWindowCatalogue.moment878_195,
    (by decide), (by decide), (by decide), step379_cover⟩

def step380 : Request :=
  ⟨⟨⟨900, 1255, 279, 8679⟩, 22452680785920, 69841856233⟩, 31, 4, 51, 514287⟩

theorem step380_nodes : P1_7_1.nodeRows step380.bank.shape = step380.bank.nodeRows :=
  node_check step380.bank (by decide) (by decide) (by decide)

private theorem step380_2330_2345 : Positive step380 2330 2345 := by decide +kernel

private theorem step380_2346_2390 : Positive step380 2346 2390 := by decide +kernel

private theorem step380_2391_2499 : Positive step380 2391 2499 := by decide +kernel

theorem step380_cover : ∃ ends, Cover step380 firstHeight ends := by
  exact ⟨[2345, 2390, 2499],
    ⟨(by decide), (by decide), step380_2330_2345,
      (by decide), (by decide), step380_2346_2390,
      (by decide), (by decide), step380_2391_2499, rfl⟩⟩

theorem step380_verified : Checked step380 :=
  ⟨step380_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step380_cover⟩

def step381 : Request :=
  ⟨⟨⟨900, 1255, 272, 9763⟩, 22024701870080, 68477558806⟩, 32, 4, 51, 514287⟩

theorem step381_nodes : P1_7_1.nodeRows step381.bank.shape = step381.bank.nodeRows :=
  node_check step381.bank (by decide) (by decide) (by decide)

private theorem step381_2330_2344 : Positive step381 2330 2344 := by decide +kernel

private theorem step381_2345_2386 : Positive step381 2345 2386 := by decide +kernel

private theorem step381_2387_2499 : Positive step381 2387 2499 := by decide +kernel

theorem step381_cover : ∃ ends, Cover step381 firstHeight ends := by
  exact ⟨[2344, 2386, 2499],
    ⟨(by decide), (by decide), step381_2330_2344,
      (by decide), (by decide), step381_2345_2386,
      (by decide), (by decide), step381_2387_2499, rfl⟩⟩

theorem step381_verified : Checked step381 :=
  ⟨step381_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step381_cover⟩

def step382 : Request :=
  ⟨⟨⟨1100, 1534, 341, 12355⟩, 40955142733824, 155702293064⟩, 44, 4, 51, 514287⟩

theorem step382_nodes : P1_7_1.nodeRows step382.bank.shape = step382.bank.nodeRows :=
  node_check step382.bank (by decide) (by decide) (by decide)

private theorem step382_2330_2336 : Positive step382 2330 2336 := by decide +kernel

private theorem step382_2337_2355 : Positive step382 2337 2355 := by decide +kernel

private theorem step382_2356_2407 : Positive step382 2356 2407 := by decide +kernel

private theorem step382_2408_2499 : Positive step382 2408 2499 := by decide +kernel

theorem step382_cover : ∃ ends, Cover step382 firstHeight ends := by
  exact ⟨[2336, 2355, 2407, 2499],
    ⟨(by decide), (by decide), step382_2330_2336,
      (by decide), (by decide), step382_2337_2355,
      (by decide), (by decide), step382_2356_2407,
      (by decide), (by decide), step382_2408_2499, rfl⟩⟩

theorem step382_verified : Checked step382 :=
  ⟨step382_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step382_cover⟩

def step383 : Request :=
  ⟨⟨⟨1650, 2301, 512, 19788⟩, 138129879859200, 787417379725⟩, 73, 4, 51, 514287⟩

theorem step383_nodes : P1_7_1.nodeRows step383.bank.shape = step383.bank.nodeRows :=
  node_check step383.bank (by decide) (by decide) (by decide)

private theorem step383_2330_2333 : Positive step383 2330 2333 := by decide +kernel

private theorem step383_2334_2343 : Positive step383 2334 2343 := by decide +kernel

private theorem step383_2344_2370 : Positive step383 2344 2370 := by decide +kernel

private theorem step383_2371_2442 : Positive step383 2371 2442 := by decide +kernel

private theorem step383_2443_2499 : Positive step383 2443 2499 := by decide +kernel

theorem step383_cover : ∃ ends, Cover step383 firstHeight ends := by
  exact ⟨[2333, 2343, 2370, 2442, 2499],
    ⟨(by decide), (by decide), step383_2330_2333,
      (by decide), (by decide), step383_2334_2343,
      (by decide), (by decide), step383_2344_2370,
      (by decide), (by decide), step383_2371_2442,
      (by decide), (by decide), step383_2443_2499, rfl⟩⟩

theorem step383_verified : Checked step383 :=
  ⟨step383_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step383_cover⟩

def step384 : Request :=
  ⟨⟨⟨2000, 2789, 620, 17590⟩, 245690786119680, 1697224818404⟩, 76, 4, 51, 514287⟩

theorem step384_nodes : P1_7_1.nodeRows step384.bank.shape = step384.bank.nodeRows :=
  node_check step384.bank (by decide) (by decide) (by decide)

private theorem step384_2330_2349 : Positive step384 2330 2349 := by decide +kernel

private theorem step384_2350_2402 : Positive step384 2350 2402 := by decide +kernel

private theorem step384_2403_2499 : Positive step384 2403 2499 := by decide +kernel

theorem step384_cover : ∃ ends, Cover step384 firstHeight ends := by
  exact ⟨[2349, 2402, 2499],
    ⟨(by decide), (by decide), step384_2330_2349,
      (by decide), (by decide), step384_2350_2402,
      (by decide), (by decide), step384_2403_2499, rfl⟩⟩

theorem step384_verified : Checked step384 :=
  ⟨step384_nodes, Research6966.HelperWindowCatalogue.moment2789_620,
    (by decide), (by decide), (by decide), step384_cover⟩

def step385 : Request :=
  ⟨⟨⟨2500, 3487, 755, 25043⟩, 470210689105920, 4060530796561⟩, 103, 4, 51, 514287⟩

theorem step385_nodes : P1_7_1.nodeRows step385.bank.shape = step385.bank.nodeRows :=
  node_check step385.bank (by decide) (by decide) (by decide)

private theorem step385_2330_2343 : Positive step385 2330 2343 := by decide +kernel

private theorem step385_2344_2380 : Positive step385 2344 2380 := by decide +kernel

private theorem step385_2381_2478 : Positive step385 2381 2478 := by decide +kernel

private theorem step385_2479_2499 : Positive step385 2479 2499 := by decide +kernel

theorem step385_cover : ∃ ends, Cover step385 firstHeight ends := by
  exact ⟨[2343, 2380, 2478, 2499],
    ⟨(by decide), (by decide), step385_2330_2343,
      (by decide), (by decide), step385_2344_2380,
      (by decide), (by decide), step385_2381_2478,
      (by decide), (by decide), step385_2479_2499, rfl⟩⟩

theorem step385_verified : Checked step385 :=
  ⟨step385_nodes, Research6966.HelperWindowCatalogue.moment3487_755,
    (by decide), (by decide), (by decide), step385_cover⟩

def step386 : Request :=
  ⟨⟨⟨170, 237, 51, 2113⟩, 150975545344, 89126689⟩, 0, 4, 71, 514287⟩

theorem step386_nodes : P1_7_1.nodeRows step386.bank.shape = step386.bank.nodeRows :=
  node_check step386.bank (by decide) (by decide) (by decide)

private theorem step386_2330_2339 : Positive step386 2330 2339 := by decide +kernel

private theorem step386_2340_2384 : Positive step386 2340 2384 := by decide +kernel

private theorem step386_2385_2499 : Positive step386 2385 2499 := by decide +kernel

theorem step386_cover : ∃ ends, Cover step386 firstHeight ends := by
  exact ⟨[2339, 2384, 2499],
    ⟨(by decide), (by decide), step386_2330_2339,
      (by decide), (by decide), step386_2340_2384,
      (by decide), (by decide), step386_2385_2499, rfl⟩⟩

theorem step386_verified : Checked step386 :=
  ⟨step386_nodes, Research6966.HelperWindowCatalogue.moment237_51,
    (by decide), (by decide), (by decide), step386_cover⟩

def step387 : Request :=
  ⟨⟨⟨210, 293, 65, 1879⟩, 289785774080, 211692234⟩, 1, 4, 71, 514287⟩

theorem step387_nodes : P1_7_1.nodeRows step387.bank.shape = step387.bank.nodeRows :=
  node_check step387.bank (by decide) (by decide) (by decide)

private theorem step387_2330_2348 : Positive step387 2330 2348 := by decide +kernel

private theorem step387_2349_2422 : Positive step387 2349 2422 := by decide +kernel

private theorem step387_2423_2499 : Positive step387 2423 2499 := by decide +kernel

theorem step387_cover : ∃ ends, Cover step387 firstHeight ends := by
  exact ⟨[2348, 2422, 2499],
    ⟨(by decide), (by decide), step387_2330_2348,
      (by decide), (by decide), step387_2349_2422,
      (by decide), (by decide), step387_2423_2499, rfl⟩⟩

theorem step387_verified : Checked step387 :=
  ⟨step387_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step387_cover⟩

def step388 : Request :=
  ⟨⟨⟨210, 293, 63, 2377⟩, 283090354176, 206678784⟩, 2, 4, 71, 514287⟩

theorem step388_nodes : P1_7_1.nodeRows step388.bank.shape = step388.bank.nodeRows :=
  node_check step388.bank (by decide) (by decide) (by decide)

private theorem step388_2330_2344 : Positive step388 2330 2344 := by decide +kernel

private theorem step388_2345_2402 : Positive step388 2345 2402 := by decide +kernel

private theorem step388_2403_2499 : Positive step388 2403 2499 := by decide +kernel

theorem step388_cover : ∃ ends, Cover step388 firstHeight ends := by
  exact ⟨[2344, 2402, 2499],
    ⟨(by decide), (by decide), step388_2330_2344,
      (by decide), (by decide), step388_2345_2402,
      (by decide), (by decide), step388_2403_2499, rfl⟩⟩

theorem step388_verified : Checked step388 :=
  ⟨step388_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step388_cover⟩

def step389 : Request :=
  ⟨⟨⟨250, 348, 74, 2377⟩, 471125196800, 405945859⟩, 3, 4, 71, 514287⟩

theorem step389_nodes : P1_7_1.nodeRows step389.bank.shape = step389.bank.nodeRows :=
  node_check step389.bank (by decide) (by decide) (by decide)

private theorem step389_2330_2347 : Positive step389 2330 2347 := by decide +kernel

private theorem step389_2348_2413 : Positive step389 2348 2413 := by decide +kernel

private theorem step389_2414_2499 : Positive step389 2414 2499 := by decide +kernel

theorem step389_cover : ∃ ends, Cover step389 firstHeight ends := by
  exact ⟨[2347, 2413, 2499],
    ⟨(by decide), (by decide), step389_2330_2347,
      (by decide), (by decide), step389_2348_2413,
      (by decide), (by decide), step389_2414_2499, rfl⟩⟩

theorem step389_verified : Checked step389 :=
  ⟨step389_nodes, Research6966.HelperWindowCatalogue.moment348_74,
    (by decide), (by decide), (by decide), step389_cover⟩

def step390 : Request :=
  ⟨⟨⟨250, 348, 76, 2674⟩, 480667500544, 414368386⟩, 4, 4, 71, 514287⟩

theorem step390_nodes : P1_7_1.nodeRows step390.bank.shape = step390.bank.nodeRows :=
  node_check step390.bank (by decide) (by decide) (by decide)

private theorem step390_2330_2375 : Positive step390 2330 2375 := by decide +kernel

private theorem step390_2376_2499 : Positive step390 2376 2499 := by decide +kernel

theorem step390_cover : ∃ ends, Cover step390 firstHeight ends := by
  exact ⟨[2375, 2499],
    ⟨(by decide), (by decide), step390_2330_2375,
      (by decide), (by decide), step390_2376_2499, rfl⟩⟩

theorem step390_verified : Checked step390 :=
  ⟨step390_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step390_cover⟩

def step391 : Request :=
  ⟨⟨⟨250, 348, 76, 3008⟩, 480667500544, 414368386⟩, 5, 4, 71, 514287⟩

theorem step391_nodes : P1_7_1.nodeRows step391.bank.shape = step391.bank.nodeRows :=
  node_check step391.bank (by decide) (by decide) (by decide)

private theorem step391_2330_2332 : Positive step391 2330 2332 := by decide +kernel

private theorem step391_2333_2343 : Positive step391 2333 2343 := by decide +kernel

private theorem step391_2344_2382 : Positive step391 2344 2382 := by decide +kernel

private theorem step391_2383_2499 : Positive step391 2383 2499 := by decide +kernel

theorem step391_cover : ∃ ends, Cover step391 firstHeight ends := by
  exact ⟨[2332, 2343, 2382, 2499],
    ⟨(by decide), (by decide), step391_2330_2332,
      (by decide), (by decide), step391_2333_2343,
      (by decide), (by decide), step391_2344_2382,
      (by decide), (by decide), step391_2383_2499, rfl⟩⟩

theorem step391_verified : Checked step391 :=
  ⟨step391_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step391_cover⟩

def step392 : Request :=
  ⟨⟨⟨294, 410, 89, 3384⟩, 777085255680, 791788817⟩, 7, 4, 71, 514287⟩

theorem step392_nodes : P1_7_1.nodeRows step392.bank.shape = step392.bank.nodeRows :=
  node_check step392.bank (by decide) (by decide) (by decide)

private theorem step392_2330_2354 : Positive step392 2330 2354 := by decide +kernel

private theorem step392_2355_2439 : Positive step392 2355 2439 := by decide +kernel

private theorem step392_2440_2499 : Positive step392 2440 2499 := by decide +kernel

theorem step392_cover : ∃ ends, Cover step392 firstHeight ends := by
  exact ⟨[2354, 2439, 2499],
    ⟨(by decide), (by decide), step392_2330_2354,
      (by decide), (by decide), step392_2355_2439,
      (by decide), (by decide), step392_2440_2499, rfl⟩⟩

theorem step392_verified : Checked step392 :=
  ⟨step392_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step392_cover⟩

def step393 : Request :=
  ⟨⟨⟨350, 488, 106, 3807⟩, 1308168290304, 1584729438⟩, 10, 4, 71, 514287⟩

theorem step393_nodes : P1_7_1.nodeRows step393.bank.shape = step393.bank.nodeRows :=
  node_check step393.bank (by decide) (by decide) (by decide)

private theorem step393_2330_2348 : Positive step393 2330 2348 := by decide +kernel

private theorem step393_2349_2410 : Positive step393 2349 2410 := by decide +kernel

private theorem step393_2411_2499 : Positive step393 2411 2499 := by decide +kernel

theorem step393_cover : ∃ ends, Cover step393 firstHeight ends := by
  exact ⟨[2348, 2410, 2499],
    ⟨(by decide), (by decide), step393_2330_2348,
      (by decide), (by decide), step393_2349_2410,
      (by decide), (by decide), step393_2411_2499, rfl⟩⟩

theorem step393_verified : Checked step393 :=
  ⟨step393_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step393_cover⟩

def step394 : Request :=
  ⟨⟨⟨420, 585, 130, 5419⟩, 2292767784960, 3321371304⟩, 16, 4, 71, 514287⟩

theorem step394_nodes : P1_7_1.nodeRows step394.bank.shape = step394.bank.nodeRows :=
  node_check step394.bank (by decide) (by decide) (by decide)

private theorem step394_2330_2331 : Positive step394 2330 2331 := by decide +kernel

private theorem step394_2332_2337 : Positive step394 2332 2337 := by decide +kernel

private theorem step394_2338_2356 : Positive step394 2338 2356 := by decide +kernel

private theorem step394_2357_2414 : Positive step394 2357 2414 := by decide +kernel

private theorem step394_2415_2499 : Positive step394 2415 2499 := by decide +kernel

theorem step394_cover : ∃ ends, Cover step394 firstHeight ends := by
  exact ⟨[2331, 2337, 2356, 2414, 2499],
    ⟨(by decide), (by decide), step394_2330_2331,
      (by decide), (by decide), step394_2332_2337,
      (by decide), (by decide), step394_2338_2356,
      (by decide), (by decide), step394_2357_2414,
      (by decide), (by decide), step394_2415_2499, rfl⟩⟩

theorem step394_verified : Checked step394 :=
  ⟨step394_nodes, Research6966.HelperWindowCatalogue.moment585_130,
    (by decide), (by decide), (by decide), step394_cover⟩

def step395 : Request :=
  ⟨⟨⟨520, 725, 161, 5419⟩, 4343013310464, 7809559934⟩, 20, 4, 71, 514287⟩

theorem step395_nodes : P1_7_1.nodeRows step395.bank.shape = step395.bank.nodeRows :=
  node_check step395.bank (by decide) (by decide) (by decide)

private theorem step395_2330_2345 : Positive step395 2330 2345 := by decide +kernel

private theorem step395_2346_2392 : Positive step395 2346 2392 := by decide +kernel

private theorem step395_2393_2499 : Positive step395 2393 2499 := by decide +kernel

theorem step395_cover : ∃ ends, Cover step395 firstHeight ends := by
  exact ⟨[2345, 2392, 2499],
    ⟨(by decide), (by decide), step395_2330_2345,
      (by decide), (by decide), step395_2346_2392,
      (by decide), (by decide), step395_2393_2499, rfl⟩⟩

theorem step395_verified : Checked step395 :=
  ⟨step395_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step395_cover⟩

def step396 : Request :=
  ⟨⟨⟨750, 1046, 232, 6858⟩, 12985818152960, 33687112323⟩, 31, 4, 71, 514287⟩

theorem step396_nodes : P1_7_1.nodeRows step396.bank.shape = step396.bank.nodeRows :=
  node_check step396.bank (by decide) (by decide) (by decide)

private theorem step396_2330_2336 : Positive step396 2330 2336 := by decide +kernel

private theorem step396_2337_2355 : Positive step396 2337 2355 := by decide +kernel

private theorem step396_2356_2409 : Positive step396 2356 2409 := by decide +kernel

private theorem step396_2410_2499 : Positive step396 2410 2499 := by decide +kernel

theorem step396_cover : ∃ ends, Cover step396 firstHeight ends := by
  exact ⟨[2336, 2355, 2409, 2499],
    ⟨(by decide), (by decide), step396_2330_2336,
      (by decide), (by decide), step396_2337_2355,
      (by decide), (by decide), step396_2356_2409,
      (by decide), (by decide), step396_2410_2499, rfl⟩⟩

theorem step396_verified : Checked step396 :=
  ⟨step396_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step396_cover⟩

def step397 : Request :=
  ⟨⟨⟨750, 1046, 226, 7715⟩, 12730741817344, 33009058589⟩, 32, 4, 71, 514287⟩

theorem step397_nodes : P1_7_1.nodeRows step397.bank.shape = step397.bank.nodeRows :=
  node_check step397.bank (by decide) (by decide) (by decide)

private theorem step397_2330_2342 : Positive step397 2330 2342 := by decide +kernel

private theorem step397_2343_2379 : Positive step397 2343 2379 := by decide +kernel

private theorem step397_2380_2484 : Positive step397 2380 2484 := by decide +kernel

private theorem step397_2485_2499 : Positive step397 2485 2499 := by decide +kernel

theorem step397_cover : ∃ ends, Cover step397 firstHeight ends := by
  exact ⟨[2342, 2379, 2484, 2499],
    ⟨(by decide), (by decide), step397_2330_2342,
      (by decide), (by decide), step397_2343_2379,
      (by decide), (by decide), step397_2380_2484,
      (by decide), (by decide), step397_2485_2499, rfl⟩⟩

theorem step397_verified : Checked step397 :=
  ⟨step397_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step397_cover⟩

def step398 : Request :=
  ⟨⟨⟨900, 1255, 272, 10983⟩, 22024701870080, 68477558806⟩, 44, 4, 71, 514287⟩

theorem step398_nodes : P1_7_1.nodeRows step398.bank.shape = step398.bank.nodeRows :=
  node_check step398.bank (by decide) (by decide) (by decide)

private theorem step398_2330_2333 : Positive step398 2330 2333 := by decide +kernel

private theorem step398_2334_2344 : Positive step398 2334 2344 := by decide +kernel

private theorem step398_2345_2375 : Positive step398 2345 2375 := by decide +kernel

private theorem step398_2376_2461 : Positive step398 2376 2461 := by decide +kernel

private theorem step398_2462_2499 : Positive step398 2462 2499 := by decide +kernel

theorem step398_cover : ∃ ends, Cover step398 firstHeight ends := by
  exact ⟨[2333, 2344, 2375, 2461, 2499],
    ⟨(by decide), (by decide), step398_2330_2333,
      (by decide), (by decide), step398_2334_2344,
      (by decide), (by decide), step398_2345_2375,
      (by decide), (by decide), step398_2376_2461,
      (by decide), (by decide), step398_2462_2499, rfl⟩⟩

theorem step398_verified : Checked step398 :=
  ⟨step398_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step398_cover⟩

def step399 : Request :=
  ⟨⟨⟨1350, 1882, 418, 17590⟩, 75578221264896, 352166349574⟩, 73, 4, 71, 514287⟩

theorem step399_nodes : P1_7_1.nodeRows step399.bank.shape = step399.bank.nodeRows :=
  node_check step399.bank (by decide) (by decide) (by decide)

private theorem step399_2330_2346 : Positive step399 2330 2346 := by decide +kernel

private theorem step399_2347_2392 : Positive step399 2347 2392 := by decide +kernel

private theorem step399_2393_2499 : Positive step399 2393 2499 := by decide +kernel

theorem step399_cover : ∃ ends, Cover step399 firstHeight ends := by
  exact ⟨[2346, 2392, 2499],
    ⟨(by decide), (by decide), step399_2330_2346,
      (by decide), (by decide), step399_2347_2392,
      (by decide), (by decide), step399_2393_2499, rfl⟩⟩

theorem step399_verified : Checked step399 :=
  ⟨step399_nodes, Research6966.HelperWindowCatalogue.moment1882_418,
    (by decide), (by decide), (by decide), step399_cover⟩

def step400 : Request :=
  ⟨⟨⟨1650, 2301, 512, 13899⟩, 138129879859200, 787417379725⟩, 76, 4, 71, 514287⟩

theorem step400_nodes : P1_7_1.nodeRows step400.bank.shape = step400.bank.nodeRows :=
  node_check step400.bank (by decide) (by decide) (by decide)

private theorem step400_2330_2336 : Positive step400 2330 2336 := by decide +kernel

private theorem step400_2337_2354 : Positive step400 2337 2354 := by decide +kernel

private theorem step400_2355_2402 : Positive step400 2355 2402 := by decide +kernel

private theorem step400_2403_2499 : Positive step400 2403 2499 := by decide +kernel

theorem step400_cover : ∃ ends, Cover step400 firstHeight ends := by
  exact ⟨[2336, 2354, 2402, 2499],
    ⟨(by decide), (by decide), step400_2330_2336,
      (by decide), (by decide), step400_2337_2354,
      (by decide), (by decide), step400_2355_2402,
      (by decide), (by decide), step400_2403_2499, rfl⟩⟩

theorem step400_verified : Checked step400 :=
  ⟨step400_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step400_cover⟩

def step401 : Request :=
  ⟨⟨⟨2000, 2788, 620, 19788⟩, 245690786119680, 1695265997069⟩, 103, 4, 71, 514287⟩

theorem step401_nodes : P1_7_1.nodeRows step401.bank.shape = step401.bank.nodeRows :=
  node_check step401.bank (by decide) (by decide) (by decide)

private theorem step401_2330_2350 : Positive step401 2330 2350 := by decide +kernel

private theorem step401_2351_2406 : Positive step401 2351 2406 := by decide +kernel

private theorem step401_2407_2499 : Positive step401 2407 2499 := by decide +kernel

theorem step401_cover : ∃ ends, Cover step401 firstHeight ends := by
  exact ⟨[2350, 2406, 2499],
    ⟨(by decide), (by decide), step401_2330_2350,
      (by decide), (by decide), step401_2351_2406,
      (by decide), (by decide), step401_2407_2499, rfl⟩⟩

theorem step401_verified : Checked step401 :=
  ⟨step401_nodes, Research6966.HelperWindowCatalogue.moment2788_620,
    (by decide), (by decide), (by decide), step401_cover⟩

def step402 : Request :=
  ⟨⟨⟨350, 488, 108, 7715⟩, 1326705278976, 1607754763⟩, 0, 5, 1, 642859⟩

theorem step402_nodes : P1_7_1.nodeRows step402.bank.shape = step402.bank.nodeRows :=
  node_check step402.bank (by decide) (by decide) (by decide)

private theorem step402_2330_2334 : Positive step402 2330 2334 := by decide +kernel

private theorem step402_2335_2350 : Positive step402 2335 2350 := by decide +kernel

private theorem step402_2351_2401 : Positive step402 2351 2401 := by decide +kernel

private theorem step402_2402_2499 : Positive step402 2402 2499 := by decide +kernel

theorem step402_cover : ∃ ends, Cover step402 firstHeight ends := by
  exact ⟨[2334, 2350, 2401, 2499],
    ⟨(by decide), (by decide), step402_2330_2334,
      (by decide), (by decide), step402_2335_2350,
      (by decide), (by decide), step402_2351_2401,
      (by decide), (by decide), step402_2402_2499, rfl⟩⟩

theorem step402_verified : Checked step402 :=
  ⟨step402_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step402_cover⟩

def step403 : Request :=
  ⟨⟨⟨350, 488, 108, 8679⟩, 1326705278976, 1607754763⟩, 1, 5, 1, 642859⟩

theorem step403_nodes : P1_7_1.nodeRows step403.bank.shape = step403.bank.nodeRows :=
  node_check step403.bank (by decide) (by decide) (by decide)

private theorem step403_2330_2332 : Positive step403 2330 2332 := by decide +kernel

private theorem step403_2333_2341 : Positive step403 2333 2341 := by decide +kernel

private theorem step403_2342_2370 : Positive step403 2342 2370 := by decide +kernel

private theorem step403_2371_2462 : Positive step403 2371 2462 := by decide +kernel

private theorem step403_2463_2499 : Positive step403 2463 2499 := by decide +kernel

theorem step403_cover : ∃ ends, Cover step403 firstHeight ends := by
  exact ⟨[2332, 2341, 2370, 2462, 2499],
    ⟨(by decide), (by decide), step403_2330_2332,
      (by decide), (by decide), step403_2333_2341,
      (by decide), (by decide), step403_2342_2370,
      (by decide), (by decide), step403_2371_2462,
      (by decide), (by decide), step403_2463_2499, rfl⟩⟩

theorem step403_verified : Checked step403 :=
  ⟨step403_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step403_cover⟩

def step404 : Request :=
  ⟨⟨⟨420, 586, 127, 9763⟩, 2252760678400, 3279920952⟩, 2, 5, 1, 642859⟩

theorem step404_nodes : P1_7_1.nodeRows step404.bank.shape = step404.bank.nodeRows :=
  node_check step404.bank (by decide) (by decide) (by decide)

private theorem step404_2330_2351 : Positive step404 2330 2351 := by decide +kernel

private theorem step404_2352_2419 : Positive step404 2352 2419 := by decide +kernel

private theorem step404_2420_2499 : Positive step404 2420 2499 := by decide +kernel

theorem step404_cover : ∃ ends, Cover step404 firstHeight ends := by
  exact ⟨[2351, 2419, 2499],
    ⟨(by decide), (by decide), step404_2330_2351,
      (by decide), (by decide), step404_2352_2419,
      (by decide), (by decide), step404_2420_2499, rfl⟩⟩

theorem step404_verified : Checked step404 :=
  ⟨step404_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step404_cover⟩

def step405 : Request :=
  ⟨⟨⟨420, 586, 127, 10983⟩, 2252760678400, 3279920952⟩, 3, 5, 1, 642859⟩

theorem step405_nodes : P1_7_1.nodeRows step405.bank.shape = step405.bank.nodeRows :=
  node_check step405.bank (by decide) (by decide) (by decide)

private theorem step405_2330_2355 : Positive step405 2330 2355 := by decide +kernel

private theorem step405_2356_2435 : Positive step405 2356 2435 := by decide +kernel

private theorem step405_2436_2499 : Positive step405 2436 2499 := by decide +kernel

theorem step405_cover : ∃ ends, Cover step405 firstHeight ends := by
  exact ⟨[2355, 2435, 2499],
    ⟨(by decide), (by decide), step405_2330_2355,
      (by decide), (by decide), step405_2356_2435,
      (by decide), (by decide), step405_2436_2499, rfl⟩⟩

theorem step405_verified : Checked step405 :=
  ⟨step405_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step405_cover⟩

def step406 : Request :=
  ⟨⟨⟨520, 725, 157, 10983⟩, 4261264752640, 7658911630⟩, 4, 5, 1, 642859⟩

theorem step406_nodes : P1_7_1.nodeRows step406.bank.shape = step406.bank.nodeRows :=
  node_check step406.bank (by decide) (by decide) (by decide)

private theorem step406_2330_2340 : Positive step406 2330 2340 := by decide +kernel

private theorem step406_2341_2372 : Positive step406 2341 2372 := by decide +kernel

private theorem step406_2373_2468 : Positive step406 2373 2468 := by decide +kernel

private theorem step406_2469_2499 : Positive step406 2469 2499 := by decide +kernel

theorem step406_cover : ∃ ends, Cover step406 firstHeight ends := by
  exact ⟨[2340, 2372, 2468, 2499],
    ⟨(by decide), (by decide), step406_2330_2340,
      (by decide), (by decide), step406_2341_2372,
      (by decide), (by decide), step406_2373_2468,
      (by decide), (by decide), step406_2469_2499, rfl⟩⟩

theorem step406_verified : Checked step406 :=
  ⟨step406_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step406_cover⟩

def step407 : Request :=
  ⟨⟨⟨520, 725, 154, 12355⟩, 4199390904320, 7545064854⟩, 5, 5, 1, 642859⟩

theorem step407_nodes : P1_7_1.nodeRows step407.bank.shape = step407.bank.nodeRows :=
  node_check step407.bank (by decide) (by decide) (by decide)

private theorem step407_2330_2333 : Positive step407 2330 2333 := by decide +kernel

private theorem step407_2334_2345 : Positive step407 2334 2345 := by decide +kernel

private theorem step407_2346_2381 : Positive step407 2346 2381 := by decide +kernel

private theorem step407_2382_2489 : Positive step407 2382 2489 := by decide +kernel

private theorem step407_2490_2499 : Positive step407 2490 2499 := by decide +kernel

theorem step407_cover : ∃ ends, Cover step407 firstHeight ends := by
  exact ⟨[2333, 2345, 2381, 2489, 2499],
    ⟨(by decide), (by decide), step407_2330_2333,
      (by decide), (by decide), step407_2334_2345,
      (by decide), (by decide), step407_2346_2381,
      (by decide), (by decide), step407_2382_2489,
      (by decide), (by decide), step407_2490_2499, rfl⟩⟩

theorem step407_verified : Checked step407 :=
  ⟨step407_nodes, Research6966.HelperWindowCatalogue.moment725_154,
    (by decide), (by decide), (by decide), step407_cover⟩

def step408 : Request :=
  ⟨⟨⟨520, 725, 157, 13899⟩, 4261264752640, 7658911630⟩, 7, 5, 1, 642859⟩

theorem step408_nodes : P1_7_1.nodeRows step408.bank.shape = step408.bank.nodeRows :=
  node_check step408.bank (by decide) (by decide) (by decide)

private theorem step408_2330_2333 : Positive step408 2330 2333 := by decide +kernel

private theorem step408_2334_2345 : Positive step408 2334 2345 := by decide +kernel

private theorem step408_2346_2380 : Positive step408 2346 2380 := by decide +kernel

private theorem step408_2381_2484 : Positive step408 2381 2484 := by decide +kernel

private theorem step408_2485_2499 : Positive step408 2485 2499 := by decide +kernel

theorem step408_cover : ∃ ends, Cover step408 firstHeight ends := by
  exact ⟨[2333, 2345, 2380, 2484, 2499],
    ⟨(by decide), (by decide), step408_2330_2333,
      (by decide), (by decide), step408_2334_2345,
      (by decide), (by decide), step408_2346_2380,
      (by decide), (by decide), step408_2381_2484,
      (by decide), (by decide), step408_2485_2499, rfl⟩⟩

theorem step408_verified : Checked step408 :=
  ⟨step408_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step408_cover⟩

def step409 : Request :=
  ⟨⟨⟨630, 879, 195, 15636⟩, 7709474160640, 16827402390⟩, 10, 5, 1, 642859⟩

theorem step409_nodes : P1_7_1.nodeRows step409.bank.shape = step409.bank.nodeRows :=
  node_check step409.bank (by decide) (by decide) (by decide)

private theorem step409_2330_2334 : Positive step409 2330 2334 := by decide +kernel

private theorem step409_2335_2348 : Positive step409 2335 2348 := by decide +kernel

private theorem step409_2349_2388 : Positive step409 2349 2388 := by decide +kernel

private theorem step409_2389_2499 : Positive step409 2389 2499 := by decide +kernel

theorem step409_cover : ∃ ends, Cover step409 firstHeight ends := by
  exact ⟨[2334, 2348, 2388, 2499],
    ⟨(by decide), (by decide), step409_2330_2334,
      (by decide), (by decide), step409_2335_2348,
      (by decide), (by decide), step409_2349_2388,
      (by decide), (by decide), step409_2389_2499, rfl⟩⟩

theorem step409_verified : Checked step409 :=
  ⟨step409_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step409_cover⟩

def step410 : Request :=
  ⟨⟨⟨900, 1256, 279, 19788⟩, 22452680785920, 70021105933⟩, 16, 5, 1, 642859⟩

theorem step410_nodes : P1_7_1.nodeRows step410.bank.shape = step410.bank.nodeRows :=
  node_check step410.bank (by decide) (by decide) (by decide)

private theorem step410_2330_2338 : Positive step410 2330 2338 := by decide +kernel

private theorem step410_2339_2362 : Positive step410 2339 2362 := by decide +kernel

private theorem step410_2363_2428 : Positive step410 2363 2428 := by decide +kernel

private theorem step410_2429_2499 : Positive step410 2429 2499 := by decide +kernel

theorem step410_cover : ∃ ends, Cover step410 firstHeight ends := by
  exact ⟨[2338, 2362, 2428, 2499],
    ⟨(by decide), (by decide), step410_2330_2338,
      (by decide), (by decide), step410_2339_2362,
      (by decide), (by decide), step410_2363_2428,
      (by decide), (by decide), step410_2429_2499, rfl⟩⟩

theorem step410_verified : Checked step410 :=
  ⟨step410_nodes, Research6966.HelperWindowCatalogue.moment1256_279,
    (by decide), (by decide), (by decide), step410_cover⟩

def step411 : Request :=
  ⟨⟨⟨1100, 1535, 341, 22261⟩, 40955142733824, 156029238110⟩, 20, 5, 1, 642859⟩

theorem step411_nodes : P1_7_1.nodeRows step411.bank.shape = step411.bank.nodeRows :=
  node_check step411.bank (by decide) (by decide) (by decide)

private theorem step411_2330_2331 : Positive step411 2330 2331 := by decide +kernel

private theorem step411_2332_2336 : Positive step411 2332 2336 := by decide +kernel

private theorem step411_2337_2350 : Positive step411 2337 2350 := by decide +kernel

private theorem step411_2351_2387 : Positive step411 2351 2387 := by decide +kernel

private theorem step411_2388_2488 : Positive step411 2388 2488 := by decide +kernel

private theorem step411_2489_2499 : Positive step411 2489 2499 := by decide +kernel

theorem step411_cover : ∃ ends, Cover step411 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2387, 2488, 2499],
    ⟨(by decide), (by decide), step411_2330_2331,
      (by decide), (by decide), step411_2332_2336,
      (by decide), (by decide), step411_2337_2350,
      (by decide), (by decide), step411_2351_2387,
      (by decide), (by decide), step411_2388_2488,
      (by decide), (by decide), step411_2489_2499, rfl⟩⟩

theorem step411_verified : Checked step411 :=
  ⟨step411_nodes, Research6966.HelperWindowCatalogue.moment1535_341,
    (by decide), (by decide), (by decide), step411_cover⟩

def step412 : Request :=
  ⟨⟨⟨1350, 1883, 408, 31694⟩, 74202776600576, 346190054868⟩, 31, 5, 1, 642859⟩

theorem step412_nodes : P1_7_1.nodeRows step412.bank.shape = step412.bank.nodeRows :=
  node_check step412.bank (by decide) (by decide) (by decide)

private theorem step412_2330_2331 : Positive step412 2330 2331 := by decide +kernel

private theorem step412_2332_2336 : Positive step412 2332 2336 := by decide +kernel

private theorem step412_2337_2349 : Positive step412 2337 2349 := by decide +kernel

private theorem step412_2350_2384 : Positive step412 2350 2384 := by decide +kernel

private theorem step412_2385_2479 : Positive step412 2385 2479 := by decide +kernel

private theorem step412_2480_2499 : Positive step412 2480 2499 := by decide +kernel

theorem step412_cover : ∃ ends, Cover step412 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2384, 2479, 2499],
    ⟨(by decide), (by decide), step412_2330_2331,
      (by decide), (by decide), step412_2332_2336,
      (by decide), (by decide), step412_2337_2349,
      (by decide), (by decide), step412_2350_2384,
      (by decide), (by decide), step412_2385_2479,
      (by decide), (by decide), step412_2480_2499, rfl⟩⟩

theorem step412_verified : Checked step412 :=
  ⟨step412_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step412_cover⟩

def step413 : Request :=
  ⟨⟨⟨1350, 1883, 418, 31694⟩, 75578221264896, 352769102024⟩, 32, 5, 1, 642859⟩

theorem step413_nodes : P1_7_1.nodeRows step413.bank.shape = step413.bank.nodeRows :=
  node_check step413.bank (by decide) (by decide) (by decide)

private theorem step413_2330_2330 : Positive step413 2330 2330 := by decide +kernel

private theorem step413_2331_2332 : Positive step413 2331 2332 := by decide +kernel

private theorem step413_2333_2338 : Positive step413 2333 2338 := by decide +kernel

private theorem step413_2339_2354 : Positive step413 2339 2354 := by decide +kernel

private theorem step413_2355_2397 : Positive step413 2355 2397 := by decide +kernel

private theorem step413_2398_2499 : Positive step413 2398 2499 := by decide +kernel

theorem step413_cover : ∃ ends, Cover step413 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2354, 2397, 2499],
    ⟨(by decide), (by decide), step413_2330_2330,
      (by decide), (by decide), step413_2331_2332,
      (by decide), (by decide), step413_2333_2338,
      (by decide), (by decide), step413_2339_2354,
      (by decide), (by decide), step413_2355_2397,
      (by decide), (by decide), step413_2398_2499, rfl⟩⟩

theorem step413_verified : Checked step413 :=
  ⟨step413_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step413_cover⟩

def step414 : Request :=
  ⟨⟨⟨2000, 2791, 620, 40111⟩, 245690786119680, 1701147081935⟩, 44, 5, 1, 642859⟩

theorem step414_nodes : P1_7_1.nodeRows step414.bank.shape = step414.bank.nodeRows :=
  node_check step414.bank (by decide) (by decide) (by decide)

private theorem step414_2330_2334 : Positive step414 2330 2334 := by decide +kernel

private theorem step414_2335_2347 : Positive step414 2335 2347 := by decide +kernel

private theorem step414_2348_2381 : Positive step414 2348 2381 := by decide +kernel

private theorem step414_2382_2471 : Positive step414 2382 2471 := by decide +kernel

private theorem step414_2472_2499 : Positive step414 2472 2499 := by decide +kernel

theorem step414_cover : ∃ ends, Cover step414 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2471, 2499],
    ⟨(by decide), (by decide), step414_2330_2334,
      (by decide), (by decide), step414_2335_2347,
      (by decide), (by decide), step414_2348_2381,
      (by decide), (by decide), step414_2382_2471,
      (by decide), (by decide), step414_2472_2499, rfl⟩⟩

theorem step414_verified : Checked step414 :=
  ⟨step414_nodes, Research6966.HelperWindowCatalogue.moment2791_620,
    (by decide), (by decide), (by decide), step414_cover⟩

def step415 : Request :=
  ⟨⟨⟨2500, 3488, 775, 64247⟩, 479640131993600, 4147842034257⟩, 73, 5, 1, 642859⟩

theorem step415_nodes : P1_7_1.nodeRows step415.bank.shape = step415.bank.nodeRows :=
  node_check step415.bank (by decide) (by decide) (by decide)

private theorem step415_2330_2330 : Positive step415 2330 2330 := by decide +kernel

private theorem step415_2331_2333 : Positive step415 2331 2333 := by decide +kernel

private theorem step415_2334_2341 : Positive step415 2334 2341 := by decide +kernel

private theorem step415_2342_2361 : Positive step415 2342 2361 := by decide +kernel

private theorem step415_2362_2414 : Positive step415 2362 2414 := by decide +kernel

private theorem step415_2415_2499 : Positive step415 2415 2499 := by decide +kernel

theorem step415_cover : ∃ ends, Cover step415 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2361, 2414, 2499],
    ⟨(by decide), (by decide), step415_2330_2330,
      (by decide), (by decide), step415_2331_2333,
      (by decide), (by decide), step415_2334_2341,
      (by decide), (by decide), step415_2342_2361,
      (by decide), (by decide), step415_2362_2414,
      (by decide), (by decide), step415_2415_2499, rfl⟩⟩

theorem step415_verified : Checked step415 :=
  ⟨step415_nodes, Research6966.HelperWindowCatalogue.moment3488_775,
    (by decide), (by decide), (by decide), step415_cover⟩

def step416 : Request :=
  ⟨⟨⟨3000, 4186, 930, 64247⟩, 828559354757120, 8600191575129⟩, 76, 5, 1, 642859⟩

theorem step416_nodes : P1_7_1.nodeRows step416.bank.shape = step416.bank.nodeRows :=
  node_check step416.bank (by decide) (by decide) (by decide)

private theorem step416_2330_2336 : Positive step416 2330 2336 := by decide +kernel

private theorem step416_2337_2354 : Positive step416 2337 2354 := by decide +kernel

private theorem step416_2355_2401 : Positive step416 2355 2401 := by decide +kernel

private theorem step416_2402_2499 : Positive step416 2402 2499 := by decide +kernel

theorem step416_cover : ∃ ends, Cover step416 firstHeight ends := by
  exact ⟨[2336, 2354, 2401, 2499],
    ⟨(by decide), (by decide), step416_2330_2336,
      (by decide), (by decide), step416_2337_2354,
      (by decide), (by decide), step416_2355_2401,
      (by decide), (by decide), step416_2402_2499, rfl⟩⟩

theorem step416_verified : Checked step416 :=
  ⟨step416_nodes, Research6966.HelperWindowCatalogue.moment4186_930,
    (by decide), (by decide), (by decide), step416_cover⟩

def step417 : Request :=
  ⟨⟨⟨3500, 4883, 1057, 91474⟩, 1289556817346560, 15600507702257⟩, 103, 5, 1, 642859⟩

theorem step417_nodes : P1_7_1.nodeRows step417.bank.shape = step417.bank.nodeRows :=
  node_check step417.bank (by decide) (by decide) (by decide)

private theorem step417_2330_2339 : Positive step417 2330 2339 := by decide +kernel

private theorem step417_2340_2365 : Positive step417 2340 2365 := by decide +kernel

private theorem step417_2366_2433 : Positive step417 2366 2433 := by decide +kernel

private theorem step417_2434_2499 : Positive step417 2434 2499 := by decide +kernel

theorem step417_cover : ∃ ends, Cover step417 firstHeight ends := by
  exact ⟨[2339, 2365, 2433, 2499],
    ⟨(by decide), (by decide), step417_2330_2339,
      (by decide), (by decide), step417_2340_2365,
      (by decide), (by decide), step417_2366_2433,
      (by decide), (by decide), step417_2434_2499, rfl⟩⟩

theorem step417_verified : Checked step417 :=
  ⟨step417_nodes, Research6966.HelperWindowCatalogue.moment4883_1057,
    (by decide), (by decide), (by decide), step417_cover⟩

def step418 : Request :=
  ⟨⟨⟨350, 488, 106, 7715⟩, 1308168290304, 1584729438⟩, 0, 5, 2, 642859⟩

theorem step418_nodes : P1_7_1.nodeRows step418.bank.shape = step418.bank.nodeRows :=
  node_check step418.bank (by decide) (by decide) (by decide)

private theorem step418_2330_2339 : Positive step418 2330 2339 := by decide +kernel

private theorem step418_2340_2371 : Positive step418 2340 2371 := by decide +kernel

private theorem step418_2372_2474 : Positive step418 2372 2474 := by decide +kernel

private theorem step418_2475_2499 : Positive step418 2475 2499 := by decide +kernel

theorem step418_cover : ∃ ends, Cover step418 firstHeight ends := by
  exact ⟨[2339, 2371, 2474, 2499],
    ⟨(by decide), (by decide), step418_2330_2339,
      (by decide), (by decide), step418_2340_2371,
      (by decide), (by decide), step418_2372_2474,
      (by decide), (by decide), step418_2475_2499, rfl⟩⟩

theorem step418_verified : Checked step418 :=
  ⟨step418_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step418_cover⟩

def step419 : Request :=
  ⟨⟨⟨350, 488, 106, 8679⟩, 1308168290304, 1584729438⟩, 1, 5, 2, 642859⟩

theorem step419_nodes : P1_7_1.nodeRows step419.bank.shape = step419.bank.nodeRows :=
  node_check step419.bank (by decide) (by decide) (by decide)

private theorem step419_2330_2335 : Positive step419 2330 2335 := by decide +kernel

private theorem step419_2336_2354 : Positive step419 2336 2354 := by decide +kernel

private theorem step419_2355_2415 : Positive step419 2355 2415 := by decide +kernel

private theorem step419_2416_2499 : Positive step419 2416 2499 := by decide +kernel

theorem step419_cover : ∃ ends, Cover step419 firstHeight ends := by
  exact ⟨[2335, 2354, 2415, 2499],
    ⟨(by decide), (by decide), step419_2330_2335,
      (by decide), (by decide), step419_2336_2354,
      (by decide), (by decide), step419_2355_2415,
      (by decide), (by decide), step419_2416_2499, rfl⟩⟩

theorem step419_verified : Checked step419 :=
  ⟨step419_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step419_cover⟩

def step420 : Request :=
  ⟨⟨⟨350, 488, 108, 9763⟩, 1326705278976, 1607754763⟩, 2, 5, 2, 642859⟩

theorem step420_nodes : P1_7_1.nodeRows step420.bank.shape = step420.bank.nodeRows :=
  node_check step420.bank (by decide) (by decide) (by decide)

private theorem step420_2330_2333 : Positive step420 2330 2333 := by decide +kernel

private theorem step420_2334_2346 : Positive step420 2334 2346 := by decide +kernel

private theorem step420_2347_2387 : Positive step420 2347 2387 := by decide +kernel

private theorem step420_2388_2499 : Positive step420 2388 2499 := by decide +kernel

theorem step420_cover : ∃ ends, Cover step420 firstHeight ends := by
  exact ⟨[2333, 2346, 2387, 2499],
    ⟨(by decide), (by decide), step420_2330_2333,
      (by decide), (by decide), step420_2334_2346,
      (by decide), (by decide), step420_2347_2387,
      (by decide), (by decide), step420_2388_2499, rfl⟩⟩

theorem step420_verified : Checked step420 :=
  ⟨step420_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step420_cover⟩

def step421 : Request :=
  ⟨⟨⟨420, 586, 124, 10983⟩, 2212364288000, 3219706108⟩, 3, 5, 2, 642859⟩

theorem step421_nodes : P1_7_1.nodeRows step421.bank.shape = step421.bank.nodeRows :=
  node_check step421.bank (by decide) (by decide) (by decide)

private theorem step421_2330_2335 : Positive step421 2330 2335 := by decide +kernel

private theorem step421_2336_2354 : Positive step421 2336 2354 := by decide +kernel

private theorem step421_2355_2413 : Positive step421 2355 2413 := by decide +kernel

private theorem step421_2414_2499 : Positive step421 2414 2499 := by decide +kernel

theorem step421_cover : ∃ ends, Cover step421 firstHeight ends := by
  exact ⟨[2335, 2354, 2413, 2499],
    ⟨(by decide), (by decide), step421_2330_2335,
      (by decide), (by decide), step421_2336_2354,
      (by decide), (by decide), step421_2355_2413,
      (by decide), (by decide), step421_2414_2499, rfl⟩⟩

theorem step421_verified : Checked step421 :=
  ⟨step421_nodes, Research6966.HelperWindowCatalogue.moment586_124,
    (by decide), (by decide), (by decide), step421_cover⟩

def step422 : Request :=
  ⟨⟨⟨420, 586, 130, 10983⟩, 2292767784960, 3339653140⟩, 4, 5, 2, 642859⟩

theorem step422_nodes : P1_7_1.nodeRows step422.bank.shape = step422.bank.nodeRows :=
  node_check step422.bank (by decide) (by decide) (by decide)

private theorem step422_2330_2330 : Positive step422 2330 2330 := by decide +kernel

private theorem step422_2331_2333 : Positive step422 2331 2333 := by decide +kernel

private theorem step422_2334_2342 : Positive step422 2334 2342 := by decide +kernel

private theorem step422_2343_2369 : Positive step422 2343 2369 := by decide +kernel

private theorem step422_2370_2451 : Positive step422 2370 2451 := by decide +kernel

private theorem step422_2452_2499 : Positive step422 2452 2499 := by decide +kernel

theorem step422_cover : ∃ ends, Cover step422 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2369, 2451, 2499],
    ⟨(by decide), (by decide), step422_2330_2330,
      (by decide), (by decide), step422_2331_2333,
      (by decide), (by decide), step422_2334_2342,
      (by decide), (by decide), step422_2343_2369,
      (by decide), (by decide), step422_2370_2451,
      (by decide), (by decide), step422_2452_2499, rfl⟩⟩

theorem step422_verified : Checked step422 :=
  ⟨step422_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step422_cover⟩

def step423 : Request :=
  ⟨⟨⟨420, 586, 127, 13899⟩, 2252760678400, 3279920952⟩, 5, 5, 2, 642859⟩

theorem step423_nodes : P1_7_1.nodeRows step423.bank.shape = step423.bank.nodeRows :=
  node_check step423.bank (by decide) (by decide) (by decide)

private theorem step423_2330_2355 : Positive step423 2330 2355 := by decide +kernel

private theorem step423_2356_2436 : Positive step423 2356 2436 := by decide +kernel

private theorem step423_2437_2499 : Positive step423 2437 2499 := by decide +kernel

theorem step423_cover : ∃ ends, Cover step423 firstHeight ends := by
  exact ⟨[2355, 2436, 2499],
    ⟨(by decide), (by decide), step423_2330_2355,
      (by decide), (by decide), step423_2356_2436,
      (by decide), (by decide), step423_2437_2499, rfl⟩⟩

theorem step423_verified : Checked step423 :=
  ⟨step423_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step423_cover⟩

def step424 : Request :=
  ⟨⟨⟨520, 725, 157, 13899⟩, 4261264752640, 7658911630⟩, 7, 5, 2, 642859⟩

theorem step424_nodes : P1_7_1.nodeRows step424.bank.shape = step424.bank.nodeRows :=
  node_check step424.bank (by decide) (by decide) (by decide)

private theorem step424_2330_2342 : Positive step424 2330 2342 := by decide +kernel

private theorem step424_2343_2381 : Positive step424 2343 2381 := by decide +kernel

private theorem step424_2382_2497 : Positive step424 2382 2497 := by decide +kernel

private theorem step424_2498_2499 : Positive step424 2498 2499 := by decide +kernel

theorem step424_cover : ∃ ends, Cover step424 firstHeight ends := by
  exact ⟨[2342, 2381, 2497, 2499],
    ⟨(by decide), (by decide), step424_2330_2342,
      (by decide), (by decide), step424_2343_2381,
      (by decide), (by decide), step424_2382_2497,
      (by decide), (by decide), step424_2498_2499, rfl⟩⟩

theorem step424_verified : Checked step424 :=
  ⟨step424_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step424_cover⟩

def step425 : Request :=
  ⟨⟨⟨630, 879, 190, 15636⟩, 7559493713920, 16491913877⟩, 10, 5, 2, 642859⟩

theorem step425_nodes : P1_7_1.nodeRows step425.bank.shape = step425.bank.nodeRows :=
  node_check step425.bank (by decide) (by decide) (by decide)

private theorem step425_2330_2331 : Positive step425 2330 2331 := by decide +kernel

private theorem step425_2332_2337 : Positive step425 2332 2337 := by decide +kernel

private theorem step425_2338_2354 : Positive step425 2338 2354 := by decide +kernel

private theorem step425_2355_2403 : Positive step425 2355 2403 := by decide +kernel

private theorem step425_2404_2499 : Positive step425 2404 2499 := by decide +kernel

theorem step425_cover : ∃ ends, Cover step425 firstHeight ends := by
  exact ⟨[2331, 2337, 2354, 2403, 2499],
    ⟨(by decide), (by decide), step425_2330_2331,
      (by decide), (by decide), step425_2332_2337,
      (by decide), (by decide), step425_2338_2354,
      (by decide), (by decide), step425_2355_2403,
      (by decide), (by decide), step425_2404_2499, rfl⟩⟩

theorem step425_verified : Checked step425 :=
  ⟨step425_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step425_cover⟩

def step426 : Request :=
  ⟨⟨⟨900, 1256, 272, 19788⟩, 22024701870080, 68653176066⟩, 16, 5, 2, 642859⟩

theorem step426_nodes : P1_7_1.nodeRows step426.bank.shape = step426.bank.nodeRows :=
  node_check step426.bank (by decide) (by decide) (by decide)

private theorem step426_2330_2337 : Positive step426 2330 2337 := by decide +kernel

private theorem step426_2338_2359 : Positive step426 2338 2359 := by decide +kernel

private theorem step426_2360_2420 : Positive step426 2360 2420 := by decide +kernel

private theorem step426_2421_2499 : Positive step426 2421 2499 := by decide +kernel

theorem step426_cover : ∃ ends, Cover step426 firstHeight ends := by
  exact ⟨[2337, 2359, 2420, 2499],
    ⟨(by decide), (by decide), step426_2330_2337,
      (by decide), (by decide), step426_2338_2359,
      (by decide), (by decide), step426_2360_2420,
      (by decide), (by decide), step426_2421_2499, rfl⟩⟩

theorem step426_verified : Checked step426 :=
  ⟨step426_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step426_cover⟩

def step427 : Request :=
  ⟨⟨⟨900, 1256, 272, 25043⟩, 22024701870080, 68653176066⟩, 20, 5, 2, 642859⟩

theorem step427_nodes : P1_7_1.nodeRows step427.bank.shape = step427.bank.nodeRows :=
  node_check step427.bank (by decide) (by decide) (by decide)

private theorem step427_2330_2347 : Positive step427 2330 2347 := by decide +kernel

private theorem step427_2348_2397 : Positive step427 2348 2397 := by decide +kernel

private theorem step427_2398_2499 : Positive step427 2398 2499 := by decide +kernel

theorem step427_cover : ∃ ends, Cover step427 firstHeight ends := by
  exact ⟨[2347, 2397, 2499],
    ⟨(by decide), (by decide), step427_2330_2347,
      (by decide), (by decide), step427_2348_2397,
      (by decide), (by decide), step427_2398_2499, rfl⟩⟩

theorem step427_verified : Checked step427 :=
  ⟨step427_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step427_cover⟩

def step428 : Request :=
  ⟨⟨⟨1100, 1534, 341, 35655⟩, 40955142733824, 155702293064⟩, 31, 5, 2, 642859⟩

theorem step428_nodes : P1_7_1.nodeRows step428.bank.shape = step428.bank.nodeRows :=
  node_check step428.bank (by decide) (by decide) (by decide)

private theorem step428_2330_2339 : Positive step428 2330 2339 := by decide +kernel

private theorem step428_2340_2366 : Positive step428 2340 2366 := by decide +kernel

private theorem step428_2367_2439 : Positive step428 2367 2439 := by decide +kernel

private theorem step428_2440_2499 : Positive step428 2440 2499 := by decide +kernel

theorem step428_cover : ∃ ends, Cover step428 firstHeight ends := by
  exact ⟨[2339, 2366, 2439, 2499],
    ⟨(by decide), (by decide), step428_2330_2339,
      (by decide), (by decide), step428_2340_2366,
      (by decide), (by decide), step428_2367_2439,
      (by decide), (by decide), step428_2440_2499, rfl⟩⟩

theorem step428_verified : Checked step428 :=
  ⟨step428_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step428_cover⟩

def step429 : Request :=
  ⟨⟨⟨1350, 1883, 418, 31694⟩, 75578221264896, 352769102024⟩, 32, 5, 2, 642859⟩

theorem step429_nodes : P1_7_1.nodeRows step429.bank.shape = step429.bank.nodeRows :=
  node_check step429.bank (by decide) (by decide) (by decide)

private theorem step429_2330_2339 : Positive step429 2330 2339 := by decide +kernel

private theorem step429_2340_2366 : Positive step429 2340 2366 := by decide +kernel

private theorem step429_2367_2439 : Positive step429 2367 2439 := by decide +kernel

private theorem step429_2440_2499 : Positive step429 2440 2499 := by decide +kernel

theorem step429_cover : ∃ ends, Cover step429 firstHeight ends := by
  exact ⟨[2339, 2366, 2439, 2499],
    ⟨(by decide), (by decide), step429_2330_2339,
      (by decide), (by decide), step429_2340_2366,
      (by decide), (by decide), step429_2367_2439,
      (by decide), (by decide), step429_2440_2499, rfl⟩⟩

theorem step429_verified : Checked step429 :=
  ⟨step429_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step429_cover⟩

def step430 : Request :=
  ⟨⟨⟨1350, 1883, 418, 50764⟩, 75578221264896, 352769102024⟩, 44, 5, 2, 642859⟩

theorem step430_nodes : P1_7_1.nodeRows step430.bank.shape = step430.bank.nodeRows :=
  node_check step430.bank (by decide) (by decide) (by decide)

private theorem step430_2330_2332 : Positive step430 2330 2332 := by decide +kernel

private theorem step430_2333_2340 : Positive step430 2333 2340 := by decide +kernel

private theorem step430_2341_2361 : Positive step430 2341 2361 := by decide +kernel

private theorem step430_2362_2417 : Positive step430 2362 2417 := by decide +kernel

private theorem step430_2418_2499 : Positive step430 2418 2499 := by decide +kernel

theorem step430_cover : ∃ ends, Cover step430 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2417, 2499],
    ⟨(by decide), (by decide), step430_2330_2332,
      (by decide), (by decide), step430_2333_2340,
      (by decide), (by decide), step430_2341_2361,
      (by decide), (by decide), step430_2362_2417,
      (by decide), (by decide), step430_2418_2499, rfl⟩⟩

theorem step430_verified : Checked step430 :=
  ⟨step430_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step430_cover⟩

def step431 : Request :=
  ⟨⟨⟨2500, 3488, 775, 64247⟩, 479640131993600, 4147842034257⟩, 73, 5, 2, 642859⟩

theorem step431_nodes : P1_7_1.nodeRows step431.bank.shape = step431.bank.nodeRows :=
  node_check step431.bank (by decide) (by decide) (by decide)

private theorem step431_2330_2339 : Positive step431 2330 2339 := by decide +kernel

private theorem step431_2340_2365 : Positive step431 2340 2365 := by decide +kernel

private theorem step431_2366_2433 : Positive step431 2366 2433 := by decide +kernel

private theorem step431_2434_2499 : Positive step431 2434 2499 := by decide +kernel

theorem step431_cover : ∃ ends, Cover step431 firstHeight ends := by
  exact ⟨[2339, 2365, 2433, 2499],
    ⟨(by decide), (by decide), step431_2330_2339,
      (by decide), (by decide), step431_2340_2365,
      (by decide), (by decide), step431_2366_2433,
      (by decide), (by decide), step431_2434_2499, rfl⟩⟩

theorem step431_verified : Checked step431 :=
  ⟨step431_nodes, Research6966.HelperWindowCatalogue.moment3488_775,
    (by decide), (by decide), (by decide), step431_cover⟩

end Research6966.HelperRescueCatalogue
