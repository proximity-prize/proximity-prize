import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt2
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments10
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step41 : Request :=
  ⟨⟨⟨900, 1256, 266, 45124⟩, 21654240231424, 67471047297⟩, 2, 2, 9, 305624⟩

theorem step41_nodes : P1_7_1.nodeRows step41.bank.shape = step41.bank.nodeRows :=
  node_check step41.bank (by decide) (by decide) (by decide)

private theorem step41_2330_2339 : Positive step41 2330 2339 := by decide +kernel

private theorem step41_2340_2367 : Positive step41 2340 2367 := by decide +kernel

private theorem step41_2368_2446 : Positive step41 2368 2446 := by decide +kernel

private theorem step41_2447_2499 : Positive step41 2447 2499 := by decide +kernel

theorem step41_cover : ∃ ends, Cover step41 firstHeight ends := by
  exact ⟨[2339, 2367, 2446, 2499],
    ⟨(by decide), (by decide), step41_2330_2339,
      (by decide), (by decide), step41_2340_2367,
      (by decide), (by decide), step41_2368_2446,
      (by decide), (by decide), step41_2447_2499, rfl⟩⟩

theorem step41_verified : Checked step41 :=
  ⟨step41_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step41_cover⟩

def step42 : Request :=
  ⟨⟨⟨900, 1256, 266, 50764⟩, 21654240231424, 67471047297⟩, 3, 2, 9, 305624⟩

theorem step42_nodes : P1_7_1.nodeRows step42.bank.shape = step42.bank.nodeRows :=
  node_check step42.bank (by decide) (by decide) (by decide)

private theorem step42_2330_2333 : Positive step42 2330 2333 := by decide +kernel

private theorem step42_2334_2345 : Positive step42 2334 2345 := by decide +kernel

private theorem step42_2346_2378 : Positive step42 2346 2378 := by decide +kernel

private theorem step42_2379_2471 : Positive step42 2379 2471 := by decide +kernel

private theorem step42_2472_2499 : Positive step42 2472 2499 := by decide +kernel

theorem step42_cover : ∃ ends, Cover step42 firstHeight ends := by
  exact ⟨[2333, 2345, 2378, 2471, 2499],
    ⟨(by decide), (by decide), step42_2330_2333,
      (by decide), (by decide), step42_2334_2345,
      (by decide), (by decide), step42_2346_2378,
      (by decide), (by decide), step42_2379_2471,
      (by decide), (by decide), step42_2472_2499, rfl⟩⟩

theorem step42_verified : Checked step42 :=
  ⟨step42_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step42_cover⟩

def step43 : Request :=
  ⟨⟨⟨998, 1387, 302, 50764⟩, 30044628975616, 102461756220⟩, 4, 2, 9, 305624⟩

theorem step43_nodes : P1_7_1.nodeRows step43.bank.shape = step43.bank.nodeRows :=
  node_check step43.bank (by decide) (by decide) (by decide)

private theorem step43_2330_2330 : Positive step43 2330 2330 := by decide +kernel

private theorem step43_2331_2333 : Positive step43 2331 2333 := by decide +kernel

private theorem step43_2334_2341 : Positive step43 2334 2341 := by decide +kernel

private theorem step43_2342_2363 : Positive step43 2342 2363 := by decide +kernel

private theorem step43_2364_2422 : Positive step43 2364 2422 := by decide +kernel

private theorem step43_2423_2499 : Positive step43 2423 2499 := by decide +kernel

theorem step43_cover : ∃ ends, Cover step43 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2422, 2499],
    ⟨(by decide), (by decide), step43_2330_2330,
      (by decide), (by decide), step43_2331_2333,
      (by decide), (by decide), step43_2334_2341,
      (by decide), (by decide), step43_2342_2363,
      (by decide), (by decide), step43_2364_2422,
      (by decide), (by decide), step43_2423_2499, rfl⟩⟩

theorem step43_verified : Checked step43 :=
  ⟨step43_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_1387_302),
    (by decide), (by decide), (by decide), step43_cover⟩

def step44 : Request :=
  ⟨⟨⟨1220, 1696, 370, 50764⟩, 54930349752320, 229159736517⟩, 5, 2, 9, 305624⟩

theorem step44_nodes : P1_7_1.nodeRows step44.bank.shape = step44.bank.nodeRows :=
  node_check step44.bank (by decide) (by decide) (by decide)

private theorem step44_2330_2335 : Positive step44 2330 2335 := by decide +kernel

private theorem step44_2336_2351 : Positive step44 2336 2351 := by decide +kernel

private theorem step44_2352_2394 : Positive step44 2352 2394 := by decide +kernel

private theorem step44_2395_2499 : Positive step44 2395 2499 := by decide +kernel

theorem step44_cover : ∃ ends, Cover step44 firstHeight ends := by
  exact ⟨[2335, 2351, 2394, 2499],
    ⟨(by decide), (by decide), step44_2330_2335,
      (by decide), (by decide), step44_2336_2351,
      (by decide), (by decide), step44_2352_2394,
      (by decide), (by decide), step44_2395_2499, rfl⟩⟩

theorem step44_verified : Checked step44 :=
  ⟨step44_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_1696_370),
    (by decide), (by decide), (by decide), step44_cover⟩

def step45 : Request :=
  ⟨⟨⟨1350, 1884, 400, 57109⟩, 73092385996800, 341469310532⟩, 7, 2, 9, 305624⟩

theorem step45_nodes : P1_7_1.nodeRows step45.bank.shape = step45.bank.nodeRows :=
  node_check step45.bank (by decide) (by decide) (by decide)

private theorem step45_2330_2333 : Positive step45 2330 2333 := by decide +kernel

private theorem step45_2334_2343 : Positive step45 2334 2343 := by decide +kernel

private theorem step45_2344_2371 : Positive step45 2344 2371 := by decide +kernel

private theorem step45_2372_2447 : Positive step45 2372 2447 := by decide +kernel

private theorem step45_2448_2499 : Positive step45 2448 2499 := by decide +kernel

theorem step45_cover : ∃ ends, Cover step45 firstHeight ends := by
  exact ⟨[2333, 2343, 2371, 2447, 2499],
    ⟨(by decide), (by decide), step45_2330_2333,
      (by decide), (by decide), step45_2334_2343,
      (by decide), (by decide), step45_2344_2371,
      (by decide), (by decide), step45_2372_2447,
      (by decide), (by decide), step45_2448_2499, rfl⟩⟩

theorem step45_verified : Checked step45 :=
  ⟨step45_nodes, Research6966.HelperWindowCatalogue.moment1884_400,
    (by decide), (by decide), (by decide), step45_cover⟩

def step46 : Request :=
  ⟨⟨⟨1644, 2285, 498, 64247⟩, 134156626165760, 753510622290⟩, 10, 2, 9, 305624⟩

theorem step46_nodes : P1_7_1.nodeRows step46.bank.shape = step46.bank.nodeRows :=
  node_check step46.bank (by decide) (by decide) (by decide)

private theorem step46_2330_2330 : Positive step46 2330 2330 := by decide +kernel

private theorem step46_2331_2333 : Positive step46 2331 2333 := by decide +kernel

private theorem step46_2334_2340 : Positive step46 2334 2340 := by decide +kernel

private theorem step46_2341_2359 : Positive step46 2341 2359 := by decide +kernel

private theorem step46_2360_2409 : Positive step46 2360 2409 := by decide +kernel

private theorem step46_2410_2499 : Positive step46 2410 2499 := by decide +kernel

theorem step46_cover : ∃ ends, Cover step46 firstHeight ends := by
  exact ⟨[2330, 2333, 2340, 2359, 2409, 2499],
    ⟨(by decide), (by decide), step46_2330_2330,
      (by decide), (by decide), step46_2331_2333,
      (by decide), (by decide), step46_2334_2340,
      (by decide), (by decide), step46_2341_2359,
      (by decide), (by decide), step46_2360_2409,
      (by decide), (by decide), step46_2410_2499, rfl⟩⟩

theorem step46_verified : Checked step46 :=
  ⟨step46_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_2285_498),
    (by decide), (by decide), (by decide), step46_cover⟩

def step47 : Request :=
  ⟨⟨⟨1927, 2678, 584, 91474⟩, 216034207334400, 1421525065183⟩, 16, 2, 9, 305624⟩

theorem step47_nodes : P1_7_1.nodeRows step47.bank.shape = step47.bank.nodeRows :=
  node_check step47.bank (by decide) (by decide) (by decide)

private theorem step47_2330_2334 : Positive step47 2330 2334 := by decide +kernel

private theorem step47_2335_2347 : Positive step47 2335 2347 := by decide +kernel

private theorem step47_2348_2381 : Positive step47 2348 2381 := by decide +kernel

private theorem step47_2382_2470 : Positive step47 2382 2470 := by decide +kernel

private theorem step47_2471_2499 : Positive step47 2471 2499 := by decide +kernel

theorem step47_cover : ∃ ends, Cover step47 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2470, 2499],
    ⟨(by decide), (by decide), step47_2330_2334,
      (by decide), (by decide), step47_2335_2347,
      (by decide), (by decide), step47_2348_2381,
      (by decide), (by decide), step47_2382_2470,
      (by decide), (by decide), step47_2471_2499, rfl⟩⟩

theorem step47_verified : Checked step47 :=
  ⟨step47_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_2678_584),
    (by decide), (by decide), (by decide), step47_cover⟩

def step48 : Request :=
  ⟨⟨⟨2000, 2791, 592, 115771⟩, 237206388080640, 1640986809111⟩, 20, 2, 9, 305624⟩

theorem step48_nodes : P1_7_1.nodeRows step48.bank.shape = step48.bank.nodeRows :=
  node_check step48.bank (by decide) (by decide) (by decide)

private theorem step48_2330_2331 : Positive step48 2330 2331 := by decide +kernel

private theorem step48_2332_2336 : Positive step48 2332 2336 := by decide +kernel

private theorem step48_2337_2350 : Positive step48 2337 2350 := by decide +kernel

private theorem step48_2351_2387 : Positive step48 2351 2387 := by decide +kernel

private theorem step48_2388_2486 : Positive step48 2388 2486 := by decide +kernel

private theorem step48_2487_2499 : Positive step48 2487 2499 := by decide +kernel

theorem step48_cover : ∃ ends, Cover step48 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2387, 2486, 2499],
    ⟨(by decide), (by decide), step48_2330_2331,
      (by decide), (by decide), step48_2332_2336,
      (by decide), (by decide), step48_2337_2350,
      (by decide), (by decide), step48_2351_2387,
      (by decide), (by decide), step48_2388_2486,
      (by decide), (by decide), step48_2487_2499, rfl⟩⟩

theorem step48_verified : Checked step48 :=
  ⟨step48_nodes, Research6966.HelperWindowCatalogue.moment2791_592,
    (by decide), (by decide), (by decide), step48_cover⟩

def step49 : Request :=
  ⟨⟨⟨3500, 4886, 1036, 130242⟩, 1269967213297664, 15388297203643⟩, 31, 2, 9, 305624⟩

theorem step49_nodes : P1_7_1.nodeRows step49.bank.shape = step49.bank.nodeRows :=
  node_check step49.bank (by decide) (by decide) (by decide)

private theorem step49_2330_2330 : Positive step49 2330 2330 := by decide +kernel

private theorem step49_2331_2332 : Positive step49 2331 2332 := by decide +kernel

private theorem step49_2333_2338 : Positive step49 2333 2338 := by decide +kernel

private theorem step49_2339_2353 : Positive step49 2339 2353 := by decide +kernel

private theorem step49_2354_2393 : Positive step49 2354 2393 := by decide +kernel

private theorem step49_2394_2498 : Positive step49 2394 2498 := by decide +kernel

private theorem step49_2499_2499 : Positive step49 2499 2499 := by decide +kernel

theorem step49_cover : ∃ ends, Cover step49 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2353, 2393, 2498, 2499],
    ⟨(by decide), (by decide), step49_2330_2330,
      (by decide), (by decide), step49_2331_2332,
      (by decide), (by decide), step49_2333_2338,
      (by decide), (by decide), step49_2339_2353,
      (by decide), (by decide), step49_2354_2393,
      (by decide), (by decide), step49_2394_2498,
      (by decide), (by decide), step49_2499_2499, rfl⟩⟩

theorem step49_verified : Checked step49 :=
  ⟨step49_nodes, Research6966.HelperWindowCatalogue.moment4886_1036,
    (by decide), (by decide), (by decide), step49_cover⟩

def step50 : Request :=
  ⟨⟨⟨3500, 4886, 1057, 130242⟩, 1289556817346560, 15631374615265⟩, 32, 2, 9, 305624⟩

theorem step50_nodes : P1_7_1.nodeRows step50.bank.shape = step50.bank.nodeRows :=
  node_check step50.bank (by decide) (by decide) (by decide)

private theorem step50_2330_2331 : Positive step50 2330 2331 := by decide +kernel

private theorem step50_2332_2336 : Positive step50 2332 2336 := by decide +kernel

private theorem step50_2337_2349 : Positive step50 2337 2349 := by decide +kernel

private theorem step50_2350_2382 : Positive step50 2350 2382 := by decide +kernel

private theorem step50_2383_2468 : Positive step50 2383 2468 := by decide +kernel

private theorem step50_2469_2499 : Positive step50 2469 2499 := by decide +kernel

theorem step50_cover : ∃ ends, Cover step50 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2382, 2468, 2499],
    ⟨(by decide), (by decide), step50_2330_2331,
      (by decide), (by decide), step50_2332_2336,
      (by decide), (by decide), step50_2337_2349,
      (by decide), (by decide), step50_2350_2382,
      (by decide), (by decide), step50_2383_2468,
      (by decide), (by decide), step50_2469_2499, rfl⟩⟩

theorem step50_verified : Checked step50 :=
  ⟨step50_nodes, Research6966.HelperWindowCatalogue.moment4886_1057,
    (by decide), (by decide), (by decide), step50_cover⟩

def step51 : Request :=
  ⟨⟨⟨3500, 4885, 1057, 208621⟩, 1289556817346560, 15621081034380⟩, 44, 2, 9, 305624⟩

theorem step51_nodes : P1_7_1.nodeRows step51.bank.shape = step51.bank.nodeRows :=
  node_check step51.bank (by decide) (by decide) (by decide)

private theorem step51_2330_2332 : Positive step51 2330 2332 := by decide +kernel

private theorem step51_2333_2340 : Positive step51 2333 2340 := by decide +kernel

private theorem step51_2341_2361 : Positive step51 2341 2361 := by decide +kernel

private theorem step51_2362_2415 : Positive step51 2362 2415 := by decide +kernel

private theorem step51_2416_2499 : Positive step51 2416 2499 := by decide +kernel

theorem step51_cover : ∃ ends, Cover step51 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2415, 2499],
    ⟨(by decide), (by decide), step51_2330_2332,
      (by decide), (by decide), step51_2333_2340,
      (by decide), (by decide), step51_2341_2361,
      (by decide), (by decide), step51_2362_2415,
      (by decide), (by decide), step51_2416_2499, rfl⟩⟩

theorem step51_verified : Checked step51 :=
  ⟨step51_nodes, Research6966.HelperWindowCatalogue.moment4885_1057,
    (by decide), (by decide), (by decide), step51_cover⟩

def step52 : Request :=
  ⟨⟨⟨900, 1256, 272, 19788⟩, 22024701870080, 68653176066⟩, 0, 2, 16, 300794⟩

theorem step52_nodes : P1_7_1.nodeRows step52.bank.shape = step52.bank.nodeRows :=
  node_check step52.bank (by decide) (by decide) (by decide)

private theorem step52_2330_2339 : Positive step52 2330 2339 := by decide +kernel

private theorem step52_2340_2367 : Positive step52 2340 2367 := by decide +kernel

private theorem step52_2368_2444 : Positive step52 2368 2444 := by decide +kernel

private theorem step52_2445_2499 : Positive step52 2445 2499 := by decide +kernel

theorem step52_cover : ∃ ends, Cover step52 firstHeight ends := by
  exact ⟨[2339, 2367, 2444, 2499],
    ⟨(by decide), (by decide), step52_2330_2339,
      (by decide), (by decide), step52_2340_2367,
      (by decide), (by decide), step52_2368_2444,
      (by decide), (by decide), step52_2445_2499, rfl⟩⟩

theorem step52_verified : Checked step52 :=
  ⟨step52_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step52_cover⟩

def step53 : Request :=
  ⟨⟨⟨900, 1256, 272, 22261⟩, 22024701870080, 68653176066⟩, 1, 2, 16, 300794⟩

theorem step53_nodes : P1_7_1.nodeRows step53.bank.shape = step53.bank.nodeRows :=
  node_check step53.bank (by decide) (by decide) (by decide)

private theorem step53_2330_2339 : Positive step53 2330 2339 := by decide +kernel

private theorem step53_2340_2366 : Positive step53 2340 2366 := by decide +kernel

private theorem step53_2367_2441 : Positive step53 2367 2441 := by decide +kernel

private theorem step53_2442_2499 : Positive step53 2442 2499 := by decide +kernel

theorem step53_cover : ∃ ends, Cover step53 firstHeight ends := by
  exact ⟨[2339, 2366, 2441, 2499],
    ⟨(by decide), (by decide), step53_2330_2339,
      (by decide), (by decide), step53_2340_2366,
      (by decide), (by decide), step53_2367_2441,
      (by decide), (by decide), step53_2442_2499, rfl⟩⟩

theorem step53_verified : Checked step53 :=
  ⟨step53_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step53_cover⟩

def step54 : Request :=
  ⟨⟨⟨900, 1256, 272, 25043⟩, 22024701870080, 68653176066⟩, 2, 2, 16, 300794⟩

theorem step54_nodes : P1_7_1.nodeRows step54.bank.shape = step54.bank.nodeRows :=
  node_check step54.bank (by decide) (by decide) (by decide)

private theorem step54_2330_2336 : Positive step54 2330 2336 := by decide +kernel

private theorem step54_2337_2355 : Positive step54 2337 2355 := by decide +kernel

private theorem step54_2356_2407 : Positive step54 2356 2407 := by decide +kernel

private theorem step54_2408_2499 : Positive step54 2408 2499 := by decide +kernel

theorem step54_cover : ∃ ends, Cover step54 firstHeight ends := by
  exact ⟨[2336, 2355, 2407, 2499],
    ⟨(by decide), (by decide), step54_2330_2336,
      (by decide), (by decide), step54_2337_2355,
      (by decide), (by decide), step54_2356_2407,
      (by decide), (by decide), step54_2408_2499, rfl⟩⟩

theorem step54_verified : Checked step54 :=
  ⟨step54_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step54_cover⟩

def step55 : Request :=
  ⟨⟨⟨1100, 1535, 332, 25043⟩, 40133103452160, 152819743367⟩, 3, 2, 16, 300794⟩

theorem step55_nodes : P1_7_1.nodeRows step55.bank.shape = step55.bank.nodeRows :=
  node_check step55.bank (by decide) (by decide) (by decide)

private theorem step55_2330_2334 : Positive step55 2330 2334 := by decide +kernel

private theorem step55_2335_2348 : Positive step55 2335 2348 := by decide +kernel

private theorem step55_2349_2386 : Positive step55 2349 2386 := by decide +kernel

private theorem step55_2387_2489 : Positive step55 2387 2489 := by decide +kernel

private theorem step55_2490_2499 : Positive step55 2490 2499 := by decide +kernel

theorem step55_cover : ∃ ends, Cover step55 firstHeight ends := by
  exact ⟨[2334, 2348, 2386, 2489, 2499],
    ⟨(by decide), (by decide), step55_2330_2334,
      (by decide), (by decide), step55_2335_2348,
      (by decide), (by decide), step55_2349_2386,
      (by decide), (by decide), step55_2387_2489,
      (by decide), (by decide), step55_2490_2499, rfl⟩⟩

theorem step55_verified : Checked step55 :=
  ⟨step55_nodes, Research6966.HelperWindowCatalogue.moment1535_332,
    (by decide), (by decide), (by decide), step55_cover⟩

def step56 : Request :=
  ⟨⟨⟨1100, 1535, 332, 28173⟩, 40133103452160, 152819743367⟩, 4, 2, 16, 300794⟩

theorem step56_nodes : P1_7_1.nodeRows step56.bank.shape = step56.bank.nodeRows :=
  node_check step56.bank (by decide) (by decide) (by decide)

private theorem step56_2330_2336 : Positive step56 2330 2336 := by decide +kernel

private theorem step56_2337_2355 : Positive step56 2337 2355 := by decide +kernel

private theorem step56_2356_2407 : Positive step56 2356 2407 := by decide +kernel

private theorem step56_2408_2499 : Positive step56 2408 2499 := by decide +kernel

theorem step56_cover : ∃ ends, Cover step56 firstHeight ends := by
  exact ⟨[2336, 2355, 2407, 2499],
    ⟨(by decide), (by decide), step56_2330_2336,
      (by decide), (by decide), step56_2337_2355,
      (by decide), (by decide), step56_2356_2407,
      (by decide), (by decide), step56_2408_2499, rfl⟩⟩

theorem step56_verified : Checked step56 :=
  ⟨step56_nodes, Research6966.HelperWindowCatalogue.moment1535_332,
    (by decide), (by decide), (by decide), step56_cover⟩

def step57 : Request :=
  ⟨⟨⟨1350, 1884, 408, 28173⟩, 74202776600576, 346781832878⟩, 5, 2, 16, 300794⟩

theorem step57_nodes : P1_7_1.nodeRows step57.bank.shape = step57.bank.nodeRows :=
  node_check step57.bank (by decide) (by decide) (by decide)

private theorem step57_2330_2333 : Positive step57 2330 2333 := by decide +kernel

private theorem step57_2334_2343 : Positive step57 2334 2343 := by decide +kernel

private theorem step57_2344_2370 : Positive step57 2344 2370 := by decide +kernel

private theorem step57_2371_2443 : Positive step57 2371 2443 := by decide +kernel

private theorem step57_2444_2499 : Positive step57 2444 2499 := by decide +kernel

theorem step57_cover : ∃ ends, Cover step57 firstHeight ends := by
  exact ⟨[2333, 2343, 2370, 2443, 2499],
    ⟨(by decide), (by decide), step57_2330_2333,
      (by decide), (by decide), step57_2334_2343,
      (by decide), (by decide), step57_2344_2370,
      (by decide), (by decide), step57_2371_2443,
      (by decide), (by decide), step57_2444_2499, rfl⟩⟩

theorem step57_verified : Checked step57 :=
  ⟨step57_nodes, Research6966.HelperWindowCatalogue.moment1884_408,
    (by decide), (by decide), (by decide), step57_cover⟩

def step58 : Request :=
  ⟨⟨⟨1650, 2303, 498, 31694⟩, 135254251667456, 772776530256⟩, 7, 2, 16, 300794⟩

theorem step58_nodes : P1_7_1.nodeRows step58.bank.shape = step58.bank.nodeRows :=
  node_check step58.bank (by decide) (by decide) (by decide)

private theorem step58_2330_2331 : Positive step58 2330 2331 := by decide +kernel

private theorem step58_2332_2337 : Positive step58 2332 2337 := by decide +kernel

private theorem step58_2338_2353 : Positive step58 2338 2353 := by decide +kernel

private theorem step58_2354_2395 : Positive step58 2354 2395 := by decide +kernel

private theorem step58_2396_2499 : Positive step58 2396 2499 := by decide +kernel

theorem step58_cover : ∃ ends, Cover step58 firstHeight ends := by
  exact ⟨[2331, 2337, 2353, 2395, 2499],
    ⟨(by decide), (by decide), step58_2330_2331,
      (by decide), (by decide), step58_2332_2337,
      (by decide), (by decide), step58_2338_2353,
      (by decide), (by decide), step58_2354_2395,
      (by decide), (by decide), step58_2396_2499, rfl⟩⟩

theorem step58_verified : Checked step58 :=
  ⟨step58_nodes, Research6966.HelperWindowCatalogue.moment2303_498,
    (by decide), (by decide), (by decide), step58_cover⟩

def step59 : Request :=
  ⟨⟨⟨1644, 2285, 498, 40111⟩, 134156626165760, 753510622290⟩, 10, 2, 16, 300794⟩

theorem step59_nodes : P1_7_1.nodeRows step59.bank.shape = step59.bank.nodeRows :=
  node_check step59.bank (by decide) (by decide) (by decide)

private theorem step59_2330_2340 : Positive step59 2330 2340 := by decide +kernel

private theorem step59_2341_2369 : Positive step59 2341 2369 := by decide +kernel

private theorem step59_2370_2446 : Positive step59 2370 2446 := by decide +kernel

private theorem step59_2447_2499 : Positive step59 2447 2499 := by decide +kernel

theorem step59_cover : ∃ ends, Cover step59 firstHeight ends := by
  exact ⟨[2340, 2369, 2446, 2499],
    ⟨(by decide), (by decide), step59_2330_2340,
      (by decide), (by decide), step59_2341_2369,
      (by decide), (by decide), step59_2370_2446,
      (by decide), (by decide), step59_2447_2499, rfl⟩⟩

theorem step59_verified : Checked step59 :=
  ⟨step59_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_2285_498),
    (by decide), (by decide), (by decide), step59_cover⟩

def step60 : Request :=
  ⟨⟨⟨2000, 2792, 604, 50764⟩, 240862397726720, 1668809144914⟩, 16, 2, 16, 300794⟩

theorem step60_nodes : P1_7_1.nodeRows step60.bank.shape = step60.bank.nodeRows :=
  node_check step60.bank (by decide) (by decide) (by decide)

private theorem step60_2330_2333 : Positive step60 2330 2333 := by decide +kernel

private theorem step60_2334_2343 : Positive step60 2334 2343 := by decide +kernel

private theorem step60_2344_2370 : Positive step60 2344 2370 := by decide +kernel

private theorem step60_2371_2441 : Positive step60 2371 2441 := by decide +kernel

private theorem step60_2442_2499 : Positive step60 2442 2499 := by decide +kernel

theorem step60_cover : ∃ ends, Cover step60 firstHeight ends := by
  exact ⟨[2333, 2343, 2370, 2441, 2499],
    ⟨(by decide), (by decide), step60_2330_2333,
      (by decide), (by decide), step60_2334_2343,
      (by decide), (by decide), step60_2344_2370,
      (by decide), (by decide), step60_2371_2441,
      (by decide), (by decide), step60_2442_2499, rfl⟩⟩

theorem step60_verified : Checked step60 :=
  ⟨step60_nodes, Research6966.HelperWindowCatalogue.moment2792_604,
    (by decide), (by decide), (by decide), step60_cover⟩

def step61 : Request :=
  ⟨⟨⟨2500, 3490, 755, 57109⟩, 470210689105920, 4071783120217⟩, 20, 2, 16, 300794⟩

theorem step61_nodes : P1_7_1.nodeRows step61.bank.shape = step61.bank.nodeRows :=
  node_check step61.bank (by decide) (by decide) (by decide)

private theorem step61_2330_2334 : Positive step61 2330 2334 := by decide +kernel

private theorem step61_2335_2348 : Positive step61 2335 2348 := by decide +kernel

private theorem step61_2349_2384 : Positive step61 2349 2384 := by decide +kernel

private theorem step61_2385_2479 : Positive step61 2385 2479 := by decide +kernel

private theorem step61_2480_2499 : Positive step61 2480 2499 := by decide +kernel

theorem step61_cover : ∃ ends, Cover step61 firstHeight ends := by
  exact ⟨[2334, 2348, 2384, 2479, 2499],
    ⟨(by decide), (by decide), step61_2330_2334,
      (by decide), (by decide), step61_2335_2348,
      (by decide), (by decide), step61_2349_2384,
      (by decide), (by decide), step61_2385_2479,
      (by decide), (by decide), step61_2480_2499, rfl⟩⟩

theorem step61_verified : Checked step61 :=
  ⟨step61_nodes, Research6966.HelperWindowCatalogue.moment3490_755,
    (by decide), (by decide), (by decide), step61_cover⟩

end Research6966.HelperRescueCatalogue
