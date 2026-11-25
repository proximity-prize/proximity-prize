import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments7
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step577 : Request :=
  ⟨⟨⟨3000, 4185, 930, 57109⟩, 828559354757120, 8593576488693⟩, 103, 6, 2, 771431⟩

theorem step577_nodes : P1_7_1.nodeRows step577.bank.shape = step577.bank.nodeRows :=
  node_check step577.bank (by decide) (by decide) (by decide)

private theorem step577_2330_2333 : Positive step577 2330 2333 := by decide +kernel

private theorem step577_2334_2343 : Positive step577 2334 2343 := by decide +kernel

private theorem step577_2344_2369 : Positive step577 2344 2369 := by decide +kernel

private theorem step577_2370_2437 : Positive step577 2370 2437 := by decide +kernel

private theorem step577_2438_2499 : Positive step577 2438 2499 := by decide +kernel

theorem step577_cover : ∃ ends, Cover step577 firstHeight ends := by
  exact ⟨[2333, 2343, 2369, 2437, 2499],
    ⟨(by decide), (by decide), step577_2330_2333,
      (by decide), (by decide), step577_2334_2343,
      (by decide), (by decide), step577_2344_2369,
      (by decide), (by decide), step577_2370_2437,
      (by decide), (by decide), step577_2438_2499, rfl⟩⟩

theorem step577_verified : Checked step577 :=
  ⟨step577_nodes, Research6966.HelperWindowCatalogue.moment4185_930,
    (by decide), (by decide), (by decide), step577_cover⟩

def step578 : Request :=
  ⟨⟨⟨250, 349, 76, 5419⟩, 480667500544, 418199213⟩, 0, 6, 4, 771431⟩

theorem step578_nodes : P1_7_1.nodeRows step578.bank.shape = step578.bank.nodeRows :=
  node_check step578.bank (by decide) (by decide) (by decide)

private theorem step578_2330_2339 : Positive step578 2330 2339 := by decide +kernel

private theorem step578_2340_2375 : Positive step578 2340 2375 := by decide +kernel

private theorem step578_2376_2499 : Positive step578 2376 2499 := by decide +kernel

theorem step578_cover : ∃ ends, Cover step578 firstHeight ends := by
  exact ⟨[2339, 2375, 2499],
    ⟨(by decide), (by decide), step578_2330_2339,
      (by decide), (by decide), step578_2340_2375,
      (by decide), (by decide), step578_2376_2499, rfl⟩⟩

theorem step578_verified : Checked step578 :=
  ⟨step578_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step578_cover⟩

def step579 : Request :=
  ⟨⟨⟨350, 488, 108, 5419⟩, 1326705278976, 1607754763⟩, 1, 6, 4, 771431⟩

theorem step579_nodes : P1_7_1.nodeRows step579.bank.shape = step579.bank.nodeRows :=
  node_check step579.bank (by decide) (by decide) (by decide)

private theorem step579_2330_2337 : Positive step579 2330 2337 := by decide +kernel

private theorem step579_2338_2363 : Positive step579 2338 2363 := by decide +kernel

private theorem step579_2364_2446 : Positive step579 2364 2446 := by decide +kernel

private theorem step579_2447_2499 : Positive step579 2447 2499 := by decide +kernel

theorem step579_cover : ∃ ends, Cover step579 firstHeight ends := by
  exact ⟨[2337, 2363, 2446, 2499],
    ⟨(by decide), (by decide), step579_2330_2337,
      (by decide), (by decide), step579_2338_2363,
      (by decide), (by decide), step579_2364_2446,
      (by decide), (by decide), step579_2447_2499, rfl⟩⟩

theorem step579_verified : Checked step579 :=
  ⟨step579_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step579_cover⟩

def step580 : Request :=
  ⟨⟨⟨350, 488, 106, 6096⟩, 1308168290304, 1584729438⟩, 2, 6, 4, 771431⟩

theorem step580_nodes : P1_7_1.nodeRows step580.bank.shape = step580.bank.nodeRows :=
  node_check step580.bank (by decide) (by decide) (by decide)

private theorem step580_2330_2341 : Positive step580 2330 2341 := by decide +kernel

private theorem step580_2342_2379 : Positive step580 2342 2379 := by decide +kernel

private theorem step580_2380_2499 : Positive step580 2380 2499 := by decide +kernel

theorem step580_cover : ∃ ends, Cover step580 firstHeight ends := by
  exact ⟨[2341, 2379, 2499],
    ⟨(by decide), (by decide), step580_2330_2341,
      (by decide), (by decide), step580_2342_2379,
      (by decide), (by decide), step580_2380_2499, rfl⟩⟩

theorem step580_verified : Checked step580 :=
  ⟨step580_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step580_cover⟩

def step581 : Request :=
  ⟨⟨⟨350, 488, 106, 6858⟩, 1308168290304, 1584729438⟩, 3, 6, 4, 771431⟩

theorem step581_nodes : P1_7_1.nodeRows step581.bank.shape = step581.bank.nodeRows :=
  node_check step581.bank (by decide) (by decide) (by decide)

private theorem step581_2330_2349 : Positive step581 2330 2349 := by decide +kernel

private theorem step581_2350_2413 : Positive step581 2350 2413 := by decide +kernel

private theorem step581_2414_2499 : Positive step581 2414 2499 := by decide +kernel

theorem step581_cover : ∃ ends, Cover step581 firstHeight ends := by
  exact ⟨[2349, 2413, 2499],
    ⟨(by decide), (by decide), step581_2330_2349,
      (by decide), (by decide), step581_2350_2413,
      (by decide), (by decide), step581_2414_2499, rfl⟩⟩

theorem step581_verified : Checked step581 :=
  ⟨step581_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step581_cover⟩

def step582 : Request :=
  ⟨⟨⟨420, 586, 130, 6858⟩, 2292767784960, 3339653140⟩, 4, 6, 4, 771431⟩

theorem step582_nodes : P1_7_1.nodeRows step582.bank.shape = step582.bank.nodeRows :=
  node_check step582.bank (by decide) (by decide) (by decide)

private theorem step582_2330_2336 : Positive step582 2330 2336 := by decide +kernel

private theorem step582_2337_2357 : Positive step582 2337 2357 := by decide +kernel

private theorem step582_2358_2421 : Positive step582 2358 2421 := by decide +kernel

private theorem step582_2422_2499 : Positive step582 2422 2499 := by decide +kernel

theorem step582_cover : ∃ ends, Cover step582 firstHeight ends := by
  exact ⟨[2336, 2357, 2421, 2499],
    ⟨(by decide), (by decide), step582_2330_2336,
      (by decide), (by decide), step582_2337_2357,
      (by decide), (by decide), step582_2358_2421,
      (by decide), (by decide), step582_2422_2499, rfl⟩⟩

theorem step582_verified : Checked step582 :=
  ⟨step582_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step582_cover⟩

def step583 : Request :=
  ⟨⟨⟨420, 586, 127, 7715⟩, 2252760678400, 3279920952⟩, 5, 6, 4, 771431⟩

theorem step583_nodes : P1_7_1.nodeRows step583.bank.shape = step583.bank.nodeRows :=
  node_check step583.bank (by decide) (by decide) (by decide)

private theorem step583_2330_2341 : Positive step583 2330 2341 := by decide +kernel

private theorem step583_2342_2378 : Positive step583 2342 2378 := by decide +kernel

private theorem step583_2379_2492 : Positive step583 2379 2492 := by decide +kernel

private theorem step583_2493_2499 : Positive step583 2493 2499 := by decide +kernel

theorem step583_cover : ∃ ends, Cover step583 firstHeight ends := by
  exact ⟨[2341, 2378, 2492, 2499],
    ⟨(by decide), (by decide), step583_2330_2341,
      (by decide), (by decide), step583_2342_2378,
      (by decide), (by decide), step583_2379_2492,
      (by decide), (by decide), step583_2493_2499, rfl⟩⟩

theorem step583_verified : Checked step583 :=
  ⟨step583_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step583_cover⟩

def step584 : Request :=
  ⟨⟨⟨520, 725, 157, 8679⟩, 4261264752640, 7658911630⟩, 7, 6, 4, 771431⟩

theorem step584_nodes : P1_7_1.nodeRows step584.bank.shape = step584.bank.nodeRows :=
  node_check step584.bank (by decide) (by decide) (by decide)

private theorem step584_2330_2346 : Positive step584 2330 2346 := by decide +kernel

private theorem step584_2347_2397 : Positive step584 2347 2397 := by decide +kernel

private theorem step584_2398_2499 : Positive step584 2398 2499 := by decide +kernel

theorem step584_cover : ∃ ends, Cover step584 firstHeight ends := by
  exact ⟨[2346, 2397, 2499],
    ⟨(by decide), (by decide), step584_2330_2346,
      (by decide), (by decide), step584_2347_2397,
      (by decide), (by decide), step584_2398_2499, rfl⟩⟩

theorem step584_verified : Checked step584 :=
  ⟨step584_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step584_cover⟩

def step585 : Request :=
  ⟨⟨⟨630, 879, 195, 9763⟩, 7709474160640, 16827402390⟩, 10, 6, 4, 771431⟩

theorem step585_nodes : P1_7_1.nodeRows step585.bank.shape = step585.bank.nodeRows :=
  node_check step585.bank (by decide) (by decide) (by decide)

private theorem step585_2330_2339 : Positive step585 2330 2339 := by decide +kernel

private theorem step585_2340_2368 : Positive step585 2340 2368 := by decide +kernel

private theorem step585_2369_2451 : Positive step585 2369 2451 := by decide +kernel

private theorem step585_2452_2499 : Positive step585 2452 2499 := by decide +kernel

theorem step585_cover : ∃ ends, Cover step585 firstHeight ends := by
  exact ⟨[2339, 2368, 2451, 2499],
    ⟨(by decide), (by decide), step585_2330_2339,
      (by decide), (by decide), step585_2340_2368,
      (by decide), (by decide), step585_2369_2451,
      (by decide), (by decide), step585_2452_2499, rfl⟩⟩

theorem step585_verified : Checked step585 :=
  ⟨step585_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step585_cover⟩

def step586 : Request :=
  ⟨⟨⟨630, 879, 195, 13899⟩, 7709474160640, 16827402390⟩, 16, 6, 4, 771431⟩

theorem step586_nodes : P1_7_1.nodeRows step586.bank.shape = step586.bank.nodeRows :=
  node_check step586.bank (by decide) (by decide) (by decide)

private theorem step586_2330_2345 : Positive step586 2330 2345 := by decide +kernel

private theorem step586_2346_2390 : Positive step586 2346 2390 := by decide +kernel

private theorem step586_2391_2499 : Positive step586 2391 2499 := by decide +kernel

theorem step586_cover : ∃ ends, Cover step586 firstHeight ends := by
  exact ⟨[2345, 2390, 2499],
    ⟨(by decide), (by decide), step586_2330_2345,
      (by decide), (by decide), step586_2346_2390,
      (by decide), (by decide), step586_2391_2499, rfl⟩⟩

theorem step586_verified : Checked step586 :=
  ⟨step586_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step586_cover⟩

def step587 : Request :=
  ⟨⟨⟨750, 1046, 232, 15636⟩, 12985818152960, 33687112323⟩, 20, 6, 4, 771431⟩

theorem step587_nodes : P1_7_1.nodeRows step587.bank.shape = step587.bank.nodeRows :=
  node_check step587.bank (by decide) (by decide) (by decide)

private theorem step587_2330_2345 : Positive step587 2330 2345 := by decide +kernel

private theorem step587_2346_2390 : Positive step587 2346 2390 := by decide +kernel

private theorem step587_2391_2499 : Positive step587 2391 2499 := by decide +kernel

theorem step587_cover : ∃ ends, Cover step587 firstHeight ends := by
  exact ⟨[2345, 2390, 2499],
    ⟨(by decide), (by decide), step587_2330_2345,
      (by decide), (by decide), step587_2346_2390,
      (by decide), (by decide), step587_2391_2499, rfl⟩⟩

theorem step587_verified : Checked step587 :=
  ⟨step587_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step587_cover⟩

def step588 : Request :=
  ⟨⟨⟨1350, 1883, 418, 19788⟩, 75578221264896, 352769102024⟩, 31, 6, 4, 771431⟩

theorem step588_nodes : P1_7_1.nodeRows step588.bank.shape = step588.bank.nodeRows :=
  node_check step588.bank (by decide) (by decide) (by decide)

private theorem step588_2330_2336 : Positive step588 2330 2336 := by decide +kernel

private theorem step588_2337_2355 : Positive step588 2337 2355 := by decide +kernel

private theorem step588_2356_2406 : Positive step588 2356 2406 := by decide +kernel

private theorem step588_2407_2499 : Positive step588 2407 2499 := by decide +kernel

theorem step588_cover : ∃ ends, Cover step588 firstHeight ends := by
  exact ⟨[2336, 2355, 2406, 2499],
    ⟨(by decide), (by decide), step588_2330_2336,
      (by decide), (by decide), step588_2337_2355,
      (by decide), (by decide), step588_2356_2406,
      (by decide), (by decide), step588_2407_2499, rfl⟩⟩

theorem step588_verified : Checked step588 :=
  ⟨step588_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step588_cover⟩

def step589 : Request :=
  ⟨⟨⟨1100, 1534, 332, 22261⟩, 40133103452160, 152499774767⟩, 32, 6, 4, 771431⟩

theorem step589_nodes : P1_7_1.nodeRows step589.bank.shape = step589.bank.nodeRows :=
  node_check step589.bank (by decide) (by decide) (by decide)

private theorem step589_2330_2347 : Positive step589 2330 2347 := by decide +kernel

private theorem step589_2348_2397 : Positive step589 2348 2397 := by decide +kernel

private theorem step589_2398_2499 : Positive step589 2398 2499 := by decide +kernel

theorem step589_cover : ∃ ends, Cover step589 firstHeight ends := by
  exact ⟨[2347, 2397, 2499],
    ⟨(by decide), (by decide), step589_2330_2347,
      (by decide), (by decide), step589_2348_2397,
      (by decide), (by decide), step589_2398_2499, rfl⟩⟩

theorem step589_verified : Checked step589 :=
  ⟨step589_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step589_cover⟩

def step590 : Request :=
  ⟨⟨⟨1350, 1883, 408, 28173⟩, 74202776600576, 346190054868⟩, 44, 6, 4, 771431⟩

theorem step590_nodes : P1_7_1.nodeRows step590.bank.shape = step590.bank.nodeRows :=
  node_check step590.bank (by decide) (by decide) (by decide)

private theorem step590_2330_2331 : Positive step590 2330 2331 := by decide +kernel

private theorem step590_2332_2337 : Positive step590 2332 2337 := by decide +kernel

private theorem step590_2338_2353 : Positive step590 2338 2353 := by decide +kernel

private theorem step590_2354_2396 : Positive step590 2354 2396 := by decide +kernel

private theorem step590_2397_2499 : Positive step590 2397 2499 := by decide +kernel

theorem step590_cover : ∃ ends, Cover step590 firstHeight ends := by
  exact ⟨[2331, 2337, 2353, 2396, 2499],
    ⟨(by decide), (by decide), step590_2330_2331,
      (by decide), (by decide), step590_2332_2337,
      (by decide), (by decide), step590_2338_2353,
      (by decide), (by decide), step590_2354_2396,
      (by decide), (by decide), step590_2397_2499, rfl⟩⟩

theorem step590_verified : Checked step590 :=
  ⟨step590_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step590_cover⟩

def step591 : Request :=
  ⟨⟨⟨2500, 3488, 775, 40111⟩, 479640131993600, 4147842034257⟩, 73, 6, 4, 771431⟩

theorem step591_nodes : P1_7_1.nodeRows step591.bank.shape = step591.bank.nodeRows :=
  node_check step591.bank (by decide) (by decide) (by decide)

private theorem step591_2330_2341 : Positive step591 2330 2341 := by decide +kernel

private theorem step591_2342_2372 : Positive step591 2342 2372 := by decide +kernel

private theorem step591_2373_2454 : Positive step591 2373 2454 := by decide +kernel

private theorem step591_2455_2499 : Positive step591 2455 2499 := by decide +kernel

theorem step591_cover : ∃ ends, Cover step591 firstHeight ends := by
  exact ⟨[2341, 2372, 2454, 2499],
    ⟨(by decide), (by decide), step591_2330_2341,
      (by decide), (by decide), step591_2342_2372,
      (by decide), (by decide), step591_2373_2454,
      (by decide), (by decide), step591_2455_2499, rfl⟩⟩

theorem step591_verified : Checked step591 :=
  ⟨step591_nodes, Research6966.HelperWindowCatalogue.moment3488_775,
    (by decide), (by decide), (by decide), step591_cover⟩

def step592 : Request :=
  ⟨⟨⟨2000, 2789, 620, 45124⟩, 245690786119680, 1697224818404⟩, 76, 6, 4, 771431⟩

theorem step592_nodes : P1_7_1.nodeRows step592.bank.shape = step592.bank.nodeRows :=
  node_check step592.bank (by decide) (by decide) (by decide)

private theorem step592_2330_2332 : Positive step592 2330 2332 := by decide +kernel

private theorem step592_2333_2340 : Positive step592 2333 2340 := by decide +kernel

private theorem step592_2341_2361 : Positive step592 2341 2361 := by decide +kernel

private theorem step592_2362_2416 : Positive step592 2362 2416 := by decide +kernel

private theorem step592_2417_2499 : Positive step592 2417 2499 := by decide +kernel

theorem step592_cover : ∃ ends, Cover step592 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2416, 2499],
    ⟨(by decide), (by decide), step592_2330_2332,
      (by decide), (by decide), step592_2333_2340,
      (by decide), (by decide), step592_2341_2361,
      (by decide), (by decide), step592_2362_2416,
      (by decide), (by decide), step592_2417_2499, rfl⟩⟩

theorem step592_verified : Checked step592 :=
  ⟨step592_nodes, Research6966.HelperWindowCatalogue.moment2789_620,
    (by decide), (by decide), (by decide), step592_cover⟩

def step593 : Request :=
  ⟨⟨⟨3000, 4185, 906, 57109⟩, 812266433019904, 8420412037186⟩, 103, 6, 4, 771431⟩

theorem step593_nodes : P1_7_1.nodeRows step593.bank.shape = step593.bank.nodeRows :=
  node_check step593.bank (by decide) (by decide) (by decide)

private theorem step593_2330_2332 : Positive step593 2330 2332 := by decide +kernel

private theorem step593_2333_2339 : Positive step593 2333 2339 := by decide +kernel

private theorem step593_2340_2358 : Positive step593 2340 2358 := by decide +kernel

private theorem step593_2359_2408 : Positive step593 2359 2408 := by decide +kernel

private theorem step593_2409_2499 : Positive step593 2409 2499 := by decide +kernel

theorem step593_cover : ∃ ends, Cover step593 firstHeight ends := by
  exact ⟨[2332, 2339, 2358, 2408, 2499],
    ⟨(by decide), (by decide), step593_2330_2332,
      (by decide), (by decide), step593_2333_2339,
      (by decide), (by decide), step593_2340_2358,
      (by decide), (by decide), step593_2359_2408,
      (by decide), (by decide), step593_2409_2499, rfl⟩⟩

theorem step593_verified : Checked step593 :=
  ⟨step593_nodes, Research6966.HelperWindowCatalogue.moment4185_906,
    (by decide), (by decide), (by decide), step593_cover⟩

def step594 : Request :=
  ⟨⟨⟨250, 349, 76, 4817⟩, 480667500544, 418199213⟩, 0, 6, 9, 771431⟩

theorem step594_nodes : P1_7_1.nodeRows step594.bank.shape = step594.bank.nodeRows :=
  node_check step594.bank (by decide) (by decide) (by decide)

private theorem step594_2330_2333 : Positive step594 2330 2333 := by decide +kernel

private theorem step594_2334_2348 : Positive step594 2334 2348 := by decide +kernel

private theorem step594_2349_2400 : Positive step594 2349 2400 := by decide +kernel

private theorem step594_2401_2499 : Positive step594 2401 2499 := by decide +kernel

theorem step594_cover : ∃ ends, Cover step594 firstHeight ends := by
  exact ⟨[2333, 2348, 2400, 2499],
    ⟨(by decide), (by decide), step594_2330_2333,
      (by decide), (by decide), step594_2334_2348,
      (by decide), (by decide), step594_2349_2400,
      (by decide), (by decide), step594_2401_2499, rfl⟩⟩

theorem step594_verified : Checked step594 :=
  ⟨step594_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step594_cover⟩

def step595 : Request :=
  ⟨⟨⟨350, 488, 108, 4817⟩, 1326705278976, 1607754763⟩, 1, 6, 9, 771431⟩

theorem step595_nodes : P1_7_1.nodeRows step595.bank.shape = step595.bank.nodeRows :=
  node_check step595.bank (by decide) (by decide) (by decide)

private theorem step595_2330_2330 : Positive step595 2330 2330 := by decide +kernel

private theorem step595_2331_2333 : Positive step595 2331 2333 := by decide +kernel

private theorem step595_2334_2343 : Positive step595 2334 2343 := by decide +kernel

private theorem step595_2344_2374 : Positive step595 2344 2374 := by decide +kernel

private theorem step595_2375_2473 : Positive step595 2375 2473 := by decide +kernel

private theorem step595_2474_2499 : Positive step595 2474 2499 := by decide +kernel

theorem step595_cover : ∃ ends, Cover step595 firstHeight ends := by
  exact ⟨[2330, 2333, 2343, 2374, 2473, 2499],
    ⟨(by decide), (by decide), step595_2330_2330,
      (by decide), (by decide), step595_2331_2333,
      (by decide), (by decide), step595_2334_2343,
      (by decide), (by decide), step595_2344_2374,
      (by decide), (by decide), step595_2375_2473,
      (by decide), (by decide), step595_2474_2499, rfl⟩⟩

theorem step595_verified : Checked step595 :=
  ⟨step595_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step595_cover⟩

def step596 : Request :=
  ⟨⟨⟨350, 488, 106, 5419⟩, 1308168290304, 1584729438⟩, 2, 6, 9, 771431⟩

theorem step596_nodes : P1_7_1.nodeRows step596.bank.shape = step596.bank.nodeRows :=
  node_check step596.bank (by decide) (by decide) (by decide)

private theorem step596_2330_2334 : Positive step596 2330 2334 := by decide +kernel

private theorem step596_2335_2350 : Positive step596 2335 2350 := by decide +kernel

private theorem step596_2351_2401 : Positive step596 2351 2401 := by decide +kernel

private theorem step596_2402_2499 : Positive step596 2402 2499 := by decide +kernel

theorem step596_cover : ∃ ends, Cover step596 firstHeight ends := by
  exact ⟨[2334, 2350, 2401, 2499],
    ⟨(by decide), (by decide), step596_2330_2334,
      (by decide), (by decide), step596_2335_2350,
      (by decide), (by decide), step596_2351_2401,
      (by decide), (by decide), step596_2402_2499, rfl⟩⟩

theorem step596_verified : Checked step596 :=
  ⟨step596_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step596_cover⟩

def step597 : Request :=
  ⟨⟨⟨350, 488, 106, 6096⟩, 1308168290304, 1584729438⟩, 3, 6, 9, 771431⟩

theorem step597_nodes : P1_7_1.nodeRows step597.bank.shape = step597.bank.nodeRows :=
  node_check step597.bank (by decide) (by decide) (by decide)

private theorem step597_2330_2343 : Positive step597 2330 2343 := by decide +kernel

private theorem step597_2344_2388 : Positive step597 2344 2388 := by decide +kernel

private theorem step597_2389_2499 : Positive step597 2389 2499 := by decide +kernel

theorem step597_cover : ∃ ends, Cover step597 firstHeight ends := by
  exact ⟨[2343, 2388, 2499],
    ⟨(by decide), (by decide), step597_2330_2343,
      (by decide), (by decide), step597_2344_2388,
      (by decide), (by decide), step597_2389_2499, rfl⟩⟩

theorem step597_verified : Checked step597 :=
  ⟨step597_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step597_cover⟩

def step598 : Request :=
  ⟨⟨⟨350, 488, 106, 6858⟩, 1308168290304, 1584729438⟩, 4, 6, 9, 771431⟩

theorem step598_nodes : P1_7_1.nodeRows step598.bank.shape = step598.bank.nodeRows :=
  node_check step598.bank (by decide) (by decide) (by decide)

private theorem step598_2330_2345 : Positive step598 2330 2345 := by decide +kernel

private theorem step598_2346_2396 : Positive step598 2346 2396 := by decide +kernel

private theorem step598_2397_2499 : Positive step598 2397 2499 := by decide +kernel

theorem step598_cover : ∃ ends, Cover step598 firstHeight ends := by
  exact ⟨[2345, 2396, 2499],
    ⟨(by decide), (by decide), step598_2330_2345,
      (by decide), (by decide), step598_2346_2396,
      (by decide), (by decide), step598_2397_2499, rfl⟩⟩

theorem step598_verified : Checked step598 :=
  ⟨step598_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step598_cover⟩

def step599 : Request :=
  ⟨⟨⟨420, 586, 127, 6858⟩, 2252760678400, 3279920952⟩, 5, 6, 9, 771431⟩

theorem step599_nodes : P1_7_1.nodeRows step599.bank.shape = step599.bank.nodeRows :=
  node_check step599.bank (by decide) (by decide) (by decide)

private theorem step599_2330_2335 : Positive step599 2330 2335 := by decide +kernel

private theorem step599_2336_2353 : Positive step599 2336 2353 := by decide +kernel

private theorem step599_2354_2408 : Positive step599 2354 2408 := by decide +kernel

private theorem step599_2409_2499 : Positive step599 2409 2499 := by decide +kernel

theorem step599_cover : ∃ ends, Cover step599 firstHeight ends := by
  exact ⟨[2335, 2353, 2408, 2499],
    ⟨(by decide), (by decide), step599_2330_2335,
      (by decide), (by decide), step599_2336_2353,
      (by decide), (by decide), step599_2354_2408,
      (by decide), (by decide), step599_2409_2499, rfl⟩⟩

theorem step599_verified : Checked step599 :=
  ⟨step599_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step599_cover⟩

def step600 : Request :=
  ⟨⟨⟨420, 586, 127, 8679⟩, 2252760678400, 3279920952⟩, 7, 6, 9, 771431⟩

theorem step600_nodes : P1_7_1.nodeRows step600.bank.shape = step600.bank.nodeRows :=
  node_check step600.bank (by decide) (by decide) (by decide)

private theorem step600_2330_2358 : Positive step600 2330 2358 := by decide +kernel

private theorem step600_2359_2447 : Positive step600 2359 2447 := by decide +kernel

private theorem step600_2448_2499 : Positive step600 2448 2499 := by decide +kernel

theorem step600_cover : ∃ ends, Cover step600 firstHeight ends := by
  exact ⟨[2358, 2447, 2499],
    ⟨(by decide), (by decide), step600_2330_2358,
      (by decide), (by decide), step600_2359_2447,
      (by decide), (by decide), step600_2448_2499, rfl⟩⟩

theorem step600_verified : Checked step600 :=
  ⟨step600_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step600_cover⟩

def step601 : Request :=
  ⟨⟨⟨630, 879, 195, 8679⟩, 7709474160640, 16827402390⟩, 10, 6, 9, 771431⟩

theorem step601_nodes : P1_7_1.nodeRows step601.bank.shape = step601.bank.nodeRows :=
  node_check step601.bank (by decide) (by decide) (by decide)

private theorem step601_2330_2332 : Positive step601 2330 2332 := by decide +kernel

private theorem step601_2333_2341 : Positive step601 2333 2341 := by decide +kernel

private theorem step601_2342_2366 : Positive step601 2342 2366 := by decide +kernel

private theorem step601_2367_2438 : Positive step601 2367 2438 := by decide +kernel

private theorem step601_2439_2499 : Positive step601 2439 2499 := by decide +kernel

theorem step601_cover : ∃ ends, Cover step601 firstHeight ends := by
  exact ⟨[2332, 2341, 2366, 2438, 2499],
    ⟨(by decide), (by decide), step601_2330_2332,
      (by decide), (by decide), step601_2333_2341,
      (by decide), (by decide), step601_2342_2366,
      (by decide), (by decide), step601_2367_2438,
      (by decide), (by decide), step601_2439_2499, rfl⟩⟩

theorem step601_verified : Checked step601 :=
  ⟨step601_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step601_cover⟩

def step602 : Request :=
  ⟨⟨⟨630, 879, 195, 12355⟩, 7709474160640, 16827402390⟩, 16, 6, 9, 771431⟩

theorem step602_nodes : P1_7_1.nodeRows step602.bank.shape = step602.bank.nodeRows :=
  node_check step602.bank (by decide) (by decide) (by decide)

private theorem step602_2330_2340 : Positive step602 2330 2340 := by decide +kernel

private theorem step602_2341_2372 : Positive step602 2341 2372 := by decide +kernel

private theorem step602_2373_2464 : Positive step602 2373 2464 := by decide +kernel

private theorem step602_2465_2499 : Positive step602 2465 2499 := by decide +kernel

theorem step602_cover : ∃ ends, Cover step602 firstHeight ends := by
  exact ⟨[2340, 2372, 2464, 2499],
    ⟨(by decide), (by decide), step602_2330_2340,
      (by decide), (by decide), step602_2341_2372,
      (by decide), (by decide), step602_2373_2464,
      (by decide), (by decide), step602_2465_2499, rfl⟩⟩

theorem step602_verified : Checked step602 :=
  ⟨step602_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step602_cover⟩

def step603 : Request :=
  ⟨⟨⟨750, 1046, 232, 13899⟩, 12985818152960, 33687112323⟩, 20, 6, 9, 771431⟩

theorem step603_nodes : P1_7_1.nodeRows step603.bank.shape = step603.bank.nodeRows :=
  node_check step603.bank (by decide) (by decide) (by decide)

private theorem step603_2330_2341 : Positive step603 2330 2341 := by decide +kernel

private theorem step603_2342_2374 : Positive step603 2342 2374 := by decide +kernel

private theorem step603_2375_2467 : Positive step603 2375 2467 := by decide +kernel

private theorem step603_2468_2499 : Positive step603 2468 2499 := by decide +kernel

theorem step603_cover : ∃ ends, Cover step603 firstHeight ends := by
  exact ⟨[2341, 2374, 2467, 2499],
    ⟨(by decide), (by decide), step603_2330_2341,
      (by decide), (by decide), step603_2342_2374,
      (by decide), (by decide), step603_2375_2467,
      (by decide), (by decide), step603_2468_2499, rfl⟩⟩

theorem step603_verified : Checked step603 :=
  ⟨step603_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step603_cover⟩

def step604 : Request :=
  ⟨⟨⟨900, 1255, 272, 22261⟩, 22024701870080, 68477558806⟩, 31, 6, 9, 771431⟩

theorem step604_nodes : P1_7_1.nodeRows step604.bank.shape = step604.bank.nodeRows :=
  node_check step604.bank (by decide) (by decide) (by decide)

private theorem step604_2330_2337 : Positive step604 2330 2337 := by decide +kernel

private theorem step604_2338_2359 : Positive step604 2338 2359 := by decide +kernel

private theorem step604_2360_2420 : Positive step604 2360 2420 := by decide +kernel

private theorem step604_2421_2499 : Positive step604 2421 2499 := by decide +kernel

theorem step604_cover : ∃ ends, Cover step604 firstHeight ends := by
  exact ⟨[2337, 2359, 2420, 2499],
    ⟨(by decide), (by decide), step604_2330_2337,
      (by decide), (by decide), step604_2338_2359,
      (by decide), (by decide), step604_2360_2420,
      (by decide), (by decide), step604_2421_2499, rfl⟩⟩

theorem step604_verified : Checked step604 :=
  ⟨step604_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step604_cover⟩

def step605 : Request :=
  ⟨⟨⟨900, 1255, 279, 22261⟩, 22452680785920, 69841856233⟩, 32, 6, 9, 771431⟩

theorem step605_nodes : P1_7_1.nodeRows step605.bank.shape = step605.bank.nodeRows :=
  node_check step605.bank (by decide) (by decide) (by decide)

private theorem step605_2330_2335 : Positive step605 2330 2335 := by decide +kernel

private theorem step605_2336_2352 : Positive step605 2336 2352 := by decide +kernel

private theorem step605_2353_2399 : Positive step605 2353 2399 := by decide +kernel

private theorem step605_2400_2499 : Positive step605 2400 2499 := by decide +kernel

theorem step605_cover : ∃ ends, Cover step605 firstHeight ends := by
  exact ⟨[2335, 2352, 2399, 2499],
    ⟨(by decide), (by decide), step605_2330_2335,
      (by decide), (by decide), step605_2336_2352,
      (by decide), (by decide), step605_2353_2399,
      (by decide), (by decide), step605_2400_2499, rfl⟩⟩

theorem step605_verified : Checked step605 :=
  ⟨step605_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step605_cover⟩

def step606 : Request :=
  ⟨⟨⟨1350, 1883, 418, 25043⟩, 75578221264896, 352769102024⟩, 44, 6, 9, 771431⟩

theorem step606_nodes : P1_7_1.nodeRows step606.bank.shape = step606.bank.nodeRows :=
  node_check step606.bank (by decide) (by decide) (by decide)

private theorem step606_2330_2344 : Positive step606 2330 2344 := by decide +kernel

private theorem step606_2345_2384 : Positive step606 2345 2384 := by decide +kernel

private theorem step606_2385_2492 : Positive step606 2385 2492 := by decide +kernel

private theorem step606_2493_2499 : Positive step606 2493 2499 := by decide +kernel

theorem step606_cover : ∃ ends, Cover step606 firstHeight ends := by
  exact ⟨[2344, 2384, 2492, 2499],
    ⟨(by decide), (by decide), step606_2330_2344,
      (by decide), (by decide), step606_2345_2384,
      (by decide), (by decide), step606_2385_2492,
      (by decide), (by decide), step606_2493_2499, rfl⟩⟩

theorem step606_verified : Checked step606 :=
  ⟨step606_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step606_cover⟩

def step607 : Request :=
  ⟨⟨⟨2000, 2790, 604, 40111⟩, 240862397726720, 1664965815864⟩, 73, 6, 9, 771431⟩

theorem step607_nodes : P1_7_1.nodeRows step607.bank.shape = step607.bank.nodeRows :=
  node_check step607.bank (by decide) (by decide) (by decide)

private theorem step607_2330_2333 : Positive step607 2330 2333 := by decide +kernel

private theorem step607_2334_2343 : Positive step607 2334 2343 := by decide +kernel

private theorem step607_2344_2370 : Positive step607 2344 2370 := by decide +kernel

private theorem step607_2371_2441 : Positive step607 2371 2441 := by decide +kernel

private theorem step607_2442_2499 : Positive step607 2442 2499 := by decide +kernel

theorem step607_cover : ∃ ends, Cover step607 firstHeight ends := by
  exact ⟨[2333, 2343, 2370, 2441, 2499],
    ⟨(by decide), (by decide), step607_2330_2333,
      (by decide), (by decide), step607_2334_2343,
      (by decide), (by decide), step607_2344_2370,
      (by decide), (by decide), step607_2371_2441,
      (by decide), (by decide), step607_2442_2499, rfl⟩⟩

theorem step607_verified : Checked step607 :=
  ⟨step607_nodes, Research6966.HelperWindowCatalogue.moment2790_604,
    (by decide), (by decide), (by decide), step607_cover⟩

def step608 : Request :=
  ⟨⟨⟨2000, 2789, 604, 45124⟩, 240862397726720, 1663046410409⟩, 76, 6, 9, 771431⟩

theorem step608_nodes : P1_7_1.nodeRows step608.bank.shape = step608.bank.nodeRows :=
  node_check step608.bank (by decide) (by decide) (by decide)

private theorem step608_2330_2350 : Positive step608 2330 2350 := by decide +kernel

private theorem step608_2351_2406 : Positive step608 2351 2406 := by decide +kernel

private theorem step608_2407_2499 : Positive step608 2407 2499 := by decide +kernel

theorem step608_cover : ∃ ends, Cover step608 firstHeight ends := by
  exact ⟨[2350, 2406, 2499],
    ⟨(by decide), (by decide), step608_2330_2350,
      (by decide), (by decide), step608_2351_2406,
      (by decide), (by decide), step608_2407_2499, rfl⟩⟩

theorem step608_verified : Checked step608 :=
  ⟨step608_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step608_cover⟩

def step609 : Request :=
  ⟨⟨⟨3000, 4185, 930, 50764⟩, 828559354757120, 8593576488693⟩, 103, 6, 9, 771431⟩

theorem step609_nodes : P1_7_1.nodeRows step609.bank.shape = step609.bank.nodeRows :=
  node_check step609.bank (by decide) (by decide) (by decide)

private theorem step609_2330_2345 : Positive step609 2330 2345 := by decide +kernel

private theorem step609_2346_2387 : Positive step609 2346 2387 := by decide +kernel

private theorem step609_2388_2497 : Positive step609 2388 2497 := by decide +kernel

private theorem step609_2498_2499 : Positive step609 2498 2499 := by decide +kernel

theorem step609_cover : ∃ ends, Cover step609 firstHeight ends := by
  exact ⟨[2345, 2387, 2497, 2499],
    ⟨(by decide), (by decide), step609_2330_2345,
      (by decide), (by decide), step609_2346_2387,
      (by decide), (by decide), step609_2388_2497,
      (by decide), (by decide), step609_2498_2499, rfl⟩⟩

theorem step609_verified : Checked step609 :=
  ⟨step609_nodes, Research6966.HelperWindowCatalogue.moment4185_930,
    (by decide), (by decide), (by decide), step609_cover⟩

def step610 : Request :=
  ⟨⟨⟨294, 410, 91, 3807⟩, 790165454848, 805457011⟩, 0, 6, 16, 771431⟩

theorem step610_nodes : P1_7_1.nodeRows step610.bank.shape = step610.bank.nodeRows :=
  node_check step610.bank (by decide) (by decide) (by decide)

private theorem step610_2330_2338 : Positive step610 2330 2338 := by decide +kernel

private theorem step610_2339_2368 : Positive step610 2339 2368 := by decide +kernel

private theorem step610_2369_2469 : Positive step610 2369 2469 := by decide +kernel

private theorem step610_2470_2499 : Positive step610 2470 2499 := by decide +kernel

theorem step610_cover : ∃ ends, Cover step610 firstHeight ends := by
  exact ⟨[2338, 2368, 2469, 2499],
    ⟨(by decide), (by decide), step610_2330_2338,
      (by decide), (by decide), step610_2339_2368,
      (by decide), (by decide), step610_2369_2469,
      (by decide), (by decide), step610_2470_2499, rfl⟩⟩

theorem step610_verified : Checked step610 :=
  ⟨step610_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step610_cover⟩

def step611 : Request :=
  ⟨⟨⟨294, 410, 91, 4282⟩, 790165454848, 805457011⟩, 1, 6, 16, 771431⟩

theorem step611_nodes : P1_7_1.nodeRows step611.bank.shape = step611.bank.nodeRows :=
  node_check step611.bank (by decide) (by decide) (by decide)

private theorem step611_2330_2339 : Positive step611 2330 2339 := by decide +kernel

private theorem step611_2340_2373 : Positive step611 2340 2373 := by decide +kernel

private theorem step611_2374_2487 : Positive step611 2374 2487 := by decide +kernel

private theorem step611_2488_2499 : Positive step611 2488 2499 := by decide +kernel

theorem step611_cover : ∃ ends, Cover step611 firstHeight ends := by
  exact ⟨[2339, 2373, 2487, 2499],
    ⟨(by decide), (by decide), step611_2330_2339,
      (by decide), (by decide), step611_2340_2373,
      (by decide), (by decide), step611_2374_2487,
      (by decide), (by decide), step611_2488_2499, rfl⟩⟩

theorem step611_verified : Checked step611 :=
  ⟨step611_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step611_cover⟩

def step612 : Request :=
  ⟨⟨⟨294, 410, 91, 4817⟩, 790165454848, 805457011⟩, 2, 6, 16, 771431⟩

theorem step612_nodes : P1_7_1.nodeRows step612.bank.shape = step612.bank.nodeRows :=
  node_check step612.bank (by decide) (by decide) (by decide)

private theorem step612_2330_2332 : Positive step612 2330 2332 := by decide +kernel

private theorem step612_2333_2342 : Positive step612 2333 2342 := by decide +kernel

private theorem step612_2343_2375 : Positive step612 2343 2375 := by decide +kernel

private theorem step612_2376_2486 : Positive step612 2376 2486 := by decide +kernel

private theorem step612_2487_2499 : Positive step612 2487 2499 := by decide +kernel

theorem step612_cover : ∃ ends, Cover step612 firstHeight ends := by
  exact ⟨[2332, 2342, 2375, 2486, 2499],
    ⟨(by decide), (by decide), step612_2330_2332,
      (by decide), (by decide), step612_2333_2342,
      (by decide), (by decide), step612_2343_2375,
      (by decide), (by decide), step612_2376_2486,
      (by decide), (by decide), step612_2487_2499, rfl⟩⟩

theorem step612_verified : Checked step612 :=
  ⟨step612_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step612_cover⟩

def step613 : Request :=
  ⟨⟨⟨350, 488, 104, 5419⟩, 1289487646720, 1561556019⟩, 3, 6, 16, 771431⟩

theorem step613_nodes : P1_7_1.nodeRows step613.bank.shape = step613.bank.nodeRows :=
  node_check step613.bank (by decide) (by decide) (by decide)

private theorem step613_2330_2337 : Positive step613 2330 2337 := by decide +kernel

private theorem step613_2338_2363 : Positive step613 2338 2363 := by decide +kernel

private theorem step613_2364_2447 : Positive step613 2364 2447 := by decide +kernel

private theorem step613_2448_2499 : Positive step613 2448 2499 := by decide +kernel

theorem step613_cover : ∃ ends, Cover step613 firstHeight ends := by
  exact ⟨[2337, 2363, 2447, 2499],
    ⟨(by decide), (by decide), step613_2330_2337,
      (by decide), (by decide), step613_2338_2363,
      (by decide), (by decide), step613_2364_2447,
      (by decide), (by decide), step613_2448_2499, rfl⟩⟩

theorem step613_verified : Checked step613 :=
  ⟨step613_nodes, Research6966.HelperWindowCatalogue.moment488_104,
    (by decide), (by decide), (by decide), step613_cover⟩

def step614 : Request :=
  ⟨⟨⟨420, 586, 127, 5419⟩, 2252760678400, 3279920952⟩, 4, 6, 16, 771431⟩

theorem step614_nodes : P1_7_1.nodeRows step614.bank.shape = step614.bank.nodeRows :=
  node_check step614.bank (by decide) (by decide) (by decide)

private theorem step614_2330_2336 : Positive step614 2330 2336 := by decide +kernel

private theorem step614_2337_2357 : Positive step614 2337 2357 := by decide +kernel

private theorem step614_2358_2422 : Positive step614 2358 2422 := by decide +kernel

private theorem step614_2423_2499 : Positive step614 2423 2499 := by decide +kernel

theorem step614_cover : ∃ ends, Cover step614 firstHeight ends := by
  exact ⟨[2336, 2357, 2422, 2499],
    ⟨(by decide), (by decide), step614_2330_2336,
      (by decide), (by decide), step614_2337_2357,
      (by decide), (by decide), step614_2358_2422,
      (by decide), (by decide), step614_2423_2499, rfl⟩⟩

theorem step614_verified : Checked step614 :=
  ⟨step614_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step614_cover⟩

def step615 : Request :=
  ⟨⟨⟨420, 586, 127, 6096⟩, 2252760678400, 3279920952⟩, 5, 6, 16, 771431⟩

theorem step615_nodes : P1_7_1.nodeRows step615.bank.shape = step615.bank.nodeRows :=
  node_check step615.bank (by decide) (by decide) (by decide)

private theorem step615_2330_2356 : Positive step615 2330 2356 := by decide +kernel

private theorem step615_2357_2440 : Positive step615 2357 2440 := by decide +kernel

private theorem step615_2441_2499 : Positive step615 2441 2499 := by decide +kernel

theorem step615_cover : ∃ ends, Cover step615 firstHeight ends := by
  exact ⟨[2356, 2440, 2499],
    ⟨(by decide), (by decide), step615_2330_2356,
      (by decide), (by decide), step615_2357_2440,
      (by decide), (by decide), step615_2441_2499, rfl⟩⟩

theorem step615_verified : Checked step615 :=
  ⟨step615_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step615_cover⟩

def step616 : Request :=
  ⟨⟨⟨420, 586, 130, 6858⟩, 2292767784960, 3339653140⟩, 7, 6, 16, 771431⟩

theorem step616_nodes : P1_7_1.nodeRows step616.bank.shape = step616.bank.nodeRows :=
  node_check step616.bank (by decide) (by decide) (by decide)

private theorem step616_2330_2342 : Positive step616 2330 2342 := by decide +kernel

private theorem step616_2343_2382 : Positive step616 2343 2382 := by decide +kernel

private theorem step616_2383_2499 : Positive step616 2383 2499 := by decide +kernel

theorem step616_cover : ∃ ends, Cover step616 firstHeight ends := by
  exact ⟨[2342, 2382, 2499],
    ⟨(by decide), (by decide), step616_2330_2342,
      (by decide), (by decide), step616_2343_2382,
      (by decide), (by decide), step616_2383_2499, rfl⟩⟩

theorem step616_verified : Checked step616 :=
  ⟨step616_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step616_cover⟩

def step617 : Request :=
  ⟨⟨⟨520, 725, 161, 7715⟩, 4343013310464, 7809559934⟩, 10, 6, 16, 771431⟩

theorem step617_nodes : P1_7_1.nodeRows step617.bank.shape = step617.bank.nodeRows :=
  node_check step617.bank (by decide) (by decide) (by decide)

private theorem step617_2330_2338 : Positive step617 2330 2338 := by decide +kernel

private theorem step617_2339_2365 : Positive step617 2339 2365 := by decide +kernel

private theorem step617_2366_2444 : Positive step617 2366 2444 := by decide +kernel

private theorem step617_2445_2499 : Positive step617 2445 2499 := by decide +kernel

theorem step617_cover : ∃ ends, Cover step617 firstHeight ends := by
  exact ⟨[2338, 2365, 2444, 2499],
    ⟨(by decide), (by decide), step617_2330_2338,
      (by decide), (by decide), step617_2339_2365,
      (by decide), (by decide), step617_2366_2444,
      (by decide), (by decide), step617_2445_2499, rfl⟩⟩

theorem step617_verified : Checked step617 :=
  ⟨step617_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step617_cover⟩

def step618 : Request :=
  ⟨⟨⟨750, 1046, 232, 9763⟩, 12985818152960, 33687112323⟩, 16, 6, 16, 771431⟩

theorem step618_nodes : P1_7_1.nodeRows step618.bank.shape = step618.bank.nodeRows :=
  node_check step618.bank (by decide) (by decide) (by decide)

private theorem step618_2330_2341 : Positive step618 2330 2341 := by decide +kernel

private theorem step618_2342_2374 : Positive step618 2342 2374 := by decide +kernel

private theorem step618_2375_2467 : Positive step618 2375 2467 := by decide +kernel

private theorem step618_2468_2499 : Positive step618 2468 2499 := by decide +kernel

theorem step618_cover : ∃ ends, Cover step618 firstHeight ends := by
  exact ⟨[2341, 2374, 2467, 2499],
    ⟨(by decide), (by decide), step618_2330_2341,
      (by decide), (by decide), step618_2342_2374,
      (by decide), (by decide), step618_2375_2467,
      (by decide), (by decide), step618_2468_2499, rfl⟩⟩

theorem step618_verified : Checked step618 :=
  ⟨step618_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step618_cover⟩

def step619 : Request :=
  ⟨⟨⟨750, 1046, 226, 12355⟩, 12730741817344, 33009058589⟩, 20, 6, 16, 771431⟩

theorem step619_nodes : P1_7_1.nodeRows step619.bank.shape = step619.bank.nodeRows :=
  node_check step619.bank (by decide) (by decide) (by decide)

private theorem step619_2330_2338 : Positive step619 2330 2338 := by decide +kernel

private theorem step619_2339_2364 : Positive step619 2339 2364 := by decide +kernel

private theorem step619_2365_2438 : Positive step619 2365 2438 := by decide +kernel

private theorem step619_2439_2499 : Positive step619 2439 2499 := by decide +kernel

theorem step619_cover : ∃ ends, Cover step619 firstHeight ends := by
  exact ⟨[2338, 2364, 2438, 2499],
    ⟨(by decide), (by decide), step619_2330_2338,
      (by decide), (by decide), step619_2339_2364,
      (by decide), (by decide), step619_2365_2438,
      (by decide), (by decide), step619_2439_2499, rfl⟩⟩

theorem step619_verified : Checked step619 :=
  ⟨step619_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step619_cover⟩

def step620 : Request :=
  ⟨⟨⟨900, 1255, 279, 17590⟩, 22452680785920, 69841856233⟩, 31, 6, 16, 771431⟩

theorem step620_nodes : P1_7_1.nodeRows step620.bank.shape = step620.bank.nodeRows :=
  node_check step620.bank (by decide) (by decide) (by decide)

private theorem step620_2330_2332 : Positive step620 2330 2332 := by decide +kernel

private theorem step620_2333_2340 : Positive step620 2333 2340 := by decide +kernel

private theorem step620_2341_2362 : Positive step620 2341 2362 := by decide +kernel

private theorem step620_2363_2423 : Positive step620 2363 2423 := by decide +kernel

private theorem step620_2424_2499 : Positive step620 2424 2499 := by decide +kernel

theorem step620_cover : ∃ ends, Cover step620 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2423, 2499],
    ⟨(by decide), (by decide), step620_2330_2332,
      (by decide), (by decide), step620_2333_2340,
      (by decide), (by decide), step620_2341_2362,
      (by decide), (by decide), step620_2363_2423,
      (by decide), (by decide), step620_2424_2499, rfl⟩⟩

theorem step620_verified : Checked step620 :=
  ⟨step620_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step620_cover⟩

def step621 : Request :=
  ⟨⟨⟨900, 1255, 272, 19788⟩, 22024701870080, 68477558806⟩, 32, 6, 16, 771431⟩

theorem step621_nodes : P1_7_1.nodeRows step621.bank.shape = step621.bank.nodeRows :=
  node_check step621.bank (by decide) (by decide) (by decide)

private theorem step621_2330_2333 : Positive step621 2330 2333 := by decide +kernel

private theorem step621_2334_2344 : Positive step621 2334 2344 := by decide +kernel

private theorem step621_2345_2374 : Positive step621 2345 2374 := by decide +kernel

private theorem step621_2375_2458 : Positive step621 2375 2458 := by decide +kernel

private theorem step621_2459_2499 : Positive step621 2459 2499 := by decide +kernel

theorem step621_cover : ∃ ends, Cover step621 firstHeight ends := by
  exact ⟨[2333, 2344, 2374, 2458, 2499],
    ⟨(by decide), (by decide), step621_2330_2333,
      (by decide), (by decide), step621_2334_2344,
      (by decide), (by decide), step621_2345_2374,
      (by decide), (by decide), step621_2375_2458,
      (by decide), (by decide), step621_2459_2499, rfl⟩⟩

theorem step621_verified : Checked step621 :=
  ⟨step621_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step621_cover⟩

def step622 : Request :=
  ⟨⟨⟨1350, 1883, 408, 22261⟩, 74202776600576, 346190054868⟩, 44, 6, 16, 771431⟩

theorem step622_nodes : P1_7_1.nodeRows step622.bank.shape = step622.bank.nodeRows :=
  node_check step622.bank (by decide) (by decide) (by decide)

private theorem step622_2330_2344 : Positive step622 2330 2344 := by decide +kernel

private theorem step622_2345_2385 : Positive step622 2345 2385 := by decide +kernel

private theorem step622_2386_2496 : Positive step622 2386 2496 := by decide +kernel

private theorem step622_2497_2499 : Positive step622 2497 2499 := by decide +kernel

theorem step622_cover : ∃ ends, Cover step622 firstHeight ends := by
  exact ⟨[2344, 2385, 2496, 2499],
    ⟨(by decide), (by decide), step622_2330_2344,
      (by decide), (by decide), step622_2345_2385,
      (by decide), (by decide), step622_2386_2496,
      (by decide), (by decide), step622_2497_2499, rfl⟩⟩

theorem step622_verified : Checked step622 :=
  ⟨step622_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step622_cover⟩

def step623 : Request :=
  ⟨⟨⟨2000, 2790, 604, 35655⟩, 240862397726720, 1664965815864⟩, 73, 6, 16, 771431⟩

theorem step623_nodes : P1_7_1.nodeRows step623.bank.shape = step623.bank.nodeRows :=
  node_check step623.bank (by decide) (by decide) (by decide)

private theorem step623_2330_2349 : Positive step623 2330 2349 := by decide +kernel

private theorem step623_2350_2402 : Positive step623 2350 2402 := by decide +kernel

private theorem step623_2403_2499 : Positive step623 2403 2499 := by decide +kernel

theorem step623_cover : ∃ ends, Cover step623 firstHeight ends := by
  exact ⟨[2349, 2402, 2499],
    ⟨(by decide), (by decide), step623_2330_2349,
      (by decide), (by decide), step623_2350_2402,
      (by decide), (by decide), step623_2403_2499, rfl⟩⟩

theorem step623_verified : Checked step623 :=
  ⟨step623_nodes, Research6966.HelperWindowCatalogue.moment2790_604,
    (by decide), (by decide), (by decide), step623_cover⟩

def step624 : Request :=
  ⟨⟨⟨2000, 2789, 620, 35655⟩, 245690786119680, 1697224818404⟩, 76, 6, 16, 771431⟩

theorem step624_nodes : P1_7_1.nodeRows step624.bank.shape = step624.bank.nodeRows :=
  node_check step624.bank (by decide) (by decide) (by decide)

private theorem step624_2330_2345 : Positive step624 2330 2345 := by decide +kernel

private theorem step624_2346_2387 : Positive step624 2346 2387 := by decide +kernel

private theorem step624_2388_2499 : Positive step624 2388 2499 := by decide +kernel

theorem step624_cover : ∃ ends, Cover step624 firstHeight ends := by
  exact ⟨[2345, 2387, 2499],
    ⟨(by decide), (by decide), step624_2330_2345,
      (by decide), (by decide), step624_2346_2387,
      (by decide), (by decide), step624_2388_2499, rfl⟩⟩

theorem step624_verified : Checked step624 :=
  ⟨step624_nodes, Research6966.HelperWindowCatalogue.moment2789_620,
    (by decide), (by decide), (by decide), step624_cover⟩

def step625 : Request :=
  ⟨⟨⟨3000, 4185, 906, 45124⟩, 812266433019904, 8420412037186⟩, 103, 6, 16, 771431⟩

theorem step625_nodes : P1_7_1.nodeRows step625.bank.shape = step625.bank.nodeRows :=
  node_check step625.bank (by decide) (by decide) (by decide)

private theorem step625_2330_2344 : Positive step625 2330 2344 := by decide +kernel

private theorem step625_2345_2383 : Positive step625 2345 2383 := by decide +kernel

private theorem step625_2384_2486 : Positive step625 2384 2486 := by decide +kernel

private theorem step625_2487_2499 : Positive step625 2487 2499 := by decide +kernel

theorem step625_cover : ∃ ends, Cover step625 firstHeight ends := by
  exact ⟨[2344, 2383, 2486, 2499],
    ⟨(by decide), (by decide), step625_2330_2344,
      (by decide), (by decide), step625_2345_2383,
      (by decide), (by decide), step625_2384_2486,
      (by decide), (by decide), step625_2487_2499, rfl⟩⟩

theorem step625_verified : Checked step625 :=
  ⟨step625_nodes, Research6966.HelperWindowCatalogue.moment4185_906,
    (by decide), (by decide), (by decide), step625_cover⟩

end Research6966.HelperRescueCatalogue
