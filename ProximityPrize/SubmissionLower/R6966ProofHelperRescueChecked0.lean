import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt2
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt3
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments7
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step0 : Request :=
  ⟨⟨⟨750, 1047, 226, 50764⟩, 12730741817344, 33110613849⟩, 0, 2, 1, 308328⟩

theorem step0_nodes : P1_7_1.nodeRows step0.bank.shape = step0.bank.nodeRows :=
  node_check step0.bank (by decide) (by decide) (by decide)

private theorem step0_2330_2330 : Positive step0 2330 2330 := by decide +kernel

private theorem step0_2331_2333 : Positive step0 2331 2333 := by decide +kernel

private theorem step0_2334_2341 : Positive step0 2334 2341 := by decide +kernel

private theorem step0_2342_2364 : Positive step0 2342 2364 := by decide +kernel

private theorem step0_2365_2428 : Positive step0 2365 2428 := by decide +kernel

private theorem step0_2429_2499 : Positive step0 2429 2499 := by decide +kernel

theorem step0_cover : ∃ ends, Cover step0 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2364, 2428, 2499],
    ⟨(by decide), (by decide), step0_2330_2330,
      (by decide), (by decide), step0_2331_2333,
      (by decide), (by decide), step0_2334_2341,
      (by decide), (by decide), step0_2342_2364,
      (by decide), (by decide), step0_2365_2428,
      (by decide), (by decide), step0_2429_2499, rfl⟩⟩

theorem step0_verified : Checked step0 :=
  ⟨step0_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step0_cover⟩

def step1 : Request :=
  ⟨⟨⟨900, 1256, 266, 57109⟩, 21654240231424, 67471047297⟩, 1, 2, 1, 308328⟩

theorem step1_nodes : P1_7_1.nodeRows step1.bank.shape = step1.bank.nodeRows :=
  node_check step1.bank (by decide) (by decide) (by decide)

private theorem step1_2330_2339 : Positive step1 2330 2339 := by decide +kernel

private theorem step1_2340_2367 : Positive step1 2340 2367 := by decide +kernel

private theorem step1_2368_2446 : Positive step1 2368 2446 := by decide +kernel

private theorem step1_2447_2499 : Positive step1 2447 2499 := by decide +kernel

theorem step1_cover : ∃ ends, Cover step1 firstHeight ends := by
  exact ⟨[2339, 2367, 2446, 2499],
    ⟨(by decide), (by decide), step1_2330_2339,
      (by decide), (by decide), step1_2340_2367,
      (by decide), (by decide), step1_2368_2446,
      (by decide), (by decide), step1_2447_2499, rfl⟩⟩

theorem step1_verified : Checked step1 :=
  ⟨step1_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step1_cover⟩

def step2 : Request :=
  ⟨⟨⟨1100, 1535, 326, 57109⟩, 39579969388544, 150663514795⟩, 2, 2, 1, 308328⟩

theorem step2_nodes : P1_7_1.nodeRows step2.bank.shape = step2.bank.nodeRows :=
  node_check step2.bank (by decide) (by decide) (by decide)

private theorem step2_2330_2332 : Positive step2 2330 2332 := by decide +kernel

private theorem step2_2333_2340 : Positive step2 2333 2340 := by decide +kernel

private theorem step2_2341_2362 : Positive step2 2341 2362 := by decide +kernel

private theorem step2_2363_2423 : Positive step2 2363 2423 := by decide +kernel

private theorem step2_2424_2499 : Positive step2 2424 2499 := by decide +kernel

theorem step2_cover : ∃ ends, Cover step2 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2423, 2499],
    ⟨(by decide), (by decide), step2_2330_2332,
      (by decide), (by decide), step2_2333_2340,
      (by decide), (by decide), step2_2341_2362,
      (by decide), (by decide), step2_2363_2423,
      (by decide), (by decide), step2_2424_2499, rfl⟩⟩

theorem step2_verified : Checked step2 :=
  ⟨step2_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step2_cover⟩

def step3 : Request :=
  ⟨⟨⟨1100, 1535, 326, 64247⟩, 39579969388544, 150663514795⟩, 3, 2, 1, 308328⟩

theorem step3_nodes : P1_7_1.nodeRows step3.bank.shape = step3.bank.nodeRows :=
  node_check step3.bank (by decide) (by decide) (by decide)

private theorem step3_2330_2336 : Positive step3 2330 2336 := by decide +kernel

private theorem step3_2337_2355 : Positive step3 2337 2355 := by decide +kernel

private theorem step3_2356_2407 : Positive step3 2356 2407 := by decide +kernel

private theorem step3_2408_2499 : Positive step3 2408 2499 := by decide +kernel

theorem step3_cover : ∃ ends, Cover step3 firstHeight ends := by
  exact ⟨[2336, 2355, 2407, 2499],
    ⟨(by decide), (by decide), step3_2330_2336,
      (by decide), (by decide), step3_2337_2355,
      (by decide), (by decide), step3_2356_2407,
      (by decide), (by decide), step3_2408_2499, rfl⟩⟩

theorem step3_verified : Checked step3 :=
  ⟨step3_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step3_cover⟩

def step4 : Request :=
  ⟨⟨⟨1100, 1535, 326, 72277⟩, 39579969388544, 150663514795⟩, 4, 2, 1, 308328⟩

theorem step4_nodes : P1_7_1.nodeRows step4.bank.shape = step4.bank.nodeRows :=
  node_check step4.bank (by decide) (by decide) (by decide)

private theorem step4_2330_2338 : Positive step4 2330 2338 := by decide +kernel

private theorem step4_2339_2362 : Positive step4 2339 2362 := by decide +kernel

private theorem step4_2363_2429 : Positive step4 2363 2429 := by decide +kernel

private theorem step4_2430_2499 : Positive step4 2430 2499 := by decide +kernel

theorem step4_cover : ∃ ends, Cover step4 firstHeight ends := by
  exact ⟨[2338, 2362, 2429, 2499],
    ⟨(by decide), (by decide), step4_2330_2338,
      (by decide), (by decide), step4_2339_2362,
      (by decide), (by decide), step4_2363_2429,
      (by decide), (by decide), step4_2430_2499, rfl⟩⟩

theorem step4_verified : Checked step4 :=
  ⟨step4_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step4_cover⟩

def step5 : Request :=
  ⟨⟨⟨1350, 1884, 400, 72277⟩, 73092385996800, 341469310532⟩, 5, 2, 1, 308328⟩

theorem step5_nodes : P1_7_1.nodeRows step5.bank.shape = step5.bank.nodeRows :=
  node_check step5.bank (by decide) (by decide) (by decide)

private theorem step5_2330_2335 : Positive step5 2330 2335 := by decide +kernel

private theorem step5_2336_2351 : Positive step5 2336 2351 := by decide +kernel

private theorem step5_2352_2394 : Positive step5 2352 2394 := by decide +kernel

private theorem step5_2395_2499 : Positive step5 2395 2499 := by decide +kernel

theorem step5_cover : ∃ ends, Cover step5 firstHeight ends := by
  exact ⟨[2335, 2351, 2394, 2499],
    ⟨(by decide), (by decide), step5_2330_2335,
      (by decide), (by decide), step5_2336_2351,
      (by decide), (by decide), step5_2352_2394,
      (by decide), (by decide), step5_2395_2499, rfl⟩⟩

theorem step5_verified : Checked step5 :=
  ⟨step5_nodes, Research6966.HelperWindowCatalogue.moment1884_400,
    (by decide), (by decide), (by decide), step5_cover⟩

def step6 : Request :=
  ⟨⟨⟨1350, 1884, 408, 81311⟩, 74202776600576, 346781832878⟩, 7, 2, 1, 308328⟩

theorem step6_nodes : P1_7_1.nodeRows step6.bank.shape = step6.bank.nodeRows :=
  node_check step6.bank (by decide) (by decide) (by decide)

private theorem step6_2330_2330 : Positive step6 2330 2330 := by decide +kernel

private theorem step6_2331_2333 : Positive step6 2331 2333 := by decide +kernel

private theorem step6_2334_2341 : Positive step6 2334 2341 := by decide +kernel

private theorem step6_2342_2362 : Positive step6 2342 2362 := by decide +kernel

private theorem step6_2363_2418 : Positive step6 2363 2418 := by decide +kernel

private theorem step6_2419_2499 : Positive step6 2419 2499 := by decide +kernel

theorem step6_cover : ∃ ends, Cover step6 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2418, 2499],
    ⟨(by decide), (by decide), step6_2330_2330,
      (by decide), (by decide), step6_2331_2333,
      (by decide), (by decide), step6_2334_2341,
      (by decide), (by decide), step6_2342_2362,
      (by decide), (by decide), step6_2363_2418,
      (by decide), (by decide), step6_2419_2499, rfl⟩⟩

theorem step6_verified : Checked step6 :=
  ⟨step6_nodes, Research6966.HelperWindowCatalogue.moment1884_408,
    (by decide), (by decide), (by decide), step6_cover⟩

def step7 : Request :=
  ⟨⟨⟨1644, 2285, 498, 102908⟩, 134156626165760, 753510622290⟩, 10, 2, 1, 308328⟩

theorem step7_nodes : P1_7_1.nodeRows step7.bank.shape = step7.bank.nodeRows :=
  node_check step7.bank (by decide) (by decide) (by decide)

private theorem step7_2330_2339 : Positive step7 2330 2339 := by decide +kernel

private theorem step7_2340_2365 : Positive step7 2340 2365 := by decide +kernel

private theorem step7_2366_2434 : Positive step7 2366 2434 := by decide +kernel

private theorem step7_2435_2499 : Positive step7 2435 2499 := by decide +kernel

theorem step7_cover : ∃ ends, Cover step7 firstHeight ends := by
  exact ⟨[2339, 2365, 2434, 2499],
    ⟨(by decide), (by decide), step7_2330_2339,
      (by decide), (by decide), step7_2340_2365,
      (by decide), (by decide), step7_2366_2434,
      (by decide), (by decide), step7_2435_2499, rfl⟩⟩

theorem step7_verified : Checked step7 :=
  ⟨step7_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_2285_498),
    (by decide), (by decide), (by decide), step7_cover⟩

def step8 : Request :=
  ⟨⟨⟨2000, 2792, 592, 130242⟩, 237206388080640, 1642878192099⟩, 16, 2, 1, 308328⟩

theorem step8_nodes : P1_7_1.nodeRows step8.bank.shape = step8.bank.nodeRows :=
  node_check step8.bank (by decide) (by decide) (by decide)

private theorem step8_2330_2334 : Positive step8 2330 2334 := by decide +kernel

private theorem step8_2335_2347 : Positive step8 2335 2347 := by decide +kernel

private theorem step8_2348_2382 : Positive step8 2348 2382 := by decide +kernel

private theorem step8_2383_2475 : Positive step8 2383 2475 := by decide +kernel

private theorem step8_2476_2499 : Positive step8 2476 2499 := by decide +kernel

theorem step8_cover : ∃ ends, Cover step8 firstHeight ends := by
  exact ⟨[2334, 2347, 2382, 2475, 2499],
    ⟨(by decide), (by decide), step8_2330_2334,
      (by decide), (by decide), step8_2335_2347,
      (by decide), (by decide), step8_2348_2382,
      (by decide), (by decide), step8_2383_2475,
      (by decide), (by decide), step8_2476_2499, rfl⟩⟩

theorem step8_verified : Checked step8 :=
  ⟨step8_nodes, Research6966.HelperWindowCatalogue.moment2792_592,
    (by decide), (by decide), (by decide), step8_cover⟩

def step9 : Request :=
  ⟨⟨⟨2500, 3490, 740, 146522⟩, 463070780456960, 4008490505414⟩, 20, 2, 1, 308328⟩

theorem step9_nodes : P1_7_1.nodeRows step9.bank.shape = step9.bank.nodeRows :=
  node_check step9.bank (by decide) (by decide) (by decide)

private theorem step9_2330_2336 : Positive step9 2330 2336 := by decide +kernel

private theorem step9_2337_2354 : Positive step9 2337 2354 := by decide +kernel

private theorem step9_2355_2402 : Positive step9 2355 2402 := by decide +kernel

private theorem step9_2403_2499 : Positive step9 2403 2499 := by decide +kernel

theorem step9_cover : ∃ ends, Cover step9 firstHeight ends := by
  exact ⟨[2336, 2354, 2402, 2499],
    ⟨(by decide), (by decide), step9_2330_2336,
      (by decide), (by decide), step9_2337_2354,
      (by decide), (by decide), step9_2355_2402,
      (by decide), (by decide), step9_2403_2499, rfl⟩⟩

theorem step9_verified : Checked step9 :=
  ⟨step9_nodes, Research6966.HelperWindowCatalogue.moment3490_740,
    (by decide), (by decide), (by decide), step9_cover⟩

def step10 : Request :=
  ⟨⟨⟨3000, 4187, 888, 208621⟩, 799929517735936, 8302251431404⟩, 31, 2, 1, 308328⟩

theorem step10_nodes : P1_7_1.nodeRows step10.bank.shape = step10.bank.nodeRows :=
  node_check step10.bank (by decide) (by decide) (by decide)

private theorem step10_2330_2332 : Positive step10 2330 2332 := by decide +kernel

private theorem step10_2333_2340 : Positive step10 2333 2340 := by decide +kernel

private theorem step10_2341_2361 : Positive step10 2341 2361 := by decide +kernel

private theorem step10_2362_2417 : Positive step10 2362 2417 := by decide +kernel

private theorem step10_2418_2499 : Positive step10 2418 2499 := by decide +kernel

theorem step10_cover : ∃ ends, Cover step10 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2417, 2499],
    ⟨(by decide), (by decide), step10_2330_2332,
      (by decide), (by decide), step10_2333_2340,
      (by decide), (by decide), step10_2341_2361,
      (by decide), (by decide), step10_2362_2417,
      (by decide), (by decide), step10_2418_2499, rfl⟩⟩

theorem step10_verified : Checked step10 :=
  ⟨step10_nodes, Research6966.HelperWindowCatalogue.moment4187_888,
    (by decide), (by decide), (by decide), step10_cover⟩

def step11 : Request :=
  ⟨⟨⟨3000, 4187, 906, 208621⟩, 812266433019904, 8433369009268⟩, 32, 2, 1, 308328⟩

theorem step11_nodes : P1_7_1.nodeRows step11.bank.shape = step11.bank.nodeRows :=
  node_check step11.bank (by decide) (by decide) (by decide)

private theorem step11_2330_2330 : Positive step11 2330 2330 := by decide +kernel

private theorem step11_2331_2332 : Positive step11 2331 2332 := by decide +kernel

private theorem step11_2333_2337 : Positive step11 2333 2337 := by decide +kernel

private theorem step11_2338_2350 : Positive step11 2338 2350 := by decide +kernel

private theorem step11_2351_2384 : Positive step11 2351 2384 := by decide +kernel

private theorem step11_2385_2473 : Positive step11 2385 2473 := by decide +kernel

private theorem step11_2474_2499 : Positive step11 2474 2499 := by decide +kernel

theorem step11_cover : ∃ ends, Cover step11 firstHeight ends := by
  exact ⟨[2330, 2332, 2337, 2350, 2384, 2473, 2499],
    ⟨(by decide), (by decide), step11_2330_2330,
      (by decide), (by decide), step11_2331_2332,
      (by decide), (by decide), step11_2333_2337,
      (by decide), (by decide), step11_2338_2350,
      (by decide), (by decide), step11_2351_2384,
      (by decide), (by decide), step11_2385_2473,
      (by decide), (by decide), step11_2474_2499, rfl⟩⟩

theorem step11_verified : Checked step11 :=
  ⟨step11_nodes, Research6966.HelperWindowCatalogue.moment4187_906,
    (by decide), (by decide), (by decide), step11_cover⟩

def step12 : Request :=
  ⟨⟨⟨4281, 5949, 1297, 264035⟩, 2364944629104640, 34550690014738⟩, 44, 2, 1, 308328⟩

theorem step12_nodes : P1_7_1.nodeRows step12.bank.shape = step12.bank.nodeRows :=
  node_check step12.bank (by decide) (by decide) (by decide)

private theorem step12_2330_2332 : Positive step12 2330 2332 := by decide +kernel

private theorem step12_2333_2339 : Positive step12 2333 2339 := by decide +kernel

private theorem step12_2340_2357 : Positive step12 2340 2357 := by decide +kernel

private theorem step12_2358_2404 : Positive step12 2358 2404 := by decide +kernel

private theorem step12_2405_2499 : Positive step12 2405 2499 := by decide +kernel

theorem step12_cover : ∃ ends, Cover step12 firstHeight ends := by
  exact ⟨[2332, 2339, 2357, 2404, 2499],
    ⟨(by decide), (by decide), step12_2330_2332,
      (by decide), (by decide), step12_2333_2339,
      (by decide), (by decide), step12_2340_2357,
      (by decide), (by decide), step12_2358_2404,
      (by decide), (by decide), step12_2405_2499, rfl⟩⟩

theorem step12_verified : Checked step12 :=
  ⟨step12_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_5949_1297),
    (by decide), (by decide), (by decide), step12_cover⟩

def step13 : Request :=
  ⟨⟨⟨900, 1256, 272, 45124⟩, 22024701870080, 68653176066⟩, 0, 2, 2, 308232⟩

theorem step13_nodes : P1_7_1.nodeRows step13.bank.shape = step13.bank.nodeRows :=
  node_check step13.bank (by decide) (by decide) (by decide)

private theorem step13_2330_2330 : Positive step13 2330 2330 := by decide +kernel

private theorem step13_2331_2333 : Positive step13 2331 2333 := by decide +kernel

private theorem step13_2334_2341 : Positive step13 2334 2341 := by decide +kernel

private theorem step13_2342_2363 : Positive step13 2342 2363 := by decide +kernel

private theorem step13_2364_2423 : Positive step13 2364 2423 := by decide +kernel

private theorem step13_2424_2499 : Positive step13 2424 2499 := by decide +kernel

theorem step13_cover : ∃ ends, Cover step13 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2423, 2499],
    ⟨(by decide), (by decide), step13_2330_2330,
      (by decide), (by decide), step13_2331_2333,
      (by decide), (by decide), step13_2334_2341,
      (by decide), (by decide), step13_2342_2363,
      (by decide), (by decide), step13_2364_2423,
      (by decide), (by decide), step13_2424_2499, rfl⟩⟩

theorem step13_verified : Checked step13 :=
  ⟨step13_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step13_cover⟩

def step14 : Request :=
  ⟨⟨⟨900, 1256, 272, 50764⟩, 22024701870080, 68653176066⟩, 1, 2, 2, 308232⟩

theorem step14_nodes : P1_7_1.nodeRows step14.bank.shape = step14.bank.nodeRows :=
  node_check step14.bank (by decide) (by decide) (by decide)

private theorem step14_2330_2330 : Positive step14 2330 2330 := by decide +kernel

private theorem step14_2331_2333 : Positive step14 2331 2333 := by decide +kernel

private theorem step14_2334_2341 : Positive step14 2334 2341 := by decide +kernel

private theorem step14_2342_2363 : Positive step14 2342 2363 := by decide +kernel

private theorem step14_2364_2424 : Positive step14 2364 2424 := by decide +kernel

private theorem step14_2425_2499 : Positive step14 2425 2499 := by decide +kernel

theorem step14_cover : ∃ ends, Cover step14 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2424, 2499],
    ⟨(by decide), (by decide), step14_2330_2330,
      (by decide), (by decide), step14_2331_2333,
      (by decide), (by decide), step14_2334_2341,
      (by decide), (by decide), step14_2342_2363,
      (by decide), (by decide), step14_2364_2424,
      (by decide), (by decide), step14_2425_2499, rfl⟩⟩

theorem step14_verified : Checked step14 :=
  ⟨step14_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step14_cover⟩

def step15 : Request :=
  ⟨⟨⟨900, 1256, 266, 64247⟩, 21654240231424, 67471047297⟩, 2, 2, 2, 308232⟩

theorem step15_nodes : P1_7_1.nodeRows step15.bank.shape = step15.bank.nodeRows :=
  node_check step15.bank (by decide) (by decide) (by decide)

private theorem step15_2330_2341 : Positive step15 2330 2341 := by decide +kernel

private theorem step15_2342_2375 : Positive step15 2342 2375 := by decide +kernel

private theorem step15_2376_2471 : Positive step15 2376 2471 := by decide +kernel

private theorem step15_2472_2499 : Positive step15 2472 2499 := by decide +kernel

theorem step15_cover : ∃ ends, Cover step15 firstHeight ends := by
  exact ⟨[2341, 2375, 2471, 2499],
    ⟨(by decide), (by decide), step15_2330_2341,
      (by decide), (by decide), step15_2342_2375,
      (by decide), (by decide), step15_2376_2471,
      (by decide), (by decide), step15_2472_2499, rfl⟩⟩

theorem step15_verified : Checked step15 :=
  ⟨step15_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step15_cover⟩

def step16 : Request :=
  ⟨⟨⟨900, 1256, 266, 72277⟩, 21654240231424, 67471047297⟩, 3, 2, 2, 308232⟩

theorem step16_nodes : P1_7_1.nodeRows step16.bank.shape = step16.bank.nodeRows :=
  node_check step16.bank (by decide) (by decide) (by decide)

private theorem step16_2330_2336 : Positive step16 2330 2336 := by decide +kernel

private theorem step16_2337_2356 : Positive step16 2337 2356 := by decide +kernel

private theorem step16_2357_2412 : Positive step16 2357 2412 := by decide +kernel

private theorem step16_2413_2499 : Positive step16 2413 2499 := by decide +kernel

theorem step16_cover : ∃ ends, Cover step16 firstHeight ends := by
  exact ⟨[2336, 2356, 2412, 2499],
    ⟨(by decide), (by decide), step16_2330_2336,
      (by decide), (by decide), step16_2337_2356,
      (by decide), (by decide), step16_2357_2412,
      (by decide), (by decide), step16_2413_2499, rfl⟩⟩

theorem step16_verified : Checked step16 :=
  ⟨step16_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step16_cover⟩

def step17 : Request :=
  ⟨⟨⟨998, 1387, 302, 72277⟩, 30044628975616, 102461756220⟩, 4, 2, 2, 308232⟩

theorem step17_nodes : P1_7_1.nodeRows step17.bank.shape = step17.bank.nodeRows :=
  node_check step17.bank (by decide) (by decide) (by decide)

private theorem step17_2330_2330 : Positive step17 2330 2330 := by decide +kernel

private theorem step17_2331_2332 : Positive step17 2331 2332 := by decide +kernel

private theorem step17_2333_2338 : Positive step17 2333 2338 := by decide +kernel

private theorem step17_2339_2354 : Positive step17 2339 2354 := by decide +kernel

private theorem step17_2355_2397 : Positive step17 2355 2397 := by decide +kernel

private theorem step17_2398_2499 : Positive step17 2398 2499 := by decide +kernel

theorem step17_cover : ∃ ends, Cover step17 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2354, 2397, 2499],
    ⟨(by decide), (by decide), step17_2330_2330,
      (by decide), (by decide), step17_2331_2332,
      (by decide), (by decide), step17_2333_2338,
      (by decide), (by decide), step17_2339_2354,
      (by decide), (by decide), step17_2355_2397,
      (by decide), (by decide), step17_2398_2499, rfl⟩⟩

theorem step17_verified : Checked step17 :=
  ⟨step17_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_1387_302),
    (by decide), (by decide), (by decide), step17_cover⟩

def step18 : Request :=
  ⟨⟨⟨1100, 1535, 332, 72277⟩, 40133103452160, 152819743367⟩, 5, 2, 2, 308232⟩

theorem step18_nodes : P1_7_1.nodeRows step18.bank.shape = step18.bank.nodeRows :=
  node_check step18.bank (by decide) (by decide) (by decide)

private theorem step18_2330_2330 : Positive step18 2330 2330 := by decide +kernel

private theorem step18_2331_2333 : Positive step18 2331 2333 := by decide +kernel

private theorem step18_2334_2341 : Positive step18 2334 2341 := by decide +kernel

private theorem step18_2342_2362 : Positive step18 2342 2362 := by decide +kernel

private theorem step18_2363_2419 : Positive step18 2363 2419 := by decide +kernel

private theorem step18_2420_2499 : Positive step18 2420 2499 := by decide +kernel

theorem step18_cover : ∃ ends, Cover step18 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2419, 2499],
    ⟨(by decide), (by decide), step18_2330_2330,
      (by decide), (by decide), step18_2331_2333,
      (by decide), (by decide), step18_2334_2341,
      (by decide), (by decide), step18_2342_2362,
      (by decide), (by decide), step18_2363_2419,
      (by decide), (by decide), step18_2420_2499, rfl⟩⟩

theorem step18_verified : Checked step18 :=
  ⟨step18_nodes, Research6966.HelperWindowCatalogue.moment1535_332,
    (by decide), (by decide), (by decide), step18_cover⟩

def step19 : Request :=
  ⟨⟨⟨1350, 1884, 400, 81311⟩, 73092385996800, 341469310532⟩, 7, 2, 2, 308232⟩

theorem step19_nodes : P1_7_1.nodeRows step19.bank.shape = step19.bank.nodeRows :=
  node_check step19.bank (by decide) (by decide) (by decide)

private theorem step19_2330_2335 : Positive step19 2330 2335 := by decide +kernel

private theorem step19_2336_2351 : Positive step19 2336 2351 := by decide +kernel

private theorem step19_2352_2394 : Positive step19 2352 2394 := by decide +kernel

private theorem step19_2395_2499 : Positive step19 2395 2499 := by decide +kernel

theorem step19_cover : ∃ ends, Cover step19 firstHeight ends := by
  exact ⟨[2335, 2351, 2394, 2499],
    ⟨(by decide), (by decide), step19_2330_2335,
      (by decide), (by decide), step19_2336_2351,
      (by decide), (by decide), step19_2352_2394,
      (by decide), (by decide), step19_2395_2499, rfl⟩⟩

theorem step19_verified : Checked step19 :=
  ⟨step19_nodes, Research6966.HelperWindowCatalogue.moment1884_400,
    (by decide), (by decide), (by decide), step19_cover⟩

def step20 : Request :=
  ⟨⟨⟨1650, 2303, 488, 91474⟩, 133179773812736, 760643620838⟩, 10, 2, 2, 308232⟩

theorem step20_nodes : P1_7_1.nodeRows step20.bank.shape = step20.bank.nodeRows :=
  node_check step20.bank (by decide) (by decide) (by decide)

private theorem step20_2330_2330 : Positive step20 2330 2330 := by decide +kernel

private theorem step20_2331_2333 : Positive step20 2331 2333 := by decide +kernel

private theorem step20_2334_2341 : Positive step20 2334 2341 := by decide +kernel

private theorem step20_2342_2363 : Positive step20 2342 2363 := by decide +kernel

private theorem step20_2364_2422 : Positive step20 2364 2422 := by decide +kernel

private theorem step20_2423_2499 : Positive step20 2423 2499 := by decide +kernel

theorem step20_cover : ∃ ends, Cover step20 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2422, 2499],
    ⟨(by decide), (by decide), step20_2330_2330,
      (by decide), (by decide), step20_2331_2333,
      (by decide), (by decide), step20_2334_2341,
      (by decide), (by decide), step20_2342_2363,
      (by decide), (by decide), step20_2364_2422,
      (by decide), (by decide), step20_2423_2499, rfl⟩⟩

theorem step20_verified : Checked step20 :=
  ⟨step20_nodes, Research6966.HelperWindowCatalogue.moment2303_488,
    (by decide), (by decide), (by decide), step20_cover⟩

def step21 : Request :=
  ⟨⟨⟨1927, 2678, 584, 130242⟩, 216034207334400, 1421525065183⟩, 16, 2, 2, 308232⟩

theorem step21_nodes : P1_7_1.nodeRows step21.bank.shape = step21.bank.nodeRows :=
  node_check step21.bank (by decide) (by decide) (by decide)

private theorem step21_2330_2333 : Positive step21 2330 2333 := by decide +kernel

private theorem step21_2334_2344 : Positive step21 2334 2344 := by decide +kernel

private theorem step21_2345_2372 : Positive step21 2345 2372 := by decide +kernel

private theorem step21_2373_2446 : Positive step21 2373 2446 := by decide +kernel

private theorem step21_2447_2499 : Positive step21 2447 2499 := by decide +kernel

theorem step21_cover : ∃ ends, Cover step21 firstHeight ends := by
  exact ⟨[2333, 2344, 2372, 2446, 2499],
    ⟨(by decide), (by decide), step21_2330_2333,
      (by decide), (by decide), step21_2334_2344,
      (by decide), (by decide), step21_2345_2372,
      (by decide), (by decide), step21_2373_2446,
      (by decide), (by decide), step21_2447_2499, rfl⟩⟩

theorem step21_verified : Checked step21 :=
  ⟨step21_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_2678_584),
    (by decide), (by decide), (by decide), step21_cover⟩

def step22 : Request :=
  ⟨⟨⟨2000, 2791, 592, 164837⟩, 237206388080640, 1640986809111⟩, 20, 2, 2, 308232⟩

theorem step22_nodes : P1_7_1.nodeRows step22.bank.shape = step22.bank.nodeRows :=
  node_check step22.bank (by decide) (by decide) (by decide)

private theorem step22_2330_2334 : Positive step22 2330 2334 := by decide +kernel

private theorem step22_2335_2347 : Positive step22 2335 2347 := by decide +kernel

private theorem step22_2348_2382 : Positive step22 2348 2382 := by decide +kernel

private theorem step22_2383_2475 : Positive step22 2383 2475 := by decide +kernel

private theorem step22_2476_2499 : Positive step22 2476 2499 := by decide +kernel

theorem step22_cover : ∃ ends, Cover step22 firstHeight ends := by
  exact ⟨[2334, 2347, 2382, 2475, 2499],
    ⟨(by decide), (by decide), step22_2330_2334,
      (by decide), (by decide), step22_2335_2347,
      (by decide), (by decide), step22_2348_2382,
      (by decide), (by decide), step22_2383_2475,
      (by decide), (by decide), step22_2476_2499, rfl⟩⟩

theorem step22_verified : Checked step22 :=
  ⟨step22_nodes, Research6966.HelperWindowCatalogue.moment2791_592,
    (by decide), (by decide), (by decide), step22_cover⟩

end Research6966.HelperRescueCatalogue
