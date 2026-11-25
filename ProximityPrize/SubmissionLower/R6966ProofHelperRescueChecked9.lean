import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments11
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments9
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step284 : Request :=
  ⟨⟨⟨2000, 2791, 604, 50764⟩, 240862397726720, 1666886727164⟩, 31, 4, 2, 514287⟩

theorem step284_nodes : P1_7_1.nodeRows step284.bank.shape = step284.bank.nodeRows :=
  node_check step284.bank (by decide) (by decide) (by decide)

private theorem step284_2330_2333 : Positive step284 2330 2333 := by decide +kernel

private theorem step284_2334_2344 : Positive step284 2334 2344 := by decide +kernel

private theorem step284_2345_2373 : Positive step284 2345 2373 := by decide +kernel

private theorem step284_2374_2450 : Positive step284 2374 2450 := by decide +kernel

private theorem step284_2451_2499 : Positive step284 2451 2499 := by decide +kernel

theorem step284_cover : ∃ ends, Cover step284 firstHeight ends := by
  exact ⟨[2333, 2344, 2373, 2450, 2499],
    ⟨(by decide), (by decide), step284_2330_2333,
      (by decide), (by decide), step284_2334_2344,
      (by decide), (by decide), step284_2345_2373,
      (by decide), (by decide), step284_2374_2450,
      (by decide), (by decide), step284_2451_2499, rfl⟩⟩

theorem step284_verified : Checked step284 :=
  ⟨step284_nodes, Research6966.HelperWindowCatalogue.moment2791_604,
    (by decide), (by decide), (by decide), step284_cover⟩

def step285 : Request :=
  ⟨⟨⟨1650, 2302, 498, 57109⟩, 135254251667456, 771697512616⟩, 32, 4, 2, 514287⟩

theorem step285_nodes : P1_7_1.nodeRows step285.bank.shape = step285.bank.nodeRows :=
  node_check step285.bank (by decide) (by decide) (by decide)

private theorem step285_2330_2341 : Positive step285 2330 2341 := by decide +kernel

private theorem step285_2342_2373 : Positive step285 2342 2373 := by decide +kernel

private theorem step285_2374_2459 : Positive step285 2374 2459 := by decide +kernel

private theorem step285_2460_2499 : Positive step285 2460 2499 := by decide +kernel

theorem step285_cover : ∃ ends, Cover step285 firstHeight ends := by
  exact ⟨[2341, 2373, 2459, 2499],
    ⟨(by decide), (by decide), step285_2330_2341,
      (by decide), (by decide), step285_2342_2373,
      (by decide), (by decide), step285_2374_2459,
      (by decide), (by decide), step285_2460_2499, rfl⟩⟩

theorem step285_verified : Checked step285 :=
  ⟨step285_nodes, Research6966.HelperWindowCatalogue.moment2302_498,
    (by decide), (by decide), (by decide), step285_cover⟩

def step286 : Request :=
  ⟨⟨⟨2500, 3489, 740, 72277⟩, 463070780456960, 4004797990029⟩, 44, 4, 2, 514287⟩

theorem step286_nodes : P1_7_1.nodeRows step286.bank.shape = step286.bank.nodeRows :=
  node_check step286.bank (by decide) (by decide) (by decide)

private theorem step286_2330_2340 : Positive step286 2330 2340 := by decide +kernel

private theorem step286_2341_2370 : Positive step286 2341 2370 := by decide +kernel

private theorem step286_2371_2450 : Positive step286 2371 2450 := by decide +kernel

private theorem step286_2451_2499 : Positive step286 2451 2499 := by decide +kernel

theorem step286_cover : ∃ ends, Cover step286 firstHeight ends := by
  exact ⟨[2340, 2370, 2450, 2499],
    ⟨(by decide), (by decide), step286_2330_2340,
      (by decide), (by decide), step286_2341_2370,
      (by decide), (by decide), step286_2371_2450,
      (by decide), (by decide), step286_2451_2499, rfl⟩⟩

theorem step286_verified : Checked step286 :=
  ⟨step286_nodes, Research6966.HelperWindowCatalogue.moment3489_740,
    (by decide), (by decide), (by decide), step286_cover⟩

def step287 : Request :=
  ⟨⟨⟨3500, 4884, 1085, 102908⟩, 1315428062986240, 15931892384151⟩, 73, 4, 2, 514287⟩

theorem step287_nodes : P1_7_1.nodeRows step287.bank.shape = step287.bank.nodeRows :=
  node_check step287.bank (by decide) (by decide) (by decide)

private theorem step287_2330_2331 : Positive step287 2330 2331 := by decide +kernel

private theorem step287_2332_2336 : Positive step287 2332 2336 := by decide +kernel

private theorem step287_2337_2349 : Positive step287 2337 2349 := by decide +kernel

private theorem step287_2350_2382 : Positive step287 2350 2382 := by decide +kernel

private theorem step287_2383_2468 : Positive step287 2383 2468 := by decide +kernel

private theorem step287_2469_2499 : Positive step287 2469 2499 := by decide +kernel

theorem step287_cover : ∃ ends, Cover step287 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2382, 2468, 2499],
    ⟨(by decide), (by decide), step287_2330_2331,
      (by decide), (by decide), step287_2332_2336,
      (by decide), (by decide), step287_2337_2349,
      (by decide), (by decide), step287_2350_2382,
      (by decide), (by decide), step287_2383_2468,
      (by decide), (by decide), step287_2469_2499, rfl⟩⟩

theorem step287_verified : Checked step287 :=
  ⟨step287_nodes, Research6966.HelperWindowCatalogue.moment4884_1085,
    (by decide), (by decide), (by decide), step287_cover⟩

def step288 : Request :=
  ⟨⟨⟨3500, 4884, 1036, 115771⟩, 1269967213297664, 15368047192365⟩, 76, 4, 2, 514287⟩

theorem step288_nodes : P1_7_1.nodeRows step288.bank.shape = step288.bank.nodeRows :=
  node_check step288.bank (by decide) (by decide) (by decide)

private theorem step288_2330_2330 : Positive step288 2330 2330 := by decide +kernel

private theorem step288_2331_2332 : Positive step288 2331 2332 := by decide +kernel

private theorem step288_2333_2338 : Positive step288 2333 2338 := by decide +kernel

private theorem step288_2339_2354 : Positive step288 2339 2354 := by decide +kernel

private theorem step288_2355_2396 : Positive step288 2355 2396 := by decide +kernel

private theorem step288_2397_2499 : Positive step288 2397 2499 := by decide +kernel

theorem step288_cover : ∃ ends, Cover step288 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2354, 2396, 2499],
    ⟨(by decide), (by decide), step288_2330_2330,
      (by decide), (by decide), step288_2331_2332,
      (by decide), (by decide), step288_2333_2338,
      (by decide), (by decide), step288_2339_2354,
      (by decide), (by decide), step288_2355_2396,
      (by decide), (by decide), step288_2397_2499, rfl⟩⟩

theorem step288_verified : Checked step288 :=
  ⟨step288_nodes, Research6966.HelperWindowCatalogue.moment4884_1036,
    (by decide), (by decide), (by decide), step288_cover⟩

def step289 : Request :=
  ⟨⟨⟨4500, 6279, 1359, 146522⟩, 2739950258749440, 42632508857204⟩, 103, 4, 2, 514287⟩

theorem step289_nodes : P1_7_1.nodeRows step289.bank.shape = step289.bank.nodeRows :=
  node_check step289.bank (by decide) (by decide) (by decide)

private theorem step289_2330_2334 : Positive step289 2330 2334 := by decide +kernel

private theorem step289_2335_2347 : Positive step289 2335 2347 := by decide +kernel

private theorem step289_2348_2380 : Positive step289 2348 2380 := by decide +kernel

private theorem step289_2381_2466 : Positive step289 2381 2466 := by decide +kernel

private theorem step289_2467_2499 : Positive step289 2467 2499 := by decide +kernel

theorem step289_cover : ∃ ends, Cover step289 firstHeight ends := by
  exact ⟨[2334, 2347, 2380, 2466, 2499],
    ⟨(by decide), (by decide), step289_2330_2334,
      (by decide), (by decide), step289_2335_2347,
      (by decide), (by decide), step289_2348_2380,
      (by decide), (by decide), step289_2381_2466,
      (by decide), (by decide), step289_2467_2499, rfl⟩⟩

theorem step289_verified : Checked step289 :=
  ⟨step289_nodes, Research6966.HelperWindowCatalogue.moment6279_1359,
    (by decide), (by decide), (by decide), step289_cover⟩

def step290 : Request :=
  ⟨⟨⟨420, 586, 127, 12355⟩, 2252760678400, 3279920952⟩, 0, 4, 4, 514287⟩

theorem step290_nodes : P1_7_1.nodeRows step290.bank.shape = step290.bank.nodeRows :=
  node_check step290.bank (by decide) (by decide) (by decide)

private theorem step290_2330_2335 : Positive step290 2330 2335 := by decide +kernel

private theorem step290_2336_2354 : Positive step290 2336 2354 := by decide +kernel

private theorem step290_2355_2412 : Positive step290 2355 2412 := by decide +kernel

private theorem step290_2413_2499 : Positive step290 2413 2499 := by decide +kernel

theorem step290_cover : ∃ ends, Cover step290 firstHeight ends := by
  exact ⟨[2335, 2354, 2412, 2499],
    ⟨(by decide), (by decide), step290_2330_2335,
      (by decide), (by decide), step290_2336_2354,
      (by decide), (by decide), step290_2355_2412,
      (by decide), (by decide), step290_2413_2499, rfl⟩⟩

theorem step290_verified : Checked step290 :=
  ⟨step290_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step290_cover⟩

def step291 : Request :=
  ⟨⟨⟨520, 726, 154, 13899⟩, 4199390904320, 7578534004⟩, 1, 4, 4, 514287⟩

theorem step291_nodes : P1_7_1.nodeRows step291.bank.shape = step291.bank.nodeRows :=
  node_check step291.bank (by decide) (by decide) (by decide)

private theorem step291_2330_2339 : Positive step291 2330 2339 := by decide +kernel

private theorem step291_2340_2369 : Positive step291 2340 2369 := by decide +kernel

private theorem step291_2370_2458 : Positive step291 2370 2458 := by decide +kernel

private theorem step291_2459_2499 : Positive step291 2459 2499 := by decide +kernel

theorem step291_cover : ∃ ends, Cover step291 firstHeight ends := by
  exact ⟨[2339, 2369, 2458, 2499],
    ⟨(by decide), (by decide), step291_2330_2339,
      (by decide), (by decide), step291_2340_2369,
      (by decide), (by decide), step291_2370_2458,
      (by decide), (by decide), step291_2459_2499, rfl⟩⟩

theorem step291_verified : Checked step291 :=
  ⟨step291_nodes, Research6966.HelperWindowCatalogue.moment726_154,
    (by decide), (by decide), (by decide), step291_cover⟩

def step292 : Request :=
  ⟨⟨⟨520, 726, 154, 15636⟩, 4199390904320, 7578534004⟩, 2, 4, 4, 514287⟩

theorem step292_nodes : P1_7_1.nodeRows step292.bank.shape = step292.bank.nodeRows :=
  node_check step292.bank (by decide) (by decide) (by decide)

private theorem step292_2330_2341 : Positive step292 2330 2341 := by decide +kernel

private theorem step292_2342_2377 : Positive step292 2342 2377 := by decide +kernel

private theorem step292_2378_2485 : Positive step292 2378 2485 := by decide +kernel

private theorem step292_2486_2499 : Positive step292 2486 2499 := by decide +kernel

theorem step292_cover : ∃ ends, Cover step292 firstHeight ends := by
  exact ⟨[2341, 2377, 2485, 2499],
    ⟨(by decide), (by decide), step292_2330_2341,
      (by decide), (by decide), step292_2342_2377,
      (by decide), (by decide), step292_2378_2485,
      (by decide), (by decide), step292_2486_2499, rfl⟩⟩

theorem step292_verified : Checked step292 :=
  ⟨step292_nodes, Research6966.HelperWindowCatalogue.moment726_154,
    (by decide), (by decide), (by decide), step292_cover⟩

def step293 : Request :=
  ⟨⟨⟨630, 879, 190, 15636⟩, 7559493713920, 16491913877⟩, 3, 4, 4, 514287⟩

theorem step293_nodes : P1_7_1.nodeRows step293.bank.shape = step293.bank.nodeRows :=
  node_check step293.bank (by decide) (by decide) (by decide)

private theorem step293_2330_2340 : Positive step293 2330 2340 := by decide +kernel

private theorem step293_2341_2372 : Positive step293 2341 2372 := by decide +kernel

private theorem step293_2373_2465 : Positive step293 2373 2465 := by decide +kernel

private theorem step293_2466_2499 : Positive step293 2466 2499 := by decide +kernel

theorem step293_cover : ∃ ends, Cover step293 firstHeight ends := by
  exact ⟨[2340, 2372, 2465, 2499],
    ⟨(by decide), (by decide), step293_2330_2340,
      (by decide), (by decide), step293_2341_2372,
      (by decide), (by decide), step293_2373_2465,
      (by decide), (by decide), step293_2466_2499, rfl⟩⟩

theorem step293_verified : Checked step293 :=
  ⟨step293_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step293_cover⟩

def step294 : Request :=
  ⟨⟨⟨630, 879, 186, 17590⟩, 7438337572864, 16221345781⟩, 4, 4, 4, 514287⟩

theorem step294_nodes : P1_7_1.nodeRows step294.bank.shape = step294.bank.nodeRows :=
  node_check step294.bank (by decide) (by decide) (by decide)

private theorem step294_2330_2332 : Positive step294 2330 2332 := by decide +kernel

private theorem step294_2333_2341 : Positive step294 2333 2341 := by decide +kernel

private theorem step294_2342_2367 : Positive step294 2342 2367 := by decide +kernel

private theorem step294_2368_2443 : Positive step294 2368 2443 := by decide +kernel

private theorem step294_2444_2499 : Positive step294 2444 2499 := by decide +kernel

theorem step294_cover : ∃ ends, Cover step294 firstHeight ends := by
  exact ⟨[2332, 2341, 2367, 2443, 2499],
    ⟨(by decide), (by decide), step294_2330_2332,
      (by decide), (by decide), step294_2333_2341,
      (by decide), (by decide), step294_2342_2367,
      (by decide), (by decide), step294_2368_2443,
      (by decide), (by decide), step294_2444_2499, rfl⟩⟩

theorem step294_verified : Checked step294 :=
  ⟨step294_nodes, Research6966.HelperWindowCatalogue.moment879_186,
    (by decide), (by decide), (by decide), step294_cover⟩

def step295 : Request :=
  ⟨⟨⟨750, 1047, 226, 17590⟩, 12730741817344, 33110613849⟩, 5, 4, 4, 514287⟩

theorem step295_nodes : P1_7_1.nodeRows step295.bank.shape = step295.bank.nodeRows :=
  node_check step295.bank (by decide) (by decide) (by decide)

private theorem step295_2330_2332 : Positive step295 2330 2332 := by decide +kernel

private theorem step295_2333_2340 : Positive step295 2333 2340 := by decide +kernel

private theorem step295_2341_2363 : Positive step295 2341 2363 := by decide +kernel

private theorem step295_2364_2427 : Positive step295 2364 2427 := by decide +kernel

private theorem step295_2428_2499 : Positive step295 2428 2499 := by decide +kernel

theorem step295_cover : ∃ ends, Cover step295 firstHeight ends := by
  exact ⟨[2332, 2340, 2363, 2427, 2499],
    ⟨(by decide), (by decide), step295_2330_2332,
      (by decide), (by decide), step295_2333_2340,
      (by decide), (by decide), step295_2341_2363,
      (by decide), (by decide), step295_2364_2427,
      (by decide), (by decide), step295_2428_2499, rfl⟩⟩

theorem step295_verified : Checked step295 :=
  ⟨step295_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step295_cover⟩

def step296 : Request :=
  ⟨⟨⟨900, 1256, 272, 19788⟩, 22024701870080, 68653176066⟩, 7, 4, 4, 514287⟩

theorem step296_nodes : P1_7_1.nodeRows step296.bank.shape = step296.bank.nodeRows :=
  node_check step296.bank (by decide) (by decide) (by decide)

private theorem step296_2330_2330 : Positive step296 2330 2330 := by decide +kernel

private theorem step296_2331_2333 : Positive step296 2331 2333 := by decide +kernel

private theorem step296_2334_2341 : Positive step296 2334 2341 := by decide +kernel

private theorem step296_2342_2364 : Positive step296 2342 2364 := by decide +kernel

private theorem step296_2365_2427 : Positive step296 2365 2427 := by decide +kernel

private theorem step296_2428_2499 : Positive step296 2428 2499 := by decide +kernel

theorem step296_cover : ∃ ends, Cover step296 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2364, 2427, 2499],
    ⟨(by decide), (by decide), step296_2330_2330,
      (by decide), (by decide), step296_2331_2333,
      (by decide), (by decide), step296_2334_2341,
      (by decide), (by decide), step296_2342_2364,
      (by decide), (by decide), step296_2365_2427,
      (by decide), (by decide), step296_2428_2499, rfl⟩⟩

theorem step296_verified : Checked step296 :=
  ⟨step296_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step296_cover⟩

def step297 : Request :=
  ⟨⟨⟨900, 1256, 266, 25043⟩, 21654240231424, 67471047297⟩, 10, 4, 4, 514287⟩

theorem step297_nodes : P1_7_1.nodeRows step297.bank.shape = step297.bank.nodeRows :=
  node_check step297.bank (by decide) (by decide) (by decide)

private theorem step297_2330_2334 : Positive step297 2330 2334 := by decide +kernel

private theorem step297_2335_2348 : Positive step297 2335 2348 := by decide +kernel

private theorem step297_2349_2387 : Positive step297 2349 2387 := by decide +kernel

private theorem step297_2388_2497 : Positive step297 2388 2497 := by decide +kernel

private theorem step297_2498_2499 : Positive step297 2498 2499 := by decide +kernel

theorem step297_cover : ∃ ends, Cover step297 firstHeight ends := by
  exact ⟨[2334, 2348, 2387, 2497, 2499],
    ⟨(by decide), (by decide), step297_2330_2334,
      (by decide), (by decide), step297_2335_2348,
      (by decide), (by decide), step297_2349_2387,
      (by decide), (by decide), step297_2388_2497,
      (by decide), (by decide), step297_2498_2499, rfl⟩⟩

theorem step297_verified : Checked step297 :=
  ⟨step297_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step297_cover⟩

def step298 : Request :=
  ⟨⟨⟨1100, 1535, 332, 31694⟩, 40133103452160, 152819743367⟩, 16, 4, 4, 514287⟩

theorem step298_nodes : P1_7_1.nodeRows step298.bank.shape = step298.bank.nodeRows :=
  node_check step298.bank (by decide) (by decide) (by decide)

private theorem step298_2330_2339 : Positive step298 2330 2339 := by decide +kernel

private theorem step298_2340_2367 : Positive step298 2340 2367 := by decide +kernel

private theorem step298_2368_2443 : Positive step298 2368 2443 := by decide +kernel

private theorem step298_2444_2499 : Positive step298 2444 2499 := by decide +kernel

theorem step298_cover : ∃ ends, Cover step298 firstHeight ends := by
  exact ⟨[2339, 2367, 2443, 2499],
    ⟨(by decide), (by decide), step298_2330_2339,
      (by decide), (by decide), step298_2340_2367,
      (by decide), (by decide), step298_2368_2443,
      (by decide), (by decide), step298_2444_2499, rfl⟩⟩

theorem step298_verified : Checked step298 :=
  ⟨step298_nodes, Research6966.HelperWindowCatalogue.moment1535_332,
    (by decide), (by decide), (by decide), step298_cover⟩

def step299 : Request :=
  ⟨⟨⟨1350, 1884, 408, 35655⟩, 74202776600576, 346781832878⟩, 20, 4, 4, 514287⟩

theorem step299_nodes : P1_7_1.nodeRows step299.bank.shape = step299.bank.nodeRows :=
  node_check step299.bank (by decide) (by decide) (by decide)

private theorem step299_2330_2339 : Positive step299 2330 2339 := by decide +kernel

private theorem step299_2340_2366 : Positive step299 2340 2366 := by decide +kernel

private theorem step299_2367_2439 : Positive step299 2367 2439 := by decide +kernel

private theorem step299_2440_2499 : Positive step299 2440 2499 := by decide +kernel

theorem step299_cover : ∃ ends, Cover step299 firstHeight ends := by
  exact ⟨[2339, 2366, 2439, 2499],
    ⟨(by decide), (by decide), step299_2330_2339,
      (by decide), (by decide), step299_2340_2366,
      (by decide), (by decide), step299_2367_2439,
      (by decide), (by decide), step299_2440_2499, rfl⟩⟩

theorem step299_verified : Checked step299 :=
  ⟨step299_nodes, Research6966.HelperWindowCatalogue.moment1884_408,
    (by decide), (by decide), (by decide), step299_cover⟩

def step300 : Request :=
  ⟨⟨⟨1650, 2302, 498, 50764⟩, 135254251667456, 771697512616⟩, 31, 4, 4, 514287⟩

theorem step300_nodes : P1_7_1.nodeRows step300.bank.shape = step300.bank.nodeRows :=
  node_check step300.bank (by decide) (by decide) (by decide)

private theorem step300_2330_2339 : Positive step300 2330 2339 := by decide +kernel

private theorem step300_2340_2365 : Positive step300 2340 2365 := by decide +kernel

private theorem step300_2366_2435 : Positive step300 2366 2435 := by decide +kernel

private theorem step300_2436_2499 : Positive step300 2436 2499 := by decide +kernel

theorem step300_cover : ∃ ends, Cover step300 firstHeight ends := by
  exact ⟨[2339, 2365, 2435, 2499],
    ⟨(by decide), (by decide), step300_2330_2339,
      (by decide), (by decide), step300_2340_2365,
      (by decide), (by decide), step300_2366_2435,
      (by decide), (by decide), step300_2436_2499, rfl⟩⟩

theorem step300_verified : Checked step300 :=
  ⟨step300_nodes, Research6966.HelperWindowCatalogue.moment2302_498,
    (by decide), (by decide), (by decide), step300_cover⟩

def step301 : Request :=
  ⟨⟨⟨1650, 2302, 512, 50764⟩, 138129879859200, 788519769358⟩, 32, 4, 4, 514287⟩

theorem step301_nodes : P1_7_1.nodeRows step301.bank.shape = step301.bank.nodeRows :=
  node_check step301.bank (by decide) (by decide) (by decide)

private theorem step301_2330_2331 : Positive step301 2330 2331 := by decide +kernel

private theorem step301_2332_2337 : Positive step301 2332 2337 := by decide +kernel

private theorem step301_2338_2352 : Positive step301 2338 2352 := by decide +kernel

private theorem step301_2353_2392 : Positive step301 2353 2392 := by decide +kernel

private theorem step301_2393_2498 : Positive step301 2393 2498 := by decide +kernel

private theorem step301_2499_2499 : Positive step301 2499 2499 := by decide +kernel

theorem step301_cover : ∃ ends, Cover step301 firstHeight ends := by
  exact ⟨[2331, 2337, 2352, 2392, 2498, 2499],
    ⟨(by decide), (by decide), step301_2330_2331,
      (by decide), (by decide), step301_2332_2337,
      (by decide), (by decide), step301_2338_2352,
      (by decide), (by decide), step301_2353_2392,
      (by decide), (by decide), step301_2393_2498,
      (by decide), (by decide), step301_2499_2499, rfl⟩⟩

theorem step301_verified : Checked step301 :=
  ⟨step301_nodes, Research6966.HelperWindowCatalogue.moment2302_512,
    (by decide), (by decide), (by decide), step301_cover⟩

def step302 : Request :=
  ⟨⟨⟨2500, 3489, 755, 64247⟩, 470210689105920, 4068029992867⟩, 44, 4, 4, 514287⟩

theorem step302_nodes : P1_7_1.nodeRows step302.bank.shape = step302.bank.nodeRows :=
  node_check step302.bank (by decide) (by decide) (by decide)

private theorem step302_2330_2342 : Positive step302 2330 2342 := by decide +kernel

private theorem step302_2343_2376 : Positive step302 2343 2376 := by decide +kernel

private theorem step302_2377_2466 : Positive step302 2377 2466 := by decide +kernel

private theorem step302_2467_2499 : Positive step302 2467 2499 := by decide +kernel

theorem step302_cover : ∃ ends, Cover step302 firstHeight ends := by
  exact ⟨[2342, 2376, 2466, 2499],
    ⟨(by decide), (by decide), step302_2330_2342,
      (by decide), (by decide), step302_2343_2376,
      (by decide), (by decide), step302_2377_2466,
      (by decide), (by decide), step302_2467_2499, rfl⟩⟩

theorem step302_verified : Checked step302 :=
  ⟨step302_nodes, Research6966.HelperWindowCatalogue.moment3489_755,
    (by decide), (by decide), (by decide), step302_cover⟩

def step303 : Request :=
  ⟨⟨⟨3500, 4884, 1036, 102908⟩, 1269967213297664, 15368047192365⟩, 73, 4, 4, 514287⟩

theorem step303_nodes : P1_7_1.nodeRows step303.bank.shape = step303.bank.nodeRows :=
  node_check step303.bank (by decide) (by decide) (by decide)

private theorem step303_2330_2330 : Positive step303 2330 2330 := by decide +kernel

private theorem step303_2331_2333 : Positive step303 2331 2333 := by decide +kernel

private theorem step303_2334_2341 : Positive step303 2334 2341 := by decide +kernel

private theorem step303_2342_2362 : Positive step303 2342 2362 := by decide +kernel

private theorem step303_2363_2417 : Positive step303 2363 2417 := by decide +kernel

private theorem step303_2418_2499 : Positive step303 2418 2499 := by decide +kernel

theorem step303_cover : ∃ ends, Cover step303 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2417, 2499],
    ⟨(by decide), (by decide), step303_2330_2330,
      (by decide), (by decide), step303_2331_2333,
      (by decide), (by decide), step303_2334_2341,
      (by decide), (by decide), step303_2342_2362,
      (by decide), (by decide), step303_2363_2417,
      (by decide), (by decide), step303_2418_2499, rfl⟩⟩

theorem step303_verified : Checked step303 :=
  ⟨step303_nodes, Research6966.HelperWindowCatalogue.moment4884_1036,
    (by decide), (by decide), (by decide), step303_cover⟩

def step304 : Request :=
  ⟨⟨⟨3500, 4884, 1057, 102908⟩, 1289556817346560, 15610792063730⟩, 76, 4, 4, 514287⟩

theorem step304_nodes : P1_7_1.nodeRows step304.bank.shape = step304.bank.nodeRows :=
  node_check step304.bank (by decide) (by decide) (by decide)

private theorem step304_2330_2333 : Positive step304 2330 2333 := by decide +kernel

private theorem step304_2334_2344 : Positive step304 2334 2344 := by decide +kernel

private theorem step304_2345_2372 : Positive step304 2345 2372 := by decide +kernel

private theorem step304_2373_2445 : Positive step304 2373 2445 := by decide +kernel

private theorem step304_2446_2499 : Positive step304 2446 2499 := by decide +kernel

theorem step304_cover : ∃ ends, Cover step304 firstHeight ends := by
  exact ⟨[2333, 2344, 2372, 2445, 2499],
    ⟨(by decide), (by decide), step304_2330_2333,
      (by decide), (by decide), step304_2334_2344,
      (by decide), (by decide), step304_2345_2372,
      (by decide), (by decide), step304_2373_2445,
      (by decide), (by decide), step304_2446_2499, rfl⟩⟩

theorem step304_verified : Checked step304 :=
  ⟨step304_nodes, Research6966.HelperWindowCatalogue.moment4884_1057,
    (by decide), (by decide), (by decide), step304_cover⟩

end Research6966.HelperRescueCatalogue
