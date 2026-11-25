import ProximityPrize.SubmissionLower.R6960RescueSourceLargest
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt5
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments10
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step62 : Request :=
  ⟨⟨⟨3000, 4187, 906, 81311⟩, 812266433019904, 8433369009268⟩, 31, 2, 16, 300794⟩

theorem step62_nodes : P1_7_1.nodeRows step62.bank.shape = step62.bank.nodeRows :=
  node_check step62.bank (by decide) (by decide) (by decide)

private theorem step62_2330_2332 : Positive step62 2330 2332 := by decide +kernel

private theorem step62_2333_2340 : Positive step62 2333 2340 := by decide +kernel

private theorem step62_2341_2360 : Positive step62 2341 2360 := by decide +kernel

private theorem step62_2361_2413 : Positive step62 2361 2413 := by decide +kernel

private theorem step62_2414_2499 : Positive step62 2414 2499 := by decide +kernel

theorem step62_cover : ∃ ends, Cover step62 firstHeight ends := by
  exact ⟨[2332, 2340, 2360, 2413, 2499],
    ⟨(by decide), (by decide), step62_2330_2332,
      (by decide), (by decide), step62_2333_2340,
      (by decide), (by decide), step62_2341_2360,
      (by decide), (by decide), step62_2361_2413,
      (by decide), (by decide), step62_2414_2499, rfl⟩⟩

theorem step62_verified : Checked step62 :=
  ⟨step62_nodes, Research6966.HelperWindowCatalogue.moment4187_906,
    (by decide), (by decide), (by decide), step62_cover⟩

def step63 : Request :=
  ⟨⟨⟨3500, 4886, 1057, 81311⟩, 1289556817346560, 15631374615265⟩, 32, 2, 16, 300794⟩

theorem step63_nodes : P1_7_1.nodeRows step63.bank.shape = step63.bank.nodeRows :=
  node_check step63.bank (by decide) (by decide) (by decide)

private theorem step63_2330_2338 : Positive step63 2330 2338 := by decide +kernel

private theorem step63_2339_2361 : Positive step63 2339 2361 := by decide +kernel

private theorem step63_2362_2421 : Positive step63 2362 2421 := by decide +kernel

private theorem step63_2422_2499 : Positive step63 2422 2499 := by decide +kernel

theorem step63_cover : ∃ ends, Cover step63 firstHeight ends := by
  exact ⟨[2338, 2361, 2421, 2499],
    ⟨(by decide), (by decide), step63_2330_2338,
      (by decide), (by decide), step63_2339_2361,
      (by decide), (by decide), step63_2362_2421,
      (by decide), (by decide), step63_2422_2499, rfl⟩⟩

theorem step63_verified : Checked step63 :=
  ⟨step63_nodes, Research6966.HelperWindowCatalogue.moment4886_1057,
    (by decide), (by decide), (by decide), step63_cover⟩

def step64 : Request :=
  ⟨⟨⟨4281, 5949, 1297, 102908⟩, 2364944629104640, 34550690014738⟩, 44, 2, 16, 300794⟩

theorem step64_nodes : P1_7_1.nodeRows step64.bank.shape = step64.bank.nodeRows :=
  node_check step64.bank (by decide) (by decide) (by decide)

private theorem step64_2330_2333 : Positive step64 2330 2333 := by decide +kernel

private theorem step64_2334_2343 : Positive step64 2334 2343 := by decide +kernel

private theorem step64_2344_2369 : Positive step64 2344 2369 := by decide +kernel

private theorem step64_2370_2436 : Positive step64 2370 2436 := by decide +kernel

private theorem step64_2437_2499 : Positive step64 2437 2499 := by decide +kernel

theorem step64_cover : ∃ ends, Cover step64 firstHeight ends := by
  exact ⟨[2333, 2343, 2369, 2436, 2499],
    ⟨(by decide), (by decide), step64_2330_2333,
      (by decide), (by decide), step64_2334_2343,
      (by decide), (by decide), step64_2344_2369,
      (by decide), (by decide), step64_2370_2436,
      (by decide), (by decide), step64_2437_2499, rfl⟩⟩

theorem step64_verified : Checked step64 :=
  ⟨step64_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_5949_1297),
    (by decide), (by decide), (by decide), step64_cover⟩

def step65 : Request :=
  ⟨⟨⟨6623, 9203, 2007, 164837⟩, 8754949968101376, 197823002949183⟩, 73, 2, 16, 300794⟩

theorem step65_nodes : P1_7_1.nodeRows step65.bank.shape = step65.bank.nodeRows :=
  node_check step65.bank (by decide) (by decide) (by decide)

private theorem step65_2330_2339 : Positive step65 2330 2339 := by decide +kernel

private theorem step65_2340_2365 : Positive step65 2340 2365 := by decide +kernel

private theorem step65_2366_2431 : Positive step65 2366 2431 := by decide +kernel

private theorem step65_2432_2499 : Positive step65 2432 2499 := by decide +kernel

theorem step65_cover : ∃ ends, Cover step65 firstHeight ends := by
  exact ⟨[2339, 2365, 2431, 2499],
    ⟨(by decide), (by decide), step65_2330_2339,
      (by decide), (by decide), step65_2340_2365,
      (by decide), (by decide), step65_2366_2431,
      (by decide), (by decide), step65_2432_2499, rfl⟩⟩

theorem step65_verified : Checked step65 :=
  ⟨step65_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_9203_2007),
    (by decide), (by decide), (by decide), step65_cover⟩

def step66 : Request :=
  ⟨⟨⟨6624, 9204, 2007, 164837⟩, 8757908515848192, 197892215121891⟩, 76, 2, 16, 300794⟩

theorem step66_nodes : P1_7_1.nodeRows step66.bank.shape = step66.bank.nodeRows :=
  node_check step66.bank (by decide) (by decide) (by decide)

private theorem step66_2330_2332 : Positive step66 2330 2332 := by decide +kernel

private theorem step66_2333_2339 : Positive step66 2333 2339 := by decide +kernel

private theorem step66_2340_2357 : Positive step66 2340 2357 := by decide +kernel

private theorem step66_2358_2404 : Positive step66 2358 2404 := by decide +kernel

private theorem step66_2405_2499 : Positive step66 2405 2499 := by decide +kernel

theorem step66_cover : ∃ ends, Cover step66 firstHeight ends := by
  exact ⟨[2332, 2339, 2357, 2404, 2499],
    ⟨(by decide), (by decide), step66_2330_2332,
      (by decide), (by decide), step66_2333_2339,
      (by decide), (by decide), step66_2340_2357,
      (by decide), (by decide), step66_2358_2404,
      (by decide), (by decide), step66_2405_2499, rfl⟩⟩

theorem step66_verified : Checked step66 :=
  ⟨step66_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_9204_2007),
    (by decide), (by decide), (by decide), step66_cover⟩

def step67 : Request :=
  ⟨⟨⟨9071, 12604, 2749, 208621⟩, 22490098892800000, 695862530200649⟩, 103, 2, 16, 300794⟩

theorem step67_nodes : P1_7_1.nodeRows step67.bank.shape = step67.bank.nodeRows :=
  node_check step67.bank (by decide) (by decide) (by decide)

private theorem step67_2330_2330 : Positive step67 2330 2330 := by decide +kernel

private theorem step67_2331_2332 : Positive step67 2331 2332 := by decide +kernel

private theorem step67_2333_2337 : Positive step67 2333 2337 := by decide +kernel

private theorem step67_2338_2350 : Positive step67 2338 2350 := by decide +kernel

private theorem step67_2351_2383 : Positive step67 2351 2383 := by decide +kernel

private theorem step67_2384_2468 : Positive step67 2384 2468 := by decide +kernel

private theorem step67_2469_2499 : Positive step67 2469 2499 := by decide +kernel

theorem step67_cover : ∃ ends, Cover step67 firstHeight ends := by
  exact ⟨[2330, 2332, 2337, 2350, 2383, 2468, 2499],
    ⟨(by decide), (by decide), step67_2330_2330,
      (by decide), (by decide), step67_2331_2332,
      (by decide), (by decide), step67_2333_2337,
      (by decide), (by decide), step67_2338_2350,
      (by decide), (by decide), step67_2351_2383,
      (by decide), (by decide), step67_2384_2468,
      (by decide), (by decide), step67_2469_2499, rfl⟩⟩

theorem step67_verified : Checked step67 :=
  ⟨step67_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_12604_2749),
    (by decide), (by decide), (by decide), step67_cover⟩

def step68 : Request :=
  ⟨⟨⟨630, 879, 190, 6858⟩, 7559493713920, 16491913877⟩, 0, 2, 26, 289021⟩

theorem step68_nodes : P1_7_1.nodeRows step68.bank.shape = step68.bank.nodeRows :=
  node_check step68.bank (by decide) (by decide) (by decide)

private theorem step68_2330_2330 : Positive step68 2330 2330 := by decide +kernel

private theorem step68_2331_2333 : Positive step68 2331 2333 := by decide +kernel

private theorem step68_2334_2341 : Positive step68 2334 2341 := by decide +kernel

private theorem step68_2342_2364 : Positive step68 2342 2364 := by decide +kernel

private theorem step68_2365_2430 : Positive step68 2365 2430 := by decide +kernel

private theorem step68_2431_2499 : Positive step68 2431 2499 := by decide +kernel

theorem step68_cover : ∃ ends, Cover step68 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2364, 2430, 2499],
    ⟨(by decide), (by decide), step68_2330_2330,
      (by decide), (by decide), step68_2331_2333,
      (by decide), (by decide), step68_2334_2341,
      (by decide), (by decide), step68_2342_2364,
      (by decide), (by decide), step68_2365_2430,
      (by decide), (by decide), step68_2431_2499, rfl⟩⟩

theorem step68_verified : Checked step68 :=
  ⟨step68_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step68_cover⟩

def step69 : Request :=
  ⟨⟨⟨630, 879, 195, 7715⟩, 7709474160640, 16827402390⟩, 1, 2, 26, 289021⟩

theorem step69_nodes : P1_7_1.nodeRows step69.bank.shape = step69.bank.nodeRows :=
  node_check step69.bank (by decide) (by decide) (by decide)

private theorem step69_2330_2336 : Positive step69 2330 2336 := by decide +kernel

private theorem step69_2337_2356 : Positive step69 2337 2356 := by decide +kernel

private theorem step69_2357_2413 : Positive step69 2357 2413 := by decide +kernel

private theorem step69_2414_2499 : Positive step69 2414 2499 := by decide +kernel

theorem step69_cover : ∃ ends, Cover step69 firstHeight ends := by
  exact ⟨[2336, 2356, 2413, 2499],
    ⟨(by decide), (by decide), step69_2330_2336,
      (by decide), (by decide), step69_2337_2356,
      (by decide), (by decide), step69_2357_2413,
      (by decide), (by decide), step69_2414_2499, rfl⟩⟩

theorem step69_verified : Checked step69 :=
  ⟨step69_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step69_cover⟩

def step70 : Request :=
  ⟨⟨⟨750, 1047, 226, 8679⟩, 12730741817344, 33110613849⟩, 2, 2, 26, 289021⟩

theorem step70_nodes : P1_7_1.nodeRows step70.bank.shape = step70.bank.nodeRows :=
  node_check step70.bank (by decide) (by decide) (by decide)

private theorem step70_2330_2339 : Positive step70 2330 2339 := by decide +kernel

private theorem step70_2340_2368 : Positive step70 2340 2368 := by decide +kernel

private theorem step70_2369_2450 : Positive step70 2369 2450 := by decide +kernel

private theorem step70_2451_2499 : Positive step70 2451 2499 := by decide +kernel

theorem step70_cover : ∃ ends, Cover step70 firstHeight ends := by
  exact ⟨[2339, 2368, 2450, 2499],
    ⟨(by decide), (by decide), step70_2330_2339,
      (by decide), (by decide), step70_2340_2368,
      (by decide), (by decide), step70_2369_2450,
      (by decide), (by decide), step70_2451_2499, rfl⟩⟩

theorem step70_verified : Checked step70 :=
  ⟨step70_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step70_cover⟩

def step71 : Request :=
  ⟨⟨⟨750, 1047, 232, 8679⟩, 12985818152960, 33790833671⟩, 3, 2, 26, 289021⟩

theorem step71_nodes : P1_7_1.nodeRows step71.bank.shape = step71.bank.nodeRows :=
  node_check step71.bank (by decide) (by decide) (by decide)

private theorem step71_2330_2330 : Positive step71 2330 2330 := by decide +kernel

private theorem step71_2331_2333 : Positive step71 2331 2333 := by decide +kernel

private theorem step71_2334_2341 : Positive step71 2334 2341 := by decide +kernel

private theorem step71_2342_2363 : Positive step71 2342 2363 := by decide +kernel

private theorem step71_2364_2425 : Positive step71 2364 2425 := by decide +kernel

private theorem step71_2426_2499 : Positive step71 2426 2499 := by decide +kernel

theorem step71_cover : ∃ ends, Cover step71 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2425, 2499],
    ⟨(by decide), (by decide), step71_2330_2330,
      (by decide), (by decide), step71_2331_2333,
      (by decide), (by decide), step71_2334_2341,
      (by decide), (by decide), step71_2342_2363,
      (by decide), (by decide), step71_2364_2425,
      (by decide), (by decide), step71_2426_2499, rfl⟩⟩

theorem step71_verified : Checked step71 :=
  ⟨step71_nodes, Research6966.HelperWindowCatalogue.moment1047_232,
    (by decide), (by decide), (by decide), step71_cover⟩

def step72 : Request :=
  ⟨⟨⟨900, 1256, 272, 9763⟩, 22024701870080, 68653176066⟩, 4, 2, 26, 289021⟩

theorem step72_nodes : P1_7_1.nodeRows step72.bank.shape = step72.bank.nodeRows :=
  node_check step72.bank (by decide) (by decide) (by decide)

private theorem step72_2330_2338 : Positive step72 2330 2338 := by decide +kernel

private theorem step72_2339_2363 : Positive step72 2339 2363 := by decide +kernel

private theorem step72_2364_2432 : Positive step72 2364 2432 := by decide +kernel

private theorem step72_2433_2499 : Positive step72 2433 2499 := by decide +kernel

theorem step72_cover : ∃ ends, Cover step72 firstHeight ends := by
  exact ⟨[2338, 2363, 2432, 2499],
    ⟨(by decide), (by decide), step72_2330_2338,
      (by decide), (by decide), step72_2339_2363,
      (by decide), (by decide), step72_2364_2432,
      (by decide), (by decide), step72_2433_2499, rfl⟩⟩

theorem step72_verified : Checked step72 :=
  ⟨step72_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step72_cover⟩

def step73 : Request :=
  ⟨⟨⟨900, 1256, 279, 9763⟩, 22452680785920, 70021105933⟩, 5, 2, 26, 289021⟩

theorem step73_nodes : P1_7_1.nodeRows step73.bank.shape = step73.bank.nodeRows :=
  node_check step73.bank (by decide) (by decide) (by decide)

private theorem step73_2330_2332 : Positive step73 2330 2332 := by decide +kernel

private theorem step73_2333_2340 : Positive step73 2333 2340 := by decide +kernel

private theorem step73_2341_2362 : Positive step73 2341 2362 := by decide +kernel

private theorem step73_2363_2422 : Positive step73 2363 2422 := by decide +kernel

private theorem step73_2423_2499 : Positive step73 2423 2499 := by decide +kernel

theorem step73_cover : ∃ ends, Cover step73 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2422, 2499],
    ⟨(by decide), (by decide), step73_2330_2332,
      (by decide), (by decide), step73_2333_2340,
      (by decide), (by decide), step73_2341_2362,
      (by decide), (by decide), step73_2363_2422,
      (by decide), (by decide), step73_2423_2499, rfl⟩⟩

theorem step73_verified : Checked step73 :=
  ⟨step73_nodes, Research6966.HelperWindowCatalogue.moment1256_279,
    (by decide), (by decide), (by decide), step73_cover⟩

end Research6966.HelperRescueCatalogue
