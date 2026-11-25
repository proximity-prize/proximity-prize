import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
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

def step135 : Request :=
  ⟨⟨⟨1100, 1535, 332, 45124⟩, 40133103452160, 152819743367⟩, 7, 3, 1, 385715⟩

theorem step135_nodes : P1_7_1.nodeRows step135.bank.shape = step135.bank.nodeRows :=
  node_check step135.bank (by decide) (by decide) (by decide)

private theorem step135_2330_2335 : Positive step135 2330 2335 := by decide +kernel

private theorem step135_2336_2351 : Positive step135 2336 2351 := by decide +kernel

private theorem step135_2352_2395 : Positive step135 2352 2395 := by decide +kernel

private theorem step135_2396_2499 : Positive step135 2396 2499 := by decide +kernel

theorem step135_cover : ∃ ends, Cover step135 firstHeight ends := by
  exact ⟨[2335, 2351, 2395, 2499],
    ⟨(by decide), (by decide), step135_2330_2335,
      (by decide), (by decide), step135_2336_2351,
      (by decide), (by decide), step135_2352_2395,
      (by decide), (by decide), step135_2396_2499, rfl⟩⟩

theorem step135_verified : Checked step135 :=
  ⟨step135_nodes, Research6966.HelperWindowCatalogue.moment1535_332,
    (by decide), (by decide), (by decide), step135_cover⟩

def step136 : Request :=
  ⟨⟨⟨1100, 1535, 332, 57109⟩, 40133103452160, 152819743367⟩, 10, 3, 1, 385715⟩

theorem step136_nodes : P1_7_1.nodeRows step136.bank.shape = step136.bank.nodeRows :=
  node_check step136.bank (by decide) (by decide) (by decide)

private theorem step136_2330_2335 : Positive step136 2330 2335 := by decide +kernel

private theorem step136_2336_2351 : Positive step136 2336 2351 := by decide +kernel

private theorem step136_2352_2395 : Positive step136 2352 2395 := by decide +kernel

private theorem step136_2396_2499 : Positive step136 2396 2499 := by decide +kernel

theorem step136_cover : ∃ ends, Cover step136 firstHeight ends := by
  exact ⟨[2335, 2351, 2395, 2499],
    ⟨(by decide), (by decide), step136_2330_2335,
      (by decide), (by decide), step136_2336_2351,
      (by decide), (by decide), step136_2352_2395,
      (by decide), (by decide), step136_2396_2499, rfl⟩⟩

theorem step136_verified : Checked step136 :=
  ⟨step136_nodes, Research6966.HelperWindowCatalogue.moment1535_332,
    (by decide), (by decide), (by decide), step136_cover⟩

def step137 : Request :=
  ⟨⟨⟨1650, 2303, 488, 72277⟩, 133179773812736, 760643620838⟩, 16, 3, 1, 385715⟩

theorem step137_nodes : P1_7_1.nodeRows step137.bank.shape = step137.bank.nodeRows :=
  node_check step137.bank (by decide) (by decide) (by decide)

private theorem step137_2330_2337 : Positive step137 2330 2337 := by decide +kernel

private theorem step137_2338_2359 : Positive step137 2338 2359 := by decide +kernel

private theorem step137_2360_2419 : Positive step137 2360 2419 := by decide +kernel

private theorem step137_2420_2499 : Positive step137 2420 2499 := by decide +kernel

theorem step137_cover : ∃ ends, Cover step137 firstHeight ends := by
  exact ⟨[2337, 2359, 2419, 2499],
    ⟨(by decide), (by decide), step137_2330_2337,
      (by decide), (by decide), step137_2338_2359,
      (by decide), (by decide), step137_2360_2419,
      (by decide), (by decide), step137_2420_2499, rfl⟩⟩

theorem step137_verified : Checked step137 :=
  ⟨step137_nodes, Research6966.HelperWindowCatalogue.moment2303_488,
    (by decide), (by decide), (by decide), step137_cover⟩

def step138 : Request :=
  ⟨⟨⟨2000, 2791, 592, 81311⟩, 237206388080640, 1640986809111⟩, 20, 3, 1, 385715⟩

theorem step138_nodes : P1_7_1.nodeRows step138.bank.shape = step138.bank.nodeRows :=
  node_check step138.bank (by decide) (by decide) (by decide)

private theorem step138_2330_2335 : Positive step138 2330 2335 := by decide +kernel

private theorem step138_2336_2352 : Positive step138 2336 2352 := by decide +kernel

private theorem step138_2353_2397 : Positive step138 2353 2397 := by decide +kernel

private theorem step138_2398_2499 : Positive step138 2398 2499 := by decide +kernel

theorem step138_cover : ∃ ends, Cover step138 firstHeight ends := by
  exact ⟨[2335, 2352, 2397, 2499],
    ⟨(by decide), (by decide), step138_2330_2335,
      (by decide), (by decide), step138_2336_2352,
      (by decide), (by decide), step138_2353_2397,
      (by decide), (by decide), step138_2398_2499, rfl⟩⟩

theorem step138_verified : Checked step138 :=
  ⟨step138_nodes, Research6966.HelperWindowCatalogue.moment2791_592,
    (by decide), (by decide), (by decide), step138_cover⟩

def step139 : Request :=
  ⟨⟨⟨2500, 3489, 740, 115771⟩, 463070780456960, 4004797990029⟩, 31, 3, 1, 385715⟩

theorem step139_nodes : P1_7_1.nodeRows step139.bank.shape = step139.bank.nodeRows :=
  node_check step139.bank (by decide) (by decide) (by decide)

private theorem step139_2330_2339 : Positive step139 2330 2339 := by decide +kernel

private theorem step139_2340_2366 : Positive step139 2340 2366 := by decide +kernel

private theorem step139_2367_2438 : Positive step139 2367 2438 := by decide +kernel

private theorem step139_2439_2499 : Positive step139 2439 2499 := by decide +kernel

theorem step139_cover : ∃ ends, Cover step139 firstHeight ends := by
  exact ⟨[2339, 2366, 2438, 2499],
    ⟨(by decide), (by decide), step139_2330_2339,
      (by decide), (by decide), step139_2340_2366,
      (by decide), (by decide), step139_2367_2438,
      (by decide), (by decide), step139_2439_2499, rfl⟩⟩

theorem step139_verified : Checked step139 :=
  ⟨step139_nodes, Research6966.HelperWindowCatalogue.moment3489_740,
    (by decide), (by decide), (by decide), step139_cover⟩

def step140 : Request :=
  ⟨⟨⟨2500, 3489, 740, 115771⟩, 463070780456960, 4004797990029⟩, 32, 3, 1, 385715⟩

theorem step140_nodes : P1_7_1.nodeRows step140.bank.shape = step140.bank.nodeRows :=
  node_check step140.bank (by decide) (by decide) (by decide)

private theorem step140_2330_2333 : Positive step140 2330 2333 := by decide +kernel

private theorem step140_2334_2343 : Positive step140 2334 2343 := by decide +kernel

private theorem step140_2344_2370 : Positive step140 2344 2370 := by decide +kernel

private theorem step140_2371_2442 : Positive step140 2371 2442 := by decide +kernel

private theorem step140_2443_2499 : Positive step140 2443 2499 := by decide +kernel

theorem step140_cover : ∃ ends, Cover step140 firstHeight ends := by
  exact ⟨[2333, 2343, 2370, 2442, 2499],
    ⟨(by decide), (by decide), step140_2330_2333,
      (by decide), (by decide), step140_2334_2343,
      (by decide), (by decide), step140_2344_2370,
      (by decide), (by decide), step140_2371_2442,
      (by decide), (by decide), step140_2443_2499, rfl⟩⟩

theorem step140_verified : Checked step140 :=
  ⟨step140_nodes, Research6966.HelperWindowCatalogue.moment3489_740,
    (by decide), (by decide), (by decide), step140_cover⟩

def step141 : Request :=
  ⟨⟨⟨3000, 4187, 906, 146522⟩, 812266433019904, 8433369009268⟩, 44, 3, 1, 385715⟩

theorem step141_nodes : P1_7_1.nodeRows step141.bank.shape = step141.bank.nodeRows :=
  node_check step141.bank (by decide) (by decide) (by decide)

private theorem step141_2330_2331 : Positive step141 2330 2331 := by decide +kernel

private theorem step141_2332_2336 : Positive step141 2332 2336 := by decide +kernel

private theorem step141_2337_2349 : Positive step141 2337 2349 := by decide +kernel

private theorem step141_2350_2383 : Positive step141 2350 2383 := by decide +kernel

private theorem step141_2384_2472 : Positive step141 2384 2472 := by decide +kernel

private theorem step141_2473_2499 : Positive step141 2473 2499 := by decide +kernel

theorem step141_cover : ∃ ends, Cover step141 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2472, 2499],
    ⟨(by decide), (by decide), step141_2330_2331,
      (by decide), (by decide), step141_2332_2336,
      (by decide), (by decide), step141_2337_2349,
      (by decide), (by decide), step141_2350_2383,
      (by decide), (by decide), step141_2384_2472,
      (by decide), (by decide), step141_2473_2499, rfl⟩⟩

theorem step141_verified : Checked step141 :=
  ⟨step141_nodes, Research6966.HelperWindowCatalogue.moment4187_906,
    (by decide), (by decide), (by decide), step141_cover⟩

def step142 : Request :=
  ⟨⟨⟨630, 879, 186, 28173⟩, 7438337572864, 16221345781⟩, 0, 3, 2, 385715⟩

theorem step142_nodes : P1_7_1.nodeRows step142.bank.shape = step142.bank.nodeRows :=
  node_check step142.bank (by decide) (by decide) (by decide)

private theorem step142_2330_2342 : Positive step142 2330 2342 := by decide +kernel

private theorem step142_2343_2380 : Positive step142 2343 2380 := by decide +kernel

private theorem step142_2381_2491 : Positive step142 2381 2491 := by decide +kernel

private theorem step142_2492_2499 : Positive step142 2492 2499 := by decide +kernel

theorem step142_cover : ∃ ends, Cover step142 firstHeight ends := by
  exact ⟨[2342, 2380, 2491, 2499],
    ⟨(by decide), (by decide), step142_2330_2342,
      (by decide), (by decide), step142_2343_2380,
      (by decide), (by decide), step142_2381_2491,
      (by decide), (by decide), step142_2492_2499, rfl⟩⟩

theorem step142_verified : Checked step142 :=
  ⟨step142_nodes, Research6966.HelperWindowCatalogue.moment879_186,
    (by decide), (by decide), (by decide), step142_cover⟩

def step143 : Request :=
  ⟨⟨⟨750, 1047, 226, 28173⟩, 12730741817344, 33110613849⟩, 1, 3, 2, 385715⟩

theorem step143_nodes : P1_7_1.nodeRows step143.bank.shape = step143.bank.nodeRows :=
  node_check step143.bank (by decide) (by decide) (by decide)

private theorem step143_2330_2334 : Positive step143 2330 2334 := by decide +kernel

private theorem step143_2335_2348 : Positive step143 2335 2348 := by decide +kernel

private theorem step143_2349_2388 : Positive step143 2349 2388 := by decide +kernel

private theorem step143_2389_2499 : Positive step143 2389 2499 := by decide +kernel

theorem step143_cover : ∃ ends, Cover step143 firstHeight ends := by
  exact ⟨[2334, 2348, 2388, 2499],
    ⟨(by decide), (by decide), step143_2330_2334,
      (by decide), (by decide), step143_2335_2348,
      (by decide), (by decide), step143_2349_2388,
      (by decide), (by decide), step143_2389_2499, rfl⟩⟩

theorem step143_verified : Checked step143 :=
  ⟨step143_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step143_cover⟩

def step144 : Request :=
  ⟨⟨⟨750, 1047, 222, 31694⟩, 12559140782080, 32653699308⟩, 2, 3, 2, 385715⟩

theorem step144_nodes : P1_7_1.nodeRows step144.bank.shape = step144.bank.nodeRows :=
  node_check step144.bank (by decide) (by decide) (by decide)

private theorem step144_2330_2331 : Positive step144 2330 2331 := by decide +kernel

private theorem step144_2332_2336 : Positive step144 2332 2336 := by decide +kernel

private theorem step144_2337_2350 : Positive step144 2337 2350 := by decide +kernel

private theorem step144_2351_2390 : Positive step144 2351 2390 := by decide +kernel

private theorem step144_2391_2499 : Positive step144 2391 2499 := by decide +kernel

theorem step144_cover : ∃ ends, Cover step144 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2390, 2499],
    ⟨(by decide), (by decide), step144_2330_2331,
      (by decide), (by decide), step144_2332_2336,
      (by decide), (by decide), step144_2337_2350,
      (by decide), (by decide), step144_2351_2390,
      (by decide), (by decide), step144_2391_2499, rfl⟩⟩

theorem step144_verified : Checked step144 :=
  ⟨step144_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_1047_222),
    (by decide), (by decide), (by decide), step144_cover⟩

def step145 : Request :=
  ⟨⟨⟨750, 1047, 222, 35655⟩, 12559140782080, 32653699308⟩, 3, 3, 2, 385715⟩

theorem step145_nodes : P1_7_1.nodeRows step145.bank.shape = step145.bank.nodeRows :=
  node_check step145.bank (by decide) (by decide) (by decide)

private theorem step145_2330_2331 : Positive step145 2330 2331 := by decide +kernel

private theorem step145_2332_2337 : Positive step145 2332 2337 := by decide +kernel

private theorem step145_2338_2354 : Positive step145 2338 2354 := by decide +kernel

private theorem step145_2355_2402 : Positive step145 2355 2402 := by decide +kernel

private theorem step145_2403_2499 : Positive step145 2403 2499 := by decide +kernel

theorem step145_cover : ∃ ends, Cover step145 firstHeight ends := by
  exact ⟨[2331, 2337, 2354, 2402, 2499],
    ⟨(by decide), (by decide), step145_2330_2331,
      (by decide), (by decide), step145_2332_2337,
      (by decide), (by decide), step145_2338_2354,
      (by decide), (by decide), step145_2355_2402,
      (by decide), (by decide), step145_2403_2499, rfl⟩⟩

theorem step145_verified : Checked step145 :=
  ⟨step145_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_1047_222),
    (by decide), (by decide), (by decide), step145_cover⟩

def step146 : Request :=
  ⟨⟨⟨900, 1256, 272, 35655⟩, 22024701870080, 68653176066⟩, 4, 3, 2, 385715⟩

theorem step146_nodes : P1_7_1.nodeRows step146.bank.shape = step146.bank.nodeRows :=
  node_check step146.bank (by decide) (by decide) (by decide)

private theorem step146_2330_2333 : Positive step146 2330 2333 := by decide +kernel

private theorem step146_2334_2344 : Positive step146 2334 2344 := by decide +kernel

private theorem step146_2345_2374 : Positive step146 2345 2374 := by decide +kernel

private theorem step146_2375_2457 : Positive step146 2375 2457 := by decide +kernel

private theorem step146_2458_2499 : Positive step146 2458 2499 := by decide +kernel

theorem step146_cover : ∃ ends, Cover step146 firstHeight ends := by
  exact ⟨[2333, 2344, 2374, 2457, 2499],
    ⟨(by decide), (by decide), step146_2330_2333,
      (by decide), (by decide), step146_2334_2344,
      (by decide), (by decide), step146_2345_2374,
      (by decide), (by decide), step146_2375_2457,
      (by decide), (by decide), step146_2458_2499, rfl⟩⟩

theorem step146_verified : Checked step146 :=
  ⟨step146_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step146_cover⟩

def step147 : Request :=
  ⟨⟨⟨900, 1256, 266, 40111⟩, 21654240231424, 67471047297⟩, 5, 3, 2, 385715⟩

theorem step147_nodes : P1_7_1.nodeRows step147.bank.shape = step147.bank.nodeRows :=
  node_check step147.bank (by decide) (by decide) (by decide)

private theorem step147_2330_2330 : Positive step147 2330 2330 := by decide +kernel

private theorem step147_2331_2333 : Positive step147 2331 2333 := by decide +kernel

private theorem step147_2334_2342 : Positive step147 2334 2342 := by decide +kernel

private theorem step147_2343_2367 : Positive step147 2343 2367 := by decide +kernel

private theorem step147_2368_2437 : Positive step147 2368 2437 := by decide +kernel

private theorem step147_2438_2499 : Positive step147 2438 2499 := by decide +kernel

theorem step147_cover : ∃ ends, Cover step147 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2367, 2437, 2499],
    ⟨(by decide), (by decide), step147_2330_2330,
      (by decide), (by decide), step147_2331_2333,
      (by decide), (by decide), step147_2334_2342,
      (by decide), (by decide), step147_2343_2367,
      (by decide), (by decide), step147_2368_2437,
      (by decide), (by decide), step147_2438_2499, rfl⟩⟩

theorem step147_verified : Checked step147 :=
  ⟨step147_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step147_cover⟩

def step148 : Request :=
  ⟨⟨⟨1100, 1535, 326, 45124⟩, 39579969388544, 150663514795⟩, 7, 3, 2, 385715⟩

theorem step148_nodes : P1_7_1.nodeRows step148.bank.shape = step148.bank.nodeRows :=
  node_check step148.bank (by decide) (by decide) (by decide)

private theorem step148_2330_2337 : Positive step148 2330 2337 := by decide +kernel

private theorem step148_2338_2359 : Positive step148 2338 2359 := by decide +kernel

private theorem step148_2360_2420 : Positive step148 2360 2420 := by decide +kernel

private theorem step148_2421_2499 : Positive step148 2421 2499 := by decide +kernel

theorem step148_cover : ∃ ends, Cover step148 firstHeight ends := by
  exact ⟨[2337, 2359, 2420, 2499],
    ⟨(by decide), (by decide), step148_2330_2337,
      (by decide), (by decide), step148_2338_2359,
      (by decide), (by decide), step148_2360_2420,
      (by decide), (by decide), step148_2421_2499, rfl⟩⟩

theorem step148_verified : Checked step148 :=
  ⟨step148_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step148_cover⟩

def step149 : Request :=
  ⟨⟨⟨1350, 1884, 408, 50764⟩, 74202776600576, 346781832878⟩, 10, 3, 2, 385715⟩

theorem step149_nodes : P1_7_1.nodeRows step149.bank.shape = step149.bank.nodeRows :=
  node_check step149.bank (by decide) (by decide) (by decide)

private theorem step149_2330_2336 : Positive step149 2330 2336 := by decide +kernel

private theorem step149_2337_2355 : Positive step149 2337 2355 := by decide +kernel

private theorem step149_2356_2406 : Positive step149 2356 2406 := by decide +kernel

private theorem step149_2407_2499 : Positive step149 2407 2499 := by decide +kernel

theorem step149_cover : ∃ ends, Cover step149 firstHeight ends := by
  exact ⟨[2336, 2355, 2406, 2499],
    ⟨(by decide), (by decide), step149_2330_2336,
      (by decide), (by decide), step149_2337_2355,
      (by decide), (by decide), step149_2356_2406,
      (by decide), (by decide), step149_2407_2499, rfl⟩⟩

theorem step149_verified : Checked step149 :=
  ⟨step149_nodes, Research6966.HelperWindowCatalogue.moment1884_408,
    (by decide), (by decide), (by decide), step149_cover⟩

def step150 : Request :=
  ⟨⟨⟨1927, 2678, 584, 64247⟩, 216034207334400, 1421525065183⟩, 16, 3, 2, 385715⟩

theorem step150_nodes : P1_7_1.nodeRows step150.bank.shape = step150.bank.nodeRows :=
  node_check step150.bank (by decide) (by decide) (by decide)

private theorem step150_2330_2334 : Positive step150 2330 2334 := by decide +kernel

private theorem step150_2335_2347 : Positive step150 2335 2347 := by decide +kernel

private theorem step150_2348_2382 : Positive step150 2348 2382 := by decide +kernel

private theorem step150_2383_2475 : Positive step150 2383 2475 := by decide +kernel

private theorem step150_2476_2499 : Positive step150 2476 2499 := by decide +kernel

theorem step150_cover : ∃ ends, Cover step150 firstHeight ends := by
  exact ⟨[2334, 2347, 2382, 2475, 2499],
    ⟨(by decide), (by decide), step150_2330_2334,
      (by decide), (by decide), step150_2335_2347,
      (by decide), (by decide), step150_2348_2382,
      (by decide), (by decide), step150_2383_2475,
      (by decide), (by decide), step150_2476_2499, rfl⟩⟩

theorem step150_verified : Checked step150 :=
  ⟨step150_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_2678_584),
    (by decide), (by decide), (by decide), step150_cover⟩

def step151 : Request :=
  ⟨⟨⟨1650, 2303, 498, 81311⟩, 135254251667456, 772776530256⟩, 20, 3, 2, 385715⟩

theorem step151_nodes : P1_7_1.nodeRows step151.bank.shape = step151.bank.nodeRows :=
  node_check step151.bank (by decide) (by decide) (by decide)

private theorem step151_2330_2335 : Positive step151 2330 2335 := by decide +kernel

private theorem step151_2336_2351 : Positive step151 2336 2351 := by decide +kernel

private theorem step151_2352_2393 : Positive step151 2352 2393 := by decide +kernel

private theorem step151_2394_2499 : Positive step151 2394 2499 := by decide +kernel

theorem step151_cover : ∃ ends, Cover step151 firstHeight ends := by
  exact ⟨[2335, 2351, 2393, 2499],
    ⟨(by decide), (by decide), step151_2330_2335,
      (by decide), (by decide), step151_2336_2351,
      (by decide), (by decide), step151_2352_2393,
      (by decide), (by decide), step151_2394_2499, rfl⟩⟩

theorem step151_verified : Checked step151 :=
  ⟨step151_nodes, Research6966.HelperWindowCatalogue.moment2303_498,
    (by decide), (by decide), (by decide), step151_cover⟩

def step152 : Request :=
  ⟨⟨⟨2500, 3489, 755, 102908⟩, 470210689105920, 4068029992867⟩, 31, 3, 2, 385715⟩

theorem step152_nodes : P1_7_1.nodeRows step152.bank.shape = step152.bank.nodeRows :=
  node_check step152.bank (by decide) (by decide) (by decide)

private theorem step152_2330_2332 : Positive step152 2330 2332 := by decide +kernel

private theorem step152_2333_2340 : Positive step152 2333 2340 := by decide +kernel

private theorem step152_2341_2361 : Positive step152 2341 2361 := by decide +kernel

private theorem step152_2362_2416 : Positive step152 2362 2416 := by decide +kernel

private theorem step152_2417_2499 : Positive step152 2417 2499 := by decide +kernel

theorem step152_cover : ∃ ends, Cover step152 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2416, 2499],
    ⟨(by decide), (by decide), step152_2330_2332,
      (by decide), (by decide), step152_2333_2340,
      (by decide), (by decide), step152_2341_2361,
      (by decide), (by decide), step152_2362_2416,
      (by decide), (by decide), step152_2417_2499, rfl⟩⟩

theorem step152_verified : Checked step152 :=
  ⟨step152_nodes, Research6966.HelperWindowCatalogue.moment3489_755,
    (by decide), (by decide), (by decide), step152_cover⟩

def step153 : Request :=
  ⟨⟨⟨3000, 4187, 906, 102908⟩, 812266433019904, 8433369009268⟩, 32, 3, 2, 385715⟩

theorem step153_nodes : P1_7_1.nodeRows step153.bank.shape = step153.bank.nodeRows :=
  node_check step153.bank (by decide) (by decide) (by decide)

private theorem step153_2330_2331 : Positive step153 2330 2331 := by decide +kernel

private theorem step153_2332_2336 : Positive step153 2332 2336 := by decide +kernel

private theorem step153_2337_2349 : Positive step153 2337 2349 := by decide +kernel

private theorem step153_2350_2383 : Positive step153 2350 2383 := by decide +kernel

private theorem step153_2384_2472 : Positive step153 2384 2472 := by decide +kernel

private theorem step153_2473_2499 : Positive step153 2473 2499 := by decide +kernel

theorem step153_cover : ∃ ends, Cover step153 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2472, 2499],
    ⟨(by decide), (by decide), step153_2330_2331,
      (by decide), (by decide), step153_2332_2336,
      (by decide), (by decide), step153_2337_2349,
      (by decide), (by decide), step153_2350_2383,
      (by decide), (by decide), step153_2384_2472,
      (by decide), (by decide), step153_2473_2499, rfl⟩⟩

theorem step153_verified : Checked step153 :=
  ⟨step153_nodes, Research6966.HelperWindowCatalogue.moment4187_906,
    (by decide), (by decide), (by decide), step153_cover⟩

def step154 : Request :=
  ⟨⟨⟨3000, 4187, 888, 146522⟩, 799929517735936, 8302251431404⟩, 44, 3, 2, 385715⟩

theorem step154_nodes : P1_7_1.nodeRows step154.bank.shape = step154.bank.nodeRows :=
  node_check step154.bank (by decide) (by decide) (by decide)

private theorem step154_2330_2330 : Positive step154 2330 2330 := by decide +kernel

private theorem step154_2331_2333 : Positive step154 2331 2333 := by decide +kernel

private theorem step154_2334_2341 : Positive step154 2334 2341 := by decide +kernel

private theorem step154_2342_2362 : Positive step154 2342 2362 := by decide +kernel

private theorem step154_2363_2417 : Positive step154 2363 2417 := by decide +kernel

private theorem step154_2418_2499 : Positive step154 2418 2499 := by decide +kernel

theorem step154_cover : ∃ ends, Cover step154 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2417, 2499],
    ⟨(by decide), (by decide), step154_2330_2330,
      (by decide), (by decide), step154_2331_2333,
      (by decide), (by decide), step154_2334_2341,
      (by decide), (by decide), step154_2342_2362,
      (by decide), (by decide), step154_2363_2417,
      (by decide), (by decide), step154_2418_2499, rfl⟩⟩

theorem step154_verified : Checked step154 :=
  ⟨step154_nodes, Research6966.HelperWindowCatalogue.moment4187_888,
    (by decide), (by decide), (by decide), step154_cover⟩

def step155 : Request :=
  ⟨⟨⟨630, 879, 186, 25043⟩, 7438337572864, 16221345781⟩, 0, 3, 4, 385715⟩

theorem step155_nodes : P1_7_1.nodeRows step155.bank.shape = step155.bank.nodeRows :=
  node_check step155.bank (by decide) (by decide) (by decide)

private theorem step155_2330_2335 : Positive step155 2330 2335 := by decide +kernel

private theorem step155_2336_2352 : Positive step155 2336 2352 := by decide +kernel

private theorem step155_2353_2402 : Positive step155 2353 2402 := by decide +kernel

private theorem step155_2403_2499 : Positive step155 2403 2499 := by decide +kernel

theorem step155_cover : ∃ ends, Cover step155 firstHeight ends := by
  exact ⟨[2335, 2352, 2402, 2499],
    ⟨(by decide), (by decide), step155_2330_2335,
      (by decide), (by decide), step155_2336_2352,
      (by decide), (by decide), step155_2353_2402,
      (by decide), (by decide), step155_2403_2499, rfl⟩⟩

theorem step155_verified : Checked step155 :=
  ⟨step155_nodes, Research6966.HelperWindowCatalogue.moment879_186,
    (by decide), (by decide), (by decide), step155_cover⟩

def step156 : Request :=
  ⟨⟨⟨630, 879, 186, 28173⟩, 7438337572864, 16221345781⟩, 1, 3, 4, 385715⟩

theorem step156_nodes : P1_7_1.nodeRows step156.bank.shape = step156.bank.nodeRows :=
  node_check step156.bank (by decide) (by decide) (by decide)

private theorem step156_2330_2330 : Positive step156 2330 2330 := by decide +kernel

private theorem step156_2331_2333 : Positive step156 2331 2333 := by decide +kernel

private theorem step156_2334_2342 : Positive step156 2334 2342 := by decide +kernel

private theorem step156_2343_2368 : Positive step156 2343 2368 := by decide +kernel

private theorem step156_2369_2444 : Positive step156 2369 2444 := by decide +kernel

private theorem step156_2445_2499 : Positive step156 2445 2499 := by decide +kernel

theorem step156_cover : ∃ ends, Cover step156 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2368, 2444, 2499],
    ⟨(by decide), (by decide), step156_2330_2330,
      (by decide), (by decide), step156_2331_2333,
      (by decide), (by decide), step156_2334_2342,
      (by decide), (by decide), step156_2343_2368,
      (by decide), (by decide), step156_2369_2444,
      (by decide), (by decide), step156_2445_2499, rfl⟩⟩

theorem step156_verified : Checked step156 :=
  ⟨step156_nodes, Research6966.HelperWindowCatalogue.moment879_186,
    (by decide), (by decide), (by decide), step156_cover⟩

def step157 : Request :=
  ⟨⟨⟨750, 1047, 226, 28173⟩, 12730741817344, 33110613849⟩, 2, 3, 4, 385715⟩

theorem step157_nodes : P1_7_1.nodeRows step157.bank.shape = step157.bank.nodeRows :=
  node_check step157.bank (by decide) (by decide) (by decide)

private theorem step157_2330_2330 : Positive step157 2330 2330 := by decide +kernel

private theorem step157_2331_2333 : Positive step157 2331 2333 := by decide +kernel

private theorem step157_2334_2342 : Positive step157 2334 2342 := by decide +kernel

private theorem step157_2343_2367 : Positive step157 2343 2367 := by decide +kernel

private theorem step157_2368_2437 : Positive step157 2368 2437 := by decide +kernel

private theorem step157_2438_2499 : Positive step157 2438 2499 := by decide +kernel

theorem step157_cover : ∃ ends, Cover step157 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2367, 2437, 2499],
    ⟨(by decide), (by decide), step157_2330_2330,
      (by decide), (by decide), step157_2331_2333,
      (by decide), (by decide), step157_2334_2342,
      (by decide), (by decide), step157_2343_2367,
      (by decide), (by decide), step157_2368_2437,
      (by decide), (by decide), step157_2438_2499, rfl⟩⟩

theorem step157_verified : Checked step157 :=
  ⟨step157_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step157_cover⟩

def step158 : Request :=
  ⟨⟨⟨750, 1047, 226, 31694⟩, 12730741817344, 33110613849⟩, 3, 3, 4, 385715⟩

theorem step158_nodes : P1_7_1.nodeRows step158.bank.shape = step158.bank.nodeRows :=
  node_check step158.bank (by decide) (by decide) (by decide)

private theorem step158_2330_2332 : Positive step158 2330 2332 := by decide +kernel

private theorem step158_2333_2340 : Positive step158 2333 2340 := by decide +kernel

private theorem step158_2341_2362 : Positive step158 2341 2362 := by decide +kernel

private theorem step158_2363_2424 : Positive step158 2363 2424 := by decide +kernel

private theorem step158_2425_2499 : Positive step158 2425 2499 := by decide +kernel

theorem step158_cover : ∃ ends, Cover step158 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2424, 2499],
    ⟨(by decide), (by decide), step158_2330_2332,
      (by decide), (by decide), step158_2333_2340,
      (by decide), (by decide), step158_2341_2362,
      (by decide), (by decide), step158_2363_2424,
      (by decide), (by decide), step158_2425_2499, rfl⟩⟩

theorem step158_verified : Checked step158 :=
  ⟨step158_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step158_cover⟩

def step159 : Request :=
  ⟨⟨⟨998, 1387, 302, 31694⟩, 30044628975616, 102461756220⟩, 4, 3, 4, 385715⟩

theorem step159_nodes : P1_7_1.nodeRows step159.bank.shape = step159.bank.nodeRows :=
  node_check step159.bank (by decide) (by decide) (by decide)

private theorem step159_2330_2331 : Positive step159 2330 2331 := by decide +kernel

private theorem step159_2332_2336 : Positive step159 2332 2336 := by decide +kernel

private theorem step159_2337_2350 : Positive step159 2337 2350 := by decide +kernel

private theorem step159_2351_2389 : Positive step159 2351 2389 := by decide +kernel

private theorem step159_2390_2496 : Positive step159 2390 2496 := by decide +kernel

private theorem step159_2497_2499 : Positive step159 2497 2499 := by decide +kernel

theorem step159_cover : ∃ ends, Cover step159 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2389, 2496, 2499],
    ⟨(by decide), (by decide), step159_2330_2331,
      (by decide), (by decide), step159_2332_2336,
      (by decide), (by decide), step159_2337_2350,
      (by decide), (by decide), step159_2351_2389,
      (by decide), (by decide), step159_2390_2496,
      (by decide), (by decide), step159_2497_2499, rfl⟩⟩

theorem step159_verified : Checked step159 :=
  ⟨step159_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_1387_302),
    (by decide), (by decide), (by decide), step159_cover⟩

def step160 : Request :=
  ⟨⟨⟨900, 1256, 272, 35655⟩, 22024701870080, 68653176066⟩, 5, 3, 4, 385715⟩

theorem step160_nodes : P1_7_1.nodeRows step160.bank.shape = step160.bank.nodeRows :=
  node_check step160.bank (by decide) (by decide) (by decide)

private theorem step160_2330_2332 : Positive step160 2330 2332 := by decide +kernel

private theorem step160_2333_2340 : Positive step160 2333 2340 := by decide +kernel

private theorem step160_2341_2363 : Positive step160 2341 2363 := by decide +kernel

private theorem step160_2364_2426 : Positive step160 2364 2426 := by decide +kernel

private theorem step160_2427_2499 : Positive step160 2427 2499 := by decide +kernel

theorem step160_cover : ∃ ends, Cover step160 firstHeight ends := by
  exact ⟨[2332, 2340, 2363, 2426, 2499],
    ⟨(by decide), (by decide), step160_2330_2332,
      (by decide), (by decide), step160_2333_2340,
      (by decide), (by decide), step160_2341_2363,
      (by decide), (by decide), step160_2364_2426,
      (by decide), (by decide), step160_2427_2499, rfl⟩⟩

theorem step160_verified : Checked step160 :=
  ⟨step160_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step160_cover⟩

def step161 : Request :=
  ⟨⟨⟨1100, 1535, 332, 40111⟩, 40133103452160, 152819743367⟩, 7, 3, 4, 385715⟩

theorem step161_nodes : P1_7_1.nodeRows step161.bank.shape = step161.bank.nodeRows :=
  node_check step161.bank (by decide) (by decide) (by decide)

private theorem step161_2330_2336 : Positive step161 2330 2336 := by decide +kernel

private theorem step161_2337_2356 : Positive step161 2337 2356 := by decide +kernel

private theorem step161_2357_2410 : Positive step161 2357 2410 := by decide +kernel

private theorem step161_2411_2499 : Positive step161 2411 2499 := by decide +kernel

theorem step161_cover : ∃ ends, Cover step161 firstHeight ends := by
  exact ⟨[2336, 2356, 2410, 2499],
    ⟨(by decide), (by decide), step161_2330_2336,
      (by decide), (by decide), step161_2337_2356,
      (by decide), (by decide), step161_2357_2410,
      (by decide), (by decide), step161_2411_2499, rfl⟩⟩

theorem step161_verified : Checked step161 :=
  ⟨step161_nodes, Research6966.HelperWindowCatalogue.moment1535_332,
    (by decide), (by decide), (by decide), step161_cover⟩

def step162 : Request :=
  ⟨⟨⟨1100, 1535, 326, 50764⟩, 39579969388544, 150663514795⟩, 10, 3, 4, 385715⟩

theorem step162_nodes : P1_7_1.nodeRows step162.bank.shape = step162.bank.nodeRows :=
  node_check step162.bank (by decide) (by decide) (by decide)

private theorem step162_2330_2330 : Positive step162 2330 2330 := by decide +kernel

private theorem step162_2331_2332 : Positive step162 2331 2332 := by decide +kernel

private theorem step162_2333_2338 : Positive step162 2333 2338 := by decide +kernel

private theorem step162_2339_2354 : Positive step162 2339 2354 := by decide +kernel

private theorem step162_2355_2398 : Positive step162 2355 2398 := by decide +kernel

private theorem step162_2399_2499 : Positive step162 2399 2499 := by decide +kernel

theorem step162_cover : ∃ ends, Cover step162 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2354, 2398, 2499],
    ⟨(by decide), (by decide), step162_2330_2330,
      (by decide), (by decide), step162_2331_2332,
      (by decide), (by decide), step162_2333_2338,
      (by decide), (by decide), step162_2339_2354,
      (by decide), (by decide), step162_2355_2398,
      (by decide), (by decide), step162_2399_2499, rfl⟩⟩

theorem step162_verified : Checked step162 :=
  ⟨step162_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step162_cover⟩

end Research6966.HelperRescueCatalogue
