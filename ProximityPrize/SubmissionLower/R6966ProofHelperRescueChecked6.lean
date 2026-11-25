import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step163 : Request :=
  ⟨⟨⟨1650, 2303, 488, 64247⟩, 133179773812736, 760643620838⟩, 16, 3, 4, 385715⟩

theorem step163_nodes : P1_7_1.nodeRows step163.bank.shape = step163.bank.nodeRows :=
  node_check step163.bank (by decide) (by decide) (by decide)

private theorem step163_2330_2338 : Positive step163 2330 2338 := by decide +kernel

private theorem step163_2339_2362 : Positive step163 2339 2362 := by decide +kernel

private theorem step163_2363_2427 : Positive step163 2363 2427 := by decide +kernel

private theorem step163_2428_2499 : Positive step163 2428 2499 := by decide +kernel

theorem step163_cover : ∃ ends, Cover step163 firstHeight ends := by
  exact ⟨[2338, 2362, 2427, 2499],
    ⟨(by decide), (by decide), step163_2330_2338,
      (by decide), (by decide), step163_2339_2362,
      (by decide), (by decide), step163_2363_2427,
      (by decide), (by decide), step163_2428_2499, rfl⟩⟩

theorem step163_verified : Checked step163 :=
  ⟨step163_nodes, Research6966.HelperWindowCatalogue.moment2303_488,
    (by decide), (by decide), (by decide), step163_cover⟩

def step164 : Request :=
  ⟨⟨⟨2000, 2791, 592, 72277⟩, 237206388080640, 1640986809111⟩, 20, 3, 4, 385715⟩

theorem step164_nodes : P1_7_1.nodeRows step164.bank.shape = step164.bank.nodeRows :=
  node_check step164.bank (by decide) (by decide) (by decide)

private theorem step164_2330_2336 : Positive step164 2330 2336 := by decide +kernel

private theorem step164_2337_2355 : Positive step164 2337 2355 := by decide +kernel

private theorem step164_2356_2406 : Positive step164 2356 2406 := by decide +kernel

private theorem step164_2407_2499 : Positive step164 2407 2499 := by decide +kernel

theorem step164_cover : ∃ ends, Cover step164 firstHeight ends := by
  exact ⟨[2336, 2355, 2406, 2499],
    ⟨(by decide), (by decide), step164_2330_2336,
      (by decide), (by decide), step164_2337_2355,
      (by decide), (by decide), step164_2356_2406,
      (by decide), (by decide), step164_2407_2499, rfl⟩⟩

theorem step164_verified : Checked step164 :=
  ⟨step164_nodes, Research6966.HelperWindowCatalogue.moment2791_592,
    (by decide), (by decide), (by decide), step164_cover⟩

def step165 : Request :=
  ⟨⟨⟨3048, 4235, 924, 91474⟩, 854327964467200, 8883701072242⟩, 31, 3, 4, 385715⟩

theorem step165_nodes : P1_7_1.nodeRows step165.bank.shape = step165.bank.nodeRows :=
  node_check step165.bank (by decide) (by decide) (by decide)

private theorem step165_2330_2331 : Positive step165 2330 2331 := by decide +kernel

private theorem step165_2332_2336 : Positive step165 2332 2336 := by decide +kernel

private theorem step165_2337_2350 : Positive step165 2337 2350 := by decide +kernel

private theorem step165_2351_2386 : Positive step165 2351 2386 := by decide +kernel

private theorem step165_2387_2481 : Positive step165 2387 2481 := by decide +kernel

private theorem step165_2482_2499 : Positive step165 2482 2499 := by decide +kernel

theorem step165_cover : ∃ ends, Cover step165 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2386, 2481, 2499],
    ⟨(by decide), (by decide), step165_2330_2331,
      (by decide), (by decide), step165_2332_2336,
      (by decide), (by decide), step165_2337_2350,
      (by decide), (by decide), step165_2351_2386,
      (by decide), (by decide), step165_2387_2481,
      (by decide), (by decide), step165_2482_2499, rfl⟩⟩

theorem step165_verified : Checked step165 :=
  ⟨step165_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_4235_924),
    (by decide), (by decide), (by decide), step165_cover⟩

def step166 : Request :=
  ⟨⟨⟨2500, 3489, 740, 102908⟩, 463070780456960, 4004797990029⟩, 32, 3, 4, 385715⟩

theorem step166_nodes : P1_7_1.nodeRows step166.bank.shape = step166.bank.nodeRows :=
  node_check step166.bank (by decide) (by decide) (by decide)

private theorem step166_2330_2333 : Positive step166 2330 2333 := by decide +kernel

private theorem step166_2334_2344 : Positive step166 2334 2344 := by decide +kernel

private theorem step166_2345_2373 : Positive step166 2345 2373 := by decide +kernel

private theorem step166_2374_2451 : Positive step166 2374 2451 := by decide +kernel

private theorem step166_2452_2499 : Positive step166 2452 2499 := by decide +kernel

theorem step166_cover : ∃ ends, Cover step166 firstHeight ends := by
  exact ⟨[2333, 2344, 2373, 2451, 2499],
    ⟨(by decide), (by decide), step166_2330_2333,
      (by decide), (by decide), step166_2334_2344,
      (by decide), (by decide), step166_2345_2373,
      (by decide), (by decide), step166_2374_2451,
      (by decide), (by decide), step166_2452_2499, rfl⟩⟩

theorem step166_verified : Checked step166 :=
  ⟨step166_nodes, Research6966.HelperWindowCatalogue.moment3489_740,
    (by decide), (by decide), (by decide), step166_cover⟩

def step167 : Request :=
  ⟨⟨⟨3000, 4187, 906, 130242⟩, 812266433019904, 8433369009268⟩, 44, 3, 4, 385715⟩

theorem step167_nodes : P1_7_1.nodeRows step167.bank.shape = step167.bank.nodeRows :=
  node_check step167.bank (by decide) (by decide) (by decide)

private theorem step167_2330_2332 : Positive step167 2330 2332 := by decide +kernel

private theorem step167_2333_2340 : Positive step167 2333 2340 := by decide +kernel

private theorem step167_2341_2361 : Positive step167 2341 2361 := by decide +kernel

private theorem step167_2362_2416 : Positive step167 2362 2416 := by decide +kernel

private theorem step167_2417_2499 : Positive step167 2417 2499 := by decide +kernel

theorem step167_cover : ∃ ends, Cover step167 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2416, 2499],
    ⟨(by decide), (by decide), step167_2330_2332,
      (by decide), (by decide), step167_2333_2340,
      (by decide), (by decide), step167_2341_2361,
      (by decide), (by decide), step167_2362_2416,
      (by decide), (by decide), step167_2417_2499, rfl⟩⟩

theorem step167_verified : Checked step167 :=
  ⟨step167_nodes, Research6966.HelperWindowCatalogue.moment4187_906,
    (by decide), (by decide), (by decide), step167_cover⟩

def step168 : Request :=
  ⟨⟨⟨630, 879, 186, 19788⟩, 7438337572864, 16221345781⟩, 0, 3, 9, 385715⟩

theorem step168_nodes : P1_7_1.nodeRows step168.bank.shape = step168.bank.nodeRows :=
  node_check step168.bank (by decide) (by decide) (by decide)

private theorem step168_2330_2335 : Positive step168 2330 2335 := by decide +kernel

private theorem step168_2336_2352 : Positive step168 2336 2352 := by decide +kernel

private theorem step168_2353_2402 : Positive step168 2353 2402 := by decide +kernel

private theorem step168_2403_2499 : Positive step168 2403 2499 := by decide +kernel

theorem step168_cover : ∃ ends, Cover step168 firstHeight ends := by
  exact ⟨[2335, 2352, 2402, 2499],
    ⟨(by decide), (by decide), step168_2330_2335,
      (by decide), (by decide), step168_2336_2352,
      (by decide), (by decide), step168_2353_2402,
      (by decide), (by decide), step168_2403_2499, rfl⟩⟩

theorem step168_verified : Checked step168 :=
  ⟨step168_nodes, Research6966.HelperWindowCatalogue.moment879_186,
    (by decide), (by decide), (by decide), step168_cover⟩

def step169 : Request :=
  ⟨⟨⟨630, 879, 186, 22261⟩, 7438337572864, 16221345781⟩, 1, 3, 9, 385715⟩

theorem step169_nodes : P1_7_1.nodeRows step169.bank.shape = step169.bank.nodeRows :=
  node_check step169.bank (by decide) (by decide) (by decide)

private theorem step169_2330_2330 : Positive step169 2330 2330 := by decide +kernel

private theorem step169_2331_2333 : Positive step169 2331 2333 := by decide +kernel

private theorem step169_2334_2342 : Positive step169 2334 2342 := by decide +kernel

private theorem step169_2343_2368 : Positive step169 2343 2368 := by decide +kernel

private theorem step169_2369_2444 : Positive step169 2369 2444 := by decide +kernel

private theorem step169_2445_2499 : Positive step169 2445 2499 := by decide +kernel

theorem step169_cover : ∃ ends, Cover step169 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2368, 2444, 2499],
    ⟨(by decide), (by decide), step169_2330_2330,
      (by decide), (by decide), step169_2331_2333,
      (by decide), (by decide), step169_2334_2342,
      (by decide), (by decide), step169_2343_2368,
      (by decide), (by decide), step169_2369_2444,
      (by decide), (by decide), step169_2445_2499, rfl⟩⟩

theorem step169_verified : Checked step169 :=
  ⟨step169_nodes, Research6966.HelperWindowCatalogue.moment879_186,
    (by decide), (by decide), (by decide), step169_cover⟩

def step170 : Request :=
  ⟨⟨⟨750, 1047, 226, 22261⟩, 12730741817344, 33110613849⟩, 2, 3, 9, 385715⟩

theorem step170_nodes : P1_7_1.nodeRows step170.bank.shape = step170.bank.nodeRows :=
  node_check step170.bank (by decide) (by decide) (by decide)

private theorem step170_2330_2333 : Positive step170 2330 2333 := by decide +kernel

private theorem step170_2334_2344 : Positive step170 2334 2344 := by decide +kernel

private theorem step170_2345_2375 : Positive step170 2345 2375 := by decide +kernel

private theorem step170_2376_2462 : Positive step170 2376 2462 := by decide +kernel

private theorem step170_2463_2499 : Positive step170 2463 2499 := by decide +kernel

theorem step170_cover : ∃ ends, Cover step170 firstHeight ends := by
  exact ⟨[2333, 2344, 2375, 2462, 2499],
    ⟨(by decide), (by decide), step170_2330_2333,
      (by decide), (by decide), step170_2334_2344,
      (by decide), (by decide), step170_2345_2375,
      (by decide), (by decide), step170_2376_2462,
      (by decide), (by decide), step170_2463_2499, rfl⟩⟩

theorem step170_verified : Checked step170 :=
  ⟨step170_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step170_cover⟩

def step171 : Request :=
  ⟨⟨⟨750, 1047, 226, 25043⟩, 12730741817344, 33110613849⟩, 3, 3, 9, 385715⟩

theorem step171_nodes : P1_7_1.nodeRows step171.bank.shape = step171.bank.nodeRows :=
  node_check step171.bank (by decide) (by decide) (by decide)

private theorem step171_2330_2334 : Positive step171 2330 2334 := by decide +kernel

private theorem step171_2335_2348 : Positive step171 2335 2348 := by decide +kernel

private theorem step171_2349_2387 : Positive step171 2349 2387 := by decide +kernel

private theorem step171_2388_2497 : Positive step171 2388 2497 := by decide +kernel

private theorem step171_2498_2499 : Positive step171 2498 2499 := by decide +kernel

theorem step171_cover : ∃ ends, Cover step171 firstHeight ends := by
  exact ⟨[2334, 2348, 2387, 2497, 2499],
    ⟨(by decide), (by decide), step171_2330_2334,
      (by decide), (by decide), step171_2335_2348,
      (by decide), (by decide), step171_2349_2387,
      (by decide), (by decide), step171_2388_2497,
      (by decide), (by decide), step171_2498_2499, rfl⟩⟩

theorem step171_verified : Checked step171 :=
  ⟨step171_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step171_cover⟩

def step172 : Request :=
  ⟨⟨⟨750, 1047, 226, 28173⟩, 12730741817344, 33110613849⟩, 4, 3, 9, 385715⟩

theorem step172_nodes : P1_7_1.nodeRows step172.bank.shape = step172.bank.nodeRows :=
  node_check step172.bank (by decide) (by decide) (by decide)

private theorem step172_2330_2332 : Positive step172 2330 2332 := by decide +kernel

private theorem step172_2333_2340 : Positive step172 2333 2340 := by decide +kernel

private theorem step172_2341_2363 : Positive step172 2341 2363 := by decide +kernel

private theorem step172_2364_2428 : Positive step172 2364 2428 := by decide +kernel

private theorem step172_2429_2499 : Positive step172 2429 2499 := by decide +kernel

theorem step172_cover : ∃ ends, Cover step172 firstHeight ends := by
  exact ⟨[2332, 2340, 2363, 2428, 2499],
    ⟨(by decide), (by decide), step172_2330_2332,
      (by decide), (by decide), step172_2333_2340,
      (by decide), (by decide), step172_2341_2363,
      (by decide), (by decide), step172_2364_2428,
      (by decide), (by decide), step172_2429_2499, rfl⟩⟩

theorem step172_verified : Checked step172 :=
  ⟨step172_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step172_cover⟩

def step173 : Request :=
  ⟨⟨⟨900, 1256, 272, 28173⟩, 22024701870080, 68653176066⟩, 5, 3, 9, 385715⟩

theorem step173_nodes : P1_7_1.nodeRows step173.bank.shape = step173.bank.nodeRows :=
  node_check step173.bank (by decide) (by decide) (by decide)

private theorem step173_2330_2334 : Positive step173 2330 2334 := by decide +kernel

private theorem step173_2335_2348 : Positive step173 2335 2348 := by decide +kernel

private theorem step173_2349_2387 : Positive step173 2349 2387 := by decide +kernel

private theorem step173_2388_2495 : Positive step173 2388 2495 := by decide +kernel

private theorem step173_2496_2499 : Positive step173 2496 2499 := by decide +kernel

theorem step173_cover : ∃ ends, Cover step173 firstHeight ends := by
  exact ⟨[2334, 2348, 2387, 2495, 2499],
    ⟨(by decide), (by decide), step173_2330_2334,
      (by decide), (by decide), step173_2335_2348,
      (by decide), (by decide), step173_2349_2387,
      (by decide), (by decide), step173_2388_2495,
      (by decide), (by decide), step173_2496_2499, rfl⟩⟩

theorem step173_verified : Checked step173 :=
  ⟨step173_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step173_cover⟩

def step174 : Request :=
  ⟨⟨⟨900, 1256, 272, 35655⟩, 22024701870080, 68653176066⟩, 7, 3, 9, 385715⟩

theorem step174_nodes : P1_7_1.nodeRows step174.bank.shape = step174.bank.nodeRows :=
  node_check step174.bank (by decide) (by decide) (by decide)

private theorem step174_2330_2339 : Positive step174 2330 2339 := by decide +kernel

private theorem step174_2340_2367 : Positive step174 2340 2367 := by decide +kernel

private theorem step174_2368_2444 : Positive step174 2368 2444 := by decide +kernel

private theorem step174_2445_2499 : Positive step174 2445 2499 := by decide +kernel

theorem step174_cover : ∃ ends, Cover step174 firstHeight ends := by
  exact ⟨[2339, 2367, 2444, 2499],
    ⟨(by decide), (by decide), step174_2330_2339,
      (by decide), (by decide), step174_2340_2367,
      (by decide), (by decide), step174_2368_2444,
      (by decide), (by decide), step174_2445_2499, rfl⟩⟩

theorem step174_verified : Checked step174 :=
  ⟨step174_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step174_cover⟩

def step175 : Request :=
  ⟨⟨⟨1100, 1535, 326, 40111⟩, 39579969388544, 150663514795⟩, 10, 3, 9, 385715⟩

theorem step175_nodes : P1_7_1.nodeRows step175.bank.shape = step175.bank.nodeRows :=
  node_check step175.bank (by decide) (by decide) (by decide)

private theorem step175_2330_2330 : Positive step175 2330 2330 := by decide +kernel

private theorem step175_2331_2333 : Positive step175 2331 2333 := by decide +kernel

private theorem step175_2334_2341 : Positive step175 2334 2341 := by decide +kernel

private theorem step175_2342_2363 : Positive step175 2342 2363 := by decide +kernel

private theorem step175_2364_2424 : Positive step175 2364 2424 := by decide +kernel

private theorem step175_2425_2499 : Positive step175 2425 2499 := by decide +kernel

theorem step175_cover : ∃ ends, Cover step175 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2424, 2499],
    ⟨(by decide), (by decide), step175_2330_2330,
      (by decide), (by decide), step175_2331_2333,
      (by decide), (by decide), step175_2334_2341,
      (by decide), (by decide), step175_2342_2363,
      (by decide), (by decide), step175_2364_2424,
      (by decide), (by decide), step175_2425_2499, rfl⟩⟩

theorem step175_verified : Checked step175 :=
  ⟨step175_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step175_cover⟩

def step176 : Request :=
  ⟨⟨⟨1350, 1884, 400, 57109⟩, 73092385996800, 341469310532⟩, 16, 3, 9, 385715⟩

theorem step176_nodes : P1_7_1.nodeRows step176.bank.shape = step176.bank.nodeRows :=
  node_check step176.bank (by decide) (by decide) (by decide)

private theorem step176_2330_2336 : Positive step176 2330 2336 := by decide +kernel

private theorem step176_2337_2355 : Positive step176 2337 2355 := by decide +kernel

private theorem step176_2356_2407 : Positive step176 2356 2407 := by decide +kernel

private theorem step176_2408_2499 : Positive step176 2408 2499 := by decide +kernel

theorem step176_cover : ∃ ends, Cover step176 firstHeight ends := by
  exact ⟨[2336, 2355, 2407, 2499],
    ⟨(by decide), (by decide), step176_2330_2336,
      (by decide), (by decide), step176_2337_2355,
      (by decide), (by decide), step176_2356_2407,
      (by decide), (by decide), step176_2408_2499, rfl⟩⟩

theorem step176_verified : Checked step176 :=
  ⟨step176_nodes, Research6966.HelperWindowCatalogue.moment1884_400,
    (by decide), (by decide), (by decide), step176_cover⟩

def step177 : Request :=
  ⟨⟨⟨1650, 2303, 498, 57109⟩, 135254251667456, 772776530256⟩, 20, 3, 9, 385715⟩

theorem step177_nodes : P1_7_1.nodeRows step177.bank.shape = step177.bank.nodeRows :=
  node_check step177.bank (by decide) (by decide) (by decide)

private theorem step177_2330_2331 : Positive step177 2330 2331 := by decide +kernel

private theorem step177_2332_2336 : Positive step177 2332 2336 := by decide +kernel

private theorem step177_2337_2350 : Positive step177 2337 2350 := by decide +kernel

private theorem step177_2351_2387 : Positive step177 2351 2387 := by decide +kernel

private theorem step177_2388_2486 : Positive step177 2388 2486 := by decide +kernel

private theorem step177_2487_2499 : Positive step177 2487 2499 := by decide +kernel

theorem step177_cover : ∃ ends, Cover step177 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2387, 2486, 2499],
    ⟨(by decide), (by decide), step177_2330_2331,
      (by decide), (by decide), step177_2332_2336,
      (by decide), (by decide), step177_2337_2350,
      (by decide), (by decide), step177_2351_2387,
      (by decide), (by decide), step177_2388_2486,
      (by decide), (by decide), step177_2487_2499, rfl⟩⟩

theorem step177_verified : Checked step177 :=
  ⟨step177_nodes, Research6966.HelperWindowCatalogue.moment2303_498,
    (by decide), (by decide), (by decide), step177_cover⟩

def step178 : Request :=
  ⟨⟨⟨2000, 2791, 604, 91474⟩, 240862397726720, 1666886727164⟩, 31, 3, 9, 385715⟩

theorem step178_nodes : P1_7_1.nodeRows step178.bank.shape = step178.bank.nodeRows :=
  node_check step178.bank (by decide) (by decide) (by decide)

private theorem step178_2330_2337 : Positive step178 2330 2337 := by decide +kernel

private theorem step178_2338_2358 : Positive step178 2338 2358 := by decide +kernel

private theorem step178_2359_2413 : Positive step178 2359 2413 := by decide +kernel

private theorem step178_2414_2499 : Positive step178 2414 2499 := by decide +kernel

theorem step178_cover : ∃ ends, Cover step178 firstHeight ends := by
  exact ⟨[2337, 2358, 2413, 2499],
    ⟨(by decide), (by decide), step178_2330_2337,
      (by decide), (by decide), step178_2338_2358,
      (by decide), (by decide), step178_2359_2413,
      (by decide), (by decide), step178_2414_2499, rfl⟩⟩

theorem step178_verified : Checked step178 :=
  ⟨step178_nodes, Research6966.HelperWindowCatalogue.moment2791_604,
    (by decide), (by decide), (by decide), step178_cover⟩

def step179 : Request :=
  ⟨⟨⟨2500, 3489, 740, 81311⟩, 463070780456960, 4004797990029⟩, 32, 3, 9, 385715⟩

theorem step179_nodes : P1_7_1.nodeRows step179.bank.shape = step179.bank.nodeRows :=
  node_check step179.bank (by decide) (by decide) (by decide)

private theorem step179_2330_2334 : Positive step179 2330 2334 := by decide +kernel

private theorem step179_2335_2347 : Positive step179 2335 2347 := by decide +kernel

private theorem step179_2348_2381 : Positive step179 2348 2381 := by decide +kernel

private theorem step179_2382_2472 : Positive step179 2382 2472 := by decide +kernel

private theorem step179_2473_2499 : Positive step179 2473 2499 := by decide +kernel

theorem step179_cover : ∃ ends, Cover step179 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2472, 2499],
    ⟨(by decide), (by decide), step179_2330_2334,
      (by decide), (by decide), step179_2335_2347,
      (by decide), (by decide), step179_2348_2381,
      (by decide), (by decide), step179_2382_2472,
      (by decide), (by decide), step179_2473_2499, rfl⟩⟩

theorem step179_verified : Checked step179 :=
  ⟨step179_nodes, Research6966.HelperWindowCatalogue.moment3489_740,
    (by decide), (by decide), (by decide), step179_cover⟩

def step180 : Request :=
  ⟨⟨⟨3000, 4187, 906, 102908⟩, 812266433019904, 8433369009268⟩, 44, 3, 9, 385715⟩

theorem step180_nodes : P1_7_1.nodeRows step180.bank.shape = step180.bank.nodeRows :=
  node_check step180.bank (by decide) (by decide) (by decide)

private theorem step180_2330_2334 : Positive step180 2330 2334 := by decide +kernel

private theorem step180_2335_2347 : Positive step180 2335 2347 := by decide +kernel

private theorem step180_2348_2381 : Positive step180 2348 2381 := by decide +kernel

private theorem step180_2382_2470 : Positive step180 2382 2470 := by decide +kernel

private theorem step180_2471_2499 : Positive step180 2471 2499 := by decide +kernel

theorem step180_cover : ∃ ends, Cover step180 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2470, 2499],
    ⟨(by decide), (by decide), step180_2330_2334,
      (by decide), (by decide), step180_2335_2347,
      (by decide), (by decide), step180_2348_2381,
      (by decide), (by decide), step180_2382_2470,
      (by decide), (by decide), step180_2471_2499, rfl⟩⟩

theorem step180_verified : Checked step180 :=
  ⟨step180_nodes, Research6966.HelperWindowCatalogue.moment4187_906,
    (by decide), (by decide), (by decide), step180_cover⟩

def step181 : Request :=
  ⟨⟨⟨630, 879, 190, 12355⟩, 7559493713920, 16491913877⟩, 0, 3, 16, 385715⟩

theorem step181_nodes : P1_7_1.nodeRows step181.bank.shape = step181.bank.nodeRows :=
  node_check step181.bank (by decide) (by decide) (by decide)

private theorem step181_2330_2342 : Positive step181 2330 2342 := by decide +kernel

private theorem step181_2343_2379 : Positive step181 2343 2379 := by decide +kernel

private theorem step181_2380_2486 : Positive step181 2380 2486 := by decide +kernel

private theorem step181_2487_2499 : Positive step181 2487 2499 := by decide +kernel

theorem step181_cover : ∃ ends, Cover step181 firstHeight ends := by
  exact ⟨[2342, 2379, 2486, 2499],
    ⟨(by decide), (by decide), step181_2330_2342,
      (by decide), (by decide), step181_2343_2379,
      (by decide), (by decide), step181_2380_2486,
      (by decide), (by decide), step181_2487_2499, rfl⟩⟩

theorem step181_verified : Checked step181 :=
  ⟨step181_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step181_cover⟩

def step182 : Request :=
  ⟨⟨⟨630, 879, 190, 13899⟩, 7559493713920, 16491913877⟩, 1, 3, 16, 385715⟩

theorem step182_nodes : P1_7_1.nodeRows step182.bank.shape = step182.bank.nodeRows :=
  node_check step182.bank (by decide) (by decide) (by decide)

private theorem step182_2330_2339 : Positive step182 2330 2339 := by decide +kernel

private theorem step182_2340_2368 : Positive step182 2340 2368 := by decide +kernel

private theorem step182_2369_2451 : Positive step182 2369 2451 := by decide +kernel

private theorem step182_2452_2499 : Positive step182 2452 2499 := by decide +kernel

theorem step182_cover : ∃ ends, Cover step182 firstHeight ends := by
  exact ⟨[2339, 2368, 2451, 2499],
    ⟨(by decide), (by decide), step182_2330_2339,
      (by decide), (by decide), step182_2340_2368,
      (by decide), (by decide), step182_2369_2451,
      (by decide), (by decide), step182_2452_2499, rfl⟩⟩

theorem step182_verified : Checked step182 :=
  ⟨step182_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step182_cover⟩

def step183 : Request :=
  ⟨⟨⟨630, 879, 190, 15636⟩, 7559493713920, 16491913877⟩, 2, 3, 16, 385715⟩

theorem step183_nodes : P1_7_1.nodeRows step183.bank.shape = step183.bank.nodeRows :=
  node_check step183.bank (by decide) (by decide) (by decide)

private theorem step183_2330_2333 : Positive step183 2330 2333 := by decide +kernel

private theorem step183_2334_2344 : Positive step183 2334 2344 := by decide +kernel

private theorem step183_2345_2376 : Positive step183 2345 2376 := by decide +kernel

private theorem step183_2377_2468 : Positive step183 2377 2468 := by decide +kernel

private theorem step183_2469_2499 : Positive step183 2469 2499 := by decide +kernel

theorem step183_cover : ∃ ends, Cover step183 firstHeight ends := by
  exact ⟨[2333, 2344, 2376, 2468, 2499],
    ⟨(by decide), (by decide), step183_2330_2333,
      (by decide), (by decide), step183_2334_2344,
      (by decide), (by decide), step183_2345_2376,
      (by decide), (by decide), step183_2377_2468,
      (by decide), (by decide), step183_2469_2499, rfl⟩⟩

theorem step183_verified : Checked step183 :=
  ⟨step183_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step183_cover⟩

def step184 : Request :=
  ⟨⟨⟨750, 1047, 226, 15636⟩, 12730741817344, 33110613849⟩, 3, 3, 16, 385715⟩

theorem step184_nodes : P1_7_1.nodeRows step184.bank.shape = step184.bank.nodeRows :=
  node_check step184.bank (by decide) (by decide) (by decide)

private theorem step184_2330_2330 : Positive step184 2330 2330 := by decide +kernel

private theorem step184_2331_2333 : Positive step184 2331 2333 := by decide +kernel

private theorem step184_2334_2341 : Positive step184 2334 2341 := by decide +kernel

private theorem step184_2342_2364 : Positive step184 2342 2364 := by decide +kernel

private theorem step184_2365_2428 : Positive step184 2365 2428 := by decide +kernel

private theorem step184_2429_2499 : Positive step184 2429 2499 := by decide +kernel

theorem step184_cover : ∃ ends, Cover step184 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2364, 2428, 2499],
    ⟨(by decide), (by decide), step184_2330_2330,
      (by decide), (by decide), step184_2331_2333,
      (by decide), (by decide), step184_2334_2341,
      (by decide), (by decide), step184_2342_2364,
      (by decide), (by decide), step184_2365_2428,
      (by decide), (by decide), step184_2429_2499, rfl⟩⟩

theorem step184_verified : Checked step184 :=
  ⟨step184_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step184_cover⟩

def step185 : Request :=
  ⟨⟨⟨750, 1047, 226, 17590⟩, 12730741817344, 33110613849⟩, 4, 3, 16, 385715⟩

theorem step185_nodes : P1_7_1.nodeRows step185.bank.shape = step185.bank.nodeRows :=
  node_check step185.bank (by decide) (by decide) (by decide)

private theorem step185_2330_2330 : Positive step185 2330 2330 := by decide +kernel

private theorem step185_2331_2333 : Positive step185 2331 2333 := by decide +kernel

private theorem step185_2334_2341 : Positive step185 2334 2341 := by decide +kernel

private theorem step185_2342_2364 : Positive step185 2342 2364 := by decide +kernel

private theorem step185_2365_2428 : Positive step185 2365 2428 := by decide +kernel

private theorem step185_2429_2499 : Positive step185 2429 2499 := by decide +kernel

theorem step185_cover : ∃ ends, Cover step185 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2364, 2428, 2499],
    ⟨(by decide), (by decide), step185_2330_2330,
      (by decide), (by decide), step185_2331_2333,
      (by decide), (by decide), step185_2334_2341,
      (by decide), (by decide), step185_2342_2364,
      (by decide), (by decide), step185_2365_2428,
      (by decide), (by decide), step185_2429_2499, rfl⟩⟩

theorem step185_verified : Checked step185 :=
  ⟨step185_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step185_cover⟩

def step186 : Request :=
  ⟨⟨⟨900, 1256, 272, 17590⟩, 22024701870080, 68653176066⟩, 5, 3, 16, 385715⟩

theorem step186_nodes : P1_7_1.nodeRows step186.bank.shape = step186.bank.nodeRows :=
  node_check step186.bank (by decide) (by decide) (by decide)

private theorem step186_2330_2331 : Positive step186 2330 2331 := by decide +kernel

private theorem step186_2332_2336 : Positive step186 2332 2336 := by decide +kernel

private theorem step186_2337_2350 : Positive step186 2337 2350 := by decide +kernel

private theorem step186_2351_2389 : Positive step186 2351 2389 := by decide +kernel

private theorem step186_2390_2497 : Positive step186 2390 2497 := by decide +kernel

private theorem step186_2498_2499 : Positive step186 2498 2499 := by decide +kernel

theorem step186_cover : ∃ ends, Cover step186 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2389, 2497, 2499],
    ⟨(by decide), (by decide), step186_2330_2331,
      (by decide), (by decide), step186_2332_2336,
      (by decide), (by decide), step186_2337_2350,
      (by decide), (by decide), step186_2351_2389,
      (by decide), (by decide), step186_2390_2497,
      (by decide), (by decide), step186_2498_2499, rfl⟩⟩

theorem step186_verified : Checked step186 :=
  ⟨step186_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step186_cover⟩

def step187 : Request :=
  ⟨⟨⟨900, 1256, 272, 22261⟩, 22024701870080, 68653176066⟩, 7, 3, 16, 385715⟩

theorem step187_nodes : P1_7_1.nodeRows step187.bank.shape = step187.bank.nodeRows :=
  node_check step187.bank (by decide) (by decide) (by decide)

private theorem step187_2330_2338 : Positive step187 2330 2338 := by decide +kernel

private theorem step187_2339_2363 : Positive step187 2339 2363 := by decide +kernel

private theorem step187_2364_2433 : Positive step187 2364 2433 := by decide +kernel

private theorem step187_2434_2499 : Positive step187 2434 2499 := by decide +kernel

theorem step187_cover : ∃ ends, Cover step187 firstHeight ends := by
  exact ⟨[2338, 2363, 2433, 2499],
    ⟨(by decide), (by decide), step187_2330_2338,
      (by decide), (by decide), step187_2339_2363,
      (by decide), (by decide), step187_2364_2433,
      (by decide), (by decide), step187_2434_2499, rfl⟩⟩

theorem step187_verified : Checked step187 :=
  ⟨step187_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step187_cover⟩

def step188 : Request :=
  ⟨⟨⟨1100, 1535, 332, 25043⟩, 40133103452160, 152819743367⟩, 10, 3, 16, 385715⟩

theorem step188_nodes : P1_7_1.nodeRows step188.bank.shape = step188.bank.nodeRows :=
  node_check step188.bank (by decide) (by decide) (by decide)

private theorem step188_2330_2336 : Positive step188 2330 2336 := by decide +kernel

private theorem step188_2337_2355 : Positive step188 2337 2355 := by decide +kernel

private theorem step188_2356_2407 : Positive step188 2356 2407 := by decide +kernel

private theorem step188_2408_2499 : Positive step188 2408 2499 := by decide +kernel

theorem step188_cover : ∃ ends, Cover step188 firstHeight ends := by
  exact ⟨[2336, 2355, 2407, 2499],
    ⟨(by decide), (by decide), step188_2330_2336,
      (by decide), (by decide), step188_2337_2355,
      (by decide), (by decide), step188_2356_2407,
      (by decide), (by decide), step188_2408_2499, rfl⟩⟩

theorem step188_verified : Checked step188 :=
  ⟨step188_nodes, Research6966.HelperWindowCatalogue.moment1535_332,
    (by decide), (by decide), (by decide), step188_cover⟩

def step189 : Request :=
  ⟨⟨⟨1350, 1884, 400, 35655⟩, 73092385996800, 341469310532⟩, 16, 3, 16, 385715⟩

theorem step189_nodes : P1_7_1.nodeRows step189.bank.shape = step189.bank.nodeRows :=
  node_check step189.bank (by decide) (by decide) (by decide)

private theorem step189_2330_2332 : Positive step189 2330 2332 := by decide +kernel

private theorem step189_2333_2340 : Positive step189 2333 2340 := by decide +kernel

private theorem step189_2341_2362 : Positive step189 2341 2362 := by decide +kernel

private theorem step189_2363_2422 : Positive step189 2363 2422 := by decide +kernel

private theorem step189_2423_2499 : Positive step189 2423 2499 := by decide +kernel

theorem step189_cover : ∃ ends, Cover step189 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2422, 2499],
    ⟨(by decide), (by decide), step189_2330_2332,
      (by decide), (by decide), step189_2333_2340,
      (by decide), (by decide), step189_2341_2362,
      (by decide), (by decide), step189_2363_2422,
      (by decide), (by decide), step189_2423_2499, rfl⟩⟩

theorem step189_verified : Checked step189 :=
  ⟨step189_nodes, Research6966.HelperWindowCatalogue.moment1884_400,
    (by decide), (by decide), (by decide), step189_cover⟩

def step190 : Request :=
  ⟨⟨⟨2000, 2791, 604, 35655⟩, 240862397726720, 1666886727164⟩, 20, 3, 16, 385715⟩

theorem step190_nodes : P1_7_1.nodeRows step190.bank.shape = step190.bank.nodeRows :=
  node_check step190.bank (by decide) (by decide) (by decide)

private theorem step190_2330_2340 : Positive step190 2330 2340 := by decide +kernel

private theorem step190_2341_2370 : Positive step190 2341 2370 := by decide +kernel

private theorem step190_2371_2449 : Positive step190 2371 2449 := by decide +kernel

private theorem step190_2450_2499 : Positive step190 2450 2499 := by decide +kernel

theorem step190_cover : ∃ ends, Cover step190 firstHeight ends := by
  exact ⟨[2340, 2370, 2449, 2499],
    ⟨(by decide), (by decide), step190_2330_2340,
      (by decide), (by decide), step190_2341_2370,
      (by decide), (by decide), step190_2371_2449,
      (by decide), (by decide), step190_2450_2499, rfl⟩⟩

theorem step190_verified : Checked step190 :=
  ⟨step190_nodes, Research6966.HelperWindowCatalogue.moment2791_604,
    (by decide), (by decide), (by decide), step190_cover⟩

def step191 : Request :=
  ⟨⟨⟨2000, 2791, 604, 57109⟩, 240862397726720, 1666886727164⟩, 31, 3, 16, 385715⟩

theorem step191_nodes : P1_7_1.nodeRows step191.bank.shape = step191.bank.nodeRows :=
  node_check step191.bank (by decide) (by decide) (by decide)

private theorem step191_2330_2337 : Positive step191 2330 2337 := by decide +kernel

private theorem step191_2338_2358 : Positive step191 2338 2358 := by decide +kernel

private theorem step191_2359_2414 : Positive step191 2359 2414 := by decide +kernel

private theorem step191_2415_2499 : Positive step191 2415 2499 := by decide +kernel

theorem step191_cover : ∃ ends, Cover step191 firstHeight ends := by
  exact ⟨[2337, 2358, 2414, 2499],
    ⟨(by decide), (by decide), step191_2330_2337,
      (by decide), (by decide), step191_2338_2358,
      (by decide), (by decide), step191_2359_2414,
      (by decide), (by decide), step191_2415_2499, rfl⟩⟩

theorem step191_verified : Checked step191 :=
  ⟨step191_nodes, Research6966.HelperWindowCatalogue.moment2791_604,
    (by decide), (by decide), (by decide), step191_cover⟩

end Research6966.HelperRescueCatalogue
