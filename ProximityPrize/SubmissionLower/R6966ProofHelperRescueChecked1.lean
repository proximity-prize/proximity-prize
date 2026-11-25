import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt2
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments10
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments9
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step23 : Request :=
  ⟨⟨⟨3500, 4886, 1036, 185441⟩, 1269967213297664, 15388297203643⟩, 31, 2, 2, 308232⟩

theorem step23_nodes : P1_7_1.nodeRows step23.bank.shape = step23.bank.nodeRows :=
  node_check step23.bank (by decide) (by decide) (by decide)

private theorem step23_2330_2332 : Positive step23 2330 2332 := by decide +kernel

private theorem step23_2333_2340 : Positive step23 2333 2340 := by decide +kernel

private theorem step23_2341_2361 : Positive step23 2341 2361 := by decide +kernel

private theorem step23_2362_2416 : Positive step23 2362 2416 := by decide +kernel

private theorem step23_2417_2499 : Positive step23 2417 2499 := by decide +kernel

theorem step23_cover : ∃ ends, Cover step23 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2416, 2499],
    ⟨(by decide), (by decide), step23_2330_2332,
      (by decide), (by decide), step23_2333_2340,
      (by decide), (by decide), step23_2341_2361,
      (by decide), (by decide), step23_2362_2416,
      (by decide), (by decide), step23_2417_2499, rfl⟩⟩

theorem step23_verified : Checked step23 :=
  ⟨step23_nodes, Research6966.HelperWindowCatalogue.moment4886_1036,
    (by decide), (by decide), (by decide), step23_cover⟩

def step24 : Request :=
  ⟨⟨⟨3500, 4886, 1057, 185441⟩, 1289556817346560, 15631374615265⟩, 32, 2, 2, 308232⟩

theorem step24_nodes : P1_7_1.nodeRows step24.bank.shape = step24.bank.nodeRows :=
  node_check step24.bank (by decide) (by decide) (by decide)

private theorem step24_2330_2330 : Positive step24 2330 2330 := by decide +kernel

private theorem step24_2331_2333 : Positive step24 2331 2333 := by decide +kernel

private theorem step24_2334_2341 : Positive step24 2334 2341 := by decide +kernel

private theorem step24_2342_2362 : Positive step24 2342 2362 := by decide +kernel

private theorem step24_2363_2416 : Positive step24 2363 2416 := by decide +kernel

private theorem step24_2417_2499 : Positive step24 2417 2499 := by decide +kernel

theorem step24_cover : ∃ ends, Cover step24 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2416, 2499],
    ⟨(by decide), (by decide), step24_2330_2330,
      (by decide), (by decide), step24_2331_2333,
      (by decide), (by decide), step24_2334_2341,
      (by decide), (by decide), step24_2342_2362,
      (by decide), (by decide), step24_2363_2416,
      (by decide), (by decide), step24_2417_2499, rfl⟩⟩

theorem step24_verified : Checked step24 :=
  ⟨step24_nodes, Research6966.HelperWindowCatalogue.moment4886_1057,
    (by decide), (by decide), (by decide), step24_cover⟩

def step25 : Request :=
  ⟨⟨⟨3500, 4885, 1036, 297039⟩, 1269967213297664, 15378169933196⟩, 44, 2, 2, 308232⟩

theorem step25_nodes : P1_7_1.nodeRows step25.bank.shape = step25.bank.nodeRows :=
  node_check step25.bank (by decide) (by decide) (by decide)

private theorem step25_2330_2331 : Positive step25 2330 2331 := by decide +kernel

private theorem step25_2332_2336 : Positive step25 2332 2336 := by decide +kernel

private theorem step25_2337_2349 : Positive step25 2337 2349 := by decide +kernel

private theorem step25_2350_2383 : Positive step25 2350 2383 := by decide +kernel

private theorem step25_2384_2473 : Positive step25 2384 2473 := by decide +kernel

private theorem step25_2474_2499 : Positive step25 2474 2499 := by decide +kernel

theorem step25_cover : ∃ ends, Cover step25 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2473, 2499],
    ⟨(by decide), (by decide), step25_2330_2331,
      (by decide), (by decide), step25_2332_2336,
      (by decide), (by decide), step25_2337_2349,
      (by decide), (by decide), step25_2350_2383,
      (by decide), (by decide), step25_2384_2473,
      (by decide), (by decide), step25_2474_2499, rfl⟩⟩

theorem step25_verified : Checked step25 :=
  ⟨step25_nodes, Research6966.HelperWindowCatalogue.moment4885_1036,
    (by decide), (by decide), (by decide), step25_cover⟩

def step26 : Request :=
  ⟨⟨⟨750, 1047, 222, 45124⟩, 12559140782080, 32653699308⟩, 0, 2, 4, 307568⟩

theorem step26_nodes : P1_7_1.nodeRows step26.bank.shape = step26.bank.nodeRows :=
  node_check step26.bank (by decide) (by decide) (by decide)

private theorem step26_2330_2330 : Positive step26 2330 2330 := by decide +kernel

private theorem step26_2331_2332 : Positive step26 2331 2332 := by decide +kernel

private theorem step26_2333_2338 : Positive step26 2333 2338 := by decide +kernel

private theorem step26_2339_2355 : Positive step26 2339 2355 := by decide +kernel

private theorem step26_2356_2403 : Positive step26 2356 2403 := by decide +kernel

private theorem step26_2404_2499 : Positive step26 2404 2499 := by decide +kernel

theorem step26_cover : ∃ ends, Cover step26 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2355, 2403, 2499],
    ⟨(by decide), (by decide), step26_2330_2330,
      (by decide), (by decide), step26_2331_2332,
      (by decide), (by decide), step26_2333_2338,
      (by decide), (by decide), step26_2339_2355,
      (by decide), (by decide), step26_2356_2403,
      (by decide), (by decide), step26_2404_2499, rfl⟩⟩

theorem step26_verified : Checked step26 :=
  ⟨step26_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_1047_222),
    (by decide), (by decide), (by decide), step26_cover⟩

def step27 : Request :=
  ⟨⟨⟨900, 1256, 266, 50764⟩, 21654240231424, 67471047297⟩, 1, 2, 4, 307568⟩

theorem step27_nodes : P1_7_1.nodeRows step27.bank.shape = step27.bank.nodeRows :=
  node_check step27.bank (by decide) (by decide) (by decide)

private theorem step27_2330_2340 : Positive step27 2330 2340 := by decide +kernel

private theorem step27_2341_2371 : Positive step27 2341 2371 := by decide +kernel

private theorem step27_2372_2458 : Positive step27 2372 2458 := by decide +kernel

private theorem step27_2459_2499 : Positive step27 2459 2499 := by decide +kernel

theorem step27_cover : ∃ ends, Cover step27 firstHeight ends := by
  exact ⟨[2340, 2371, 2458, 2499],
    ⟨(by decide), (by decide), step27_2330_2340,
      (by decide), (by decide), step27_2341_2371,
      (by decide), (by decide), step27_2372_2458,
      (by decide), (by decide), step27_2459_2499, rfl⟩⟩

theorem step27_verified : Checked step27 :=
  ⟨step27_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step27_cover⟩

def step28 : Request :=
  ⟨⟨⟨900, 1256, 266, 57109⟩, 21654240231424, 67471047297⟩, 2, 2, 4, 307568⟩

theorem step28_nodes : P1_7_1.nodeRows step28.bank.shape = step28.bank.nodeRows :=
  node_check step28.bank (by decide) (by decide) (by decide)

private theorem step28_2330_2337 : Positive step28 2330 2337 := by decide +kernel

private theorem step28_2338_2360 : Positive step28 2338 2360 := by decide +kernel

private theorem step28_2361_2424 : Positive step28 2361 2424 := by decide +kernel

private theorem step28_2425_2499 : Positive step28 2425 2499 := by decide +kernel

theorem step28_cover : ∃ ends, Cover step28 firstHeight ends := by
  exact ⟨[2337, 2360, 2424, 2499],
    ⟨(by decide), (by decide), step28_2330_2337,
      (by decide), (by decide), step28_2338_2360,
      (by decide), (by decide), step28_2361_2424,
      (by decide), (by decide), step28_2425_2499, rfl⟩⟩

theorem step28_verified : Checked step28 :=
  ⟨step28_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step28_cover⟩

def step29 : Request :=
  ⟨⟨⟨900, 1256, 266, 64247⟩, 21654240231424, 67471047297⟩, 3, 2, 4, 307568⟩

theorem step29_nodes : P1_7_1.nodeRows step29.bank.shape = step29.bank.nodeRows :=
  node_check step29.bank (by decide) (by decide) (by decide)

private theorem step29_2330_2332 : Positive step29 2330 2332 := by decide +kernel

private theorem step29_2333_2341 : Positive step29 2333 2341 := by decide +kernel

private theorem step29_2342_2366 : Positive step29 2342 2366 := by decide +kernel

private theorem step29_2367_2436 : Positive step29 2367 2436 := by decide +kernel

private theorem step29_2437_2499 : Positive step29 2437 2499 := by decide +kernel

theorem step29_cover : ∃ ends, Cover step29 firstHeight ends := by
  exact ⟨[2332, 2341, 2366, 2436, 2499],
    ⟨(by decide), (by decide), step29_2330_2332,
      (by decide), (by decide), step29_2333_2341,
      (by decide), (by decide), step29_2342_2366,
      (by decide), (by decide), step29_2367_2436,
      (by decide), (by decide), step29_2437_2499, rfl⟩⟩

theorem step29_verified : Checked step29 :=
  ⟨step29_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step29_cover⟩

def step30 : Request :=
  ⟨⟨⟨1100, 1535, 326, 64247⟩, 39579969388544, 150663514795⟩, 4, 2, 4, 307568⟩

theorem step30_nodes : P1_7_1.nodeRows step30.bank.shape = step30.bank.nodeRows :=
  node_check step30.bank (by decide) (by decide) (by decide)

private theorem step30_2330_2339 : Positive step30 2330 2339 := by decide +kernel

private theorem step30_2340_2367 : Positive step30 2340 2367 := by decide +kernel

private theorem step30_2368_2444 : Positive step30 2368 2444 := by decide +kernel

private theorem step30_2445_2499 : Positive step30 2445 2499 := by decide +kernel

theorem step30_cover : ∃ ends, Cover step30 firstHeight ends := by
  exact ⟨[2339, 2367, 2444, 2499],
    ⟨(by decide), (by decide), step30_2330_2339,
      (by decide), (by decide), step30_2340_2367,
      (by decide), (by decide), step30_2368_2444,
      (by decide), (by decide), step30_2445_2499, rfl⟩⟩

theorem step30_verified : Checked step30 :=
  ⟨step30_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step30_cover⟩

def step31 : Request :=
  ⟨⟨⟨1220, 1696, 370, 64247⟩, 54930349752320, 229159736517⟩, 5, 2, 4, 307568⟩

theorem step31_nodes : P1_7_1.nodeRows step31.bank.shape = step31.bank.nodeRows :=
  node_check step31.bank (by decide) (by decide) (by decide)

private theorem step31_2330_2330 : Positive step31 2330 2330 := by decide +kernel

private theorem step31_2331_2333 : Positive step31 2331 2333 := by decide +kernel

private theorem step31_2334_2341 : Positive step31 2334 2341 := by decide +kernel

private theorem step31_2342_2362 : Positive step31 2342 2362 := by decide +kernel

private theorem step31_2363_2418 : Positive step31 2363 2418 := by decide +kernel

private theorem step31_2419_2499 : Positive step31 2419 2499 := by decide +kernel

theorem step31_cover : ∃ ends, Cover step31 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2418, 2499],
    ⟨(by decide), (by decide), step31_2330_2330,
      (by decide), (by decide), step31_2331_2333,
      (by decide), (by decide), step31_2334_2341,
      (by decide), (by decide), step31_2342_2362,
      (by decide), (by decide), step31_2363_2418,
      (by decide), (by decide), step31_2419_2499, rfl⟩⟩

theorem step31_verified : Checked step31 :=
  ⟨step31_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_1696_370),
    (by decide), (by decide), (by decide), step31_cover⟩

def step32 : Request :=
  ⟨⟨⟨1350, 1884, 400, 72277⟩, 73092385996800, 341469310532⟩, 7, 2, 4, 307568⟩

theorem step32_nodes : P1_7_1.nodeRows step32.bank.shape = step32.bank.nodeRows :=
  node_check step32.bank (by decide) (by decide) (by decide)

private theorem step32_2330_2330 : Positive step32 2330 2330 := by decide +kernel

private theorem step32_2331_2333 : Positive step32 2331 2333 := by decide +kernel

private theorem step32_2334_2341 : Positive step32 2334 2341 := by decide +kernel

private theorem step32_2342_2363 : Positive step32 2342 2363 := by decide +kernel

private theorem step32_2364_2422 : Positive step32 2364 2422 := by decide +kernel

private theorem step32_2423_2499 : Positive step32 2423 2499 := by decide +kernel

theorem step32_cover : ∃ ends, Cover step32 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2422, 2499],
    ⟨(by decide), (by decide), step32_2330_2330,
      (by decide), (by decide), step32_2331_2333,
      (by decide), (by decide), step32_2334_2341,
      (by decide), (by decide), step32_2342_2363,
      (by decide), (by decide), step32_2364_2422,
      (by decide), (by decide), step32_2423_2499, rfl⟩⟩

theorem step32_verified : Checked step32 :=
  ⟨step32_nodes, Research6966.HelperWindowCatalogue.moment1884_400,
    (by decide), (by decide), (by decide), step32_cover⟩

def step33 : Request :=
  ⟨⟨⟨1644, 2285, 498, 91474⟩, 134156626165760, 753510622290⟩, 10, 2, 4, 307568⟩

theorem step33_nodes : P1_7_1.nodeRows step33.bank.shape = step33.bank.nodeRows :=
  node_check step33.bank (by decide) (by decide) (by decide)

private theorem step33_2330_2341 : Positive step33 2330 2341 := by decide +kernel

private theorem step33_2342_2373 : Positive step33 2342 2373 := by decide +kernel

private theorem step33_2374_2458 : Positive step33 2374 2458 := by decide +kernel

private theorem step33_2459_2499 : Positive step33 2459 2499 := by decide +kernel

theorem step33_cover : ∃ ends, Cover step33 firstHeight ends := by
  exact ⟨[2341, 2373, 2458, 2499],
    ⟨(by decide), (by decide), step33_2330_2341,
      (by decide), (by decide), step33_2342_2373,
      (by decide), (by decide), step33_2374_2458,
      (by decide), (by decide), step33_2459_2499, rfl⟩⟩

theorem step33_verified : Checked step33 :=
  ⟨step33_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_2285_498),
    (by decide), (by decide), (by decide), step33_cover⟩

def step34 : Request :=
  ⟨⟨⟨1927, 2678, 584, 115771⟩, 216034207334400, 1421525065183⟩, 16, 2, 4, 307568⟩

theorem step34_nodes : P1_7_1.nodeRows step34.bank.shape = step34.bank.nodeRows :=
  node_check step34.bank (by decide) (by decide) (by decide)

private theorem step34_2330_2330 : Positive step34 2330 2330 := by decide +kernel

private theorem step34_2331_2332 : Positive step34 2331 2332 := by decide +kernel

private theorem step34_2333_2338 : Positive step34 2333 2338 := by decide +kernel

private theorem step34_2339_2353 : Positive step34 2339 2353 := by decide +kernel

private theorem step34_2354_2393 : Positive step34 2354 2393 := by decide +kernel

private theorem step34_2394_2497 : Positive step34 2394 2497 := by decide +kernel

private theorem step34_2498_2499 : Positive step34 2498 2499 := by decide +kernel

theorem step34_cover : ∃ ends, Cover step34 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2353, 2393, 2497, 2499],
    ⟨(by decide), (by decide), step34_2330_2330,
      (by decide), (by decide), step34_2331_2332,
      (by decide), (by decide), step34_2333_2338,
      (by decide), (by decide), step34_2339_2353,
      (by decide), (by decide), step34_2354_2393,
      (by decide), (by decide), step34_2394_2497,
      (by decide), (by decide), step34_2498_2499, rfl⟩⟩

theorem step34_verified : Checked step34 :=
  ⟨step34_nodes, ((P1_7_1_3.grouped_bound _ _).trans_eq Lower6960.RescueSource.moment_2678_584),
    (by decide), (by decide), (by decide), step34_cover⟩

def step35 : Request :=
  ⟨⟨⟨2000, 2791, 592, 146522⟩, 237206388080640, 1640986809111⟩, 20, 2, 4, 307568⟩

theorem step35_nodes : P1_7_1.nodeRows step35.bank.shape = step35.bank.nodeRows :=
  node_check step35.bank (by decide) (by decide) (by decide)

private theorem step35_2330_2330 : Positive step35 2330 2330 := by decide +kernel

private theorem step35_2331_2333 : Positive step35 2331 2333 := by decide +kernel

private theorem step35_2334_2341 : Positive step35 2334 2341 := by decide +kernel

private theorem step35_2342_2362 : Positive step35 2342 2362 := by decide +kernel

private theorem step35_2363_2418 : Positive step35 2363 2418 := by decide +kernel

private theorem step35_2419_2499 : Positive step35 2419 2499 := by decide +kernel

theorem step35_cover : ∃ ends, Cover step35 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2418, 2499],
    ⟨(by decide), (by decide), step35_2330_2330,
      (by decide), (by decide), step35_2331_2333,
      (by decide), (by decide), step35_2334_2341,
      (by decide), (by decide), step35_2342_2362,
      (by decide), (by decide), step35_2363_2418,
      (by decide), (by decide), step35_2419_2499, rfl⟩⟩

theorem step35_verified : Checked step35 :=
  ⟨step35_nodes, Research6966.HelperWindowCatalogue.moment2791_592,
    (by decide), (by decide), (by decide), step35_cover⟩

def step36 : Request :=
  ⟨⟨⟨3500, 4886, 1057, 164837⟩, 1289556817346560, 15631374615265⟩, 31, 2, 4, 307568⟩

theorem step36_nodes : P1_7_1.nodeRows step36.bank.shape = step36.bank.nodeRows :=
  node_check step36.bank (by decide) (by decide) (by decide)

private theorem step36_2330_2331 : Positive step36 2330 2331 := by decide +kernel

private theorem step36_2332_2336 : Positive step36 2332 2336 := by decide +kernel

private theorem step36_2337_2349 : Positive step36 2337 2349 := by decide +kernel

private theorem step36_2350_2382 : Positive step36 2350 2382 := by decide +kernel

private theorem step36_2383_2468 : Positive step36 2383 2468 := by decide +kernel

private theorem step36_2469_2499 : Positive step36 2469 2499 := by decide +kernel

theorem step36_cover : ∃ ends, Cover step36 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2382, 2468, 2499],
    ⟨(by decide), (by decide), step36_2330_2331,
      (by decide), (by decide), step36_2332_2336,
      (by decide), (by decide), step36_2337_2349,
      (by decide), (by decide), step36_2350_2382,
      (by decide), (by decide), step36_2383_2468,
      (by decide), (by decide), step36_2469_2499, rfl⟩⟩

theorem step36_verified : Checked step36 :=
  ⟨step36_nodes, Research6966.HelperWindowCatalogue.moment4886_1057,
    (by decide), (by decide), (by decide), step36_cover⟩

def step37 : Request :=
  ⟨⟨⟨3000, 4187, 906, 185441⟩, 812266433019904, 8433369009268⟩, 32, 2, 4, 307568⟩

theorem step37_nodes : P1_7_1.nodeRows step37.bank.shape = step37.bank.nodeRows :=
  node_check step37.bank (by decide) (by decide) (by decide)

private theorem step37_2330_2331 : Positive step37 2330 2331 := by decide +kernel

private theorem step37_2332_2336 : Positive step37 2332 2336 := by decide +kernel

private theorem step37_2337_2349 : Positive step37 2337 2349 := by decide +kernel

private theorem step37_2350_2383 : Positive step37 2350 2383 := by decide +kernel

private theorem step37_2384_2472 : Positive step37 2384 2472 := by decide +kernel

private theorem step37_2473_2499 : Positive step37 2473 2499 := by decide +kernel

theorem step37_cover : ∃ ends, Cover step37 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2472, 2499],
    ⟨(by decide), (by decide), step37_2330_2331,
      (by decide), (by decide), step37_2332_2336,
      (by decide), (by decide), step37_2337_2349,
      (by decide), (by decide), step37_2350_2383,
      (by decide), (by decide), step37_2384_2472,
      (by decide), (by decide), step37_2473_2499, rfl⟩⟩

theorem step37_verified : Checked step37 :=
  ⟨step37_nodes, Research6966.HelperWindowCatalogue.moment4187_906,
    (by decide), (by decide), (by decide), step37_cover⟩

def step38 : Request :=
  ⟨⟨⟨3500, 4885, 1057, 264035⟩, 1289556817346560, 15621081034380⟩, 44, 2, 4, 307568⟩

theorem step38_nodes : P1_7_1.nodeRows step38.bank.shape = step38.bank.nodeRows :=
  node_check step38.bank (by decide) (by decide) (by decide)

private theorem step38_2330_2330 : Positive step38 2330 2330 := by decide +kernel

private theorem step38_2331_2333 : Positive step38 2331 2333 := by decide +kernel

private theorem step38_2334_2341 : Positive step38 2334 2341 := by decide +kernel

private theorem step38_2342_2361 : Positive step38 2342 2361 := by decide +kernel

private theorem step38_2362_2413 : Positive step38 2362 2413 := by decide +kernel

private theorem step38_2414_2499 : Positive step38 2414 2499 := by decide +kernel

theorem step38_cover : ∃ ends, Cover step38 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2361, 2413, 2499],
    ⟨(by decide), (by decide), step38_2330_2330,
      (by decide), (by decide), step38_2331_2333,
      (by decide), (by decide), step38_2334_2341,
      (by decide), (by decide), step38_2342_2361,
      (by decide), (by decide), step38_2362_2413,
      (by decide), (by decide), step38_2414_2499, rfl⟩⟩

theorem step38_verified : Checked step38 :=
  ⟨step38_nodes, Research6966.HelperWindowCatalogue.moment4885_1057,
    (by decide), (by decide), (by decide), step38_cover⟩

def step39 : Request :=
  ⟨⟨⟨900, 1256, 272, 31694⟩, 22024701870080, 68653176066⟩, 0, 2, 9, 305624⟩

theorem step39_nodes : P1_7_1.nodeRows step39.bank.shape = step39.bank.nodeRows :=
  node_check step39.bank (by decide) (by decide) (by decide)

private theorem step39_2330_2331 : Positive step39 2330 2331 := by decide +kernel

private theorem step39_2332_2336 : Positive step39 2332 2336 := by decide +kernel

private theorem step39_2337_2350 : Positive step39 2337 2350 := by decide +kernel

private theorem step39_2351_2388 : Positive step39 2351 2388 := by decide +kernel

private theorem step39_2389_2493 : Positive step39 2389 2493 := by decide +kernel

private theorem step39_2494_2499 : Positive step39 2494 2499 := by decide +kernel

theorem step39_cover : ∃ ends, Cover step39 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2388, 2493, 2499],
    ⟨(by decide), (by decide), step39_2330_2331,
      (by decide), (by decide), step39_2332_2336,
      (by decide), (by decide), step39_2337_2350,
      (by decide), (by decide), step39_2351_2388,
      (by decide), (by decide), step39_2389_2493,
      (by decide), (by decide), step39_2494_2499, rfl⟩⟩

theorem step39_verified : Checked step39 :=
  ⟨step39_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step39_cover⟩

def step40 : Request :=
  ⟨⟨⟨900, 1256, 272, 35655⟩, 22024701870080, 68653176066⟩, 1, 2, 9, 305624⟩

theorem step40_nodes : P1_7_1.nodeRows step40.bank.shape = step40.bank.nodeRows :=
  node_check step40.bank (by decide) (by decide) (by decide)

private theorem step40_2330_2331 : Positive step40 2330 2331 := by decide +kernel

private theorem step40_2332_2336 : Positive step40 2332 2336 := by decide +kernel

private theorem step40_2337_2350 : Positive step40 2337 2350 := by decide +kernel

private theorem step40_2351_2388 : Positive step40 2351 2388 := by decide +kernel

private theorem step40_2389_2493 : Positive step40 2389 2493 := by decide +kernel

private theorem step40_2494_2499 : Positive step40 2494 2499 := by decide +kernel

theorem step40_cover : ∃ ends, Cover step40 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2388, 2493, 2499],
    ⟨(by decide), (by decide), step40_2330_2331,
      (by decide), (by decide), step40_2332_2336,
      (by decide), (by decide), step40_2337_2350,
      (by decide), (by decide), step40_2351_2388,
      (by decide), (by decide), step40_2389_2493,
      (by decide), (by decide), step40_2494_2499, rfl⟩⟩

theorem step40_verified : Checked step40 :=
  ⟨step40_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step40_cover⟩

end Research6966.HelperRescueCatalogue
