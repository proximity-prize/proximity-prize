import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments11
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments7
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments9
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step192 : Request :=
  ⟨⟨⟨2500, 3489, 755, 50764⟩, 470210689105920, 4068029992867⟩, 32, 3, 16, 385715⟩

theorem step192_nodes : P1_7_1.nodeRows step192.bank.shape = step192.bank.nodeRows :=
  node_check step192.bank (by decide) (by decide) (by decide)

private theorem step192_2330_2340 : Positive step192 2330 2340 := by decide +kernel

private theorem step192_2341_2369 : Positive step192 2341 2369 := by decide +kernel

private theorem step192_2370_2445 : Positive step192 2370 2445 := by decide +kernel

private theorem step192_2446_2499 : Positive step192 2446 2499 := by decide +kernel

theorem step192_cover : ∃ ends, Cover step192 firstHeight ends := by
  exact ⟨[2340, 2369, 2445, 2499],
    ⟨(by decide), (by decide), step192_2330_2340,
      (by decide), (by decide), step192_2341_2369,
      (by decide), (by decide), step192_2370_2445,
      (by decide), (by decide), step192_2446_2499, rfl⟩⟩

theorem step192_verified : Checked step192 :=
  ⟨step192_nodes, Research6966.HelperWindowCatalogue.moment3489_755,
    (by decide), (by decide), (by decide), step192_cover⟩

def step193 : Request :=
  ⟨⟨⟨3000, 4187, 906, 64247⟩, 812266433019904, 8433369009268⟩, 44, 3, 16, 385715⟩

theorem step193_nodes : P1_7_1.nodeRows step193.bank.shape = step193.bank.nodeRows :=
  node_check step193.bank (by decide) (by decide) (by decide)

private theorem step193_2330_2331 : Positive step193 2330 2331 := by decide +kernel

private theorem step193_2332_2337 : Positive step193 2332 2337 := by decide +kernel

private theorem step193_2338_2352 : Positive step193 2338 2352 := by decide +kernel

private theorem step193_2353_2392 : Positive step193 2353 2392 := by decide +kernel

private theorem step193_2393_2496 : Positive step193 2393 2496 := by decide +kernel

private theorem step193_2497_2499 : Positive step193 2497 2499 := by decide +kernel

theorem step193_cover : ∃ ends, Cover step193 firstHeight ends := by
  exact ⟨[2331, 2337, 2352, 2392, 2496, 2499],
    ⟨(by decide), (by decide), step193_2330_2331,
      (by decide), (by decide), step193_2332_2337,
      (by decide), (by decide), step193_2338_2352,
      (by decide), (by decide), step193_2353_2392,
      (by decide), (by decide), step193_2393_2496,
      (by decide), (by decide), step193_2497_2499, rfl⟩⟩

theorem step193_verified : Checked step193 :=
  ⟨step193_nodes, Research6966.HelperWindowCatalogue.moment4187_906,
    (by decide), (by decide), (by decide), step193_cover⟩

def step194 : Request :=
  ⟨⟨⟨420, 586, 130, 6096⟩, 2292767784960, 3339653140⟩, 0, 3, 26, 385715⟩

theorem step194_nodes : P1_7_1.nodeRows step194.bank.shape = step194.bank.nodeRows :=
  node_check step194.bank (by decide) (by decide) (by decide)

private theorem step194_2330_2331 : Positive step194 2330 2331 := by decide +kernel

private theorem step194_2332_2337 : Positive step194 2332 2337 := by decide +kernel

private theorem step194_2338_2356 : Positive step194 2338 2356 := by decide +kernel

private theorem step194_2357_2414 : Positive step194 2357 2414 := by decide +kernel

private theorem step194_2415_2499 : Positive step194 2415 2499 := by decide +kernel

theorem step194_cover : ∃ ends, Cover step194 firstHeight ends := by
  exact ⟨[2331, 2337, 2356, 2414, 2499],
    ⟨(by decide), (by decide), step194_2330_2331,
      (by decide), (by decide), step194_2332_2337,
      (by decide), (by decide), step194_2338_2356,
      (by decide), (by decide), step194_2357_2414,
      (by decide), (by decide), step194_2415_2499, rfl⟩⟩

theorem step194_verified : Checked step194 :=
  ⟨step194_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step194_cover⟩

def step195 : Request :=
  ⟨⟨⟨520, 726, 161, 6096⟩, 4343013310464, 7844248211⟩, 1, 3, 26, 385715⟩

theorem step195_nodes : P1_7_1.nodeRows step195.bank.shape = step195.bank.nodeRows :=
  node_check step195.bank (by decide) (by decide) (by decide)

private theorem step195_2330_2338 : Positive step195 2330 2338 := by decide +kernel

private theorem step195_2339_2365 : Positive step195 2339 2365 := by decide +kernel

private theorem step195_2366_2444 : Positive step195 2366 2444 := by decide +kernel

private theorem step195_2445_2499 : Positive step195 2445 2499 := by decide +kernel

theorem step195_cover : ∃ ends, Cover step195 firstHeight ends := by
  exact ⟨[2338, 2365, 2444, 2499],
    ⟨(by decide), (by decide), step195_2330_2338,
      (by decide), (by decide), step195_2339_2365,
      (by decide), (by decide), step195_2366_2444,
      (by decide), (by decide), step195_2445_2499, rfl⟩⟩

theorem step195_verified : Checked step195 :=
  ⟨step195_nodes, Research6966.HelperWindowCatalogue.moment726_161,
    (by decide), (by decide), (by decide), step195_cover⟩

def step196 : Request :=
  ⟨⟨⟨520, 726, 161, 6858⟩, 4343013310464, 7844248211⟩, 2, 3, 26, 385715⟩

theorem step196_nodes : P1_7_1.nodeRows step196.bank.shape = step196.bank.nodeRows :=
  node_check step196.bank (by decide) (by decide) (by decide)

private theorem step196_2330_2330 : Positive step196 2330 2330 := by decide +kernel

private theorem step196_2331_2333 : Positive step196 2331 2333 := by decide +kernel

private theorem step196_2334_2341 : Positive step196 2334 2341 := by decide +kernel

private theorem step196_2342_2365 : Positive step196 2342 2365 := by decide +kernel

private theorem step196_2366_2435 : Positive step196 2366 2435 := by decide +kernel

private theorem step196_2436_2499 : Positive step196 2436 2499 := by decide +kernel

theorem step196_cover : ∃ ends, Cover step196 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2365, 2435, 2499],
    ⟨(by decide), (by decide), step196_2330_2330,
      (by decide), (by decide), step196_2331_2333,
      (by decide), (by decide), step196_2334_2341,
      (by decide), (by decide), step196_2342_2365,
      (by decide), (by decide), step196_2366_2435,
      (by decide), (by decide), step196_2436_2499, rfl⟩⟩

theorem step196_verified : Checked step196 :=
  ⟨step196_nodes, Research6966.HelperWindowCatalogue.moment726_161,
    (by decide), (by decide), (by decide), step196_cover⟩

def step197 : Request :=
  ⟨⟨⟨630, 879, 195, 6858⟩, 7709474160640, 16827402390⟩, 3, 3, 26, 385715⟩

theorem step197_nodes : P1_7_1.nodeRows step197.bank.shape = step197.bank.nodeRows :=
  node_check step197.bank (by decide) (by decide) (by decide)

private theorem step197_2330_2332 : Positive step197 2330 2332 := by decide +kernel

private theorem step197_2333_2341 : Positive step197 2333 2341 := by decide +kernel

private theorem step197_2342_2367 : Positive step197 2342 2367 := by decide +kernel

private theorem step197_2368_2441 : Positive step197 2368 2441 := by decide +kernel

private theorem step197_2442_2499 : Positive step197 2442 2499 := by decide +kernel

theorem step197_cover : ∃ ends, Cover step197 firstHeight ends := by
  exact ⟨[2332, 2341, 2367, 2441, 2499],
    ⟨(by decide), (by decide), step197_2330_2332,
      (by decide), (by decide), step197_2333_2341,
      (by decide), (by decide), step197_2342_2367,
      (by decide), (by decide), step197_2368_2441,
      (by decide), (by decide), step197_2442_2499, rfl⟩⟩

theorem step197_verified : Checked step197 :=
  ⟨step197_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step197_cover⟩

def step198 : Request :=
  ⟨⟨⟨630, 879, 195, 7715⟩, 7709474160640, 16827402390⟩, 4, 3, 26, 385715⟩

theorem step198_nodes : P1_7_1.nodeRows step198.bank.shape = step198.bank.nodeRows :=
  node_check step198.bank (by decide) (by decide) (by decide)

private theorem step198_2330_2334 : Positive step198 2330 2334 := by decide +kernel

private theorem step198_2335_2348 : Positive step198 2335 2348 := by decide +kernel

private theorem step198_2349_2388 : Positive step198 2349 2388 := by decide +kernel

private theorem step198_2389_2499 : Positive step198 2389 2499 := by decide +kernel

theorem step198_cover : ∃ ends, Cover step198 firstHeight ends := by
  exact ⟨[2334, 2348, 2388, 2499],
    ⟨(by decide), (by decide), step198_2330_2334,
      (by decide), (by decide), step198_2335_2348,
      (by decide), (by decide), step198_2349_2388,
      (by decide), (by decide), step198_2389_2499, rfl⟩⟩

theorem step198_verified : Checked step198 :=
  ⟨step198_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step198_cover⟩

def step199 : Request :=
  ⟨⟨⟨630, 879, 190, 9763⟩, 7559493713920, 16491913877⟩, 5, 3, 26, 385715⟩

theorem step199_nodes : P1_7_1.nodeRows step199.bank.shape = step199.bank.nodeRows :=
  node_check step199.bank (by decide) (by decide) (by decide)

private theorem step199_2330_2337 : Positive step199 2330 2337 := by decide +kernel

private theorem step199_2338_2360 : Positive step199 2338 2360 := by decide +kernel

private theorem step199_2361_2426 : Positive step199 2361 2426 := by decide +kernel

private theorem step199_2427_2499 : Positive step199 2427 2499 := by decide +kernel

theorem step199_cover : ∃ ends, Cover step199 firstHeight ends := by
  exact ⟨[2337, 2360, 2426, 2499],
    ⟨(by decide), (by decide), step199_2330_2337,
      (by decide), (by decide), step199_2338_2360,
      (by decide), (by decide), step199_2361_2426,
      (by decide), (by decide), step199_2427_2499, rfl⟩⟩

theorem step199_verified : Checked step199 :=
  ⟨step199_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step199_cover⟩

def step200 : Request :=
  ⟨⟨⟨750, 1047, 232, 9763⟩, 12985818152960, 33790833671⟩, 7, 3, 26, 385715⟩

theorem step200_nodes : P1_7_1.nodeRows step200.bank.shape = step200.bank.nodeRows :=
  node_check step200.bank (by decide) (by decide) (by decide)

private theorem step200_2330_2338 : Positive step200 2330 2338 := by decide +kernel

private theorem step200_2339_2364 : Positive step200 2339 2364 := by decide +kernel

private theorem step200_2365_2437 : Positive step200 2365 2437 := by decide +kernel

private theorem step200_2438_2499 : Positive step200 2438 2499 := by decide +kernel

theorem step200_cover : ∃ ends, Cover step200 firstHeight ends := by
  exact ⟨[2338, 2364, 2437, 2499],
    ⟨(by decide), (by decide), step200_2330_2338,
      (by decide), (by decide), step200_2339_2364,
      (by decide), (by decide), step200_2365_2437,
      (by decide), (by decide), step200_2438_2499, rfl⟩⟩

theorem step200_verified : Checked step200 :=
  ⟨step200_nodes, Research6966.HelperWindowCatalogue.moment1047_232,
    (by decide), (by decide), (by decide), step200_cover⟩

def step201 : Request :=
  ⟨⟨⟨900, 1256, 279, 10983⟩, 22452680785920, 70021105933⟩, 10, 3, 26, 385715⟩

theorem step201_nodes : P1_7_1.nodeRows step201.bank.shape = step201.bank.nodeRows :=
  node_check step201.bank (by decide) (by decide) (by decide)

private theorem step201_2330_2335 : Positive step201 2330 2335 := by decide +kernel

private theorem step201_2336_2352 : Positive step201 2336 2352 := by decide +kernel

private theorem step201_2353_2399 : Positive step201 2353 2399 := by decide +kernel

private theorem step201_2400_2499 : Positive step201 2400 2499 := by decide +kernel

theorem step201_cover : ∃ ends, Cover step201 firstHeight ends := by
  exact ⟨[2335, 2352, 2399, 2499],
    ⟨(by decide), (by decide), step201_2330_2335,
      (by decide), (by decide), step201_2336_2352,
      (by decide), (by decide), step201_2353_2399,
      (by decide), (by decide), step201_2400_2499, rfl⟩⟩

theorem step201_verified : Checked step201 :=
  ⟨step201_nodes, Research6966.HelperWindowCatalogue.moment1256_279,
    (by decide), (by decide), (by decide), step201_cover⟩

def step202 : Request :=
  ⟨⟨⟨1100, 1535, 332, 15636⟩, 40133103452160, 152819743367⟩, 16, 3, 26, 385715⟩

theorem step202_nodes : P1_7_1.nodeRows step202.bank.shape = step202.bank.nodeRows :=
  node_check step202.bank (by decide) (by decide) (by decide)

private theorem step202_2330_2330 : Positive step202 2330 2330 := by decide +kernel

private theorem step202_2331_2332 : Positive step202 2331 2332 := by decide +kernel

private theorem step202_2333_2338 : Positive step202 2333 2338 := by decide +kernel

private theorem step202_2339_2354 : Positive step202 2339 2354 := by decide +kernel

private theorem step202_2355_2398 : Positive step202 2355 2398 := by decide +kernel

private theorem step202_2399_2499 : Positive step202 2399 2499 := by decide +kernel

theorem step202_cover : ∃ ends, Cover step202 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2354, 2398, 2499],
    ⟨(by decide), (by decide), step202_2330_2330,
      (by decide), (by decide), step202_2331_2332,
      (by decide), (by decide), step202_2333_2338,
      (by decide), (by decide), step202_2339_2354,
      (by decide), (by decide), step202_2355_2398,
      (by decide), (by decide), step202_2399_2499, rfl⟩⟩

theorem step202_verified : Checked step202 :=
  ⟨step202_nodes, Research6966.HelperWindowCatalogue.moment1535_332,
    (by decide), (by decide), (by decide), step202_cover⟩

def step203 : Request :=
  ⟨⟨⟨1350, 1884, 408, 17590⟩, 74202776600576, 346781832878⟩, 20, 3, 26, 385715⟩

theorem step203_nodes : P1_7_1.nodeRows step203.bank.shape = step203.bank.nodeRows :=
  node_check step203.bank (by decide) (by decide) (by decide)

private theorem step203_2330_2339 : Positive step203 2330 2339 := by decide +kernel

private theorem step203_2340_2366 : Positive step203 2340 2366 := by decide +kernel

private theorem step203_2367_2439 : Positive step203 2367 2439 := by decide +kernel

private theorem step203_2440_2499 : Positive step203 2440 2499 := by decide +kernel

theorem step203_cover : ∃ ends, Cover step203 firstHeight ends := by
  exact ⟨[2339, 2366, 2439, 2499],
    ⟨(by decide), (by decide), step203_2330_2339,
      (by decide), (by decide), step203_2340_2366,
      (by decide), (by decide), step203_2367_2439,
      (by decide), (by decide), step203_2440_2499, rfl⟩⟩

theorem step203_verified : Checked step203 :=
  ⟨step203_nodes, Research6966.HelperWindowCatalogue.moment1884_408,
    (by decide), (by decide), (by decide), step203_cover⟩

def step204 : Request :=
  ⟨⟨⟨1650, 2302, 512, 25043⟩, 138129879859200, 788519769358⟩, 31, 3, 26, 385715⟩

theorem step204_nodes : P1_7_1.nodeRows step204.bank.shape = step204.bank.nodeRows :=
  node_check step204.bank (by decide) (by decide) (by decide)

private theorem step204_2330_2332 : Positive step204 2330 2332 := by decide +kernel

private theorem step204_2333_2340 : Positive step204 2333 2340 := by decide +kernel

private theorem step204_2341_2361 : Positive step204 2341 2361 := by decide +kernel

private theorem step204_2362_2417 : Positive step204 2362 2417 := by decide +kernel

private theorem step204_2418_2499 : Positive step204 2418 2499 := by decide +kernel

theorem step204_cover : ∃ ends, Cover step204 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2417, 2499],
    ⟨(by decide), (by decide), step204_2330_2332,
      (by decide), (by decide), step204_2333_2340,
      (by decide), (by decide), step204_2341_2361,
      (by decide), (by decide), step204_2362_2417,
      (by decide), (by decide), step204_2418_2499, rfl⟩⟩

theorem step204_verified : Checked step204 :=
  ⟨step204_nodes, Research6966.HelperWindowCatalogue.moment2302_512,
    (by decide), (by decide), (by decide), step204_cover⟩

def step205 : Request :=
  ⟨⟨⟨2000, 2791, 620, 22261⟩, 245690786119680, 1701147081935⟩, 32, 3, 26, 385715⟩

theorem step205_nodes : P1_7_1.nodeRows step205.bank.shape = step205.bank.nodeRows :=
  node_check step205.bank (by decide) (by decide) (by decide)

private theorem step205_2330_2339 : Positive step205 2330 2339 := by decide +kernel

private theorem step205_2340_2365 : Positive step205 2340 2365 := by decide +kernel

private theorem step205_2366_2434 : Positive step205 2366 2434 := by decide +kernel

private theorem step205_2435_2499 : Positive step205 2435 2499 := by decide +kernel

theorem step205_cover : ∃ ends, Cover step205 firstHeight ends := by
  exact ⟨[2339, 2365, 2434, 2499],
    ⟨(by decide), (by decide), step205_2330_2339,
      (by decide), (by decide), step205_2340_2365,
      (by decide), (by decide), step205_2366_2434,
      (by decide), (by decide), step205_2435_2499, rfl⟩⟩

theorem step205_verified : Checked step205 :=
  ⟨step205_nodes, Research6966.HelperWindowCatalogue.moment2791_620,
    (by decide), (by decide), (by decide), step205_cover⟩

def step206 : Request :=
  ⟨⟨⟨2500, 3489, 775, 28173⟩, 479640131993600, 4151672878537⟩, 44, 3, 26, 385715⟩

theorem step206_nodes : P1_7_1.nodeRows step206.bank.shape = step206.bank.nodeRows :=
  node_check step206.bank (by decide) (by decide) (by decide)

private theorem step206_2330_2332 : Positive step206 2330 2332 := by decide +kernel

private theorem step206_2333_2340 : Positive step206 2333 2340 := by decide +kernel

private theorem step206_2341_2361 : Positive step206 2341 2361 := by decide +kernel

private theorem step206_2362_2416 : Positive step206 2362 2416 := by decide +kernel

private theorem step206_2417_2499 : Positive step206 2417 2499 := by decide +kernel

theorem step206_cover : ∃ ends, Cover step206 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2416, 2499],
    ⟨(by decide), (by decide), step206_2330_2332,
      (by decide), (by decide), step206_2333_2340,
      (by decide), (by decide), step206_2341_2361,
      (by decide), (by decide), step206_2362_2416,
      (by decide), (by decide), step206_2417_2499, rfl⟩⟩

theorem step206_verified : Checked step206 :=
  ⟨step206_nodes, Research6966.HelperWindowCatalogue.moment3489_775,
    (by decide), (by decide), (by decide), step206_cover⟩

def step207 : Request :=
  ⟨⟨⟨3500, 4884, 1057, 50764⟩, 1289556817346560, 15610792063730⟩, 73, 3, 26, 385715⟩

theorem step207_nodes : P1_7_1.nodeRows step207.bank.shape = step207.bank.nodeRows :=
  node_check step207.bank (by decide) (by decide) (by decide)

private theorem step207_2330_2335 : Positive step207 2330 2335 := by decide +kernel

private theorem step207_2336_2351 : Positive step207 2336 2351 := by decide +kernel

private theorem step207_2352_2393 : Positive step207 2352 2393 := by decide +kernel

private theorem step207_2394_2499 : Positive step207 2394 2499 := by decide +kernel

theorem step207_cover : ∃ ends, Cover step207 firstHeight ends := by
  exact ⟨[2335, 2351, 2393, 2499],
    ⟨(by decide), (by decide), step207_2330_2335,
      (by decide), (by decide), step207_2336_2351,
      (by decide), (by decide), step207_2352_2393,
      (by decide), (by decide), step207_2394_2499, rfl⟩⟩

theorem step207_verified : Checked step207 :=
  ⟨step207_nodes, Research6966.HelperWindowCatalogue.moment4884_1057,
    (by decide), (by decide), (by decide), step207_cover⟩

def step208 : Request :=
  ⟨⟨⟨3500, 4884, 1085, 50764⟩, 1315428062986240, 15931892384151⟩, 76, 3, 26, 385715⟩

theorem step208_nodes : P1_7_1.nodeRows step208.bank.shape = step208.bank.nodeRows :=
  node_check step208.bank (by decide) (by decide) (by decide)

private theorem step208_2330_2332 : Positive step208 2330 2332 := by decide +kernel

private theorem step208_2333_2340 : Positive step208 2333 2340 := by decide +kernel

private theorem step208_2341_2361 : Positive step208 2341 2361 := by decide +kernel

private theorem step208_2362_2415 : Positive step208 2362 2415 := by decide +kernel

private theorem step208_2416_2499 : Positive step208 2416 2499 := by decide +kernel

theorem step208_cover : ∃ ends, Cover step208 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2415, 2499],
    ⟨(by decide), (by decide), step208_2330_2332,
      (by decide), (by decide), step208_2333_2340,
      (by decide), (by decide), step208_2341_2361,
      (by decide), (by decide), step208_2362_2415,
      (by decide), (by decide), step208_2416_2499, rfl⟩⟩

theorem step208_verified : Checked step208 :=
  ⟨step208_nodes, Research6966.HelperWindowCatalogue.moment4884_1085,
    (by decide), (by decide), (by decide), step208_cover⟩

def step209 : Request :=
  ⟨⟨⟨4500, 6279, 1395, 72277⟩, 2794932370145280, 43509614052359⟩, 103, 3, 26, 385715⟩

theorem step209_nodes : P1_7_1.nodeRows step209.bank.shape = step209.bank.nodeRows :=
  node_check step209.bank (by decide) (by decide) (by decide)

private theorem step209_2330_2337 : Positive step209 2330 2337 := by decide +kernel

private theorem step209_2338_2357 : Positive step209 2338 2357 := by decide +kernel

private theorem step209_2358_2409 : Positive step209 2358 2409 := by decide +kernel

private theorem step209_2410_2499 : Positive step209 2410 2499 := by decide +kernel

theorem step209_cover : ∃ ends, Cover step209 firstHeight ends := by
  exact ⟨[2337, 2357, 2409, 2499],
    ⟨(by decide), (by decide), step209_2330_2337,
      (by decide), (by decide), step209_2338_2357,
      (by decide), (by decide), step209_2358_2409,
      (by decide), (by decide), step209_2410_2499, rfl⟩⟩

theorem step209_verified : Checked step209 :=
  ⟨step209_nodes, Research6966.HelperWindowCatalogue.moment6279_1395,
    (by decide), (by decide), (by decide), step209_cover⟩

def step210 : Request :=
  ⟨⟨⟨294, 410, 91, 2674⟩, 790165454848, 805457011⟩, 0, 3, 41, 385715⟩

theorem step210_nodes : P1_7_1.nodeRows step210.bank.shape = step210.bank.nodeRows :=
  node_check step210.bank (by decide) (by decide) (by decide)

private theorem step210_2330_2338 : Positive step210 2330 2338 := by decide +kernel

private theorem step210_2339_2369 : Positive step210 2339 2369 := by decide +kernel

private theorem step210_2370_2473 : Positive step210 2370 2473 := by decide +kernel

private theorem step210_2474_2499 : Positive step210 2474 2499 := by decide +kernel

theorem step210_cover : ∃ ends, Cover step210 firstHeight ends := by
  exact ⟨[2338, 2369, 2473, 2499],
    ⟨(by decide), (by decide), step210_2330_2338,
      (by decide), (by decide), step210_2339_2369,
      (by decide), (by decide), step210_2370_2473,
      (by decide), (by decide), step210_2474_2499, rfl⟩⟩

theorem step210_verified : Checked step210 :=
  ⟨step210_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step210_cover⟩

def step211 : Request :=
  ⟨⟨⟨294, 410, 91, 3384⟩, 790165454848, 805457011⟩, 1, 3, 41, 385715⟩

theorem step211_nodes : P1_7_1.nodeRows step211.bank.shape = step211.bank.nodeRows :=
  node_check step211.bank (by decide) (by decide) (by decide)

private theorem step211_2330_2343 : Positive step211 2330 2343 := by decide +kernel

private theorem step211_2344_2390 : Positive step211 2344 2390 := by decide +kernel

private theorem step211_2391_2499 : Positive step211 2391 2499 := by decide +kernel

theorem step211_cover : ∃ ends, Cover step211 firstHeight ends := by
  exact ⟨[2343, 2390, 2499],
    ⟨(by decide), (by decide), step211_2330_2343,
      (by decide), (by decide), step211_2344_2390,
      (by decide), (by decide), step211_2391_2499, rfl⟩⟩

theorem step211_verified : Checked step211 :=
  ⟨step211_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step211_cover⟩

def step212 : Request :=
  ⟨⟨⟨350, 488, 106, 3384⟩, 1308168290304, 1584729438⟩, 2, 3, 41, 385715⟩

theorem step212_nodes : P1_7_1.nodeRows step212.bank.shape = step212.bank.nodeRows :=
  node_check step212.bank (by decide) (by decide) (by decide)

private theorem step212_2330_2344 : Positive step212 2330 2344 := by decide +kernel

private theorem step212_2345_2392 : Positive step212 2345 2392 := by decide +kernel

private theorem step212_2393_2499 : Positive step212 2393 2499 := by decide +kernel

theorem step212_cover : ∃ ends, Cover step212 firstHeight ends := by
  exact ⟨[2344, 2392, 2499],
    ⟨(by decide), (by decide), step212_2330_2344,
      (by decide), (by decide), step212_2345_2392,
      (by decide), (by decide), step212_2393_2499, rfl⟩⟩

theorem step212_verified : Checked step212 :=
  ⟨step212_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step212_cover⟩

def step213 : Request :=
  ⟨⟨⟨350, 488, 108, 3807⟩, 1326705278976, 1607754763⟩, 3, 3, 41, 385715⟩

theorem step213_nodes : P1_7_1.nodeRows step213.bank.shape = step213.bank.nodeRows :=
  node_check step213.bank (by decide) (by decide) (by decide)

private theorem step213_2330_2339 : Positive step213 2330 2339 := by decide +kernel

private theorem step213_2340_2371 : Positive step213 2340 2371 := by decide +kernel

private theorem step213_2372_2474 : Positive step213 2372 2474 := by decide +kernel

private theorem step213_2475_2499 : Positive step213 2475 2499 := by decide +kernel

theorem step213_cover : ∃ ends, Cover step213 firstHeight ends := by
  exact ⟨[2339, 2371, 2474, 2499],
    ⟨(by decide), (by decide), step213_2330_2339,
      (by decide), (by decide), step213_2340_2371,
      (by decide), (by decide), step213_2372_2474,
      (by decide), (by decide), step213_2475_2499, rfl⟩⟩

theorem step213_verified : Checked step213 :=
  ⟨step213_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step213_cover⟩

def step214 : Request :=
  ⟨⟨⟨420, 586, 127, 3807⟩, 2252760678400, 3279920952⟩, 4, 3, 41, 385715⟩

theorem step214_nodes : P1_7_1.nodeRows step214.bank.shape = step214.bank.nodeRows :=
  node_check step214.bank (by decide) (by decide) (by decide)

private theorem step214_2330_2333 : Positive step214 2330 2333 := by decide +kernel

private theorem step214_2334_2345 : Positive step214 2334 2345 := by decide +kernel

private theorem step214_2346_2382 : Positive step214 2346 2382 := by decide +kernel

private theorem step214_2383_2496 : Positive step214 2383 2496 := by decide +kernel

private theorem step214_2497_2499 : Positive step214 2497 2499 := by decide +kernel

theorem step214_cover : ∃ ends, Cover step214 firstHeight ends := by
  exact ⟨[2333, 2345, 2382, 2496, 2499],
    ⟨(by decide), (by decide), step214_2330_2333,
      (by decide), (by decide), step214_2334_2345,
      (by decide), (by decide), step214_2346_2382,
      (by decide), (by decide), step214_2383_2496,
      (by decide), (by decide), step214_2497_2499, rfl⟩⟩

theorem step214_verified : Checked step214 :=
  ⟨step214_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step214_cover⟩

def step215 : Request :=
  ⟨⟨⟨420, 586, 127, 4282⟩, 2252760678400, 3279920952⟩, 5, 3, 41, 385715⟩

theorem step215_nodes : P1_7_1.nodeRows step215.bank.shape = step215.bank.nodeRows :=
  node_check step215.bank (by decide) (by decide) (by decide)

private theorem step215_2330_2331 : Positive step215 2330 2331 := by decide +kernel

private theorem step215_2332_2338 : Positive step215 2332 2338 := by decide +kernel

private theorem step215_2339_2359 : Positive step215 2339 2359 := by decide +kernel

private theorem step215_2360_2424 : Positive step215 2360 2424 := by decide +kernel

private theorem step215_2425_2499 : Positive step215 2425 2499 := by decide +kernel

theorem step215_cover : ∃ ends, Cover step215 firstHeight ends := by
  exact ⟨[2331, 2338, 2359, 2424, 2499],
    ⟨(by decide), (by decide), step215_2330_2331,
      (by decide), (by decide), step215_2332_2338,
      (by decide), (by decide), step215_2339_2359,
      (by decide), (by decide), step215_2360_2424,
      (by decide), (by decide), step215_2425_2499, rfl⟩⟩

theorem step215_verified : Checked step215 :=
  ⟨step215_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step215_cover⟩

def step216 : Request :=
  ⟨⟨⟨520, 725, 157, 4817⟩, 4261264752640, 7658911630⟩, 7, 3, 41, 385715⟩

theorem step216_nodes : P1_7_1.nodeRows step216.bank.shape = step216.bank.nodeRows :=
  node_check step216.bank (by decide) (by decide) (by decide)

private theorem step216_2330_2356 : Positive step216 2330 2356 := by decide +kernel

private theorem step216_2357_2437 : Positive step216 2357 2437 := by decide +kernel

private theorem step216_2438_2499 : Positive step216 2438 2499 := by decide +kernel

theorem step216_cover : ∃ ends, Cover step216 firstHeight ends := by
  exact ⟨[2356, 2437, 2499],
    ⟨(by decide), (by decide), step216_2330_2356,
      (by decide), (by decide), step216_2357_2437,
      (by decide), (by decide), step216_2438_2499, rfl⟩⟩

theorem step216_verified : Checked step216 :=
  ⟨step216_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step216_cover⟩

def step217 : Request :=
  ⟨⟨⟨520, 725, 161, 6096⟩, 4343013310464, 7809559934⟩, 10, 3, 41, 385715⟩

theorem step217_nodes : P1_7_1.nodeRows step217.bank.shape = step217.bank.nodeRows :=
  node_check step217.bank (by decide) (by decide) (by decide)

private theorem step217_2330_2335 : Positive step217 2330 2335 := by decide +kernel

private theorem step217_2336_2352 : Positive step217 2336 2352 := by decide +kernel

private theorem step217_2353_2403 : Positive step217 2353 2403 := by decide +kernel

private theorem step217_2404_2499 : Positive step217 2404 2499 := by decide +kernel

theorem step217_cover : ∃ ends, Cover step217 firstHeight ends := by
  exact ⟨[2335, 2352, 2403, 2499],
    ⟨(by decide), (by decide), step217_2330_2335,
      (by decide), (by decide), step217_2336_2352,
      (by decide), (by decide), step217_2353_2403,
      (by decide), (by decide), step217_2404_2499, rfl⟩⟩

theorem step217_verified : Checked step217 :=
  ⟨step217_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step217_cover⟩

def step218 : Request :=
  ⟨⟨⟨750, 1046, 232, 6858⟩, 12985818152960, 33687112323⟩, 16, 3, 41, 385715⟩

theorem step218_nodes : P1_7_1.nodeRows step218.bank.shape = step218.bank.nodeRows :=
  node_check step218.bank (by decide) (by decide) (by decide)

private theorem step218_2330_2339 : Positive step218 2330 2339 := by decide +kernel

private theorem step218_2340_2367 : Positive step218 2340 2367 := by decide +kernel

private theorem step218_2368_2446 : Positive step218 2368 2446 := by decide +kernel

private theorem step218_2447_2499 : Positive step218 2447 2499 := by decide +kernel

theorem step218_cover : ∃ ends, Cover step218 firstHeight ends := by
  exact ⟨[2339, 2367, 2446, 2499],
    ⟨(by decide), (by decide), step218_2330_2339,
      (by decide), (by decide), step218_2340_2367,
      (by decide), (by decide), step218_2368_2446,
      (by decide), (by decide), step218_2447_2499, rfl⟩⟩

theorem step218_verified : Checked step218 :=
  ⟨step218_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step218_cover⟩

def step219 : Request :=
  ⟨⟨⟨900, 1256, 279, 7715⟩, 22452680785920, 70021105933⟩, 20, 3, 41, 385715⟩

theorem step219_nodes : P1_7_1.nodeRows step219.bank.shape = step219.bank.nodeRows :=
  node_check step219.bank (by decide) (by decide) (by decide)

private theorem step219_2330_2335 : Positive step219 2330 2335 := by decide +kernel

private theorem step219_2336_2351 : Positive step219 2336 2351 := by decide +kernel

private theorem step219_2352_2396 : Positive step219 2352 2396 := by decide +kernel

private theorem step219_2397_2499 : Positive step219 2397 2499 := by decide +kernel

theorem step219_cover : ∃ ends, Cover step219 firstHeight ends := by
  exact ⟨[2335, 2351, 2396, 2499],
    ⟨(by decide), (by decide), step219_2330_2335,
      (by decide), (by decide), step219_2336_2351,
      (by decide), (by decide), step219_2352_2396,
      (by decide), (by decide), step219_2397_2499, rfl⟩⟩

theorem step219_verified : Checked step219 :=
  ⟨step219_nodes, Research6966.HelperWindowCatalogue.moment1256_279,
    (by decide), (by decide), (by decide), step219_cover⟩

def step220 : Request :=
  ⟨⟨⟨1100, 1534, 332, 12355⟩, 40133103452160, 152499774767⟩, 31, 3, 41, 385715⟩

theorem step220_nodes : P1_7_1.nodeRows step220.bank.shape = step220.bank.nodeRows :=
  node_check step220.bank (by decide) (by decide) (by decide)

private theorem step220_2330_2332 : Positive step220 2330 2332 := by decide +kernel

private theorem step220_2333_2340 : Positive step220 2333 2340 := by decide +kernel

private theorem step220_2341_2362 : Positive step220 2341 2362 := by decide +kernel

private theorem step220_2363_2422 : Positive step220 2363 2422 := by decide +kernel

private theorem step220_2423_2499 : Positive step220 2423 2499 := by decide +kernel

theorem step220_cover : ∃ ends, Cover step220 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2422, 2499],
    ⟨(by decide), (by decide), step220_2330_2332,
      (by decide), (by decide), step220_2333_2340,
      (by decide), (by decide), step220_2341_2362,
      (by decide), (by decide), step220_2363_2422,
      (by decide), (by decide), step220_2423_2499, rfl⟩⟩

theorem step220_verified : Checked step220 :=
  ⟨step220_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step220_cover⟩

def step221 : Request :=
  ⟨⟨⟨1100, 1534, 341, 12355⟩, 40955142733824, 155702293064⟩, 32, 3, 41, 385715⟩

theorem step221_nodes : P1_7_1.nodeRows step221.bank.shape = step221.bank.nodeRows :=
  node_check step221.bank (by decide) (by decide) (by decide)

private theorem step221_2330_2338 : Positive step221 2330 2338 := by decide +kernel

private theorem step221_2339_2363 : Positive step221 2339 2363 := by decide +kernel

private theorem step221_2364_2431 : Positive step221 2364 2431 := by decide +kernel

private theorem step221_2432_2499 : Positive step221 2432 2499 := by decide +kernel

theorem step221_cover : ∃ ends, Cover step221 firstHeight ends := by
  exact ⟨[2338, 2363, 2431, 2499],
    ⟨(by decide), (by decide), step221_2330_2338,
      (by decide), (by decide), step221_2339_2363,
      (by decide), (by decide), step221_2364_2431,
      (by decide), (by decide), step221_2432_2499, rfl⟩⟩

theorem step221_verified : Checked step221 :=
  ⟨step221_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step221_cover⟩

def step222 : Request :=
  ⟨⟨⟨1650, 2302, 512, 13899⟩, 138129879859200, 788519769358⟩, 44, 3, 41, 385715⟩

theorem step222_nodes : P1_7_1.nodeRows step222.bank.shape = step222.bank.nodeRows :=
  node_check step222.bank (by decide) (by decide) (by decide)

private theorem step222_2330_2341 : Positive step222 2330 2341 := by decide +kernel

private theorem step222_2342_2373 : Positive step222 2342 2373 := by decide +kernel

private theorem step222_2374_2459 : Positive step222 2374 2459 := by decide +kernel

private theorem step222_2460_2499 : Positive step222 2460 2499 := by decide +kernel

theorem step222_cover : ∃ ends, Cover step222 firstHeight ends := by
  exact ⟨[2341, 2373, 2459, 2499],
    ⟨(by decide), (by decide), step222_2330_2341,
      (by decide), (by decide), step222_2342_2373,
      (by decide), (by decide), step222_2374_2459,
      (by decide), (by decide), step222_2460_2499, rfl⟩⟩

theorem step222_verified : Checked step222 :=
  ⟨step222_nodes, Research6966.HelperWindowCatalogue.moment2302_512,
    (by decide), (by decide), (by decide), step222_cover⟩

def step223 : Request :=
  ⟨⟨⟨2500, 3488, 755, 22261⟩, 470210689105920, 4064279218567⟩, 73, 3, 41, 385715⟩

theorem step223_nodes : P1_7_1.nodeRows step223.bank.shape = step223.bank.nodeRows :=
  node_check step223.bank (by decide) (by decide) (by decide)

private theorem step223_2330_2333 : Positive step223 2330 2333 := by decide +kernel

private theorem step223_2334_2344 : Positive step223 2334 2344 := by decide +kernel

private theorem step223_2345_2373 : Positive step223 2345 2373 := by decide +kernel

private theorem step223_2374_2450 : Positive step223 2374 2450 := by decide +kernel

private theorem step223_2451_2499 : Positive step223 2451 2499 := by decide +kernel

theorem step223_cover : ∃ ends, Cover step223 firstHeight ends := by
  exact ⟨[2333, 2344, 2373, 2450, 2499],
    ⟨(by decide), (by decide), step223_2330_2333,
      (by decide), (by decide), step223_2334_2344,
      (by decide), (by decide), step223_2345_2373,
      (by decide), (by decide), step223_2374_2450,
      (by decide), (by decide), step223_2451_2499, rfl⟩⟩

theorem step223_verified : Checked step223 :=
  ⟨step223_nodes, Research6966.HelperWindowCatalogue.moment3488_755,
    (by decide), (by decide), (by decide), step223_cover⟩

def step224 : Request :=
  ⟨⟨⟨2500, 3488, 775, 22261⟩, 479640131993600, 4147842034257⟩, 76, 3, 41, 385715⟩

theorem step224_nodes : P1_7_1.nodeRows step224.bank.shape = step224.bank.nodeRows :=
  node_check step224.bank (by decide) (by decide) (by decide)

private theorem step224_2330_2338 : Positive step224 2330 2338 := by decide +kernel

private theorem step224_2339_2362 : Positive step224 2339 2362 := by decide +kernel

private theorem step224_2363_2425 : Positive step224 2363 2425 := by decide +kernel

private theorem step224_2426_2499 : Positive step224 2426 2499 := by decide +kernel

theorem step224_cover : ∃ ends, Cover step224 firstHeight ends := by
  exact ⟨[2338, 2362, 2425, 2499],
    ⟨(by decide), (by decide), step224_2330_2338,
      (by decide), (by decide), step224_2339_2362,
      (by decide), (by decide), step224_2363_2425,
      (by decide), (by decide), step224_2426_2499, rfl⟩⟩

theorem step224_verified : Checked step224 :=
  ⟨step224_nodes, Research6966.HelperWindowCatalogue.moment3488_775,
    (by decide), (by decide), (by decide), step224_cover⟩

def step225 : Request :=
  ⟨⟨⟨3000, 4185, 930, 31694⟩, 828559354757120, 8593576488693⟩, 103, 3, 41, 385715⟩

theorem step225_nodes : P1_7_1.nodeRows step225.bank.shape = step225.bank.nodeRows :=
  node_check step225.bank (by decide) (by decide) (by decide)

private theorem step225_2330_2337 : Positive step225 2330 2337 := by decide +kernel

private theorem step225_2338_2358 : Positive step225 2338 2358 := by decide +kernel

private theorem step225_2359_2413 : Positive step225 2359 2413 := by decide +kernel

private theorem step225_2414_2499 : Positive step225 2414 2499 := by decide +kernel

theorem step225_cover : ∃ ends, Cover step225 firstHeight ends := by
  exact ⟨[2337, 2358, 2413, 2499],
    ⟨(by decide), (by decide), step225_2330_2337,
      (by decide), (by decide), step225_2338_2358,
      (by decide), (by decide), step225_2359_2413,
      (by decide), (by decide), step225_2414_2499, rfl⟩⟩

theorem step225_verified : Checked step225 :=
  ⟨step225_nodes, Research6966.HelperWindowCatalogue.moment4185_930,
    (by decide), (by decide), (by decide), step225_cover⟩

def step226 : Request :=
  ⟨⟨⟨250, 349, 78, 2113⟩, 490108092416, 426627288⟩, 0, 3, 51, 385715⟩

theorem step226_nodes : P1_7_1.nodeRows step226.bank.shape = step226.bank.nodeRows :=
  node_check step226.bank (by decide) (by decide) (by decide)

private theorem step226_2330_2332 : Positive step226 2330 2332 := by decide +kernel

private theorem step226_2333_2343 : Positive step226 2333 2343 := by decide +kernel

private theorem step226_2344_2381 : Positive step226 2344 2381 := by decide +kernel

private theorem step226_2382_2499 : Positive step226 2382 2499 := by decide +kernel

theorem step226_cover : ∃ ends, Cover step226 firstHeight ends := by
  exact ⟨[2332, 2343, 2381, 2499],
    ⟨(by decide), (by decide), step226_2330_2332,
      (by decide), (by decide), step226_2333_2343,
      (by decide), (by decide), step226_2344_2381,
      (by decide), (by decide), step226_2382_2499, rfl⟩⟩

theorem step226_verified : Checked step226 :=
  ⟨step226_nodes, Research6966.HelperWindowCatalogue.moment349_78,
    (by decide), (by decide), (by decide), step226_cover⟩

def step227 : Request :=
  ⟨⟨⟨250, 349, 76, 2674⟩, 480667500544, 418199213⟩, 1, 3, 51, 385715⟩

theorem step227_nodes : P1_7_1.nodeRows step227.bank.shape = step227.bank.nodeRows :=
  node_check step227.bank (by decide) (by decide) (by decide)

private theorem step227_2330_2345 : Positive step227 2330 2345 := by decide +kernel

private theorem step227_2346_2402 : Positive step227 2346 2402 := by decide +kernel

private theorem step227_2403_2499 : Positive step227 2403 2499 := by decide +kernel

theorem step227_cover : ∃ ends, Cover step227 firstHeight ends := by
  exact ⟨[2345, 2402, 2499],
    ⟨(by decide), (by decide), step227_2330_2345,
      (by decide), (by decide), step227_2346_2402,
      (by decide), (by decide), step227_2403_2499, rfl⟩⟩

theorem step227_verified : Checked step227 :=
  ⟨step227_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step227_cover⟩

end Research6966.HelperRescueCatalogue
