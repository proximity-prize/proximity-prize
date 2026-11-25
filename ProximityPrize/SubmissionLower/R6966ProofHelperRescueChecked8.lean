import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments11
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments9
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step228 : Request :=
  ⟨⟨⟨294, 410, 89, 2674⟩, 777085255680, 791788817⟩, 2, 3, 51, 385715⟩

theorem step228_nodes : P1_7_1.nodeRows step228.bank.shape = step228.bank.nodeRows :=
  node_check step228.bank (by decide) (by decide) (by decide)

private theorem step228_2330_2344 : Positive step228 2330 2344 := by decide +kernel

private theorem step228_2345_2395 : Positive step228 2345 2395 := by decide +kernel

private theorem step228_2396_2499 : Positive step228 2396 2499 := by decide +kernel

theorem step228_cover : ∃ ends, Cover step228 firstHeight ends := by
  exact ⟨[2344, 2395, 2499],
    ⟨(by decide), (by decide), step228_2330_2344,
      (by decide), (by decide), step228_2345_2395,
      (by decide), (by decide), step228_2396_2499, rfl⟩⟩

theorem step228_verified : Checked step228 :=
  ⟨step228_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step228_cover⟩

def step229 : Request :=
  ⟨⟨⟨294, 410, 91, 3008⟩, 790165454848, 805457011⟩, 3, 3, 51, 385715⟩

theorem step229_nodes : P1_7_1.nodeRows step229.bank.shape = step229.bank.nodeRows :=
  node_check step229.bank (by decide) (by decide) (by decide)

private theorem step229_2330_2346 : Positive step229 2330 2346 := by decide +kernel

private theorem step229_2347_2403 : Positive step229 2347 2403 := by decide +kernel

private theorem step229_2404_2499 : Positive step229 2404 2499 := by decide +kernel

theorem step229_cover : ∃ ends, Cover step229 firstHeight ends := by
  exact ⟨[2346, 2403, 2499],
    ⟨(by decide), (by decide), step229_2330_2346,
      (by decide), (by decide), step229_2347_2403,
      (by decide), (by decide), step229_2404_2499, rfl⟩⟩

theorem step229_verified : Checked step229 :=
  ⟨step229_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step229_cover⟩

def step230 : Request :=
  ⟨⟨⟨350, 488, 106, 3008⟩, 1308168290304, 1584729438⟩, 4, 3, 51, 385715⟩

theorem step230_nodes : P1_7_1.nodeRows step230.bank.shape = step230.bank.nodeRows :=
  node_check step230.bank (by decide) (by decide) (by decide)

private theorem step230_2330_2332 : Positive step230 2330 2332 := by decide +kernel

private theorem step230_2333_2341 : Positive step230 2333 2341 := by decide +kernel

private theorem step230_2342_2370 : Positive step230 2342 2370 := by decide +kernel

private theorem step230_2371_2464 : Positive step230 2371 2464 := by decide +kernel

private theorem step230_2465_2499 : Positive step230 2465 2499 := by decide +kernel

theorem step230_cover : ∃ ends, Cover step230 firstHeight ends := by
  exact ⟨[2332, 2341, 2370, 2464, 2499],
    ⟨(by decide), (by decide), step230_2330_2332,
      (by decide), (by decide), step230_2333_2341,
      (by decide), (by decide), step230_2342_2370,
      (by decide), (by decide), step230_2371_2464,
      (by decide), (by decide), step230_2465_2499, rfl⟩⟩

theorem step230_verified : Checked step230 :=
  ⟨step230_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step230_cover⟩

def step231 : Request :=
  ⟨⟨⟨350, 488, 106, 3384⟩, 1308168290304, 1584729438⟩, 5, 3, 51, 385715⟩

theorem step231_nodes : P1_7_1.nodeRows step231.bank.shape = step231.bank.nodeRows :=
  node_check step231.bank (by decide) (by decide) (by decide)

private theorem step231_2330_2335 : Positive step231 2330 2335 := by decide +kernel

private theorem step231_2336_2354 : Positive step231 2336 2354 := by decide +kernel

private theorem step231_2355_2415 : Positive step231 2355 2415 := by decide +kernel

private theorem step231_2416_2499 : Positive step231 2416 2499 := by decide +kernel

theorem step231_cover : ∃ ends, Cover step231 firstHeight ends := by
  exact ⟨[2335, 2354, 2415, 2499],
    ⟨(by decide), (by decide), step231_2330_2335,
      (by decide), (by decide), step231_2336_2354,
      (by decide), (by decide), step231_2355_2415,
      (by decide), (by decide), step231_2416_2499, rfl⟩⟩

theorem step231_verified : Checked step231 :=
  ⟨step231_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step231_cover⟩

def step232 : Request :=
  ⟨⟨⟨420, 586, 127, 3807⟩, 2252760678400, 3279920952⟩, 7, 3, 51, 385715⟩

theorem step232_nodes : P1_7_1.nodeRows step232.bank.shape = step232.bank.nodeRows :=
  node_check step232.bank (by decide) (by decide) (by decide)

private theorem step232_2330_2348 : Positive step232 2330 2348 := by decide +kernel

private theorem step232_2349_2407 : Positive step232 2349 2407 := by decide +kernel

private theorem step232_2408_2499 : Positive step232 2408 2499 := by decide +kernel

theorem step232_cover : ∃ ends, Cover step232 firstHeight ends := by
  exact ⟨[2348, 2407, 2499],
    ⟨(by decide), (by decide), step232_2330_2348,
      (by decide), (by decide), step232_2349_2407,
      (by decide), (by decide), step232_2408_2499, rfl⟩⟩

theorem step232_verified : Checked step232 :=
  ⟨step232_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step232_cover⟩

def step233 : Request :=
  ⟨⟨⟨520, 725, 157, 4282⟩, 4261264752640, 7658911630⟩, 10, 3, 51, 385715⟩

theorem step233_nodes : P1_7_1.nodeRows step233.bank.shape = step233.bank.nodeRows :=
  node_check step233.bank (by decide) (by decide) (by decide)

private theorem step233_2330_2334 : Positive step233 2330 2334 := by decide +kernel

private theorem step233_2335_2349 : Positive step233 2335 2349 := by decide +kernel

private theorem step233_2350_2394 : Positive step233 2350 2394 := by decide +kernel

private theorem step233_2395_2499 : Positive step233 2395 2499 := by decide +kernel

theorem step233_cover : ∃ ends, Cover step233 firstHeight ends := by
  exact ⟨[2334, 2349, 2394, 2499],
    ⟨(by decide), (by decide), step233_2330_2334,
      (by decide), (by decide), step233_2335_2349,
      (by decide), (by decide), step233_2350_2394,
      (by decide), (by decide), step233_2395_2499, rfl⟩⟩

theorem step233_verified : Checked step233 :=
  ⟨step233_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step233_cover⟩

def step234 : Request :=
  ⟨⟨⟨630, 879, 195, 5419⟩, 7709474160640, 16827402390⟩, 16, 3, 51, 385715⟩

theorem step234_nodes : P1_7_1.nodeRows step234.bank.shape = step234.bank.nodeRows :=
  node_check step234.bank (by decide) (by decide) (by decide)

private theorem step234_2330_2333 : Positive step234 2330 2333 := by decide +kernel

private theorem step234_2334_2344 : Positive step234 2334 2344 := by decide +kernel

private theorem step234_2345_2376 : Positive step234 2345 2376 := by decide +kernel

private theorem step234_2377_2468 : Positive step234 2377 2468 := by decide +kernel

private theorem step234_2469_2499 : Positive step234 2469 2499 := by decide +kernel

theorem step234_cover : ∃ ends, Cover step234 firstHeight ends := by
  exact ⟨[2333, 2344, 2376, 2468, 2499],
    ⟨(by decide), (by decide), step234_2330_2333,
      (by decide), (by decide), step234_2334_2344,
      (by decide), (by decide), step234_2345_2376,
      (by decide), (by decide), step234_2377_2468,
      (by decide), (by decide), step234_2469_2499, rfl⟩⟩

theorem step234_verified : Checked step234 :=
  ⟨step234_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step234_cover⟩

def step235 : Request :=
  ⟨⟨⟨630, 878, 195, 7715⟩, 7709474160640, 16765904450⟩, 20, 3, 51, 385715⟩

theorem step235_nodes : P1_7_1.nodeRows step235.bank.shape = step235.bank.nodeRows :=
  node_check step235.bank (by decide) (by decide) (by decide)

private theorem step235_2330_2332 : Positive step235 2330 2332 := by decide +kernel

private theorem step235_2333_2340 : Positive step235 2333 2340 := by decide +kernel

private theorem step235_2341_2363 : Positive step235 2341 2363 := by decide +kernel

private theorem step235_2364_2429 : Positive step235 2364 2429 := by decide +kernel

private theorem step235_2430_2499 : Positive step235 2430 2499 := by decide +kernel

theorem step235_cover : ∃ ends, Cover step235 firstHeight ends := by
  exact ⟨[2332, 2340, 2363, 2429, 2499],
    ⟨(by decide), (by decide), step235_2330_2332,
      (by decide), (by decide), step235_2333_2340,
      (by decide), (by decide), step235_2341_2363,
      (by decide), (by decide), step235_2364_2429,
      (by decide), (by decide), step235_2430_2499, rfl⟩⟩

theorem step235_verified : Checked step235 :=
  ⟨step235_nodes, Research6966.HelperWindowCatalogue.moment878_195,
    (by decide), (by decide), (by decide), step235_cover⟩

def step236 : Request :=
  ⟨⟨⟨900, 1255, 279, 9763⟩, 22452680785920, 69841856233⟩, 31, 3, 51, 385715⟩

theorem step236_nodes : P1_7_1.nodeRows step236.bank.shape = step236.bank.nodeRows :=
  node_check step236.bank (by decide) (by decide) (by decide)

private theorem step236_2330_2348 : Positive step236 2330 2348 := by decide +kernel

private theorem step236_2349_2401 : Positive step236 2349 2401 := by decide +kernel

private theorem step236_2402_2499 : Positive step236 2402 2499 := by decide +kernel

theorem step236_cover : ∃ ends, Cover step236 firstHeight ends := by
  exact ⟨[2348, 2401, 2499],
    ⟨(by decide), (by decide), step236_2330_2348,
      (by decide), (by decide), step236_2349_2401,
      (by decide), (by decide), step236_2402_2499, rfl⟩⟩

theorem step236_verified : Checked step236 :=
  ⟨step236_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step236_cover⟩

def step237 : Request :=
  ⟨⟨⟨900, 1255, 279, 9763⟩, 22452680785920, 69841856233⟩, 32, 3, 51, 385715⟩

theorem step237_nodes : P1_7_1.nodeRows step237.bank.shape = step237.bank.nodeRows :=
  node_check step237.bank (by decide) (by decide) (by decide)

private theorem step237_2330_2330 : Positive step237 2330 2330 := by decide +kernel

private theorem step237_2331_2333 : Positive step237 2331 2333 := by decide +kernel

private theorem step237_2334_2341 : Positive step237 2334 2341 := by decide +kernel

private theorem step237_2342_2363 : Positive step237 2342 2363 := by decide +kernel

private theorem step237_2364_2424 : Positive step237 2364 2424 := by decide +kernel

private theorem step237_2425_2499 : Positive step237 2425 2499 := by decide +kernel

theorem step237_cover : ∃ ends, Cover step237 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2424, 2499],
    ⟨(by decide), (by decide), step237_2330_2330,
      (by decide), (by decide), step237_2331_2333,
      (by decide), (by decide), step237_2334_2341,
      (by decide), (by decide), step237_2342_2363,
      (by decide), (by decide), step237_2364_2424,
      (by decide), (by decide), step237_2425_2499, rfl⟩⟩

theorem step237_verified : Checked step237 :=
  ⟨step237_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step237_cover⟩

def step238 : Request :=
  ⟨⟨⟨1350, 1883, 418, 10983⟩, 75578221264896, 352769102024⟩, 44, 3, 51, 385715⟩

theorem step238_nodes : P1_7_1.nodeRows step238.bank.shape = step238.bank.nodeRows :=
  node_check step238.bank (by decide) (by decide) (by decide)

private theorem step238_2330_2330 : Positive step238 2330 2330 := by decide +kernel

private theorem step238_2331_2333 : Positive step238 2331 2333 := by decide +kernel

private theorem step238_2334_2341 : Positive step238 2334 2341 := by decide +kernel

private theorem step238_2342_2362 : Positive step238 2342 2362 := by decide +kernel

private theorem step238_2363_2419 : Positive step238 2363 2419 := by decide +kernel

private theorem step238_2420_2499 : Positive step238 2420 2499 := by decide +kernel

theorem step238_cover : ∃ ends, Cover step238 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2419, 2499],
    ⟨(by decide), (by decide), step238_2330_2330,
      (by decide), (by decide), step238_2331_2333,
      (by decide), (by decide), step238_2334_2341,
      (by decide), (by decide), step238_2342_2362,
      (by decide), (by decide), step238_2363_2419,
      (by decide), (by decide), step238_2420_2499, rfl⟩⟩

theorem step238_verified : Checked step238 :=
  ⟨step238_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step238_cover⟩

def step239 : Request :=
  ⟨⟨⟨2000, 2790, 620, 17590⟩, 245690786119680, 1699185179819⟩, 73, 3, 51, 385715⟩

theorem step239_nodes : P1_7_1.nodeRows step239.bank.shape = step239.bank.nodeRows :=
  node_check step239.bank (by decide) (by decide) (by decide)

private theorem step239_2330_2346 : Positive step239 2330 2346 := by decide +kernel

private theorem step239_2347_2392 : Positive step239 2347 2392 := by decide +kernel

private theorem step239_2393_2499 : Positive step239 2393 2499 := by decide +kernel

theorem step239_cover : ∃ ends, Cover step239 firstHeight ends := by
  exact ⟨[2346, 2392, 2499],
    ⟨(by decide), (by decide), step239_2330_2346,
      (by decide), (by decide), step239_2347_2392,
      (by decide), (by decide), step239_2393_2499, rfl⟩⟩

theorem step239_verified : Checked step239 :=
  ⟨step239_nodes, Research6966.HelperWindowCatalogue.moment2790_620,
    (by decide), (by decide), (by decide), step239_cover⟩

def step240 : Request :=
  ⟨⟨⟨2000, 2789, 604, 19788⟩, 240862397726720, 1663046410409⟩, 76, 3, 51, 385715⟩

theorem step240_nodes : P1_7_1.nodeRows step240.bank.shape = step240.bank.nodeRows :=
  node_check step240.bank (by decide) (by decide) (by decide)

private theorem step240_2330_2344 : Positive step240 2330 2344 := by decide +kernel

private theorem step240_2345_2384 : Positive step240 2345 2384 := by decide +kernel

private theorem step240_2385_2491 : Positive step240 2385 2491 := by decide +kernel

private theorem step240_2492_2499 : Positive step240 2492 2499 := by decide +kernel

theorem step240_cover : ∃ ends, Cover step240 firstHeight ends := by
  exact ⟨[2344, 2384, 2491, 2499],
    ⟨(by decide), (by decide), step240_2330_2344,
      (by decide), (by decide), step240_2345_2384,
      (by decide), (by decide), step240_2385_2491,
      (by decide), (by decide), step240_2492_2499, rfl⟩⟩

theorem step240_verified : Checked step240 :=
  ⟨step240_nodes, Research6966.HelperWindowCatalogue.moment2789_604,
    (by decide), (by decide), (by decide), step240_cover⟩

def step241 : Request :=
  ⟨⟨⟨2500, 3487, 775, 25043⟩, 479640131993600, 4144013596741⟩, 103, 3, 51, 385715⟩

theorem step241_nodes : P1_7_1.nodeRows step241.bank.shape = step241.bank.nodeRows :=
  node_check step241.bank (by decide) (by decide) (by decide)

private theorem step241_2330_2336 : Positive step241 2330 2336 := by decide +kernel

private theorem step241_2337_2355 : Positive step241 2337 2355 := by decide +kernel

private theorem step241_2356_2405 : Positive step241 2356 2405 := by decide +kernel

private theorem step241_2406_2499 : Positive step241 2406 2499 := by decide +kernel

theorem step241_cover : ∃ ends, Cover step241 firstHeight ends := by
  exact ⟨[2336, 2355, 2405, 2499],
    ⟨(by decide), (by decide), step241_2330_2336,
      (by decide), (by decide), step241_2337_2355,
      (by decide), (by decide), step241_2356_2405,
      (by decide), (by decide), step241_2406_2499, rfl⟩⟩

theorem step241_verified : Checked step241 :=
  ⟨step241_nodes, Research6966.HelperWindowCatalogue.moment3487_775,
    (by decide), (by decide), (by decide), step241_cover⟩

def step242 : Request :=
  ⟨⟨⟨170, 237, 53, 2113⟩, 155362000896, 91783289⟩, 0, 3, 71, 385715⟩

theorem step242_nodes : P1_7_1.nodeRows step242.bank.shape = step242.bank.nodeRows :=
  node_check step242.bank (by decide) (by decide) (by decide)

private theorem step242_2330_2332 : Positive step242 2330 2332 := by decide +kernel

private theorem step242_2333_2345 : Positive step242 2333 2345 := by decide +kernel

private theorem step242_2346_2401 : Positive step242 2346 2401 := by decide +kernel

private theorem step242_2402_2499 : Positive step242 2402 2499 := by decide +kernel

theorem step242_cover : ∃ ends, Cover step242 firstHeight ends := by
  exact ⟨[2332, 2345, 2401, 2499],
    ⟨(by decide), (by decide), step242_2330_2332,
      (by decide), (by decide), step242_2333_2345,
      (by decide), (by decide), step242_2346_2401,
      (by decide), (by decide), step242_2402_2499, rfl⟩⟩

theorem step242_verified : Checked step242 :=
  ⟨step242_nodes, Research6966.HelperWindowCatalogue.moment237_53,
    (by decide), (by decide), (by decide), step242_cover⟩

def step243 : Request :=
  ⟨⟨⟨210, 293, 62, 2113⟩, 279710269440, 204151930⟩, 1, 3, 71, 385715⟩

theorem step243_nodes : P1_7_1.nodeRows step243.bank.shape = step243.bank.nodeRows :=
  node_check step243.bank (by decide) (by decide) (by decide)

private theorem step243_2330_2333 : Positive step243 2330 2333 := by decide +kernel

private theorem step243_2334_2348 : Positive step243 2334 2348 := by decide +kernel

private theorem step243_2349_2407 : Positive step243 2349 2407 := by decide +kernel

private theorem step243_2408_2499 : Positive step243 2408 2499 := by decide +kernel

theorem step243_cover : ∃ ends, Cover step243 firstHeight ends := by
  exact ⟨[2333, 2348, 2407, 2499],
    ⟨(by decide), (by decide), step243_2330_2333,
      (by decide), (by decide), step243_2334_2348,
      (by decide), (by decide), step243_2349_2407,
      (by decide), (by decide), step243_2408_2499, rfl⟩⟩

theorem step243_verified : Checked step243 :=
  ⟨step243_nodes, Research6966.HelperWindowCatalogue.moment293_62,
    (by decide), (by decide), (by decide), step243_cover⟩

def step244 : Request :=
  ⟨⟨⟨210, 293, 65, 2377⟩, 289785774080, 211692234⟩, 2, 3, 71, 385715⟩

theorem step244_nodes : P1_7_1.nodeRows step244.bank.shape = step244.bank.nodeRows :=
  node_check step244.bank (by decide) (by decide) (by decide)

private theorem step244_2330_2347 : Positive step244 2330 2347 := by decide +kernel

private theorem step244_2348_2416 : Positive step244 2348 2416 := by decide +kernel

private theorem step244_2417_2499 : Positive step244 2417 2499 := by decide +kernel

theorem step244_cover : ∃ ends, Cover step244 firstHeight ends := by
  exact ⟨[2347, 2416, 2499],
    ⟨(by decide), (by decide), step244_2330_2347,
      (by decide), (by decide), step244_2348_2416,
      (by decide), (by decide), step244_2417_2499, rfl⟩⟩

theorem step244_verified : Checked step244 :=
  ⟨step244_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step244_cover⟩

def step245 : Request :=
  ⟨⟨⟨250, 348, 76, 2377⟩, 480667500544, 414368386⟩, 3, 3, 71, 385715⟩

theorem step245_nodes : P1_7_1.nodeRows step245.bank.shape = step245.bank.nodeRows :=
  node_check step245.bank (by decide) (by decide) (by decide)

private theorem step245_2330_2376 : Positive step245 2330 2376 := by decide +kernel

private theorem step245_2377_2499 : Positive step245 2377 2499 := by decide +kernel

theorem step245_cover : ∃ ends, Cover step245 firstHeight ends := by
  exact ⟨[2376, 2499],
    ⟨(by decide), (by decide), step245_2330_2376,
      (by decide), (by decide), step245_2377_2499, rfl⟩⟩

theorem step245_verified : Checked step245 :=
  ⟨step245_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step245_cover⟩

def step246 : Request :=
  ⟨⟨⟨250, 348, 76, 2674⟩, 480667500544, 414368386⟩, 4, 3, 71, 385715⟩

theorem step246_nodes : P1_7_1.nodeRows step246.bank.shape = step246.bank.nodeRows :=
  node_check step246.bank (by decide) (by decide) (by decide)

private theorem step246_2330_2348 : Positive step246 2330 2348 := by decide +kernel

private theorem step246_2349_2416 : Positive step246 2349 2416 := by decide +kernel

private theorem step246_2417_2499 : Positive step246 2417 2499 := by decide +kernel

theorem step246_cover : ∃ ends, Cover step246 firstHeight ends := by
  exact ⟨[2348, 2416, 2499],
    ⟨(by decide), (by decide), step246_2330_2348,
      (by decide), (by decide), step246_2349_2416,
      (by decide), (by decide), step246_2417_2499, rfl⟩⟩

theorem step246_verified : Checked step246 :=
  ⟨step246_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step246_cover⟩

def step247 : Request :=
  ⟨⟨⟨250, 348, 78, 3384⟩, 490108092416, 422716393⟩, 5, 3, 71, 385715⟩

theorem step247_nodes : P1_7_1.nodeRows step247.bank.shape = step247.bank.nodeRows :=
  node_check step247.bank (by decide) (by decide) (by decide)

private theorem step247_2330_2335 : Positive step247 2330 2335 := by decide +kernel

private theorem step247_2336_2357 : Positive step247 2336 2357 := by decide +kernel

private theorem step247_2358_2435 : Positive step247 2358 2435 := by decide +kernel

private theorem step247_2436_2499 : Positive step247 2436 2499 := by decide +kernel

theorem step247_cover : ∃ ends, Cover step247 firstHeight ends := by
  exact ⟨[2335, 2357, 2435, 2499],
    ⟨(by decide), (by decide), step247_2330_2335,
      (by decide), (by decide), step247_2336_2357,
      (by decide), (by decide), step247_2358_2435,
      (by decide), (by decide), step247_2436_2499, rfl⟩⟩

theorem step247_verified : Checked step247 :=
  ⟨step247_nodes, Research6966.HelperWindowCatalogue.moment348_78,
    (by decide), (by decide), (by decide), step247_cover⟩

def step248 : Request :=
  ⟨⟨⟨294, 410, 91, 3384⟩, 790165454848, 805457011⟩, 7, 3, 71, 385715⟩

theorem step248_nodes : P1_7_1.nodeRows step248.bank.shape = step248.bank.nodeRows :=
  node_check step248.bank (by decide) (by decide) (by decide)

private theorem step248_2330_2346 : Positive step248 2330 2346 := by decide +kernel

private theorem step248_2347_2403 : Positive step248 2347 2403 := by decide +kernel

private theorem step248_2404_2499 : Positive step248 2404 2499 := by decide +kernel

theorem step248_cover : ∃ ends, Cover step248 firstHeight ends := by
  exact ⟨[2346, 2403, 2499],
    ⟨(by decide), (by decide), step248_2330_2346,
      (by decide), (by decide), step248_2347_2403,
      (by decide), (by decide), step248_2404_2499, rfl⟩⟩

theorem step248_verified : Checked step248 :=
  ⟨step248_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step248_cover⟩

def step249 : Request :=
  ⟨⟨⟨350, 488, 108, 3807⟩, 1326705278976, 1607754763⟩, 10, 3, 71, 385715⟩

theorem step249_nodes : P1_7_1.nodeRows step249.bank.shape = step249.bank.nodeRows :=
  node_check step249.bank (by decide) (by decide) (by decide)

private theorem step249_2330_2342 : Positive step249 2330 2342 := by decide +kernel

private theorem step249_2343_2384 : Positive step249 2343 2384 := by decide +kernel

private theorem step249_2385_2499 : Positive step249 2385 2499 := by decide +kernel

theorem step249_cover : ∃ ends, Cover step249 firstHeight ends := by
  exact ⟨[2342, 2384, 2499],
    ⟨(by decide), (by decide), step249_2330_2342,
      (by decide), (by decide), step249_2343_2384,
      (by decide), (by decide), step249_2385_2499, rfl⟩⟩

theorem step249_verified : Checked step249 :=
  ⟨step249_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step249_cover⟩

def step250 : Request :=
  ⟨⟨⟨520, 725, 161, 4282⟩, 4343013310464, 7809559934⟩, 16, 3, 71, 385715⟩

theorem step250_nodes : P1_7_1.nodeRows step250.bank.shape = step250.bank.nodeRows :=
  node_check step250.bank (by decide) (by decide) (by decide)

private theorem step250_2330_2336 : Positive step250 2330 2336 := by decide +kernel

private theorem step250_2337_2357 : Positive step250 2337 2357 := by decide +kernel

private theorem step250_2358_2419 : Positive step250 2358 2419 := by decide +kernel

private theorem step250_2420_2499 : Positive step250 2420 2499 := by decide +kernel

theorem step250_cover : ∃ ends, Cover step250 firstHeight ends := by
  exact ⟨[2336, 2357, 2419, 2499],
    ⟨(by decide), (by decide), step250_2330_2336,
      (by decide), (by decide), step250_2337_2357,
      (by decide), (by decide), step250_2358_2419,
      (by decide), (by decide), step250_2420_2499, rfl⟩⟩

theorem step250_verified : Checked step250 :=
  ⟨step250_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step250_cover⟩

def step251 : Request :=
  ⟨⟨⟨520, 725, 157, 6096⟩, 4261264752640, 7658911630⟩, 20, 3, 71, 385715⟩

theorem step251_nodes : P1_7_1.nodeRows step251.bank.shape = step251.bank.nodeRows :=
  node_check step251.bank (by decide) (by decide) (by decide)

private theorem step251_2330_2335 : Positive step251 2330 2335 := by decide +kernel

private theorem step251_2336_2353 : Positive step251 2336 2353 := by decide +kernel

private theorem step251_2354_2406 : Positive step251 2354 2406 := by decide +kernel

private theorem step251_2407_2499 : Positive step251 2407 2499 := by decide +kernel

theorem step251_cover : ∃ ends, Cover step251 firstHeight ends := by
  exact ⟨[2335, 2353, 2406, 2499],
    ⟨(by decide), (by decide), step251_2330_2335,
      (by decide), (by decide), step251_2336_2353,
      (by decide), (by decide), step251_2354_2406,
      (by decide), (by decide), step251_2407_2499, rfl⟩⟩

theorem step251_verified : Checked step251 :=
  ⟨step251_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step251_cover⟩

def step252 : Request :=
  ⟨⟨⟨750, 1046, 226, 7715⟩, 12730741817344, 33009058589⟩, 31, 3, 71, 385715⟩

theorem step252_nodes : P1_7_1.nodeRows step252.bank.shape = step252.bank.nodeRows :=
  node_check step252.bank (by decide) (by decide) (by decide)

private theorem step252_2330_2345 : Positive step252 2330 2345 := by decide +kernel

private theorem step252_2346_2391 : Positive step252 2346 2391 := by decide +kernel

private theorem step252_2392_2499 : Positive step252 2392 2499 := by decide +kernel

theorem step252_cover : ∃ ends, Cover step252 firstHeight ends := by
  exact ⟨[2345, 2391, 2499],
    ⟨(by decide), (by decide), step252_2330_2345,
      (by decide), (by decide), step252_2346_2391,
      (by decide), (by decide), step252_2392_2499, rfl⟩⟩

theorem step252_verified : Checked step252 :=
  ⟨step252_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step252_cover⟩

def step253 : Request :=
  ⟨⟨⟨750, 1046, 232, 7715⟩, 12985818152960, 33687112323⟩, 32, 3, 71, 385715⟩

theorem step253_nodes : P1_7_1.nodeRows step253.bank.shape = step253.bank.nodeRows :=
  node_check step253.bank (by decide) (by decide) (by decide)

private theorem step253_2330_2350 : Positive step253 2330 2350 := by decide +kernel

private theorem step253_2351_2409 : Positive step253 2351 2409 := by decide +kernel

private theorem step253_2410_2499 : Positive step253 2410 2499 := by decide +kernel

theorem step253_cover : ∃ ends, Cover step253 firstHeight ends := by
  exact ⟨[2350, 2409, 2499],
    ⟨(by decide), (by decide), step253_2330_2350,
      (by decide), (by decide), step253_2351_2409,
      (by decide), (by decide), step253_2410_2499, rfl⟩⟩

theorem step253_verified : Checked step253 :=
  ⟨step253_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step253_cover⟩

def step254 : Request :=
  ⟨⟨⟨900, 1255, 279, 10983⟩, 22452680785920, 69841856233⟩, 44, 3, 71, 385715⟩

theorem step254_nodes : P1_7_1.nodeRows step254.bank.shape = step254.bank.nodeRows :=
  node_check step254.bank (by decide) (by decide) (by decide)

private theorem step254_2330_2331 : Positive step254 2330 2331 := by decide +kernel

private theorem step254_2332_2336 : Positive step254 2332 2336 := by decide +kernel

private theorem step254_2337_2350 : Positive step254 2337 2350 := by decide +kernel

private theorem step254_2351_2389 : Positive step254 2351 2389 := by decide +kernel

private theorem step254_2390_2497 : Positive step254 2390 2497 := by decide +kernel

private theorem step254_2498_2499 : Positive step254 2498 2499 := by decide +kernel

theorem step254_cover : ∃ ends, Cover step254 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2389, 2497, 2499],
    ⟨(by decide), (by decide), step254_2330_2331,
      (by decide), (by decide), step254_2332_2336,
      (by decide), (by decide), step254_2337_2350,
      (by decide), (by decide), step254_2351_2389,
      (by decide), (by decide), step254_2390_2497,
      (by decide), (by decide), step254_2498_2499, rfl⟩⟩

theorem step254_verified : Checked step254 :=
  ⟨step254_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step254_cover⟩

def step255 : Request :=
  ⟨⟨⟨1650, 2301, 512, 13899⟩, 138129879859200, 787417379725⟩, 73, 3, 71, 385715⟩

theorem step255_nodes : P1_7_1.nodeRows step255.bank.shape = step255.bank.nodeRows :=
  node_check step255.bank (by decide) (by decide) (by decide)

private theorem step255_2330_2352 : Positive step255 2330 2352 := by decide +kernel

private theorem step255_2353_2414 : Positive step255 2353 2414 := by decide +kernel

private theorem step255_2415_2499 : Positive step255 2415 2499 := by decide +kernel

theorem step255_cover : ∃ ends, Cover step255 firstHeight ends := by
  exact ⟨[2352, 2414, 2499],
    ⟨(by decide), (by decide), step255_2330_2352,
      (by decide), (by decide), step255_2353_2414,
      (by decide), (by decide), step255_2415_2499, rfl⟩⟩

theorem step255_verified : Checked step255 :=
  ⟨step255_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step255_cover⟩

def step256 : Request :=
  ⟨⟨⟨1650, 2301, 498, 15636⟩, 135254251667456, 770619519922⟩, 76, 3, 71, 385715⟩

theorem step256_nodes : P1_7_1.nodeRows step256.bank.shape = step256.bank.nodeRows :=
  node_check step256.bank (by decide) (by decide) (by decide)

private theorem step256_2330_2357 : Positive step256 2330 2357 := by decide +kernel

private theorem step256_2358_2433 : Positive step256 2358 2433 := by decide +kernel

private theorem step256_2434_2499 : Positive step256 2434 2499 := by decide +kernel

theorem step256_cover : ∃ ends, Cover step256 firstHeight ends := by
  exact ⟨[2357, 2433, 2499],
    ⟨(by decide), (by decide), step256_2330_2357,
      (by decide), (by decide), step256_2358_2433,
      (by decide), (by decide), step256_2434_2499, rfl⟩⟩

theorem step256_verified : Checked step256 :=
  ⟨step256_nodes, Research6966.HelperWindowCatalogue.moment2301_498,
    (by decide), (by decide), (by decide), step256_cover⟩

def step257 : Request :=
  ⟨⟨⟨2000, 2788, 620, 19788⟩, 245690786119680, 1695265997069⟩, 103, 3, 71, 385715⟩

theorem step257_nodes : P1_7_1.nodeRows step257.bank.shape = step257.bank.nodeRows :=
  node_check step257.bank (by decide) (by decide) (by decide)

private theorem step257_2330_2333 : Positive step257 2330 2333 := by decide +kernel

private theorem step257_2334_2343 : Positive step257 2334 2343 := by decide +kernel

private theorem step257_2344_2370 : Positive step257 2344 2370 := by decide +kernel

private theorem step257_2371_2441 : Positive step257 2371 2441 := by decide +kernel

private theorem step257_2442_2499 : Positive step257 2442 2499 := by decide +kernel

theorem step257_cover : ∃ ends, Cover step257 firstHeight ends := by
  exact ⟨[2333, 2343, 2370, 2441, 2499],
    ⟨(by decide), (by decide), step257_2330_2333,
      (by decide), (by decide), step257_2334_2343,
      (by decide), (by decide), step257_2344_2370,
      (by decide), (by decide), step257_2371_2441,
      (by decide), (by decide), step257_2442_2499, rfl⟩⟩

theorem step257_verified : Checked step257 :=
  ⟨step257_nodes, Research6966.HelperWindowCatalogue.moment2788_620,
    (by decide), (by decide), (by decide), step257_cover⟩

def step258 : Request :=
  ⟨⟨⟨420, 586, 127, 13899⟩, 2252760678400, 3279920952⟩, 0, 4, 1, 514287⟩

theorem step258_nodes : P1_7_1.nodeRows step258.bank.shape = step258.bank.nodeRows :=
  node_check step258.bank (by decide) (by decide) (by decide)

private theorem step258_2330_2340 : Positive step258 2330 2340 := by decide +kernel

private theorem step258_2341_2374 : Positive step258 2341 2374 := by decide +kernel

private theorem step258_2375_2478 : Positive step258 2375 2478 := by decide +kernel

private theorem step258_2479_2499 : Positive step258 2479 2499 := by decide +kernel

theorem step258_cover : ∃ ends, Cover step258 firstHeight ends := by
  exact ⟨[2340, 2374, 2478, 2499],
    ⟨(by decide), (by decide), step258_2330_2340,
      (by decide), (by decide), step258_2341_2374,
      (by decide), (by decide), step258_2375_2478,
      (by decide), (by decide), step258_2479_2499, rfl⟩⟩

theorem step258_verified : Checked step258 :=
  ⟨step258_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step258_cover⟩

def step259 : Request :=
  ⟨⟨⟨420, 586, 127, 15636⟩, 2252760678400, 3279920952⟩, 1, 4, 1, 514287⟩

theorem step259_nodes : P1_7_1.nodeRows step259.bank.shape = step259.bank.nodeRows :=
  node_check step259.bank (by decide) (by decide) (by decide)

private theorem step259_2330_2330 : Positive step259 2330 2330 := by decide +kernel

private theorem step259_2331_2333 : Positive step259 2331 2333 := by decide +kernel

private theorem step259_2334_2342 : Positive step259 2334 2342 := by decide +kernel

private theorem step259_2343_2369 : Positive step259 2343 2369 := by decide +kernel

private theorem step259_2370_2452 : Positive step259 2370 2452 := by decide +kernel

private theorem step259_2453_2499 : Positive step259 2453 2499 := by decide +kernel

theorem step259_cover : ∃ ends, Cover step259 firstHeight ends := by
  exact ⟨[2330, 2333, 2342, 2369, 2452, 2499],
    ⟨(by decide), (by decide), step259_2330_2330,
      (by decide), (by decide), step259_2331_2333,
      (by decide), (by decide), step259_2334_2342,
      (by decide), (by decide), step259_2343_2369,
      (by decide), (by decide), step259_2370_2452,
      (by decide), (by decide), step259_2453_2499, rfl⟩⟩

theorem step259_verified : Checked step259 :=
  ⟨step259_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step259_cover⟩

def step260 : Request :=
  ⟨⟨⟨630, 879, 190, 15636⟩, 7559493713920, 16491913877⟩, 2, 4, 1, 514287⟩

theorem step260_nodes : P1_7_1.nodeRows step260.bank.shape = step260.bank.nodeRows :=
  node_check step260.bank (by decide) (by decide) (by decide)

private theorem step260_2330_2332 : Positive step260 2330 2332 := by decide +kernel

private theorem step260_2333_2340 : Positive step260 2333 2340 := by decide +kernel

private theorem step260_2341_2363 : Positive step260 2341 2363 := by decide +kernel

private theorem step260_2364_2429 : Positive step260 2364 2429 := by decide +kernel

private theorem step260_2430_2499 : Positive step260 2430 2499 := by decide +kernel

theorem step260_cover : ∃ ends, Cover step260 firstHeight ends := by
  exact ⟨[2332, 2340, 2363, 2429, 2499],
    ⟨(by decide), (by decide), step260_2330_2332,
      (by decide), (by decide), step260_2333_2340,
      (by decide), (by decide), step260_2341_2363,
      (by decide), (by decide), step260_2364_2429,
      (by decide), (by decide), step260_2430_2499, rfl⟩⟩

theorem step260_verified : Checked step260 :=
  ⟨step260_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step260_cover⟩

def step261 : Request :=
  ⟨⟨⟨630, 879, 190, 17590⟩, 7559493713920, 16491913877⟩, 3, 4, 1, 514287⟩

theorem step261_nodes : P1_7_1.nodeRows step261.bank.shape = step261.bank.nodeRows :=
  node_check step261.bank (by decide) (by decide) (by decide)

private theorem step261_2330_2346 : Positive step261 2330 2346 := by decide +kernel

private theorem step261_2347_2395 : Positive step261 2347 2395 := by decide +kernel

private theorem step261_2396_2499 : Positive step261 2396 2499 := by decide +kernel

theorem step261_cover : ∃ ends, Cover step261 firstHeight ends := by
  exact ⟨[2346, 2395, 2499],
    ⟨(by decide), (by decide), step261_2330_2346,
      (by decide), (by decide), step261_2347_2395,
      (by decide), (by decide), step261_2396_2499, rfl⟩⟩

theorem step261_verified : Checked step261 :=
  ⟨step261_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step261_cover⟩

def step262 : Request :=
  ⟨⟨⟨630, 879, 186, 19788⟩, 7438337572864, 16221345781⟩, 4, 4, 1, 514287⟩

theorem step262_nodes : P1_7_1.nodeRows step262.bank.shape = step262.bank.nodeRows :=
  node_check step262.bank (by decide) (by decide) (by decide)

private theorem step262_2330_2338 : Positive step262 2330 2338 := by decide +kernel

private theorem step262_2339_2364 : Positive step262 2339 2364 := by decide +kernel

private theorem step262_2365_2440 : Positive step262 2365 2440 := by decide +kernel

private theorem step262_2441_2499 : Positive step262 2441 2499 := by decide +kernel

theorem step262_cover : ∃ ends, Cover step262 firstHeight ends := by
  exact ⟨[2338, 2364, 2440, 2499],
    ⟨(by decide), (by decide), step262_2330_2338,
      (by decide), (by decide), step262_2339_2364,
      (by decide), (by decide), step262_2365_2440,
      (by decide), (by decide), step262_2441_2499, rfl⟩⟩

theorem step262_verified : Checked step262 :=
  ⟨step262_nodes, Research6966.HelperWindowCatalogue.moment879_186,
    (by decide), (by decide), (by decide), step262_cover⟩

def step263 : Request :=
  ⟨⟨⟨750, 1047, 226, 19788⟩, 12730741817344, 33110613849⟩, 5, 4, 1, 514287⟩

theorem step263_nodes : P1_7_1.nodeRows step263.bank.shape = step263.bank.nodeRows :=
  node_check step263.bank (by decide) (by decide) (by decide)

private theorem step263_2330_2338 : Positive step263 2330 2338 := by decide +kernel

private theorem step263_2339_2363 : Positive step263 2339 2363 := by decide +kernel

private theorem step263_2364_2434 : Positive step263 2364 2434 := by decide +kernel

private theorem step263_2435_2499 : Positive step263 2435 2499 := by decide +kernel

theorem step263_cover : ∃ ends, Cover step263 firstHeight ends := by
  exact ⟨[2338, 2363, 2434, 2499],
    ⟨(by decide), (by decide), step263_2330_2338,
      (by decide), (by decide), step263_2339_2363,
      (by decide), (by decide), step263_2364_2434,
      (by decide), (by decide), step263_2435_2499, rfl⟩⟩

theorem step263_verified : Checked step263 :=
  ⟨step263_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step263_cover⟩

def step264 : Request :=
  ⟨⟨⟨750, 1047, 226, 22261⟩, 12730741817344, 33110613849⟩, 7, 4, 1, 514287⟩

theorem step264_nodes : P1_7_1.nodeRows step264.bank.shape = step264.bank.nodeRows :=
  node_check step264.bank (by decide) (by decide) (by decide)

private theorem step264_2330_2331 : Positive step264 2330 2331 := by decide +kernel

private theorem step264_2332_2337 : Positive step264 2332 2337 := by decide +kernel

private theorem step264_2338_2353 : Positive step264 2338 2353 := by decide +kernel

private theorem step264_2354_2398 : Positive step264 2354 2398 := by decide +kernel

private theorem step264_2399_2499 : Positive step264 2399 2499 := by decide +kernel

theorem step264_cover : ∃ ends, Cover step264 firstHeight ends := by
  exact ⟨[2331, 2337, 2353, 2398, 2499],
    ⟨(by decide), (by decide), step264_2330_2331,
      (by decide), (by decide), step264_2332_2337,
      (by decide), (by decide), step264_2338_2353,
      (by decide), (by decide), step264_2354_2398,
      (by decide), (by decide), step264_2399_2499, rfl⟩⟩

theorem step264_verified : Checked step264 :=
  ⟨step264_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step264_cover⟩

def step265 : Request :=
  ⟨⟨⟨750, 1046, 232, 28173⟩, 12985818152960, 33687112323⟩, 10, 4, 1, 514287⟩

theorem step265_nodes : P1_7_1.nodeRows step265.bank.shape = step265.bank.nodeRows :=
  node_check step265.bank (by decide) (by decide) (by decide)

private theorem step265_2330_2331 : Positive step265 2330 2331 := by decide +kernel

private theorem step265_2332_2336 : Positive step265 2332 2336 := by decide +kernel

private theorem step265_2337_2350 : Positive step265 2337 2350 := by decide +kernel

private theorem step265_2351_2389 : Positive step265 2351 2389 := by decide +kernel

private theorem step265_2390_2498 : Positive step265 2390 2498 := by decide +kernel

private theorem step265_2499_2499 : Positive step265 2499 2499 := by decide +kernel

theorem step265_cover : ∃ ends, Cover step265 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2389, 2498, 2499],
    ⟨(by decide), (by decide), step265_2330_2331,
      (by decide), (by decide), step265_2332_2336,
      (by decide), (by decide), step265_2337_2350,
      (by decide), (by decide), step265_2351_2389,
      (by decide), (by decide), step265_2390_2498,
      (by decide), (by decide), step265_2499_2499, rfl⟩⟩

theorem step265_verified : Checked step265 :=
  ⟨step265_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step265_cover⟩

def step266 : Request :=
  ⟨⟨⟨1100, 1535, 326, 35655⟩, 39579969388544, 150663514795⟩, 16, 4, 1, 514287⟩

theorem step266_nodes : P1_7_1.nodeRows step266.bank.shape = step266.bank.nodeRows :=
  node_check step266.bank (by decide) (by decide) (by decide)

private theorem step266_2330_2330 : Positive step266 2330 2330 := by decide +kernel

private theorem step266_2331_2333 : Positive step266 2331 2333 := by decide +kernel

private theorem step266_2334_2341 : Positive step266 2334 2341 := by decide +kernel

private theorem step266_2342_2363 : Positive step266 2342 2363 := by decide +kernel

private theorem step266_2364_2424 : Positive step266 2364 2424 := by decide +kernel

private theorem step266_2425_2499 : Positive step266 2425 2499 := by decide +kernel

theorem step266_cover : ∃ ends, Cover step266 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2424, 2499],
    ⟨(by decide), (by decide), step266_2330_2330,
      (by decide), (by decide), step266_2331_2333,
      (by decide), (by decide), step266_2334_2341,
      (by decide), (by decide), step266_2342_2363,
      (by decide), (by decide), step266_2364_2424,
      (by decide), (by decide), step266_2425_2499, rfl⟩⟩

theorem step266_verified : Checked step266 :=
  ⟨step266_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step266_cover⟩

def step267 : Request :=
  ⟨⟨⟨1350, 1884, 408, 40111⟩, 74202776600576, 346781832878⟩, 20, 4, 1, 514287⟩

theorem step267_nodes : P1_7_1.nodeRows step267.bank.shape = step267.bank.nodeRows :=
  node_check step267.bank (by decide) (by decide) (by decide)

private theorem step267_2330_2344 : Positive step267 2330 2344 := by decide +kernel

private theorem step267_2345_2384 : Positive step267 2345 2384 := by decide +kernel

private theorem step267_2385_2492 : Positive step267 2385 2492 := by decide +kernel

private theorem step267_2493_2499 : Positive step267 2493 2499 := by decide +kernel

theorem step267_cover : ∃ ends, Cover step267 firstHeight ends := by
  exact ⟨[2344, 2384, 2492, 2499],
    ⟨(by decide), (by decide), step267_2330_2344,
      (by decide), (by decide), step267_2345_2384,
      (by decide), (by decide), step267_2385_2492,
      (by decide), (by decide), step267_2493_2499, rfl⟩⟩

theorem step267_verified : Checked step267 :=
  ⟨step267_nodes, Research6966.HelperWindowCatalogue.moment1884_408,
    (by decide), (by decide), (by decide), step267_cover⟩

def step268 : Request :=
  ⟨⟨⟨1650, 2302, 498, 57109⟩, 135254251667456, 771697512616⟩, 31, 4, 1, 514287⟩

theorem step268_nodes : P1_7_1.nodeRows step268.bank.shape = step268.bank.nodeRows :=
  node_check step268.bank (by decide) (by decide) (by decide)

private theorem step268_2330_2343 : Positive step268 2330 2343 := by decide +kernel

private theorem step268_2344_2380 : Positive step268 2344 2380 := by decide +kernel

private theorem step268_2381_2480 : Positive step268 2381 2480 := by decide +kernel

private theorem step268_2481_2499 : Positive step268 2481 2499 := by decide +kernel

theorem step268_cover : ∃ ends, Cover step268 firstHeight ends := by
  exact ⟨[2343, 2380, 2480, 2499],
    ⟨(by decide), (by decide), step268_2330_2343,
      (by decide), (by decide), step268_2344_2380,
      (by decide), (by decide), step268_2381_2480,
      (by decide), (by decide), step268_2481_2499, rfl⟩⟩

theorem step268_verified : Checked step268 :=
  ⟨step268_nodes, Research6966.HelperWindowCatalogue.moment2302_498,
    (by decide), (by decide), (by decide), step268_cover⟩

def step269 : Request :=
  ⟨⟨⟨1650, 2302, 498, 57109⟩, 135254251667456, 771697512616⟩, 32, 4, 1, 514287⟩

theorem step269_nodes : P1_7_1.nodeRows step269.bank.shape = step269.bank.nodeRows :=
  node_check step269.bank (by decide) (by decide) (by decide)

private theorem step269_2330_2333 : Positive step269 2330 2333 := by decide +kernel

private theorem step269_2334_2344 : Positive step269 2334 2344 := by decide +kernel

private theorem step269_2345_2373 : Positive step269 2345 2373 := by decide +kernel

private theorem step269_2374_2451 : Positive step269 2374 2451 := by decide +kernel

private theorem step269_2452_2499 : Positive step269 2452 2499 := by decide +kernel

theorem step269_cover : ∃ ends, Cover step269 firstHeight ends := by
  exact ⟨[2333, 2344, 2373, 2451, 2499],
    ⟨(by decide), (by decide), step269_2330_2333,
      (by decide), (by decide), step269_2334_2344,
      (by decide), (by decide), step269_2345_2373,
      (by decide), (by decide), step269_2374_2451,
      (by decide), (by decide), step269_2452_2499, rfl⟩⟩

theorem step269_verified : Checked step269 :=
  ⟨step269_nodes, Research6966.HelperWindowCatalogue.moment2302_498,
    (by decide), (by decide), (by decide), step269_cover⟩

def step270 : Request :=
  ⟨⟨⟨2500, 3489, 740, 72277⟩, 463070780456960, 4004797990029⟩, 44, 4, 1, 514287⟩

theorem step270_nodes : P1_7_1.nodeRows step270.bank.shape = step270.bank.nodeRows :=
  node_check step270.bank (by decide) (by decide) (by decide)

private theorem step270_2330_2331 : Positive step270 2330 2331 := by decide +kernel

private theorem step270_2332_2336 : Positive step270 2332 2336 := by decide +kernel

private theorem step270_2337_2349 : Positive step270 2337 2349 := by decide +kernel

private theorem step270_2350_2384 : Positive step270 2350 2384 := by decide +kernel

private theorem step270_2385_2477 : Positive step270 2385 2477 := by decide +kernel

private theorem step270_2478_2499 : Positive step270 2478 2499 := by decide +kernel

theorem step270_cover : ∃ ends, Cover step270 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2384, 2477, 2499],
    ⟨(by decide), (by decide), step270_2330_2331,
      (by decide), (by decide), step270_2332_2336,
      (by decide), (by decide), step270_2337_2349,
      (by decide), (by decide), step270_2350_2384,
      (by decide), (by decide), step270_2385_2477,
      (by decide), (by decide), step270_2478_2499, rfl⟩⟩

theorem step270_verified : Checked step270 :=
  ⟨step270_nodes, Research6966.HelperWindowCatalogue.moment3489_740,
    (by decide), (by decide), (by decide), step270_cover⟩

def step271 : Request :=
  ⟨⟨⟨3500, 4884, 1036, 115771⟩, 1269967213297664, 15368047192365⟩, 73, 4, 1, 514287⟩

theorem step271_nodes : P1_7_1.nodeRows step271.bank.shape = step271.bank.nodeRows :=
  node_check step271.bank (by decide) (by decide) (by decide)

private theorem step271_2330_2335 : Positive step271 2330 2335 := by decide +kernel

private theorem step271_2336_2351 : Positive step271 2336 2351 := by decide +kernel

private theorem step271_2352_2393 : Positive step271 2352 2393 := by decide +kernel

private theorem step271_2394_2499 : Positive step271 2394 2499 := by decide +kernel

theorem step271_cover : ∃ ends, Cover step271 firstHeight ends := by
  exact ⟨[2335, 2351, 2393, 2499],
    ⟨(by decide), (by decide), step271_2330_2335,
      (by decide), (by decide), step271_2336_2351,
      (by decide), (by decide), step271_2352_2393,
      (by decide), (by decide), step271_2394_2499, rfl⟩⟩

theorem step271_verified : Checked step271 :=
  ⟨step271_nodes, Research6966.HelperWindowCatalogue.moment4884_1036,
    (by decide), (by decide), (by decide), step271_cover⟩

def step272 : Request :=
  ⟨⟨⟨3500, 4884, 1057, 115771⟩, 1289556817346560, 15610792063730⟩, 76, 4, 1, 514287⟩

theorem step272_nodes : P1_7_1.nodeRows step272.bank.shape = step272.bank.nodeRows :=
  node_check step272.bank (by decide) (by decide) (by decide)

private theorem step272_2330_2337 : Positive step272 2330 2337 := by decide +kernel

private theorem step272_2338_2358 : Positive step272 2338 2358 := by decide +kernel

private theorem step272_2359_2413 : Positive step272 2359 2413 := by decide +kernel

private theorem step272_2414_2499 : Positive step272 2414 2499 := by decide +kernel

theorem step272_cover : ∃ ends, Cover step272 firstHeight ends := by
  exact ⟨[2337, 2358, 2413, 2499],
    ⟨(by decide), (by decide), step272_2330_2337,
      (by decide), (by decide), step272_2338_2358,
      (by decide), (by decide), step272_2359_2413,
      (by decide), (by decide), step272_2414_2499, rfl⟩⟩

theorem step272_verified : Checked step272 :=
  ⟨step272_nodes, Research6966.HelperWindowCatalogue.moment4884_1057,
    (by decide), (by decide), (by decide), step272_cover⟩

def step273 : Request :=
  ⟨⟨⟨4500, 6279, 1332, 164837⟩, 2698317932789760, 41969435185037⟩, 103, 4, 1, 514287⟩

theorem step273_nodes : P1_7_1.nodeRows step273.bank.shape = step273.bank.nodeRows :=
  node_check step273.bank (by decide) (by decide) (by decide)

private theorem step273_2330_2339 : Positive step273 2330 2339 := by decide +kernel

private theorem step273_2340_2365 : Positive step273 2340 2365 := by decide +kernel

private theorem step273_2366_2433 : Positive step273 2366 2433 := by decide +kernel

private theorem step273_2434_2499 : Positive step273 2434 2499 := by decide +kernel

theorem step273_cover : ∃ ends, Cover step273 firstHeight ends := by
  exact ⟨[2339, 2365, 2433, 2499],
    ⟨(by decide), (by decide), step273_2330_2339,
      (by decide), (by decide), step273_2340_2365,
      (by decide), (by decide), step273_2366_2433,
      (by decide), (by decide), step273_2434_2499, rfl⟩⟩

theorem step273_verified : Checked step273 :=
  ⟨step273_nodes, Research6966.HelperWindowCatalogue.moment6279_1332,
    (by decide), (by decide), (by decide), step273_cover⟩

def step274 : Request :=
  ⟨⟨⟨420, 586, 124, 13899⟩, 2212364288000, 3219706108⟩, 0, 4, 2, 514287⟩

theorem step274_nodes : P1_7_1.nodeRows step274.bank.shape = step274.bank.nodeRows :=
  node_check step274.bank (by decide) (by decide) (by decide)

private theorem step274_2330_2331 : Positive step274 2330 2331 := by decide +kernel

private theorem step274_2332_2337 : Positive step274 2332 2337 := by decide +kernel

private theorem step274_2338_2356 : Positive step274 2338 2356 := by decide +kernel

private theorem step274_2357_2415 : Positive step274 2357 2415 := by decide +kernel

private theorem step274_2416_2499 : Positive step274 2416 2499 := by decide +kernel

theorem step274_cover : ∃ ends, Cover step274 firstHeight ends := by
  exact ⟨[2331, 2337, 2356, 2415, 2499],
    ⟨(by decide), (by decide), step274_2330_2331,
      (by decide), (by decide), step274_2332_2337,
      (by decide), (by decide), step274_2338_2356,
      (by decide), (by decide), step274_2357_2415,
      (by decide), (by decide), step274_2416_2499, rfl⟩⟩

theorem step274_verified : Checked step274 :=
  ⟨step274_nodes, Research6966.HelperWindowCatalogue.moment586_124,
    (by decide), (by decide), (by decide), step274_cover⟩

def step275 : Request :=
  ⟨⟨⟨520, 726, 157, 13899⟩, 4261264752640, 7692905725⟩, 1, 4, 2, 514287⟩

theorem step275_nodes : P1_7_1.nodeRows step275.bank.shape = step275.bank.nodeRows :=
  node_check step275.bank (by decide) (by decide) (by decide)

private theorem step275_2330_2331 : Positive step275 2330 2331 := by decide +kernel

private theorem step275_2332_2337 : Positive step275 2332 2337 := by decide +kernel

private theorem step275_2338_2355 : Positive step275 2338 2355 := by decide +kernel

private theorem step275_2356_2407 : Positive step275 2356 2407 := by decide +kernel

private theorem step275_2408_2499 : Positive step275 2408 2499 := by decide +kernel

theorem step275_cover : ∃ ends, Cover step275 firstHeight ends := by
  exact ⟨[2331, 2337, 2355, 2407, 2499],
    ⟨(by decide), (by decide), step275_2330_2331,
      (by decide), (by decide), step275_2332_2337,
      (by decide), (by decide), step275_2338_2355,
      (by decide), (by decide), step275_2356_2407,
      (by decide), (by decide), step275_2408_2499, rfl⟩⟩

theorem step275_verified : Checked step275 :=
  ⟨step275_nodes, Research6966.HelperWindowCatalogue.moment726_157,
    (by decide), (by decide), (by decide), step275_cover⟩

def step276 : Request :=
  ⟨⟨⟨520, 726, 157, 15636⟩, 4261264752640, 7692905725⟩, 2, 4, 2, 514287⟩

theorem step276_nodes : P1_7_1.nodeRows step276.bank.shape = step276.bank.nodeRows :=
  node_check step276.bank (by decide) (by decide) (by decide)

private theorem step276_2330_2335 : Positive step276 2330 2335 := by decide +kernel

private theorem step276_2336_2353 : Positive step276 2336 2353 := by decide +kernel

private theorem step276_2354_2406 : Positive step276 2354 2406 := by decide +kernel

private theorem step276_2407_2499 : Positive step276 2407 2499 := by decide +kernel

theorem step276_cover : ∃ ends, Cover step276 firstHeight ends := by
  exact ⟨[2335, 2353, 2406, 2499],
    ⟨(by decide), (by decide), step276_2330_2335,
      (by decide), (by decide), step276_2336_2353,
      (by decide), (by decide), step276_2354_2406,
      (by decide), (by decide), step276_2407_2499, rfl⟩⟩

theorem step276_verified : Checked step276 :=
  ⟨step276_nodes, Research6966.HelperWindowCatalogue.moment726_157,
    (by decide), (by decide), (by decide), step276_cover⟩

def step277 : Request :=
  ⟨⟨⟨520, 725, 157, 17590⟩, 4261264752640, 7658911630⟩, 3, 4, 2, 514287⟩

theorem step277_nodes : P1_7_1.nodeRows step277.bank.shape = step277.bank.nodeRows :=
  node_check step277.bank (by decide) (by decide) (by decide)

private theorem step277_2330_2337 : Positive step277 2330 2337 := by decide +kernel

private theorem step277_2338_2361 : Positive step277 2338 2361 := by decide +kernel

private theorem step277_2362_2432 : Positive step277 2362 2432 := by decide +kernel

private theorem step277_2433_2499 : Positive step277 2433 2499 := by decide +kernel

theorem step277_cover : ∃ ends, Cover step277 firstHeight ends := by
  exact ⟨[2337, 2361, 2432, 2499],
    ⟨(by decide), (by decide), step277_2330_2337,
      (by decide), (by decide), step277_2338_2361,
      (by decide), (by decide), step277_2362_2432,
      (by decide), (by decide), step277_2433_2499, rfl⟩⟩

theorem step277_verified : Checked step277 :=
  ⟨step277_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step277_cover⟩

def step278 : Request :=
  ⟨⟨⟨630, 879, 195, 17590⟩, 7709474160640, 16827402390⟩, 4, 4, 2, 514287⟩

theorem step278_nodes : P1_7_1.nodeRows step278.bank.shape = step278.bank.nodeRows :=
  node_check step278.bank (by decide) (by decide) (by decide)

private theorem step278_2330_2331 : Positive step278 2330 2331 := by decide +kernel

private theorem step278_2332_2336 : Positive step278 2332 2336 := by decide +kernel

private theorem step278_2337_2350 : Positive step278 2337 2350 := by decide +kernel

private theorem step278_2351_2390 : Positive step278 2351 2390 := by decide +kernel

private theorem step278_2391_2499 : Positive step278 2391 2499 := by decide +kernel

theorem step278_cover : ∃ ends, Cover step278 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2390, 2499],
    ⟨(by decide), (by decide), step278_2330_2331,
      (by decide), (by decide), step278_2332_2336,
      (by decide), (by decide), step278_2337_2350,
      (by decide), (by decide), step278_2351_2390,
      (by decide), (by decide), step278_2391_2499, rfl⟩⟩

theorem step278_verified : Checked step278 :=
  ⟨step278_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step278_cover⟩

def step279 : Request :=
  ⟨⟨⟨630, 879, 190, 19788⟩, 7559493713920, 16491913877⟩, 5, 4, 2, 514287⟩

theorem step279_nodes : P1_7_1.nodeRows step279.bank.shape = step279.bank.nodeRows :=
  node_check step279.bank (by decide) (by decide) (by decide)

private theorem step279_2330_2338 : Positive step279 2330 2338 := by decide +kernel

private theorem step279_2339_2363 : Positive step279 2339 2363 := by decide +kernel

private theorem step279_2364_2436 : Positive step279 2364 2436 := by decide +kernel

private theorem step279_2437_2499 : Positive step279 2437 2499 := by decide +kernel

theorem step279_cover : ∃ ends, Cover step279 firstHeight ends := by
  exact ⟨[2338, 2363, 2436, 2499],
    ⟨(by decide), (by decide), step279_2330_2338,
      (by decide), (by decide), step279_2339_2363,
      (by decide), (by decide), step279_2364_2436,
      (by decide), (by decide), step279_2437_2499, rfl⟩⟩

theorem step279_verified : Checked step279 :=
  ⟨step279_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step279_cover⟩

def step280 : Request :=
  ⟨⟨⟨750, 1047, 226, 22261⟩, 12730741817344, 33110613849⟩, 7, 4, 2, 514287⟩

theorem step280_nodes : P1_7_1.nodeRows step280.bank.shape = step280.bank.nodeRows :=
  node_check step280.bank (by decide) (by decide) (by decide)

private theorem step280_2330_2341 : Positive step280 2330 2341 := by decide +kernel

private theorem step280_2342_2375 : Positive step280 2342 2375 := by decide +kernel

private theorem step280_2376_2471 : Positive step280 2376 2471 := by decide +kernel

private theorem step280_2472_2499 : Positive step280 2472 2499 := by decide +kernel

theorem step280_cover : ∃ ends, Cover step280 firstHeight ends := by
  exact ⟨[2341, 2375, 2471, 2499],
    ⟨(by decide), (by decide), step280_2330_2341,
      (by decide), (by decide), step280_2342_2375,
      (by decide), (by decide), step280_2376_2471,
      (by decide), (by decide), step280_2472_2499, rfl⟩⟩

theorem step280_verified : Checked step280 :=
  ⟨step280_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step280_cover⟩

def step281 : Request :=
  ⟨⟨⟨900, 1256, 272, 25043⟩, 22024701870080, 68653176066⟩, 10, 4, 2, 514287⟩

theorem step281_nodes : P1_7_1.nodeRows step281.bank.shape = step281.bank.nodeRows :=
  node_check step281.bank (by decide) (by decide) (by decide)

private theorem step281_2330_2332 : Positive step281 2330 2332 := by decide +kernel

private theorem step281_2333_2340 : Positive step281 2333 2340 := by decide +kernel

private theorem step281_2341_2362 : Positive step281 2341 2362 := by decide +kernel

private theorem step281_2363_2423 : Positive step281 2363 2423 := by decide +kernel

private theorem step281_2424_2499 : Positive step281 2424 2499 := by decide +kernel

theorem step281_cover : ∃ ends, Cover step281 firstHeight ends := by
  exact ⟨[2332, 2340, 2362, 2423, 2499],
    ⟨(by decide), (by decide), step281_2330_2332,
      (by decide), (by decide), step281_2333_2340,
      (by decide), (by decide), step281_2341_2362,
      (by decide), (by decide), step281_2363_2423,
      (by decide), (by decide), step281_2424_2499, rfl⟩⟩

theorem step281_verified : Checked step281 :=
  ⟨step281_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step281_cover⟩

def step282 : Request :=
  ⟨⟨⟨1100, 1535, 326, 35655⟩, 39579969388544, 150663514795⟩, 16, 4, 2, 514287⟩

theorem step282_nodes : P1_7_1.nodeRows step282.bank.shape = step282.bank.nodeRows :=
  node_check step282.bank (by decide) (by decide) (by decide)

private theorem step282_2330_2339 : Positive step282 2330 2339 := by decide +kernel

private theorem step282_2340_2366 : Positive step282 2340 2366 := by decide +kernel

private theorem step282_2367_2441 : Positive step282 2367 2441 := by decide +kernel

private theorem step282_2442_2499 : Positive step282 2442 2499 := by decide +kernel

theorem step282_cover : ∃ ends, Cover step282 firstHeight ends := by
  exact ⟨[2339, 2366, 2441, 2499],
    ⟨(by decide), (by decide), step282_2330_2339,
      (by decide), (by decide), step282_2340_2366,
      (by decide), (by decide), step282_2367_2441,
      (by decide), (by decide), step282_2442_2499, rfl⟩⟩

theorem step282_verified : Checked step282 :=
  ⟨step282_nodes, Research6966.HelperWindowCatalogue.moment1535_326,
    (by decide), (by decide), (by decide), step282_cover⟩

def step283 : Request :=
  ⟨⟨⟨1350, 1884, 400, 40111⟩, 73092385996800, 341469310532⟩, 20, 4, 2, 514287⟩

theorem step283_nodes : P1_7_1.nodeRows step283.bank.shape = step283.bank.nodeRows :=
  node_check step283.bank (by decide) (by decide) (by decide)

private theorem step283_2330_2338 : Positive step283 2330 2338 := by decide +kernel

private theorem step283_2339_2363 : Positive step283 2339 2363 := by decide +kernel

private theorem step283_2364_2431 : Positive step283 2364 2431 := by decide +kernel

private theorem step283_2432_2499 : Positive step283 2432 2499 := by decide +kernel

theorem step283_cover : ∃ ends, Cover step283 firstHeight ends := by
  exact ⟨[2338, 2363, 2431, 2499],
    ⟨(by decide), (by decide), step283_2330_2338,
      (by decide), (by decide), step283_2339_2363,
      (by decide), (by decide), step283_2364_2431,
      (by decide), (by decide), step283_2432_2499, rfl⟩⟩

theorem step283_verified : Checked step283 :=
  ⟨step283_nodes, Research6966.HelperWindowCatalogue.moment1884_400,
    (by decide), (by decide), (by decide), step283_cover⟩

end Research6966.HelperRescueCatalogue
