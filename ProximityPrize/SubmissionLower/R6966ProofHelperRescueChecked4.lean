import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments4
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments6
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments8
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step74 : Request :=
  ⟨⟨⟨1100, 1535, 341, 10983⟩, 40955142733824, 156029238110⟩, 7, 2, 26, 289021⟩

theorem step74_nodes : P1_7_1.nodeRows step74.bank.shape = step74.bank.nodeRows :=
  node_check step74.bank (by decide) (by decide) (by decide)

private theorem step74_2330_2335 : Positive step74 2330 2335 := by decide +kernel

private theorem step74_2336_2351 : Positive step74 2336 2351 := by decide +kernel

private theorem step74_2352_2394 : Positive step74 2352 2394 := by decide +kernel

private theorem step74_2395_2499 : Positive step74 2395 2499 := by decide +kernel

theorem step74_cover : ∃ ends, Cover step74 firstHeight ends := by
  exact ⟨[2335, 2351, 2394, 2499],
    ⟨(by decide), (by decide), step74_2330_2335,
      (by decide), (by decide), step74_2336_2351,
      (by decide), (by decide), step74_2352_2394,
      (by decide), (by decide), step74_2395_2499, rfl⟩⟩

theorem step74_verified : Checked step74 :=
  ⟨step74_nodes, Research6966.HelperWindowCatalogue.moment1535_341,
    (by decide), (by decide), (by decide), step74_cover⟩

def step75 : Request :=
  ⟨⟨⟨1100, 1535, 341, 13899⟩, 40955142733824, 156029238110⟩, 10, 2, 26, 289021⟩

theorem step75_nodes : P1_7_1.nodeRows step75.bank.shape = step75.bank.nodeRows :=
  node_check step75.bank (by decide) (by decide) (by decide)

private theorem step75_2330_2333 : Positive step75 2330 2333 := by decide +kernel

private theorem step75_2334_2343 : Positive step75 2334 2343 := by decide +kernel

private theorem step75_2344_2371 : Positive step75 2344 2371 := by decide +kernel

private theorem step75_2372_2446 : Positive step75 2372 2446 := by decide +kernel

private theorem step75_2447_2499 : Positive step75 2447 2499 := by decide +kernel

theorem step75_cover : ∃ ends, Cover step75 firstHeight ends := by
  exact ⟨[2333, 2343, 2371, 2446, 2499],
    ⟨(by decide), (by decide), step75_2330_2333,
      (by decide), (by decide), step75_2334_2343,
      (by decide), (by decide), step75_2344_2371,
      (by decide), (by decide), step75_2372_2446,
      (by decide), (by decide), step75_2447_2499, rfl⟩⟩

theorem step75_verified : Checked step75 :=
  ⟨step75_nodes, Research6966.HelperWindowCatalogue.moment1535_341,
    (by decide), (by decide), (by decide), step75_cover⟩

def step76 : Request :=
  ⟨⟨⟨1350, 1884, 418, 19788⟩, 75578221264896, 353372556299⟩, 16, 2, 26, 289021⟩

theorem step76_nodes : P1_7_1.nodeRows step76.bank.shape = step76.bank.nodeRows :=
  node_check step76.bank (by decide) (by decide) (by decide)

private theorem step76_2330_2331 : Positive step76 2330 2331 := by decide +kernel

private theorem step76_2332_2337 : Positive step76 2332 2337 := by decide +kernel

private theorem step76_2338_2353 : Positive step76 2338 2353 := by decide +kernel

private theorem step76_2354_2395 : Positive step76 2354 2395 := by decide +kernel

private theorem step76_2396_2499 : Positive step76 2396 2499 := by decide +kernel

theorem step76_cover : ∃ ends, Cover step76 firstHeight ends := by
  exact ⟨[2331, 2337, 2353, 2395, 2499],
    ⟨(by decide), (by decide), step76_2330_2331,
      (by decide), (by decide), step76_2332_2337,
      (by decide), (by decide), step76_2338_2353,
      (by decide), (by decide), step76_2354_2395,
      (by decide), (by decide), step76_2396_2499, rfl⟩⟩

theorem step76_verified : Checked step76 :=
  ⟨step76_nodes, Research6966.HelperWindowCatalogue.moment1884_418,
    (by decide), (by decide), (by decide), step76_cover⟩

def step77 : Request :=
  ⟨⟨⟨2000, 2791, 620, 19788⟩, 245690786119680, 1701147081935⟩, 20, 2, 26, 289021⟩

theorem step77_nodes : P1_7_1.nodeRows step77.bank.shape = step77.bank.nodeRows :=
  node_check step77.bank (by decide) (by decide) (by decide)

private theorem step77_2330_2342 : Positive step77 2330 2342 := by decide +kernel

private theorem step77_2343_2377 : Positive step77 2343 2377 := by decide +kernel

private theorem step77_2378_2469 : Positive step77 2378 2469 := by decide +kernel

private theorem step77_2470_2499 : Positive step77 2470 2499 := by decide +kernel

theorem step77_cover : ∃ ends, Cover step77 firstHeight ends := by
  exact ⟨[2342, 2377, 2469, 2499],
    ⟨(by decide), (by decide), step77_2330_2342,
      (by decide), (by decide), step77_2343_2377,
      (by decide), (by decide), step77_2378_2469,
      (by decide), (by decide), step77_2470_2499, rfl⟩⟩

theorem step77_verified : Checked step77 :=
  ⟨step77_nodes, Research6966.HelperWindowCatalogue.moment2791_620,
    (by decide), (by decide), (by decide), step77_cover⟩

def step78 : Request :=
  ⟨⟨⟨2500, 3489, 755, 28173⟩, 470210689105920, 4068029992867⟩, 31, 2, 26, 289021⟩

theorem step78_nodes : P1_7_1.nodeRows step78.bank.shape = step78.bank.nodeRows :=
  node_check step78.bank (by decide) (by decide) (by decide)

private theorem step78_2330_2335 : Positive step78 2330 2335 := by decide +kernel

private theorem step78_2336_2350 : Positive step78 2336 2350 := by decide +kernel

private theorem step78_2351_2390 : Positive step78 2351 2390 := by decide +kernel

private theorem step78_2391_2495 : Positive step78 2391 2495 := by decide +kernel

private theorem step78_2496_2499 : Positive step78 2496 2499 := by decide +kernel

theorem step78_cover : ∃ ends, Cover step78 firstHeight ends := by
  exact ⟨[2335, 2350, 2390, 2495, 2499],
    ⟨(by decide), (by decide), step78_2330_2335,
      (by decide), (by decide), step78_2336_2350,
      (by decide), (by decide), step78_2351_2390,
      (by decide), (by decide), step78_2391_2495,
      (by decide), (by decide), step78_2496_2499, rfl⟩⟩

theorem step78_verified : Checked step78 :=
  ⟨step78_nodes, Research6966.HelperWindowCatalogue.moment3489_755,
    (by decide), (by decide), (by decide), step78_cover⟩

def step79 : Request :=
  ⟨⟨⟨2500, 3489, 775, 28173⟩, 479640131993600, 4151672878537⟩, 32, 2, 26, 289021⟩

theorem step79_nodes : P1_7_1.nodeRows step79.bank.shape = step79.bank.nodeRows :=
  node_check step79.bank (by decide) (by decide) (by decide)

private theorem step79_2330_2341 : Positive step79 2330 2341 := by decide +kernel

private theorem step79_2342_2372 : Positive step79 2342 2372 := by decide +kernel

private theorem step79_2373_2453 : Positive step79 2373 2453 := by decide +kernel

private theorem step79_2454_2499 : Positive step79 2454 2499 := by decide +kernel

theorem step79_cover : ∃ ends, Cover step79 firstHeight ends := by
  exact ⟨[2341, 2372, 2453, 2499],
    ⟨(by decide), (by decide), step79_2330_2341,
      (by decide), (by decide), step79_2342_2372,
      (by decide), (by decide), step79_2373_2453,
      (by decide), (by decide), step79_2454_2499, rfl⟩⟩

theorem step79_verified : Checked step79 :=
  ⟨step79_nodes, Research6966.HelperWindowCatalogue.moment3489_775,
    (by decide), (by decide), (by decide), step79_cover⟩

def step80 : Request :=
  ⟨⟨⟨3000, 4187, 930, 35655⟩, 828559354757120, 8606810126747⟩, 44, 2, 26, 289021⟩

theorem step80_nodes : P1_7_1.nodeRows step80.bank.shape = step80.bank.nodeRows :=
  node_check step80.bank (by decide) (by decide) (by decide)

private theorem step80_2330_2331 : Positive step80 2330 2331 := by decide +kernel

private theorem step80_2332_2336 : Positive step80 2332 2336 := by decide +kernel

private theorem step80_2337_2349 : Positive step80 2337 2349 := by decide +kernel

private theorem step80_2350_2383 : Positive step80 2350 2383 := by decide +kernel

private theorem step80_2384_2471 : Positive step80 2384 2471 := by decide +kernel

private theorem step80_2472_2499 : Positive step80 2472 2499 := by decide +kernel

theorem step80_cover : ∃ ends, Cover step80 firstHeight ends := by
  exact ⟨[2331, 2336, 2349, 2383, 2471, 2499],
    ⟨(by decide), (by decide), step80_2330_2331,
      (by decide), (by decide), step80_2332_2336,
      (by decide), (by decide), step80_2337_2349,
      (by decide), (by decide), step80_2350_2383,
      (by decide), (by decide), step80_2384_2471,
      (by decide), (by decide), step80_2472_2499, rfl⟩⟩

theorem step80_verified : Checked step80 :=
  ⟨step80_nodes, Research6966.HelperWindowCatalogue.moment4187_930,
    (by decide), (by decide), (by decide), step80_cover⟩

def step81 : Request :=
  ⟨⟨⟨294, 410, 91, 3008⟩, 790165454848, 805457011⟩, 0, 2, 41, 278153⟩

theorem step81_nodes : P1_7_1.nodeRows step81.bank.shape = step81.bank.nodeRows :=
  node_check step81.bank (by decide) (by decide) (by decide)

private theorem step81_2330_2335 : Positive step81 2330 2335 := by decide +kernel

private theorem step81_2336_2355 : Positive step81 2336 2355 := by decide +kernel

private theorem step81_2356_2422 : Positive step81 2356 2422 := by decide +kernel

private theorem step81_2423_2499 : Positive step81 2423 2499 := by decide +kernel

theorem step81_cover : ∃ ends, Cover step81 firstHeight ends := by
  exact ⟨[2335, 2355, 2422, 2499],
    ⟨(by decide), (by decide), step81_2330_2335,
      (by decide), (by decide), step81_2336_2355,
      (by decide), (by decide), step81_2356_2422,
      (by decide), (by decide), step81_2423_2499, rfl⟩⟩

theorem step81_verified : Checked step81 :=
  ⟨step81_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step81_cover⟩

def step82 : Request :=
  ⟨⟨⟨350, 488, 106, 3384⟩, 1308168290304, 1584729438⟩, 1, 2, 41, 278153⟩

theorem step82_nodes : P1_7_1.nodeRows step82.bank.shape = step82.bank.nodeRows :=
  node_check step82.bank (by decide) (by decide) (by decide)

private theorem step82_2330_2357 : Positive step82 2330 2357 := by decide +kernel

private theorem step82_2358_2448 : Positive step82 2358 2448 := by decide +kernel

private theorem step82_2449_2499 : Positive step82 2449 2499 := by decide +kernel

theorem step82_cover : ∃ ends, Cover step82 firstHeight ends := by
  exact ⟨[2357, 2448, 2499],
    ⟨(by decide), (by decide), step82_2330_2357,
      (by decide), (by decide), step82_2358_2448,
      (by decide), (by decide), step82_2449_2499, rfl⟩⟩

theorem step82_verified : Checked step82 :=
  ⟨step82_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step82_cover⟩

def step83 : Request :=
  ⟨⟨⟨350, 488, 108, 3807⟩, 1326705278976, 1607754763⟩, 2, 2, 41, 278153⟩

theorem step83_nodes : P1_7_1.nodeRows step83.bank.shape = step83.bank.nodeRows :=
  node_check step83.bank (by decide) (by decide) (by decide)

private theorem step83_2330_2344 : Positive step83 2330 2344 := by decide +kernel

private theorem step83_2345_2392 : Positive step83 2345 2392 := by decide +kernel

private theorem step83_2393_2499 : Positive step83 2393 2499 := by decide +kernel

theorem step83_cover : ∃ ends, Cover step83 firstHeight ends := by
  exact ⟨[2344, 2392, 2499],
    ⟨(by decide), (by decide), step83_2330_2344,
      (by decide), (by decide), step83_2345_2392,
      (by decide), (by decide), step83_2393_2499, rfl⟩⟩

theorem step83_verified : Checked step83 :=
  ⟨step83_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step83_cover⟩

def step84 : Request :=
  ⟨⟨⟨420, 586, 127, 3807⟩, 2252760678400, 3279920952⟩, 3, 2, 41, 278153⟩

theorem step84_nodes : P1_7_1.nodeRows step84.bank.shape = step84.bank.nodeRows :=
  node_check step84.bank (by decide) (by decide) (by decide)

private theorem step84_2330_2341 : Positive step84 2330 2341 := by decide +kernel

private theorem step84_2342_2378 : Positive step84 2342 2378 := by decide +kernel

private theorem step84_2379_2492 : Positive step84 2379 2492 := by decide +kernel

private theorem step84_2493_2499 : Positive step84 2493 2499 := by decide +kernel

theorem step84_cover : ∃ ends, Cover step84 firstHeight ends := by
  exact ⟨[2341, 2378, 2492, 2499],
    ⟨(by decide), (by decide), step84_2330_2341,
      (by decide), (by decide), step84_2342_2378,
      (by decide), (by decide), step84_2379_2492,
      (by decide), (by decide), step84_2493_2499, rfl⟩⟩

theorem step84_verified : Checked step84 :=
  ⟨step84_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step84_cover⟩

def step85 : Request :=
  ⟨⟨⟨420, 586, 127, 4282⟩, 2252760678400, 3279920952⟩, 4, 2, 41, 278153⟩

theorem step85_nodes : P1_7_1.nodeRows step85.bank.shape = step85.bank.nodeRows :=
  node_check step85.bank (by decide) (by decide) (by decide)

private theorem step85_2330_2332 : Positive step85 2330 2332 := by decide +kernel

private theorem step85_2333_2342 : Positive step85 2333 2342 := by decide +kernel

private theorem step85_2343_2372 : Positive step85 2343 2372 := by decide +kernel

private theorem step85_2373_2465 : Positive step85 2373 2465 := by decide +kernel

private theorem step85_2466_2499 : Positive step85 2466 2499 := by decide +kernel

theorem step85_cover : ∃ ends, Cover step85 firstHeight ends := by
  exact ⟨[2332, 2342, 2372, 2465, 2499],
    ⟨(by decide), (by decide), step85_2330_2332,
      (by decide), (by decide), step85_2333_2342,
      (by decide), (by decide), step85_2343_2372,
      (by decide), (by decide), step85_2373_2465,
      (by decide), (by decide), step85_2466_2499, rfl⟩⟩

theorem step85_verified : Checked step85 :=
  ⟨step85_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step85_cover⟩

def step86 : Request :=
  ⟨⟨⟨520, 725, 157, 4282⟩, 4261264752640, 7658911630⟩, 5, 2, 41, 278153⟩

theorem step86_nodes : P1_7_1.nodeRows step86.bank.shape = step86.bank.nodeRows :=
  node_check step86.bank (by decide) (by decide) (by decide)

private theorem step86_2330_2339 : Positive step86 2330 2339 := by decide +kernel

private theorem step86_2340_2369 : Positive step86 2340 2369 := by decide +kernel

private theorem step86_2370_2458 : Positive step86 2370 2458 := by decide +kernel

private theorem step86_2459_2499 : Positive step86 2459 2499 := by decide +kernel

theorem step86_cover : ∃ ends, Cover step86 firstHeight ends := by
  exact ⟨[2339, 2369, 2458, 2499],
    ⟨(by decide), (by decide), step86_2330_2339,
      (by decide), (by decide), step86_2340_2369,
      (by decide), (by decide), step86_2370_2458,
      (by decide), (by decide), step86_2459_2499, rfl⟩⟩

theorem step86_verified : Checked step86 :=
  ⟨step86_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step86_cover⟩

def step87 : Request :=
  ⟨⟨⟨520, 725, 161, 4817⟩, 4343013310464, 7809559934⟩, 7, 2, 41, 278153⟩

theorem step87_nodes : P1_7_1.nodeRows step87.bank.shape = step87.bank.nodeRows :=
  node_check step87.bank (by decide) (by decide) (by decide)

private theorem step87_2330_2341 : Positive step87 2330 2341 := by decide +kernel

private theorem step87_2342_2377 : Positive step87 2342 2377 := by decide +kernel

private theorem step87_2378_2483 : Positive step87 2378 2483 := by decide +kernel

private theorem step87_2484_2499 : Positive step87 2484 2499 := by decide +kernel

theorem step87_cover : ∃ ends, Cover step87 firstHeight ends := by
  exact ⟨[2341, 2377, 2483, 2499],
    ⟨(by decide), (by decide), step87_2330_2341,
      (by decide), (by decide), step87_2342_2377,
      (by decide), (by decide), step87_2378_2483,
      (by decide), (by decide), step87_2484_2499, rfl⟩⟩

theorem step87_verified : Checked step87 :=
  ⟨step87_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step87_cover⟩

def step88 : Request :=
  ⟨⟨⟨630, 879, 195, 5419⟩, 7709474160640, 16827402390⟩, 10, 2, 41, 278153⟩

theorem step88_nodes : P1_7_1.nodeRows step88.bank.shape = step88.bank.nodeRows :=
  node_check step88.bank (by decide) (by decide) (by decide)

private theorem step88_2330_2330 : Positive step88 2330 2330 := by decide +kernel

private theorem step88_2331_2333 : Positive step88 2331 2333 := by decide +kernel

private theorem step88_2334_2341 : Positive step88 2334 2341 := by decide +kernel

private theorem step88_2342_2364 : Positive step88 2342 2364 := by decide +kernel

private theorem step88_2365_2430 : Positive step88 2365 2430 := by decide +kernel

private theorem step88_2431_2499 : Positive step88 2431 2499 := by decide +kernel

theorem step88_cover : ∃ ends, Cover step88 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2364, 2430, 2499],
    ⟨(by decide), (by decide), step88_2330_2330,
      (by decide), (by decide), step88_2331_2333,
      (by decide), (by decide), step88_2334_2341,
      (by decide), (by decide), step88_2342_2364,
      (by decide), (by decide), step88_2365_2430,
      (by decide), (by decide), step88_2431_2499, rfl⟩⟩

theorem step88_verified : Checked step88 :=
  ⟨step88_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step88_cover⟩

def step89 : Request :=
  ⟨⟨⟨750, 1046, 232, 7715⟩, 12985818152960, 33687112323⟩, 16, 2, 41, 278153⟩

theorem step89_nodes : P1_7_1.nodeRows step89.bank.shape = step89.bank.nodeRows :=
  node_check step89.bank (by decide) (by decide) (by decide)

private theorem step89_2330_2335 : Positive step89 2330 2335 := by decide +kernel

private theorem step89_2336_2352 : Positive step89 2336 2352 := by decide +kernel

private theorem step89_2353_2400 : Positive step89 2353 2400 := by decide +kernel

private theorem step89_2401_2499 : Positive step89 2401 2499 := by decide +kernel

theorem step89_cover : ∃ ends, Cover step89 firstHeight ends := by
  exact ⟨[2335, 2352, 2400, 2499],
    ⟨(by decide), (by decide), step89_2330_2335,
      (by decide), (by decide), step89_2336_2352,
      (by decide), (by decide), step89_2353_2400,
      (by decide), (by decide), step89_2401_2499, rfl⟩⟩

theorem step89_verified : Checked step89 :=
  ⟨step89_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step89_cover⟩

def step90 : Request :=
  ⟨⟨⟨900, 1256, 279, 8679⟩, 22452680785920, 70021105933⟩, 20, 2, 41, 278153⟩

theorem step90_nodes : P1_7_1.nodeRows step90.bank.shape = step90.bank.nodeRows :=
  node_check step90.bank (by decide) (by decide) (by decide)

private theorem step90_2330_2344 : Positive step90 2330 2344 := by decide +kernel

private theorem step90_2345_2385 : Positive step90 2345 2385 := by decide +kernel

private theorem step90_2386_2499 : Positive step90 2386 2499 := by decide +kernel

theorem step90_cover : ∃ ends, Cover step90 firstHeight ends := by
  exact ⟨[2344, 2385, 2499],
    ⟨(by decide), (by decide), step90_2330_2344,
      (by decide), (by decide), step90_2345_2385,
      (by decide), (by decide), step90_2386_2499, rfl⟩⟩

theorem step90_verified : Checked step90 :=
  ⟨step90_nodes, Research6966.HelperWindowCatalogue.moment1256_279,
    (by decide), (by decide), (by decide), step90_cover⟩

def step91 : Request :=
  ⟨⟨⟨1350, 1883, 418, 10983⟩, 75578221264896, 352769102024⟩, 31, 2, 41, 278153⟩

theorem step91_nodes : P1_7_1.nodeRows step91.bank.shape = step91.bank.nodeRows :=
  node_check step91.bank (by decide) (by decide) (by decide)

private theorem step91_2330_2335 : Positive step91 2330 2335 := by decide +kernel

private theorem step91_2336_2351 : Positive step91 2336 2351 := by decide +kernel

private theorem step91_2352_2394 : Positive step91 2352 2394 := by decide +kernel

private theorem step91_2395_2499 : Positive step91 2395 2499 := by decide +kernel

theorem step91_cover : ∃ ends, Cover step91 firstHeight ends := by
  exact ⟨[2335, 2351, 2394, 2499],
    ⟨(by decide), (by decide), step91_2330_2335,
      (by decide), (by decide), step91_2336_2351,
      (by decide), (by decide), step91_2352_2394,
      (by decide), (by decide), step91_2395_2499, rfl⟩⟩

theorem step91_verified : Checked step91 :=
  ⟨step91_nodes, Research6966.HelperWindowCatalogue.moment1883_418,
    (by decide), (by decide), (by decide), step91_cover⟩

def step92 : Request :=
  ⟨⟨⟨1350, 1883, 408, 12355⟩, 74202776600576, 346190054868⟩, 32, 2, 41, 278153⟩

theorem step92_nodes : P1_7_1.nodeRows step92.bank.shape = step92.bank.nodeRows :=
  node_check step92.bank (by decide) (by decide) (by decide)

private theorem step92_2330_2347 : Positive step92 2330 2347 := by decide +kernel

private theorem step92_2348_2396 : Positive step92 2348 2396 := by decide +kernel

private theorem step92_2397_2499 : Positive step92 2397 2499 := by decide +kernel

theorem step92_cover : ∃ ends, Cover step92 firstHeight ends := by
  exact ⟨[2347, 2396, 2499],
    ⟨(by decide), (by decide), step92_2330_2347,
      (by decide), (by decide), step92_2348_2396,
      (by decide), (by decide), step92_2397_2499, rfl⟩⟩

theorem step92_verified : Checked step92 :=
  ⟨step92_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step92_cover⟩

def step93 : Request :=
  ⟨⟨⟨1650, 2302, 512, 15636⟩, 138129879859200, 788519769358⟩, 44, 2, 41, 278153⟩

theorem step93_nodes : P1_7_1.nodeRows step93.bank.shape = step93.bank.nodeRows :=
  node_check step93.bank (by decide) (by decide) (by decide)

private theorem step93_2330_2353 : Positive step93 2330 2353 := by decide +kernel

private theorem step93_2354_2417 : Positive step93 2354 2417 := by decide +kernel

private theorem step93_2418_2499 : Positive step93 2418 2499 := by decide +kernel

theorem step93_cover : ∃ ends, Cover step93 firstHeight ends := by
  exact ⟨[2353, 2417, 2499],
    ⟨(by decide), (by decide), step93_2330_2353,
      (by decide), (by decide), step93_2354_2417,
      (by decide), (by decide), step93_2418_2499, rfl⟩⟩

theorem step93_verified : Checked step93 :=
  ⟨step93_nodes, Research6966.HelperWindowCatalogue.moment2302_512,
    (by decide), (by decide), (by decide), step93_cover⟩

def step94 : Request :=
  ⟨⟨⟨2500, 3488, 755, 25043⟩, 470210689105920, 4064279218567⟩, 73, 2, 41, 278153⟩

theorem step94_nodes : P1_7_1.nodeRows step94.bank.shape = step94.bank.nodeRows :=
  node_check step94.bank (by decide) (by decide) (by decide)

private theorem step94_2330_2336 : Positive step94 2330 2336 := by decide +kernel

private theorem step94_2337_2355 : Positive step94 2337 2355 := by decide +kernel

private theorem step94_2356_2405 : Positive step94 2356 2405 := by decide +kernel

private theorem step94_2406_2499 : Positive step94 2406 2499 := by decide +kernel

theorem step94_cover : ∃ ends, Cover step94 firstHeight ends := by
  exact ⟨[2336, 2355, 2405, 2499],
    ⟨(by decide), (by decide), step94_2330_2336,
      (by decide), (by decide), step94_2337_2355,
      (by decide), (by decide), step94_2356_2405,
      (by decide), (by decide), step94_2406_2499, rfl⟩⟩

theorem step94_verified : Checked step94 :=
  ⟨step94_nodes, Research6966.HelperWindowCatalogue.moment3488_755,
    (by decide), (by decide), (by decide), step94_cover⟩

def step95 : Request :=
  ⟨⟨⟨2500, 3488, 775, 25043⟩, 479640131993600, 4147842034257⟩, 76, 2, 41, 278153⟩

theorem step95_nodes : P1_7_1.nodeRows step95.bank.shape = step95.bank.nodeRows :=
  node_check step95.bank (by decide) (by decide) (by decide)

private theorem step95_2330_2339 : Positive step95 2330 2339 := by decide +kernel

private theorem step95_2340_2366 : Positive step95 2340 2366 := by decide +kernel

private theorem step95_2367_2436 : Positive step95 2367 2436 := by decide +kernel

private theorem step95_2437_2499 : Positive step95 2437 2499 := by decide +kernel

theorem step95_cover : ∃ ends, Cover step95 firstHeight ends := by
  exact ⟨[2339, 2366, 2436, 2499],
    ⟨(by decide), (by decide), step95_2330_2339,
      (by decide), (by decide), step95_2340_2366,
      (by decide), (by decide), step95_2367_2436,
      (by decide), (by decide), step95_2437_2499, rfl⟩⟩

theorem step95_verified : Checked step95 :=
  ⟨step95_nodes, Research6966.HelperWindowCatalogue.moment3488_775,
    (by decide), (by decide), (by decide), step95_cover⟩

def step96 : Request :=
  ⟨⟨⟨3500, 4883, 1085, 31694⟩, 1315428062986240, 15921388386716⟩, 103, 2, 41, 278153⟩

theorem step96_nodes : P1_7_1.nodeRows step96.bank.shape = step96.bank.nodeRows :=
  node_check step96.bank (by decide) (by decide) (by decide)

private theorem step96_2330_2347 : Positive step96 2330 2347 := by decide +kernel

private theorem step96_2348_2394 : Positive step96 2348 2394 := by decide +kernel

private theorem step96_2395_2499 : Positive step96 2395 2499 := by decide +kernel

theorem step96_cover : ∃ ends, Cover step96 firstHeight ends := by
  exact ⟨[2347, 2394, 2499],
    ⟨(by decide), (by decide), step96_2330_2347,
      (by decide), (by decide), step96_2348_2394,
      (by decide), (by decide), step96_2395_2499, rfl⟩⟩

theorem step96_verified : Checked step96 :=
  ⟨step96_nodes, Research6966.HelperWindowCatalogue.moment4883_1085,
    (by decide), (by decide), (by decide), step96_cover⟩

def step97 : Request :=
  ⟨⟨⟨250, 349, 76, 2377⟩, 480667500544, 418199213⟩, 0, 2, 51, 257143⟩

theorem step97_nodes : P1_7_1.nodeRows step97.bank.shape = step97.bank.nodeRows :=
  node_check step97.bank (by decide) (by decide) (by decide)

private theorem step97_2330_2346 : Positive step97 2330 2346 := by decide +kernel

private theorem step97_2347_2406 : Positive step97 2347 2406 := by decide +kernel

private theorem step97_2407_2499 : Positive step97 2407 2499 := by decide +kernel

theorem step97_cover : ∃ ends, Cover step97 firstHeight ends := by
  exact ⟨[2346, 2406, 2499],
    ⟨(by decide), (by decide), step97_2330_2346,
      (by decide), (by decide), step97_2347_2406,
      (by decide), (by decide), step97_2407_2499, rfl⟩⟩

theorem step97_verified : Checked step97 :=
  ⟨step97_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step97_cover⟩

def step98 : Request :=
  ⟨⟨⟨250, 349, 78, 3008⟩, 490108092416, 426627288⟩, 1, 2, 51, 257143⟩

theorem step98_nodes : P1_7_1.nodeRows step98.bank.shape = step98.bank.nodeRows :=
  node_check step98.bank (by decide) (by decide) (by decide)

private theorem step98_2330_2331 : Positive step98 2330 2331 := by decide +kernel

private theorem step98_2332_2338 : Positive step98 2332 2338 := by decide +kernel

private theorem step98_2339_2362 : Positive step98 2339 2362 := by decide +kernel

private theorem step98_2363_2447 : Positive step98 2363 2447 := by decide +kernel

private theorem step98_2448_2499 : Positive step98 2448 2499 := by decide +kernel

theorem step98_cover : ∃ ends, Cover step98 firstHeight ends := by
  exact ⟨[2331, 2338, 2362, 2447, 2499],
    ⟨(by decide), (by decide), step98_2330_2331,
      (by decide), (by decide), step98_2332_2338,
      (by decide), (by decide), step98_2339_2362,
      (by decide), (by decide), step98_2363_2447,
      (by decide), (by decide), step98_2448_2499, rfl⟩⟩

theorem step98_verified : Checked step98 :=
  ⟨step98_nodes, Research6966.HelperWindowCatalogue.moment349_78,
    (by decide), (by decide), (by decide), step98_cover⟩

def step99 : Request :=
  ⟨⟨⟨294, 410, 91, 2674⟩, 790165454848, 805457011⟩, 2, 2, 51, 257143⟩

theorem step99_nodes : P1_7_1.nodeRows step99.bank.shape = step99.bank.nodeRows :=
  node_check step99.bank (by decide) (by decide) (by decide)

private theorem step99_2330_2331 : Positive step99 2330 2331 := by decide +kernel

private theorem step99_2332_2337 : Positive step99 2332 2337 := by decide +kernel

private theorem step99_2338_2357 : Positive step99 2338 2357 := by decide +kernel

private theorem step99_2358_2424 : Positive step99 2358 2424 := by decide +kernel

private theorem step99_2425_2499 : Positive step99 2425 2499 := by decide +kernel

theorem step99_cover : ∃ ends, Cover step99 firstHeight ends := by
  exact ⟨[2331, 2337, 2357, 2424, 2499],
    ⟨(by decide), (by decide), step99_2330_2331,
      (by decide), (by decide), step99_2332_2337,
      (by decide), (by decide), step99_2338_2357,
      (by decide), (by decide), step99_2358_2424,
      (by decide), (by decide), step99_2425_2499, rfl⟩⟩

theorem step99_verified : Checked step99 :=
  ⟨step99_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step99_cover⟩

def step100 : Request :=
  ⟨⟨⟨294, 410, 91, 3807⟩, 790165454848, 805457011⟩, 3, 2, 51, 257143⟩

theorem step100_nodes : P1_7_1.nodeRows step100.bank.shape = step100.bank.nodeRows :=
  node_check step100.bank (by decide) (by decide) (by decide)

private theorem step100_2330_2334 : Positive step100 2330 2334 := by decide +kernel

private theorem step100_2335_2351 : Positive step100 2335 2351 := by decide +kernel

private theorem step100_2352_2408 : Positive step100 2352 2408 := by decide +kernel

private theorem step100_2409_2499 : Positive step100 2409 2499 := by decide +kernel

theorem step100_cover : ∃ ends, Cover step100 firstHeight ends := by
  exact ⟨[2334, 2351, 2408, 2499],
    ⟨(by decide), (by decide), step100_2330_2334,
      (by decide), (by decide), step100_2335_2351,
      (by decide), (by decide), step100_2352_2408,
      (by decide), (by decide), step100_2409_2499, rfl⟩⟩

theorem step100_verified : Checked step100 :=
  ⟨step100_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step100_cover⟩

def step101 : Request :=
  ⟨⟨⟨350, 488, 106, 3384⟩, 1308168290304, 1584729438⟩, 4, 2, 51, 257143⟩

theorem step101_nodes : P1_7_1.nodeRows step101.bank.shape = step101.bank.nodeRows :=
  node_check step101.bank (by decide) (by decide) (by decide)

private theorem step101_2330_2356 : Positive step101 2330 2356 := by decide +kernel

private theorem step101_2357_2443 : Positive step101 2357 2443 := by decide +kernel

private theorem step101_2444_2499 : Positive step101 2444 2499 := by decide +kernel

theorem step101_cover : ∃ ends, Cover step101 firstHeight ends := by
  exact ⟨[2356, 2443, 2499],
    ⟨(by decide), (by decide), step101_2330_2356,
      (by decide), (by decide), step101_2357_2443,
      (by decide), (by decide), step101_2444_2499, rfl⟩⟩

theorem step101_verified : Checked step101 :=
  ⟨step101_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step101_cover⟩

def step102 : Request :=
  ⟨⟨⟨350, 488, 106, 3807⟩, 1308168290304, 1584729438⟩, 5, 2, 51, 257143⟩

theorem step102_nodes : P1_7_1.nodeRows step102.bank.shape = step102.bank.nodeRows :=
  node_check step102.bank (by decide) (by decide) (by decide)

private theorem step102_2330_2332 : Positive step102 2330 2332 := by decide +kernel

private theorem step102_2333_2342 : Positive step102 2333 2342 := by decide +kernel

private theorem step102_2343_2374 : Positive step102 2343 2374 := by decide +kernel

private theorem step102_2375_2477 : Positive step102 2375 2477 := by decide +kernel

private theorem step102_2478_2499 : Positive step102 2478 2499 := by decide +kernel

theorem step102_cover : ∃ ends, Cover step102 firstHeight ends := by
  exact ⟨[2332, 2342, 2374, 2477, 2499],
    ⟨(by decide), (by decide), step102_2330_2332,
      (by decide), (by decide), step102_2333_2342,
      (by decide), (by decide), step102_2343_2374,
      (by decide), (by decide), step102_2375_2477,
      (by decide), (by decide), step102_2478_2499, rfl⟩⟩

theorem step102_verified : Checked step102 :=
  ⟨step102_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step102_cover⟩

def step103 : Request :=
  ⟨⟨⟨420, 586, 130, 3807⟩, 2292767784960, 3339653140⟩, 7, 2, 51, 257143⟩

theorem step103_nodes : P1_7_1.nodeRows step103.bank.shape = step103.bank.nodeRows :=
  node_check step103.bank (by decide) (by decide) (by decide)

private theorem step103_2330_2339 : Positive step103 2330 2339 := by decide +kernel

private theorem step103_2340_2370 : Positive step103 2340 2370 := by decide +kernel

private theorem step103_2371_2465 : Positive step103 2371 2465 := by decide +kernel

private theorem step103_2466_2499 : Positive step103 2466 2499 := by decide +kernel

theorem step103_cover : ∃ ends, Cover step103 firstHeight ends := by
  exact ⟨[2339, 2370, 2465, 2499],
    ⟨(by decide), (by decide), step103_2330_2339,
      (by decide), (by decide), step103_2340_2370,
      (by decide), (by decide), step103_2371_2465,
      (by decide), (by decide), step103_2466_2499, rfl⟩⟩

theorem step103_verified : Checked step103 :=
  ⟨step103_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step103_cover⟩

def step104 : Request :=
  ⟨⟨⟨520, 725, 161, 4282⟩, 4343013310464, 7809559934⟩, 10, 2, 51, 257143⟩

theorem step104_nodes : P1_7_1.nodeRows step104.bank.shape = step104.bank.nodeRows :=
  node_check step104.bank (by decide) (by decide) (by decide)

private theorem step104_2330_2335 : Positive step104 2330 2335 := by decide +kernel

private theorem step104_2336_2352 : Positive step104 2336 2352 := by decide +kernel

private theorem step104_2353_2403 : Positive step104 2353 2403 := by decide +kernel

private theorem step104_2404_2499 : Positive step104 2404 2499 := by decide +kernel

theorem step104_cover : ∃ ends, Cover step104 firstHeight ends := by
  exact ⟨[2335, 2352, 2403, 2499],
    ⟨(by decide), (by decide), step104_2330_2335,
      (by decide), (by decide), step104_2336_2352,
      (by decide), (by decide), step104_2353_2403,
      (by decide), (by decide), step104_2404_2499, rfl⟩⟩

theorem step104_verified : Checked step104 :=
  ⟨step104_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step104_cover⟩

def step105 : Request :=
  ⟨⟨⟨630, 879, 195, 6096⟩, 7709474160640, 16827402390⟩, 16, 2, 51, 257143⟩

theorem step105_nodes : P1_7_1.nodeRows step105.bank.shape = step105.bank.nodeRows :=
  node_check step105.bank (by decide) (by decide) (by decide)

private theorem step105_2330_2353 : Positive step105 2330 2353 := by decide +kernel

private theorem step105_2354_2422 : Positive step105 2354 2422 := by decide +kernel

private theorem step105_2423_2499 : Positive step105 2423 2499 := by decide +kernel

theorem step105_cover : ∃ ends, Cover step105 firstHeight ends := by
  exact ⟨[2353, 2422, 2499],
    ⟨(by decide), (by decide), step105_2330_2353,
      (by decide), (by decide), step105_2354_2422,
      (by decide), (by decide), step105_2423_2499, rfl⟩⟩

theorem step105_verified : Checked step105 :=
  ⟨step105_nodes, Research6966.HelperWindowCatalogue.moment879_195,
    (by decide), (by decide), (by decide), step105_cover⟩

def step106 : Request :=
  ⟨⟨⟨750, 1046, 226, 6858⟩, 12730741817344, 33009058589⟩, 20, 2, 51, 257143⟩

theorem step106_nodes : P1_7_1.nodeRows step106.bank.shape = step106.bank.nodeRows :=
  node_check step106.bank (by decide) (by decide) (by decide)

private theorem step106_2330_2331 : Positive step106 2330 2331 := by decide +kernel

private theorem step106_2332_2336 : Positive step106 2332 2336 := by decide +kernel

private theorem step106_2337_2350 : Positive step106 2337 2350 := by decide +kernel

private theorem step106_2351_2390 : Positive step106 2351 2390 := by decide +kernel

private theorem step106_2391_2499 : Positive step106 2391 2499 := by decide +kernel

theorem step106_cover : ∃ ends, Cover step106 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2390, 2499],
    ⟨(by decide), (by decide), step106_2330_2331,
      (by decide), (by decide), step106_2332_2336,
      (by decide), (by decide), step106_2337_2350,
      (by decide), (by decide), step106_2351_2390,
      (by decide), (by decide), step106_2391_2499, rfl⟩⟩

theorem step106_verified : Checked step106 :=
  ⟨step106_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step106_cover⟩

def step107 : Request :=
  ⟨⟨⟨1100, 1534, 341, 8679⟩, 40955142733824, 155702293064⟩, 31, 2, 51, 257143⟩

theorem step107_nodes : P1_7_1.nodeRows step107.bank.shape = step107.bank.nodeRows :=
  node_check step107.bank (by decide) (by decide) (by decide)

private theorem step107_2330_2336 : Positive step107 2330 2336 := by decide +kernel

private theorem step107_2337_2355 : Positive step107 2337 2355 := by decide +kernel

private theorem step107_2356_2407 : Positive step107 2356 2407 := by decide +kernel

private theorem step107_2408_2499 : Positive step107 2408 2499 := by decide +kernel

theorem step107_cover : ∃ ends, Cover step107 firstHeight ends := by
  exact ⟨[2336, 2355, 2407, 2499],
    ⟨(by decide), (by decide), step107_2330_2336,
      (by decide), (by decide), step107_2337_2355,
      (by decide), (by decide), step107_2356_2407,
      (by decide), (by decide), step107_2408_2499, rfl⟩⟩

theorem step107_verified : Checked step107 :=
  ⟨step107_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step107_cover⟩

def step108 : Request :=
  ⟨⟨⟨1100, 1534, 332, 9763⟩, 40133103452160, 152499774767⟩, 32, 2, 51, 257143⟩

theorem step108_nodes : P1_7_1.nodeRows step108.bank.shape = step108.bank.nodeRows :=
  node_check step108.bank (by decide) (by decide) (by decide)

private theorem step108_2330_2353 : Positive step108 2330 2353 := by decide +kernel

private theorem step108_2354_2420 : Positive step108 2354 2420 := by decide +kernel

private theorem step108_2421_2499 : Positive step108 2421 2499 := by decide +kernel

theorem step108_cover : ∃ ends, Cover step108 firstHeight ends := by
  exact ⟨[2353, 2420, 2499],
    ⟨(by decide), (by decide), step108_2330_2353,
      (by decide), (by decide), step108_2354_2420,
      (by decide), (by decide), step108_2421_2499, rfl⟩⟩

theorem step108_verified : Checked step108 :=
  ⟨step108_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step108_cover⟩

def step109 : Request :=
  ⟨⟨⟨1350, 1883, 408, 12355⟩, 74202776600576, 346190054868⟩, 44, 2, 51, 257143⟩

theorem step109_nodes : P1_7_1.nodeRows step109.bank.shape = step109.bank.nodeRows :=
  node_check step109.bank (by decide) (by decide) (by decide)

private theorem step109_2330_2337 : Positive step109 2330 2337 := by decide +kernel

private theorem step109_2338_2358 : Positive step109 2338 2358 := by decide +kernel

private theorem step109_2359_2415 : Positive step109 2359 2415 := by decide +kernel

private theorem step109_2416_2499 : Positive step109 2416 2499 := by decide +kernel

theorem step109_cover : ∃ ends, Cover step109 firstHeight ends := by
  exact ⟨[2337, 2358, 2415, 2499],
    ⟨(by decide), (by decide), step109_2330_2337,
      (by decide), (by decide), step109_2338_2358,
      (by decide), (by decide), step109_2359_2415,
      (by decide), (by decide), step109_2416_2499, rfl⟩⟩

theorem step109_verified : Checked step109 :=
  ⟨step109_nodes, Research6966.HelperWindowCatalogue.moment1883_408,
    (by decide), (by decide), (by decide), step109_cover⟩

def step110 : Request :=
  ⟨⟨⟨2000, 2790, 604, 19788⟩, 240862397726720, 1664965815864⟩, 73, 2, 51, 257143⟩

theorem step110_nodes : P1_7_1.nodeRows step110.bank.shape = step110.bank.nodeRows :=
  node_check step110.bank (by decide) (by decide) (by decide)

private theorem step110_2330_2337 : Positive step110 2330 2337 := by decide +kernel

private theorem step110_2338_2358 : Positive step110 2338 2358 := by decide +kernel

private theorem step110_2359_2414 : Positive step110 2359 2414 := by decide +kernel

private theorem step110_2415_2499 : Positive step110 2415 2499 := by decide +kernel

theorem step110_cover : ∃ ends, Cover step110 firstHeight ends := by
  exact ⟨[2337, 2358, 2414, 2499],
    ⟨(by decide), (by decide), step110_2330_2337,
      (by decide), (by decide), step110_2338_2358,
      (by decide), (by decide), step110_2359_2414,
      (by decide), (by decide), step110_2415_2499, rfl⟩⟩

theorem step110_verified : Checked step110 :=
  ⟨step110_nodes, Research6966.HelperWindowCatalogue.moment2790_604,
    (by decide), (by decide), (by decide), step110_cover⟩

def step111 : Request :=
  ⟨⟨⟨2000, 2789, 620, 19788⟩, 245690786119680, 1697224818404⟩, 76, 2, 51, 257143⟩

theorem step111_nodes : P1_7_1.nodeRows step111.bank.shape = step111.bank.nodeRows :=
  node_check step111.bank (by decide) (by decide) (by decide)

private theorem step111_2330_2338 : Positive step111 2330 2338 := by decide +kernel

private theorem step111_2339_2361 : Positive step111 2339 2361 := by decide +kernel

private theorem step111_2362_2422 : Positive step111 2362 2422 := by decide +kernel

private theorem step111_2423_2499 : Positive step111 2423 2499 := by decide +kernel

theorem step111_cover : ∃ ends, Cover step111 firstHeight ends := by
  exact ⟨[2338, 2361, 2422, 2499],
    ⟨(by decide), (by decide), step111_2330_2338,
      (by decide), (by decide), step111_2339_2361,
      (by decide), (by decide), step111_2362_2422,
      (by decide), (by decide), step111_2423_2499, rfl⟩⟩

theorem step111_verified : Checked step111 :=
  ⟨step111_nodes, Research6966.HelperWindowCatalogue.moment2789_620,
    (by decide), (by decide), (by decide), step111_cover⟩

def step112 : Request :=
  ⟨⟨⟨2500, 3487, 775, 31694⟩, 479640131993600, 4144013596741⟩, 103, 2, 51, 257143⟩

theorem step112_nodes : P1_7_1.nodeRows step112.bank.shape = step112.bank.nodeRows :=
  node_check step112.bank (by decide) (by decide) (by decide)

private theorem step112_2330_2333 : Positive step112 2330 2333 := by decide +kernel

private theorem step112_2334_2344 : Positive step112 2334 2344 := by decide +kernel

private theorem step112_2345_2373 : Positive step112 2345 2373 := by decide +kernel

private theorem step112_2374_2449 : Positive step112 2374 2449 := by decide +kernel

private theorem step112_2450_2499 : Positive step112 2450 2499 := by decide +kernel

theorem step112_cover : ∃ ends, Cover step112 firstHeight ends := by
  exact ⟨[2333, 2344, 2373, 2449, 2499],
    ⟨(by decide), (by decide), step112_2330_2333,
      (by decide), (by decide), step112_2334_2344,
      (by decide), (by decide), step112_2345_2373,
      (by decide), (by decide), step112_2374_2449,
      (by decide), (by decide), step112_2450_2499, rfl⟩⟩

theorem step112_verified : Checked step112 :=
  ⟨step112_nodes, Research6966.HelperWindowCatalogue.moment3487_775,
    (by decide), (by decide), (by decide), step112_cover⟩

def step113 : Request :=
  ⟨⟨⟨210, 293, 62, 1879⟩, 279710269440, 204151930⟩, 0, 2, 71, 257143⟩

theorem step113_nodes : P1_7_1.nodeRows step113.bank.shape = step113.bank.nodeRows :=
  node_check step113.bank (by decide) (by decide) (by decide)

private theorem step113_2330_2345 : Positive step113 2330 2345 := by decide +kernel

private theorem step113_2346_2408 : Positive step113 2346 2408 := by decide +kernel

private theorem step113_2409_2499 : Positive step113 2409 2499 := by decide +kernel

theorem step113_cover : ∃ ends, Cover step113 firstHeight ends := by
  exact ⟨[2345, 2408, 2499],
    ⟨(by decide), (by decide), step113_2330_2345,
      (by decide), (by decide), step113_2346_2408,
      (by decide), (by decide), step113_2409_2499, rfl⟩⟩

theorem step113_verified : Checked step113 :=
  ⟨step113_nodes, Research6966.HelperWindowCatalogue.moment293_62,
    (by decide), (by decide), (by decide), step113_cover⟩

def step114 : Request :=
  ⟨⟨⟨210, 293, 63, 2113⟩, 283090354176, 206678784⟩, 1, 2, 71, 257143⟩

theorem step114_nodes : P1_7_1.nodeRows step114.bank.shape = step114.bank.nodeRows :=
  node_check step114.bank (by decide) (by decide) (by decide)

private theorem step114_2330_2343 : Positive step114 2330 2343 := by decide +kernel

private theorem step114_2344_2398 : Positive step114 2344 2398 := by decide +kernel

private theorem step114_2399_2499 : Positive step114 2399 2499 := by decide +kernel

theorem step114_cover : ∃ ends, Cover step114 firstHeight ends := by
  exact ⟨[2343, 2398, 2499],
    ⟨(by decide), (by decide), step114_2330_2343,
      (by decide), (by decide), step114_2344_2398,
      (by decide), (by decide), step114_2399_2499, rfl⟩⟩

theorem step114_verified : Checked step114 :=
  ⟨step114_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step114_cover⟩

def step115 : Request :=
  ⟨⟨⟨210, 293, 65, 2674⟩, 289785774080, 211692234⟩, 2, 2, 71, 257143⟩

theorem step115_nodes : P1_7_1.nodeRows step115.bank.shape = step115.bank.nodeRows :=
  node_check step115.bank (by decide) (by decide) (by decide)

private theorem step115_2330_2341 : Positive step115 2330 2341 := by decide +kernel

private theorem step115_2342_2387 : Positive step115 2342 2387 := by decide +kernel

private theorem step115_2388_2499 : Positive step115 2388 2499 := by decide +kernel

theorem step115_cover : ∃ ends, Cover step115 firstHeight ends := by
  exact ⟨[2341, 2387, 2499],
    ⟨(by decide), (by decide), step115_2330_2341,
      (by decide), (by decide), step115_2342_2387,
      (by decide), (by decide), step115_2388_2499, rfl⟩⟩

theorem step115_verified : Checked step115 :=
  ⟨step115_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step115_cover⟩

def step116 : Request :=
  ⟨⟨⟨250, 348, 76, 2377⟩, 480667500544, 414368386⟩, 3, 2, 71, 257143⟩

theorem step116_nodes : P1_7_1.nodeRows step116.bank.shape = step116.bank.nodeRows :=
  node_check step116.bank (by decide) (by decide) (by decide)

private theorem step116_2330_2353 : Positive step116 2330 2353 := by decide +kernel

private theorem step116_2354_2440 : Positive step116 2354 2440 := by decide +kernel

private theorem step116_2441_2499 : Positive step116 2441 2499 := by decide +kernel

theorem step116_cover : ∃ ends, Cover step116 firstHeight ends := by
  exact ⟨[2353, 2440, 2499],
    ⟨(by decide), (by decide), step116_2330_2353,
      (by decide), (by decide), step116_2354_2440,
      (by decide), (by decide), step116_2441_2499, rfl⟩⟩

theorem step116_verified : Checked step116 :=
  ⟨step116_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step116_cover⟩

def step117 : Request :=
  ⟨⟨⟨250, 348, 78, 2674⟩, 490108092416, 422716393⟩, 4, 2, 71, 257143⟩

theorem step117_nodes : P1_7_1.nodeRows step117.bank.shape = step117.bank.nodeRows :=
  node_check step117.bank (by decide) (by decide) (by decide)

private theorem step117_2330_2338 : Positive step117 2330 2338 := by decide +kernel

private theorem step117_2339_2370 : Positive step117 2339 2370 := by decide +kernel

private theorem step117_2371_2484 : Positive step117 2371 2484 := by decide +kernel

private theorem step117_2485_2499 : Positive step117 2485 2499 := by decide +kernel

theorem step117_cover : ∃ ends, Cover step117 firstHeight ends := by
  exact ⟨[2338, 2370, 2484, 2499],
    ⟨(by decide), (by decide), step117_2330_2338,
      (by decide), (by decide), step117_2339_2370,
      (by decide), (by decide), step117_2371_2484,
      (by decide), (by decide), step117_2485_2499, rfl⟩⟩

theorem step117_verified : Checked step117 :=
  ⟨step117_nodes, Research6966.HelperWindowCatalogue.moment348_78,
    (by decide), (by decide), (by decide), step117_cover⟩

def step118 : Request :=
  ⟨⟨⟨294, 410, 89, 2674⟩, 777085255680, 791788817⟩, 5, 2, 71, 257143⟩

theorem step118_nodes : P1_7_1.nodeRows step118.bank.shape = step118.bank.nodeRows :=
  node_check step118.bank (by decide) (by decide) (by decide)

private theorem step118_2330_2336 : Positive step118 2330 2336 := by decide +kernel

private theorem step118_2337_2360 : Positive step118 2337 2360 := by decide +kernel

private theorem step118_2361_2441 : Positive step118 2361 2441 := by decide +kernel

private theorem step118_2442_2499 : Positive step118 2442 2499 := by decide +kernel

theorem step118_cover : ∃ ends, Cover step118 firstHeight ends := by
  exact ⟨[2336, 2360, 2441, 2499],
    ⟨(by decide), (by decide), step118_2330_2336,
      (by decide), (by decide), step118_2337_2360,
      (by decide), (by decide), step118_2361_2441,
      (by decide), (by decide), step118_2442_2499, rfl⟩⟩

theorem step118_verified : Checked step118 :=
  ⟨step118_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step118_cover⟩

def step119 : Request :=
  ⟨⟨⟨294, 410, 91, 3807⟩, 790165454848, 805457011⟩, 7, 2, 71, 257143⟩

theorem step119_nodes : P1_7_1.nodeRows step119.bank.shape = step119.bank.nodeRows :=
  node_check step119.bank (by decide) (by decide) (by decide)

private theorem step119_2330_2336 : Positive step119 2330 2336 := by decide +kernel

private theorem step119_2337_2360 : Positive step119 2337 2360 := by decide +kernel

private theorem step119_2361_2440 : Positive step119 2361 2440 := by decide +kernel

private theorem step119_2441_2499 : Positive step119 2441 2499 := by decide +kernel

theorem step119_cover : ∃ ends, Cover step119 firstHeight ends := by
  exact ⟨[2336, 2360, 2440, 2499],
    ⟨(by decide), (by decide), step119_2330_2336,
      (by decide), (by decide), step119_2337_2360,
      (by decide), (by decide), step119_2361_2440,
      (by decide), (by decide), step119_2441_2499, rfl⟩⟩

theorem step119_verified : Checked step119 :=
  ⟨step119_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step119_cover⟩

def step120 : Request :=
  ⟨⟨⟨350, 488, 108, 4282⟩, 1326705278976, 1607754763⟩, 10, 2, 71, 257143⟩

theorem step120_nodes : P1_7_1.nodeRows step120.bank.shape = step120.bank.nodeRows :=
  node_check step120.bank (by decide) (by decide) (by decide)

private theorem step120_2330_2345 : Positive step120 2330 2345 := by decide +kernel

private theorem step120_2346_2396 : Positive step120 2346 2396 := by decide +kernel

private theorem step120_2397_2499 : Positive step120 2397 2499 := by decide +kernel

theorem step120_cover : ∃ ends, Cover step120 firstHeight ends := by
  exact ⟨[2345, 2396, 2499],
    ⟨(by decide), (by decide), step120_2330_2345,
      (by decide), (by decide), step120_2346_2396,
      (by decide), (by decide), step120_2397_2499, rfl⟩⟩

theorem step120_verified : Checked step120 :=
  ⟨step120_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step120_cover⟩

def step121 : Request :=
  ⟨⟨⟨520, 725, 154, 4817⟩, 4199390904320, 7545064854⟩, 16, 2, 71, 257143⟩

theorem step121_nodes : P1_7_1.nodeRows step121.bank.shape = step121.bank.nodeRows :=
  node_check step121.bank (by decide) (by decide) (by decide)

private theorem step121_2330_2331 : Positive step121 2330 2331 := by decide +kernel

private theorem step121_2332_2337 : Positive step121 2332 2337 := by decide +kernel

private theorem step121_2338_2355 : Positive step121 2338 2355 := by decide +kernel

private theorem step121_2356_2409 : Positive step121 2356 2409 := by decide +kernel

private theorem step121_2410_2499 : Positive step121 2410 2499 := by decide +kernel

theorem step121_cover : ∃ ends, Cover step121 firstHeight ends := by
  exact ⟨[2331, 2337, 2355, 2409, 2499],
    ⟨(by decide), (by decide), step121_2330_2331,
      (by decide), (by decide), step121_2332_2337,
      (by decide), (by decide), step121_2338_2355,
      (by decide), (by decide), step121_2356_2409,
      (by decide), (by decide), step121_2410_2499, rfl⟩⟩

theorem step121_verified : Checked step121 :=
  ⟨step121_nodes, Research6966.HelperWindowCatalogue.moment725_154,
    (by decide), (by decide), (by decide), step121_cover⟩

def step122 : Request :=
  ⟨⟨⟨520, 725, 161, 6096⟩, 4343013310464, 7809559934⟩, 20, 2, 71, 257143⟩

theorem step122_nodes : P1_7_1.nodeRows step122.bank.shape = step122.bank.nodeRows :=
  node_check step122.bank (by decide) (by decide) (by decide)

private theorem step122_2330_2333 : Positive step122 2330 2333 := by decide +kernel

private theorem step122_2334_2345 : Positive step122 2334 2345 := by decide +kernel

private theorem step122_2346_2380 : Positive step122 2346 2380 := by decide +kernel

private theorem step122_2381_2484 : Positive step122 2381 2484 := by decide +kernel

private theorem step122_2485_2499 : Positive step122 2485 2499 := by decide +kernel

theorem step122_cover : ∃ ends, Cover step122 firstHeight ends := by
  exact ⟨[2333, 2345, 2380, 2484, 2499],
    ⟨(by decide), (by decide), step122_2330_2333,
      (by decide), (by decide), step122_2334_2345,
      (by decide), (by decide), step122_2346_2380,
      (by decide), (by decide), step122_2381_2484,
      (by decide), (by decide), step122_2485_2499, rfl⟩⟩

theorem step122_verified : Checked step122 :=
  ⟨step122_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step122_cover⟩

def step123 : Request :=
  ⟨⟨⟨750, 1046, 232, 7715⟩, 12985818152960, 33687112323⟩, 31, 2, 71, 257143⟩

theorem step123_nodes : P1_7_1.nodeRows step123.bank.shape = step123.bank.nodeRows :=
  node_check step123.bank (by decide) (by decide) (by decide)

private theorem step123_2330_2353 : Positive step123 2330 2353 := by decide +kernel

private theorem step123_2354_2421 : Positive step123 2354 2421 := by decide +kernel

private theorem step123_2422_2499 : Positive step123 2422 2499 := by decide +kernel

theorem step123_cover : ∃ ends, Cover step123 firstHeight ends := by
  exact ⟨[2353, 2421, 2499],
    ⟨(by decide), (by decide), step123_2330_2353,
      (by decide), (by decide), step123_2354_2421,
      (by decide), (by decide), step123_2422_2499, rfl⟩⟩

theorem step123_verified : Checked step123 :=
  ⟨step123_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step123_cover⟩

def step124 : Request :=
  ⟨⟨⟨750, 1046, 232, 7715⟩, 12985818152960, 33687112323⟩, 32, 2, 71, 257143⟩

theorem step124_nodes : P1_7_1.nodeRows step124.bank.shape = step124.bank.nodeRows :=
  node_check step124.bank (by decide) (by decide) (by decide)

private theorem step124_2330_2330 : Positive step124 2330 2330 := by decide +kernel

private theorem step124_2331_2333 : Positive step124 2331 2333 := by decide +kernel

private theorem step124_2334_2341 : Positive step124 2334 2341 := by decide +kernel

private theorem step124_2342_2364 : Positive step124 2342 2364 := by decide +kernel

private theorem step124_2365_2428 : Positive step124 2365 2428 := by decide +kernel

private theorem step124_2429_2499 : Positive step124 2429 2499 := by decide +kernel

theorem step124_cover : ∃ ends, Cover step124 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2364, 2428, 2499],
    ⟨(by decide), (by decide), step124_2330_2330,
      (by decide), (by decide), step124_2331_2333,
      (by decide), (by decide), step124_2334_2341,
      (by decide), (by decide), step124_2342_2364,
      (by decide), (by decide), step124_2365_2428,
      (by decide), (by decide), step124_2429_2499, rfl⟩⟩

theorem step124_verified : Checked step124 :=
  ⟨step124_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step124_cover⟩

def step125 : Request :=
  ⟨⟨⟨1100, 1534, 332, 9763⟩, 40133103452160, 152499774767⟩, 44, 2, 71, 257143⟩

theorem step125_nodes : P1_7_1.nodeRows step125.bank.shape = step125.bank.nodeRows :=
  node_check step125.bank (by decide) (by decide) (by decide)

private theorem step125_2330_2359 : Positive step125 2330 2359 := by decide +kernel

private theorem step125_2360_2443 : Positive step125 2360 2443 := by decide +kernel

private theorem step125_2444_2499 : Positive step125 2444 2499 := by decide +kernel

theorem step125_cover : ∃ ends, Cover step125 firstHeight ends := by
  exact ⟨[2359, 2443, 2499],
    ⟨(by decide), (by decide), step125_2330_2359,
      (by decide), (by decide), step125_2360_2443,
      (by decide), (by decide), step125_2444_2499, rfl⟩⟩

theorem step125_verified : Checked step125 :=
  ⟨step125_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step125_cover⟩

def step126 : Request :=
  ⟨⟨⟨1650, 2301, 512, 13899⟩, 138129879859200, 787417379725⟩, 73, 2, 71, 257143⟩

theorem step126_nodes : P1_7_1.nodeRows step126.bank.shape = step126.bank.nodeRows :=
  node_check step126.bank (by decide) (by decide) (by decide)

private theorem step126_2330_2339 : Positive step126 2330 2339 := by decide +kernel

private theorem step126_2340_2366 : Positive step126 2340 2366 := by decide +kernel

private theorem step126_2367_2438 : Positive step126 2367 2438 := by decide +kernel

private theorem step126_2439_2499 : Positive step126 2439 2499 := by decide +kernel

theorem step126_cover : ∃ ends, Cover step126 firstHeight ends := by
  exact ⟨[2339, 2366, 2438, 2499],
    ⟨(by decide), (by decide), step126_2330_2339,
      (by decide), (by decide), step126_2340_2366,
      (by decide), (by decide), step126_2367_2438,
      (by decide), (by decide), step126_2439_2499, rfl⟩⟩

theorem step126_verified : Checked step126 :=
  ⟨step126_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step126_cover⟩

def step127 : Request :=
  ⟨⟨⟨1650, 2301, 498, 15636⟩, 135254251667456, 770619519922⟩, 76, 2, 71, 257143⟩

theorem step127_nodes : P1_7_1.nodeRows step127.bank.shape = step127.bank.nodeRows :=
  node_check step127.bank (by decide) (by decide) (by decide)

private theorem step127_2330_2341 : Positive step127 2330 2341 := by decide +kernel

private theorem step127_2342_2373 : Positive step127 2342 2373 := by decide +kernel

private theorem step127_2374_2460 : Positive step127 2374 2460 := by decide +kernel

private theorem step127_2461_2499 : Positive step127 2461 2499 := by decide +kernel

theorem step127_cover : ∃ ends, Cover step127 firstHeight ends := by
  exact ⟨[2341, 2373, 2460, 2499],
    ⟨(by decide), (by decide), step127_2330_2341,
      (by decide), (by decide), step127_2342_2373,
      (by decide), (by decide), step127_2374_2460,
      (by decide), (by decide), step127_2461_2499, rfl⟩⟩

theorem step127_verified : Checked step127 :=
  ⟨step127_nodes, Research6966.HelperWindowCatalogue.moment2301_498,
    (by decide), (by decide), (by decide), step127_cover⟩

def step128 : Request :=
  ⟨⟨⟨2000, 2788, 620, 22261⟩, 245690786119680, 1695265997069⟩, 103, 2, 71, 257143⟩

theorem step128_nodes : P1_7_1.nodeRows step128.bank.shape = step128.bank.nodeRows :=
  node_check step128.bank (by decide) (by decide) (by decide)

private theorem step128_2330_2350 : Positive step128 2330 2350 := by decide +kernel

private theorem step128_2351_2406 : Positive step128 2351 2406 := by decide +kernel

private theorem step128_2407_2499 : Positive step128 2407 2499 := by decide +kernel

theorem step128_cover : ∃ ends, Cover step128 firstHeight ends := by
  exact ⟨[2350, 2406, 2499],
    ⟨(by decide), (by decide), step128_2330_2350,
      (by decide), (by decide), step128_2351_2406,
      (by decide), (by decide), step128_2407_2499, rfl⟩⟩

theorem step128_verified : Checked step128 :=
  ⟨step128_nodes, Research6966.HelperWindowCatalogue.moment2788_620,
    (by decide), (by decide), (by decide), step128_cover⟩

def step129 : Request :=
  ⟨⟨⟨630, 879, 186, 28173⟩, 7438337572864, 16221345781⟩, 0, 3, 1, 385715⟩

theorem step129_nodes : P1_7_1.nodeRows step129.bank.shape = step129.bank.nodeRows :=
  node_check step129.bank (by decide) (by decide) (by decide)

private theorem step129_2330_2334 : Positive step129 2330 2334 := by decide +kernel

private theorem step129_2335_2348 : Positive step129 2335 2348 := by decide +kernel

private theorem step129_2349_2389 : Positive step129 2349 2389 := by decide +kernel

private theorem step129_2390_2499 : Positive step129 2390 2499 := by decide +kernel

theorem step129_cover : ∃ ends, Cover step129 firstHeight ends := by
  exact ⟨[2334, 2348, 2389, 2499],
    ⟨(by decide), (by decide), step129_2330_2334,
      (by decide), (by decide), step129_2335_2348,
      (by decide), (by decide), step129_2349_2389,
      (by decide), (by decide), step129_2390_2499, rfl⟩⟩

theorem step129_verified : Checked step129 :=
  ⟨step129_nodes, Research6966.HelperWindowCatalogue.moment879_186,
    (by decide), (by decide), (by decide), step129_cover⟩

def step130 : Request :=
  ⟨⟨⟨630, 879, 190, 31694⟩, 7559493713920, 16491913877⟩, 1, 3, 1, 385715⟩

theorem step130_nodes : P1_7_1.nodeRows step130.bank.shape = step130.bank.nodeRows :=
  node_check step130.bank (by decide) (by decide) (by decide)

private theorem step130_2330_2337 : Positive step130 2330 2337 := by decide +kernel

private theorem step130_2338_2360 : Positive step130 2338 2360 := by decide +kernel

private theorem step130_2361_2427 : Positive step130 2361 2427 := by decide +kernel

private theorem step130_2428_2499 : Positive step130 2428 2499 := by decide +kernel

theorem step130_cover : ∃ ends, Cover step130 firstHeight ends := by
  exact ⟨[2337, 2360, 2427, 2499],
    ⟨(by decide), (by decide), step130_2330_2337,
      (by decide), (by decide), step130_2338_2360,
      (by decide), (by decide), step130_2361_2427,
      (by decide), (by decide), step130_2428_2499, rfl⟩⟩

theorem step130_verified : Checked step130 :=
  ⟨step130_nodes, Research6966.HelperWindowCatalogue.moment879_190,
    (by decide), (by decide), (by decide), step130_cover⟩

def step131 : Request :=
  ⟨⟨⟨900, 1256, 272, 31694⟩, 22024701870080, 68653176066⟩, 2, 3, 1, 385715⟩

theorem step131_nodes : P1_7_1.nodeRows step131.bank.shape = step131.bank.nodeRows :=
  node_check step131.bank (by decide) (by decide) (by decide)

private theorem step131_2330_2333 : Positive step131 2330 2333 := by decide +kernel

private theorem step131_2334_2344 : Positive step131 2334 2344 := by decide +kernel

private theorem step131_2345_2374 : Positive step131 2345 2374 := by decide +kernel

private theorem step131_2375_2458 : Positive step131 2375 2458 := by decide +kernel

private theorem step131_2459_2499 : Positive step131 2459 2499 := by decide +kernel

theorem step131_cover : ∃ ends, Cover step131 firstHeight ends := by
  exact ⟨[2333, 2344, 2374, 2458, 2499],
    ⟨(by decide), (by decide), step131_2330_2333,
      (by decide), (by decide), step131_2334_2344,
      (by decide), (by decide), step131_2345_2374,
      (by decide), (by decide), step131_2375_2458,
      (by decide), (by decide), step131_2459_2499, rfl⟩⟩

theorem step131_verified : Checked step131 :=
  ⟨step131_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step131_cover⟩

def step132 : Request :=
  ⟨⟨⟨750, 1047, 226, 35655⟩, 12730741817344, 33110613849⟩, 3, 3, 1, 385715⟩

theorem step132_nodes : P1_7_1.nodeRows step132.bank.shape = step132.bank.nodeRows :=
  node_check step132.bank (by decide) (by decide) (by decide)

private theorem step132_2330_2330 : Positive step132 2330 2330 := by decide +kernel

private theorem step132_2331_2333 : Positive step132 2331 2333 := by decide +kernel

private theorem step132_2334_2341 : Positive step132 2334 2341 := by decide +kernel

private theorem step132_2342_2364 : Positive step132 2342 2364 := by decide +kernel

private theorem step132_2365_2428 : Positive step132 2365 2428 := by decide +kernel

private theorem step132_2429_2499 : Positive step132 2429 2499 := by decide +kernel

theorem step132_cover : ∃ ends, Cover step132 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2364, 2428, 2499],
    ⟨(by decide), (by decide), step132_2330_2330,
      (by decide), (by decide), step132_2331_2333,
      (by decide), (by decide), step132_2334_2341,
      (by decide), (by decide), step132_2342_2364,
      (by decide), (by decide), step132_2365_2428,
      (by decide), (by decide), step132_2429_2499, rfl⟩⟩

theorem step132_verified : Checked step132 :=
  ⟨step132_nodes, Research6966.HelperWindowCatalogue.moment1047_226,
    (by decide), (by decide), (by decide), step132_cover⟩

def step133 : Request :=
  ⟨⟨⟨900, 1256, 266, 40111⟩, 21654240231424, 67471047297⟩, 4, 3, 1, 385715⟩

theorem step133_nodes : P1_7_1.nodeRows step133.bank.shape = step133.bank.nodeRows :=
  node_check step133.bank (by decide) (by decide) (by decide)

private theorem step133_2330_2341 : Positive step133 2330 2341 := by decide +kernel

private theorem step133_2342_2375 : Positive step133 2342 2375 := by decide +kernel

private theorem step133_2376_2471 : Positive step133 2376 2471 := by decide +kernel

private theorem step133_2472_2499 : Positive step133 2472 2499 := by decide +kernel

theorem step133_cover : ∃ ends, Cover step133 firstHeight ends := by
  exact ⟨[2341, 2375, 2471, 2499],
    ⟨(by decide), (by decide), step133_2330_2341,
      (by decide), (by decide), step133_2342_2375,
      (by decide), (by decide), step133_2376_2471,
      (by decide), (by decide), step133_2472_2499, rfl⟩⟩

theorem step133_verified : Checked step133 :=
  ⟨step133_nodes, Research6966.HelperWindowCatalogue.moment1256_266,
    (by decide), (by decide), (by decide), step133_cover⟩

def step134 : Request :=
  ⟨⟨⟨900, 1256, 272, 40111⟩, 22024701870080, 68653176066⟩, 5, 3, 1, 385715⟩

theorem step134_nodes : P1_7_1.nodeRows step134.bank.shape = step134.bank.nodeRows :=
  node_check step134.bank (by decide) (by decide) (by decide)

private theorem step134_2330_2331 : Positive step134 2330 2331 := by decide +kernel

private theorem step134_2332_2336 : Positive step134 2332 2336 := by decide +kernel

private theorem step134_2337_2350 : Positive step134 2337 2350 := by decide +kernel

private theorem step134_2351_2389 : Positive step134 2351 2389 := by decide +kernel

private theorem step134_2390_2496 : Positive step134 2390 2496 := by decide +kernel

private theorem step134_2497_2499 : Positive step134 2497 2499 := by decide +kernel

theorem step134_cover : ∃ ends, Cover step134 firstHeight ends := by
  exact ⟨[2331, 2336, 2350, 2389, 2496, 2499],
    ⟨(by decide), (by decide), step134_2330_2331,
      (by decide), (by decide), step134_2332_2336,
      (by decide), (by decide), step134_2337_2350,
      (by decide), (by decide), step134_2351_2389,
      (by decide), (by decide), step134_2390_2496,
      (by decide), (by decide), step134_2497_2499, rfl⟩⟩

theorem step134_verified : Checked step134 :=
  ⟨step134_nodes, Research6966.HelperWindowCatalogue.moment1256_272,
    (by decide), (by decide), (by decide), step134_cover⟩

end Research6966.HelperRescueCatalogue
