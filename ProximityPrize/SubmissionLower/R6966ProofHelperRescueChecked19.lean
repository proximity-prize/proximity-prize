import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments0
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments1
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments2
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments3
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueMoments5
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def step767 : Request :=
  ⟨⟨⟨1650, 2301, 512, 28173⟩, 138129879859200, 787417379725⟩, 73, 7, 16, 900003⟩

theorem step767_nodes : P1_7_1.nodeRows step767.bank.shape = step767.bank.nodeRows :=
  node_check step767.bank (by decide) (by decide) (by decide)

private theorem step767_2330_2332 : Positive step767 2330 2332 := by decide +kernel

private theorem step767_2333_2340 : Positive step767 2333 2340 := by decide +kernel

private theorem step767_2341_2361 : Positive step767 2341 2361 := by decide +kernel

private theorem step767_2362_2417 : Positive step767 2362 2417 := by decide +kernel

private theorem step767_2418_2499 : Positive step767 2418 2499 := by decide +kernel

theorem step767_cover : ∃ ends, Cover step767 firstHeight ends := by
  exact ⟨[2332, 2340, 2361, 2417, 2499],
    ⟨(by decide), (by decide), step767_2330_2332,
      (by decide), (by decide), step767_2333_2340,
      (by decide), (by decide), step767_2341_2361,
      (by decide), (by decide), step767_2362_2417,
      (by decide), (by decide), step767_2418_2499, rfl⟩⟩

theorem step767_verified : Checked step767 :=
  ⟨step767_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step767_cover⟩

def step768 : Request :=
  ⟨⟨⟨1650, 2301, 512, 31694⟩, 138129879859200, 787417379725⟩, 76, 7, 16, 900003⟩

theorem step768_nodes : P1_7_1.nodeRows step768.bank.shape = step768.bank.nodeRows :=
  node_check step768.bank (by decide) (by decide) (by decide)

private theorem step768_2330_2347 : Positive step768 2330 2347 := by decide +kernel

private theorem step768_2348_2395 : Positive step768 2348 2395 := by decide +kernel

private theorem step768_2396_2499 : Positive step768 2396 2499 := by decide +kernel

theorem step768_cover : ∃ ends, Cover step768 firstHeight ends := by
  exact ⟨[2347, 2395, 2499],
    ⟨(by decide), (by decide), step768_2330_2347,
      (by decide), (by decide), step768_2348_2395,
      (by decide), (by decide), step768_2396_2499, rfl⟩⟩

theorem step768_verified : Checked step768 :=
  ⟨step768_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step768_cover⟩

def step769 : Request :=
  ⟨⟨⟨2500, 3487, 775, 35655⟩, 479640131993600, 4144013596741⟩, 103, 7, 16, 900003⟩

theorem step769_nodes : P1_7_1.nodeRows step769.bank.shape = step769.bank.nodeRows :=
  node_check step769.bank (by decide) (by decide) (by decide)

private theorem step769_2330_2334 : Positive step769 2330 2334 := by decide +kernel

private theorem step769_2335_2347 : Positive step769 2335 2347 := by decide +kernel

private theorem step769_2348_2381 : Positive step769 2348 2381 := by decide +kernel

private theorem step769_2382_2470 : Positive step769 2382 2470 := by decide +kernel

private theorem step769_2471_2499 : Positive step769 2471 2499 := by decide +kernel

theorem step769_cover : ∃ ends, Cover step769 firstHeight ends := by
  exact ⟨[2334, 2347, 2381, 2470, 2499],
    ⟨(by decide), (by decide), step769_2330_2334,
      (by decide), (by decide), step769_2335_2347,
      (by decide), (by decide), step769_2348_2381,
      (by decide), (by decide), step769_2382_2470,
      (by decide), (by decide), step769_2471_2499, rfl⟩⟩

theorem step769_verified : Checked step769 :=
  ⟨step769_nodes, Research6966.HelperWindowCatalogue.moment3487_775,
    (by decide), (by decide), (by decide), step769_cover⟩

def step770 : Request :=
  ⟨⟨⟨210, 293, 63, 3008⟩, 283090354176, 206678784⟩, 0, 7, 26, 900003⟩

theorem step770_nodes : P1_7_1.nodeRows step770.bank.shape = step770.bank.nodeRows :=
  node_check step770.bank (by decide) (by decide) (by decide)

private theorem step770_2330_2336 : Positive step770 2330 2336 := by decide +kernel

private theorem step770_2337_2363 : Positive step770 2337 2363 := by decide +kernel

private theorem step770_2364_2467 : Positive step770 2364 2467 := by decide +kernel

private theorem step770_2468_2499 : Positive step770 2468 2499 := by decide +kernel

theorem step770_cover : ∃ ends, Cover step770 firstHeight ends := by
  exact ⟨[2336, 2363, 2467, 2499],
    ⟨(by decide), (by decide), step770_2330_2336,
      (by decide), (by decide), step770_2337_2363,
      (by decide), (by decide), step770_2364_2467,
      (by decide), (by decide), step770_2468_2499, rfl⟩⟩

theorem step770_verified : Checked step770 :=
  ⟨step770_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step770_cover⟩

def step771 : Request :=
  ⟨⟨⟨250, 349, 78, 3008⟩, 490108092416, 426627288⟩, 1, 7, 26, 900003⟩

theorem step771_nodes : P1_7_1.nodeRows step771.bank.shape = step771.bank.nodeRows :=
  node_check step771.bank (by decide) (by decide) (by decide)

private theorem step771_2330_2339 : Positive step771 2330 2339 := by decide +kernel

private theorem step771_2340_2375 : Positive step771 2340 2375 := by decide +kernel

private theorem step771_2376_2499 : Positive step771 2376 2499 := by decide +kernel

theorem step771_cover : ∃ ends, Cover step771 firstHeight ends := by
  exact ⟨[2339, 2375, 2499],
    ⟨(by decide), (by decide), step771_2330_2339,
      (by decide), (by decide), step771_2340_2375,
      (by decide), (by decide), step771_2376_2499, rfl⟩⟩

theorem step771_verified : Checked step771 :=
  ⟨step771_nodes, Research6966.HelperWindowCatalogue.moment349_78,
    (by decide), (by decide), (by decide), step771_cover⟩

def step772 : Request :=
  ⟨⟨⟨250, 349, 74, 3807⟩, 471125196800, 409695834⟩, 2, 7, 26, 900003⟩

theorem step772_nodes : P1_7_1.nodeRows step772.bank.shape = step772.bank.nodeRows :=
  node_check step772.bank (by decide) (by decide) (by decide)

private theorem step772_2330_2336 : Positive step772 2330 2336 := by decide +kernel

private theorem step772_2337_2361 : Positive step772 2337 2361 := by decide +kernel

private theorem step772_2362_2451 : Positive step772 2362 2451 := by decide +kernel

private theorem step772_2452_2499 : Positive step772 2452 2499 := by decide +kernel

theorem step772_cover : ∃ ends, Cover step772 firstHeight ends := by
  exact ⟨[2336, 2361, 2451, 2499],
    ⟨(by decide), (by decide), step772_2330_2336,
      (by decide), (by decide), step772_2337_2361,
      (by decide), (by decide), step772_2362_2451,
      (by decide), (by decide), step772_2452_2499, rfl⟩⟩

theorem step772_verified : Checked step772 :=
  ⟨step772_nodes, Research6966.HelperWindowCatalogue.moment349_74,
    (by decide), (by decide), (by decide), step772_cover⟩

def step773 : Request :=
  ⟨⟨⟨250, 348, 76, 4282⟩, 480667500544, 414368386⟩, 3, 7, 26, 900003⟩

theorem step773_nodes : P1_7_1.nodeRows step773.bank.shape = step773.bank.nodeRows :=
  node_check step773.bank (by decide) (by decide) (by decide)

private theorem step773_2330_2360 : Positive step773 2330 2360 := by decide +kernel

private theorem step773_2361_2472 : Positive step773 2361 2472 := by decide +kernel

private theorem step773_2473_2499 : Positive step773 2473 2499 := by decide +kernel

theorem step773_cover : ∃ ends, Cover step773 firstHeight ends := by
  exact ⟨[2360, 2472, 2499],
    ⟨(by decide), (by decide), step773_2330_2360,
      (by decide), (by decide), step773_2361_2472,
      (by decide), (by decide), step773_2473_2499, rfl⟩⟩

theorem step773_verified : Checked step773 :=
  ⟨step773_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step773_cover⟩

def step774 : Request :=
  ⟨⟨⟨250, 348, 78, 4817⟩, 490108092416, 422716393⟩, 4, 7, 26, 900003⟩

theorem step774_nodes : P1_7_1.nodeRows step774.bank.shape = step774.bank.nodeRows :=
  node_check step774.bank (by decide) (by decide) (by decide)

private theorem step774_2330_2337 : Positive step774 2330 2337 := by decide +kernel

private theorem step774_2338_2365 : Positive step774 2338 2365 := by decide +kernel

private theorem step774_2366_2465 : Positive step774 2366 2465 := by decide +kernel

private theorem step774_2466_2499 : Positive step774 2466 2499 := by decide +kernel

theorem step774_cover : ∃ ends, Cover step774 firstHeight ends := by
  exact ⟨[2337, 2365, 2465, 2499],
    ⟨(by decide), (by decide), step774_2330_2337,
      (by decide), (by decide), step774_2338_2365,
      (by decide), (by decide), step774_2366_2465,
      (by decide), (by decide), step774_2466_2499, rfl⟩⟩

theorem step774_verified : Checked step774 :=
  ⟨step774_nodes, Research6966.HelperWindowCatalogue.moment348_78,
    (by decide), (by decide), (by decide), step774_cover⟩

def step775 : Request :=
  ⟨⟨⟨294, 410, 89, 4817⟩, 777085255680, 791788817⟩, 5, 7, 26, 900003⟩

theorem step775_nodes : P1_7_1.nodeRows step775.bank.shape = step775.bank.nodeRows :=
  node_check step775.bank (by decide) (by decide) (by decide)

private theorem step775_2330_2351 : Positive step775 2330 2351 := by decide +kernel

private theorem step775_2352_2426 : Positive step775 2352 2426 := by decide +kernel

private theorem step775_2427_2499 : Positive step775 2427 2499 := by decide +kernel

theorem step775_cover : ∃ ends, Cover step775 firstHeight ends := by
  exact ⟨[2351, 2426, 2499],
    ⟨(by decide), (by decide), step775_2330_2351,
      (by decide), (by decide), step775_2352_2426,
      (by decide), (by decide), step775_2427_2499, rfl⟩⟩

theorem step775_verified : Checked step775 :=
  ⟨step775_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step775_cover⟩

def step776 : Request :=
  ⟨⟨⟨350, 488, 108, 4817⟩, 1326705278976, 1607754763⟩, 7, 7, 26, 900003⟩

theorem step776_nodes : P1_7_1.nodeRows step776.bank.shape = step776.bank.nodeRows :=
  node_check step776.bank (by decide) (by decide) (by decide)

private theorem step776_2330_2334 : Positive step776 2330 2334 := by decide +kernel

private theorem step776_2335_2350 : Positive step776 2335 2350 := by decide +kernel

private theorem step776_2351_2401 : Positive step776 2351 2401 := by decide +kernel

private theorem step776_2402_2499 : Positive step776 2402 2499 := by decide +kernel

theorem step776_cover : ∃ ends, Cover step776 firstHeight ends := by
  exact ⟨[2334, 2350, 2401, 2499],
    ⟨(by decide), (by decide), step776_2330_2334,
      (by decide), (by decide), step776_2335_2350,
      (by decide), (by decide), step776_2351_2401,
      (by decide), (by decide), step776_2402_2499, rfl⟩⟩

theorem step776_verified : Checked step776 :=
  ⟨step776_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step776_cover⟩

def step777 : Request :=
  ⟨⟨⟨420, 586, 127, 6096⟩, 2252760678400, 3279920952⟩, 10, 7, 26, 900003⟩

theorem step777_nodes : P1_7_1.nodeRows step777.bank.shape = step777.bank.nodeRows :=
  node_check step777.bank (by decide) (by decide) (by decide)

private theorem step777_2330_2360 : Positive step777 2330 2360 := by decide +kernel

private theorem step777_2361_2456 : Positive step777 2361 2456 := by decide +kernel

private theorem step777_2457_2499 : Positive step777 2457 2499 := by decide +kernel

theorem step777_cover : ∃ ends, Cover step777 firstHeight ends := by
  exact ⟨[2360, 2456, 2499],
    ⟨(by decide), (by decide), step777_2330_2360,
      (by decide), (by decide), step777_2361_2456,
      (by decide), (by decide), step777_2457_2499, rfl⟩⟩

theorem step777_verified : Checked step777 :=
  ⟨step777_nodes, Research6966.HelperWindowCatalogue.moment586_127,
    (by decide), (by decide), (by decide), step777_cover⟩

def step778 : Request :=
  ⟨⟨⟨520, 725, 161, 7715⟩, 4343013310464, 7809559934⟩, 16, 7, 26, 900003⟩

theorem step778_nodes : P1_7_1.nodeRows step778.bank.shape = step778.bank.nodeRows :=
  node_check step778.bank (by decide) (by decide) (by decide)

private theorem step778_2330_2350 : Positive step778 2330 2350 := by decide +kernel

private theorem step778_2351_2412 : Positive step778 2351 2412 := by decide +kernel

private theorem step778_2413_2499 : Positive step778 2413 2499 := by decide +kernel

theorem step778_cover : ∃ ends, Cover step778 firstHeight ends := by
  exact ⟨[2350, 2412, 2499],
    ⟨(by decide), (by decide), step778_2330_2350,
      (by decide), (by decide), step778_2351_2412,
      (by decide), (by decide), step778_2413_2499, rfl⟩⟩

theorem step778_verified : Checked step778 :=
  ⟨step778_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step778_cover⟩

def step779 : Request :=
  ⟨⟨⟨630, 878, 190, 8679⟩, 7559493713920, 16431687757⟩, 20, 7, 26, 900003⟩

theorem step779_nodes : P1_7_1.nodeRows step779.bank.shape = step779.bank.nodeRows :=
  node_check step779.bank (by decide) (by decide) (by decide)

private theorem step779_2330_2336 : Positive step779 2330 2336 := by decide +kernel

private theorem step779_2337_2356 : Positive step779 2337 2356 := by decide +kernel

private theorem step779_2357_2414 : Positive step779 2357 2414 := by decide +kernel

private theorem step779_2415_2499 : Positive step779 2415 2499 := by decide +kernel

theorem step779_cover : ∃ ends, Cover step779 firstHeight ends := by
  exact ⟨[2336, 2356, 2414, 2499],
    ⟨(by decide), (by decide), step779_2330_2336,
      (by decide), (by decide), step779_2337_2356,
      (by decide), (by decide), step779_2357_2414,
      (by decide), (by decide), step779_2415_2499, rfl⟩⟩

theorem step779_verified : Checked step779 :=
  ⟨step779_nodes, Research6966.HelperWindowCatalogue.moment878_190,
    (by decide), (by decide), (by decide), step779_cover⟩

def step780 : Request :=
  ⟨⟨⟨900, 1255, 279, 10983⟩, 22452680785920, 69841856233⟩, 31, 7, 26, 900003⟩

theorem step780_nodes : P1_7_1.nodeRows step780.bank.shape = step780.bank.nodeRows :=
  node_check step780.bank (by decide) (by decide) (by decide)

private theorem step780_2330_2337 : Positive step780 2330 2337 := by decide +kernel

private theorem step780_2338_2359 : Positive step780 2338 2359 := by decide +kernel

private theorem step780_2360_2420 : Positive step780 2360 2420 := by decide +kernel

private theorem step780_2421_2499 : Positive step780 2421 2499 := by decide +kernel

theorem step780_cover : ∃ ends, Cover step780 firstHeight ends := by
  exact ⟨[2337, 2359, 2420, 2499],
    ⟨(by decide), (by decide), step780_2330_2337,
      (by decide), (by decide), step780_2338_2359,
      (by decide), (by decide), step780_2360_2420,
      (by decide), (by decide), step780_2421_2499, rfl⟩⟩

theorem step780_verified : Checked step780 :=
  ⟨step780_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step780_cover⟩

def step781 : Request :=
  ⟨⟨⟨750, 1046, 232, 13899⟩, 12985818152960, 33687112323⟩, 32, 7, 26, 900003⟩

theorem step781_nodes : P1_7_1.nodeRows step781.bank.shape = step781.bank.nodeRows :=
  node_check step781.bank (by decide) (by decide) (by decide)

private theorem step781_2330_2332 : Positive step781 2330 2332 := by decide +kernel

private theorem step781_2333_2341 : Positive step781 2333 2341 := by decide +kernel

private theorem step781_2342_2366 : Positive step781 2342 2366 := by decide +kernel

private theorem step781_2367_2436 : Positive step781 2367 2436 := by decide +kernel

private theorem step781_2437_2499 : Positive step781 2437 2499 := by decide +kernel

theorem step781_cover : ∃ ends, Cover step781 firstHeight ends := by
  exact ⟨[2332, 2341, 2366, 2436, 2499],
    ⟨(by decide), (by decide), step781_2330_2332,
      (by decide), (by decide), step781_2333_2341,
      (by decide), (by decide), step781_2342_2366,
      (by decide), (by decide), step781_2367_2436,
      (by decide), (by decide), step781_2437_2499, rfl⟩⟩

theorem step781_verified : Checked step781 :=
  ⟨step781_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step781_cover⟩

def step782 : Request :=
  ⟨⟨⟨1100, 1534, 341, 15636⟩, 40955142733824, 155702293064⟩, 44, 7, 26, 900003⟩

theorem step782_nodes : P1_7_1.nodeRows step782.bank.shape = step782.bank.nodeRows :=
  node_check step782.bank (by decide) (by decide) (by decide)

private theorem step782_2330_2351 : Positive step782 2330 2351 := by decide +kernel

private theorem step782_2352_2411 : Positive step782 2352 2411 := by decide +kernel

private theorem step782_2412_2499 : Positive step782 2412 2499 := by decide +kernel

theorem step782_cover : ∃ ends, Cover step782 firstHeight ends := by
  exact ⟨[2351, 2411, 2499],
    ⟨(by decide), (by decide), step782_2330_2351,
      (by decide), (by decide), step782_2352_2411,
      (by decide), (by decide), step782_2412_2499, rfl⟩⟩

theorem step782_verified : Checked step782 :=
  ⟨step782_nodes, Research6966.HelperWindowCatalogue.moment1534_341,
    (by decide), (by decide), (by decide), step782_cover⟩

def step783 : Request :=
  ⟨⟨⟨1650, 2301, 498, 25043⟩, 135254251667456, 770619519922⟩, 73, 7, 26, 900003⟩

theorem step783_nodes : P1_7_1.nodeRows step783.bank.shape = step783.bank.nodeRows :=
  node_check step783.bank (by decide) (by decide) (by decide)

private theorem step783_2330_2335 : Positive step783 2330 2335 := by decide +kernel

private theorem step783_2336_2351 : Positive step783 2336 2351 := by decide +kernel

private theorem step783_2352_2394 : Positive step783 2352 2394 := by decide +kernel

private theorem step783_2395_2499 : Positive step783 2395 2499 := by decide +kernel

theorem step783_cover : ∃ ends, Cover step783 firstHeight ends := by
  exact ⟨[2335, 2351, 2394, 2499],
    ⟨(by decide), (by decide), step783_2330_2335,
      (by decide), (by decide), step783_2336_2351,
      (by decide), (by decide), step783_2352_2394,
      (by decide), (by decide), step783_2395_2499, rfl⟩⟩

theorem step783_verified : Checked step783 :=
  ⟨step783_nodes, Research6966.HelperWindowCatalogue.moment2301_498,
    (by decide), (by decide), (by decide), step783_cover⟩

def step784 : Request :=
  ⟨⟨⟨1650, 2301, 512, 25043⟩, 138129879859200, 787417379725⟩, 76, 7, 26, 900003⟩

theorem step784_nodes : P1_7_1.nodeRows step784.bank.shape = step784.bank.nodeRows :=
  node_check step784.bank (by decide) (by decide) (by decide)

private theorem step784_2330_2330 : Positive step784 2330 2330 := by decide +kernel

private theorem step784_2331_2333 : Positive step784 2331 2333 := by decide +kernel

private theorem step784_2334_2341 : Positive step784 2334 2341 := by decide +kernel

private theorem step784_2342_2362 : Positive step784 2342 2362 := by decide +kernel

private theorem step784_2363_2418 : Positive step784 2363 2418 := by decide +kernel

private theorem step784_2419_2499 : Positive step784 2419 2499 := by decide +kernel

theorem step784_cover : ∃ ends, Cover step784 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2362, 2418, 2499],
    ⟨(by decide), (by decide), step784_2330_2330,
      (by decide), (by decide), step784_2331_2333,
      (by decide), (by decide), step784_2334_2341,
      (by decide), (by decide), step784_2342_2362,
      (by decide), (by decide), step784_2363_2418,
      (by decide), (by decide), step784_2419_2499, rfl⟩⟩

theorem step784_verified : Checked step784 :=
  ⟨step784_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step784_cover⟩

def step785 : Request :=
  ⟨⟨⟨2500, 3487, 755, 31694⟩, 470210689105920, 4060530796561⟩, 103, 7, 26, 900003⟩

theorem step785_nodes : P1_7_1.nodeRows step785.bank.shape = step785.bank.nodeRows :=
  node_check step785.bank (by decide) (by decide) (by decide)

private theorem step785_2330_2341 : Positive step785 2330 2341 := by decide +kernel

private theorem step785_2342_2372 : Positive step785 2342 2372 := by decide +kernel

private theorem step785_2373_2455 : Positive step785 2373 2455 := by decide +kernel

private theorem step785_2456_2499 : Positive step785 2456 2499 := by decide +kernel

theorem step785_cover : ∃ ends, Cover step785 firstHeight ends := by
  exact ⟨[2341, 2372, 2455, 2499],
    ⟨(by decide), (by decide), step785_2330_2341,
      (by decide), (by decide), step785_2342_2372,
      (by decide), (by decide), step785_2373_2455,
      (by decide), (by decide), step785_2456_2499, rfl⟩⟩

theorem step785_verified : Checked step785 :=
  ⟨step785_nodes, Research6966.HelperWindowCatalogue.moment3487_755,
    (by decide), (by decide), (by decide), step785_cover⟩

def step786 : Request :=
  ⟨⟨⟨210, 293, 63, 2377⟩, 283090354176, 206678784⟩, 0, 7, 41, 900003⟩

theorem step786_nodes : P1_7_1.nodeRows step786.bank.shape = step786.bank.nodeRows :=
  node_check step786.bank (by decide) (by decide) (by decide)

private theorem step786_2330_2365 : Positive step786 2330 2365 := by decide +kernel

private theorem step786_2366_2499 : Positive step786 2366 2499 := by decide +kernel

theorem step786_cover : ∃ ends, Cover step786 firstHeight ends := by
  exact ⟨[2365, 2499],
    ⟨(by decide), (by decide), step786_2330_2365,
      (by decide), (by decide), step786_2366_2499, rfl⟩⟩

theorem step786_verified : Checked step786 :=
  ⟨step786_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step786_cover⟩

def step787 : Request :=
  ⟨⟨⟨210, 293, 65, 2674⟩, 289785774080, 211692234⟩, 1, 7, 41, 900003⟩

theorem step787_nodes : P1_7_1.nodeRows step787.bank.shape = step787.bank.nodeRows :=
  node_check step787.bank (by decide) (by decide) (by decide)

private theorem step787_2330_2359 : Positive step787 2330 2359 := by decide +kernel

private theorem step787_2360_2475 : Positive step787 2360 2475 := by decide +kernel

private theorem step787_2476_2499 : Positive step787 2476 2499 := by decide +kernel

theorem step787_cover : ∃ ends, Cover step787 firstHeight ends := by
  exact ⟨[2359, 2475, 2499],
    ⟨(by decide), (by decide), step787_2330_2359,
      (by decide), (by decide), step787_2360_2475,
      (by decide), (by decide), step787_2476_2499, rfl⟩⟩

theorem step787_verified : Checked step787 :=
  ⟨step787_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step787_cover⟩

def step788 : Request :=
  ⟨⟨⟨250, 349, 76, 2674⟩, 480667500544, 418199213⟩, 2, 7, 41, 900003⟩

theorem step788_nodes : P1_7_1.nodeRows step788.bank.shape = step788.bank.nodeRows :=
  node_check step788.bank (by decide) (by decide) (by decide)

private theorem step788_2330_2338 : Positive step788 2330 2338 := by decide +kernel

private theorem step788_2339_2369 : Positive step788 2339 2369 := by decide +kernel

private theorem step788_2370_2480 : Positive step788 2370 2480 := by decide +kernel

private theorem step788_2481_2499 : Positive step788 2481 2499 := by decide +kernel

theorem step788_cover : ∃ ends, Cover step788 firstHeight ends := by
  exact ⟨[2338, 2369, 2480, 2499],
    ⟨(by decide), (by decide), step788_2330_2338,
      (by decide), (by decide), step788_2339_2369,
      (by decide), (by decide), step788_2370_2480,
      (by decide), (by decide), step788_2481_2499, rfl⟩⟩

theorem step788_verified : Checked step788 :=
  ⟨step788_nodes, Research6966.HelperWindowCatalogue.moment349_76,
    (by decide), (by decide), (by decide), step788_cover⟩

def step789 : Request :=
  ⟨⟨⟨250, 348, 76, 3008⟩, 480667500544, 414368386⟩, 3, 7, 41, 900003⟩

theorem step789_nodes : P1_7_1.nodeRows step789.bank.shape = step789.bank.nodeRows :=
  node_check step789.bank (by decide) (by decide) (by decide)

private theorem step789_2330_2333 : Positive step789 2330 2333 := by decide +kernel

private theorem step789_2334_2347 : Positive step789 2334 2347 := by decide +kernel

private theorem step789_2348_2397 : Positive step789 2348 2397 := by decide +kernel

private theorem step789_2398_2499 : Positive step789 2398 2499 := by decide +kernel

theorem step789_cover : ∃ ends, Cover step789 firstHeight ends := by
  exact ⟨[2333, 2347, 2397, 2499],
    ⟨(by decide), (by decide), step789_2330_2333,
      (by decide), (by decide), step789_2334_2347,
      (by decide), (by decide), step789_2348_2397,
      (by decide), (by decide), step789_2398_2499, rfl⟩⟩

theorem step789_verified : Checked step789 :=
  ⟨step789_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step789_cover⟩

def step790 : Request :=
  ⟨⟨⟨294, 410, 91, 3008⟩, 790165454848, 805457011⟩, 4, 7, 41, 900003⟩

theorem step790_nodes : P1_7_1.nodeRows step790.bank.shape = step790.bank.nodeRows :=
  node_check step790.bank (by decide) (by decide) (by decide)

private theorem step790_2330_2338 : Positive step790 2330 2338 := by decide +kernel

private theorem step790_2339_2368 : Positive step790 2339 2368 := by decide +kernel

private theorem step790_2369_2469 : Positive step790 2369 2469 := by decide +kernel

private theorem step790_2470_2499 : Positive step790 2470 2499 := by decide +kernel

theorem step790_cover : ∃ ends, Cover step790 firstHeight ends := by
  exact ⟨[2338, 2368, 2469, 2499],
    ⟨(by decide), (by decide), step790_2330_2338,
      (by decide), (by decide), step790_2339_2368,
      (by decide), (by decide), step790_2369_2469,
      (by decide), (by decide), step790_2470_2499, rfl⟩⟩

theorem step790_verified : Checked step790 :=
  ⟨step790_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step790_cover⟩

def step791 : Request :=
  ⟨⟨⟨294, 410, 91, 3384⟩, 790165454848, 805457011⟩, 5, 7, 41, 900003⟩

theorem step791_nodes : P1_7_1.nodeRows step791.bank.shape = step791.bank.nodeRows :=
  node_check step791.bank (by decide) (by decide) (by decide)

private theorem step791_2330_2340 : Positive step791 2330 2340 := by decide +kernel

private theorem step791_2341_2377 : Positive step791 2341 2377 := by decide +kernel

private theorem step791_2378_2499 : Positive step791 2378 2499 := by decide +kernel

theorem step791_cover : ∃ ends, Cover step791 firstHeight ends := by
  exact ⟨[2340, 2377, 2499],
    ⟨(by decide), (by decide), step791_2330_2340,
      (by decide), (by decide), step791_2341_2377,
      (by decide), (by decide), step791_2378_2499, rfl⟩⟩

theorem step791_verified : Checked step791 :=
  ⟨step791_nodes, Research6966.HelperWindowCatalogue.moment410_91,
    (by decide), (by decide), (by decide), step791_cover⟩

def step792 : Request :=
  ⟨⟨⟨350, 488, 106, 3807⟩, 1308168290304, 1584729438⟩, 7, 7, 41, 900003⟩

theorem step792_nodes : P1_7_1.nodeRows step792.bank.shape = step792.bank.nodeRows :=
  node_check step792.bank (by decide) (by decide) (by decide)

private theorem step792_2330_2340 : Positive step792 2330 2340 := by decide +kernel

private theorem step792_2341_2375 : Positive step792 2341 2375 := by decide +kernel

private theorem step792_2376_2488 : Positive step792 2376 2488 := by decide +kernel

private theorem step792_2489_2499 : Positive step792 2489 2499 := by decide +kernel

theorem step792_cover : ∃ ends, Cover step792 firstHeight ends := by
  exact ⟨[2340, 2375, 2488, 2499],
    ⟨(by decide), (by decide), step792_2330_2340,
      (by decide), (by decide), step792_2341_2375,
      (by decide), (by decide), step792_2376_2488,
      (by decide), (by decide), step792_2489_2499, rfl⟩⟩

theorem step792_verified : Checked step792 :=
  ⟨step792_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step792_cover⟩

def step793 : Request :=
  ⟨⟨⟨420, 586, 130, 4282⟩, 2292767784960, 3339653140⟩, 10, 7, 41, 900003⟩

theorem step793_nodes : P1_7_1.nodeRows step793.bank.shape = step793.bank.nodeRows :=
  node_check step793.bank (by decide) (by decide) (by decide)

private theorem step793_2330_2339 : Positive step793 2330 2339 := by decide +kernel

private theorem step793_2340_2370 : Positive step793 2340 2370 := by decide +kernel

private theorem step793_2371_2465 : Positive step793 2371 2465 := by decide +kernel

private theorem step793_2466_2499 : Positive step793 2466 2499 := by decide +kernel

theorem step793_cover : ∃ ends, Cover step793 firstHeight ends := by
  exact ⟨[2339, 2370, 2465, 2499],
    ⟨(by decide), (by decide), step793_2330_2339,
      (by decide), (by decide), step793_2340_2370,
      (by decide), (by decide), step793_2371_2465,
      (by decide), (by decide), step793_2466_2499, rfl⟩⟩

theorem step793_verified : Checked step793 :=
  ⟨step793_nodes, Research6966.HelperWindowCatalogue.moment586_130,
    (by decide), (by decide), (by decide), step793_cover⟩

def step794 : Request :=
  ⟨⟨⟨520, 725, 157, 6096⟩, 4261264752640, 7658911630⟩, 16, 7, 41, 900003⟩

theorem step794_nodes : P1_7_1.nodeRows step794.bank.shape = step794.bank.nodeRows :=
  node_check step794.bank (by decide) (by decide) (by decide)

private theorem step794_2330_2351 : Positive step794 2330 2351 := by decide +kernel

private theorem step794_2352_2417 : Positive step794 2352 2417 := by decide +kernel

private theorem step794_2418_2499 : Positive step794 2418 2499 := by decide +kernel

theorem step794_cover : ∃ ends, Cover step794 firstHeight ends := by
  exact ⟨[2351, 2417, 2499],
    ⟨(by decide), (by decide), step794_2330_2351,
      (by decide), (by decide), step794_2352_2417,
      (by decide), (by decide), step794_2418_2499, rfl⟩⟩

theorem step794_verified : Checked step794 :=
  ⟨step794_nodes, Research6966.HelperWindowCatalogue.moment725_157,
    (by decide), (by decide), (by decide), step794_cover⟩

def step795 : Request :=
  ⟨⟨⟨520, 725, 161, 7715⟩, 4343013310464, 7809559934⟩, 20, 7, 41, 900003⟩

theorem step795_nodes : P1_7_1.nodeRows step795.bank.shape = step795.bank.nodeRows :=
  node_check step795.bank (by decide) (by decide) (by decide)

private theorem step795_2330_2334 : Positive step795 2330 2334 := by decide +kernel

private theorem step795_2335_2349 : Positive step795 2335 2349 := by decide +kernel

private theorem step795_2350_2393 : Positive step795 2350 2393 := by decide +kernel

private theorem step795_2394_2499 : Positive step795 2394 2499 := by decide +kernel

theorem step795_cover : ∃ ends, Cover step795 firstHeight ends := by
  exact ⟨[2334, 2349, 2393, 2499],
    ⟨(by decide), (by decide), step795_2330_2334,
      (by decide), (by decide), step795_2335_2349,
      (by decide), (by decide), step795_2350_2393,
      (by decide), (by decide), step795_2394_2499, rfl⟩⟩

theorem step795_verified : Checked step795 :=
  ⟨step795_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step795_cover⟩

def step796 : Request :=
  ⟨⟨⟨750, 1046, 232, 9763⟩, 12985818152960, 33687112323⟩, 31, 7, 41, 900003⟩

theorem step796_nodes : P1_7_1.nodeRows step796.bank.shape = step796.bank.nodeRows :=
  node_check step796.bank (by decide) (by decide) (by decide)

private theorem step796_2330_2340 : Positive step796 2330 2340 := by decide +kernel

private theorem step796_2341_2371 : Positive step796 2341 2371 := by decide +kernel

private theorem step796_2372_2458 : Positive step796 2372 2458 := by decide +kernel

private theorem step796_2459_2499 : Positive step796 2459 2499 := by decide +kernel

theorem step796_cover : ∃ ends, Cover step796 firstHeight ends := by
  exact ⟨[2340, 2371, 2458, 2499],
    ⟨(by decide), (by decide), step796_2330_2340,
      (by decide), (by decide), step796_2341_2371,
      (by decide), (by decide), step796_2372_2458,
      (by decide), (by decide), step796_2459_2499, rfl⟩⟩

theorem step796_verified : Checked step796 :=
  ⟨step796_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step796_cover⟩

def step797 : Request :=
  ⟨⟨⟨900, 1255, 279, 8679⟩, 22452680785920, 69841856233⟩, 32, 7, 41, 900003⟩

theorem step797_nodes : P1_7_1.nodeRows step797.bank.shape = step797.bank.nodeRows :=
  node_check step797.bank (by decide) (by decide) (by decide)

private theorem step797_2330_2333 : Positive step797 2330 2333 := by decide +kernel

private theorem step797_2334_2344 : Positive step797 2334 2344 := by decide +kernel

private theorem step797_2345_2374 : Positive step797 2345 2374 := by decide +kernel

private theorem step797_2375_2457 : Positive step797 2375 2457 := by decide +kernel

private theorem step797_2458_2499 : Positive step797 2458 2499 := by decide +kernel

theorem step797_cover : ∃ ends, Cover step797 firstHeight ends := by
  exact ⟨[2333, 2344, 2374, 2457, 2499],
    ⟨(by decide), (by decide), step797_2330_2333,
      (by decide), (by decide), step797_2334_2344,
      (by decide), (by decide), step797_2345_2374,
      (by decide), (by decide), step797_2375_2457,
      (by decide), (by decide), step797_2458_2499, rfl⟩⟩

theorem step797_verified : Checked step797 :=
  ⟨step797_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step797_cover⟩

def step798 : Request :=
  ⟨⟨⟨1100, 1534, 332, 12355⟩, 40133103452160, 152499774767⟩, 44, 7, 41, 900003⟩

theorem step798_nodes : P1_7_1.nodeRows step798.bank.shape = step798.bank.nodeRows :=
  node_check step798.bank (by decide) (by decide) (by decide)

private theorem step798_2330_2347 : Positive step798 2330 2347 := by decide +kernel

private theorem step798_2348_2397 : Positive step798 2348 2397 := by decide +kernel

private theorem step798_2398_2499 : Positive step798 2398 2499 := by decide +kernel

theorem step798_cover : ∃ ends, Cover step798 firstHeight ends := by
  exact ⟨[2347, 2397, 2499],
    ⟨(by decide), (by decide), step798_2330_2347,
      (by decide), (by decide), step798_2348_2397,
      (by decide), (by decide), step798_2398_2499, rfl⟩⟩

theorem step798_verified : Checked step798 :=
  ⟨step798_nodes, Research6966.HelperWindowCatalogue.moment1534_332,
    (by decide), (by decide), (by decide), step798_cover⟩

def step799 : Request :=
  ⟨⟨⟨1650, 2301, 512, 17590⟩, 138129879859200, 787417379725⟩, 73, 7, 41, 900003⟩

theorem step799_nodes : P1_7_1.nodeRows step799.bank.shape = step799.bank.nodeRows :=
  node_check step799.bank (by decide) (by decide) (by decide)

private theorem step799_2330_2330 : Positive step799 2330 2330 := by decide +kernel

private theorem step799_2331_2332 : Positive step799 2331 2332 := by decide +kernel

private theorem step799_2333_2338 : Positive step799 2333 2338 := by decide +kernel

private theorem step799_2339_2353 : Positive step799 2339 2353 := by decide +kernel

private theorem step799_2354_2393 : Positive step799 2354 2393 := by decide +kernel

private theorem step799_2394_2499 : Positive step799 2394 2499 := by decide +kernel

theorem step799_cover : ∃ ends, Cover step799 firstHeight ends := by
  exact ⟨[2330, 2332, 2338, 2353, 2393, 2499],
    ⟨(by decide), (by decide), step799_2330_2330,
      (by decide), (by decide), step799_2331_2332,
      (by decide), (by decide), step799_2333_2338,
      (by decide), (by decide), step799_2339_2353,
      (by decide), (by decide), step799_2354_2393,
      (by decide), (by decide), step799_2394_2499, rfl⟩⟩

theorem step799_verified : Checked step799 :=
  ⟨step799_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step799_cover⟩

def step800 : Request :=
  ⟨⟨⟨1650, 2301, 512, 19788⟩, 138129879859200, 787417379725⟩, 76, 7, 41, 900003⟩

theorem step800_nodes : P1_7_1.nodeRows step800.bank.shape = step800.bank.nodeRows :=
  node_check step800.bank (by decide) (by decide) (by decide)

private theorem step800_2330_2354 : Positive step800 2330 2354 := by decide +kernel

private theorem step800_2355_2421 : Positive step800 2355 2421 := by decide +kernel

private theorem step800_2422_2499 : Positive step800 2422 2499 := by decide +kernel

theorem step800_cover : ∃ ends, Cover step800 firstHeight ends := by
  exact ⟨[2354, 2421, 2499],
    ⟨(by decide), (by decide), step800_2330_2354,
      (by decide), (by decide), step800_2355_2421,
      (by decide), (by decide), step800_2422_2499, rfl⟩⟩

theorem step800_verified : Checked step800 :=
  ⟨step800_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step800_cover⟩

def step801 : Request :=
  ⟨⟨⟨2000, 2788, 620, 28173⟩, 245690786119680, 1695265997069⟩, 103, 7, 41, 900003⟩

theorem step801_nodes : P1_7_1.nodeRows step801.bank.shape = step801.bank.nodeRows :=
  node_check step801.bank (by decide) (by decide) (by decide)

private theorem step801_2330_2344 : Positive step801 2330 2344 := by decide +kernel

private theorem step801_2345_2384 : Positive step801 2345 2384 := by decide +kernel

private theorem step801_2385_2490 : Positive step801 2385 2490 := by decide +kernel

private theorem step801_2491_2499 : Positive step801 2491 2499 := by decide +kernel

theorem step801_cover : ∃ ends, Cover step801 firstHeight ends := by
  exact ⟨[2344, 2384, 2490, 2499],
    ⟨(by decide), (by decide), step801_2330_2344,
      (by decide), (by decide), step801_2345_2384,
      (by decide), (by decide), step801_2385_2490,
      (by decide), (by decide), step801_2491_2499, rfl⟩⟩

theorem step801_verified : Checked step801 :=
  ⟨step801_nodes, Research6966.HelperWindowCatalogue.moment2788_620,
    (by decide), (by decide), (by decide), step801_cover⟩

def step802 : Request :=
  ⟨⟨⟨210, 293, 65, 1879⟩, 289785774080, 211692234⟩, 0, 7, 51, 900003⟩

theorem step802_nodes : P1_7_1.nodeRows step802.bank.shape = step802.bank.nodeRows :=
  node_check step802.bank (by decide) (by decide) (by decide)

private theorem step802_2330_2338 : Positive step802 2330 2338 := by decide +kernel

private theorem step802_2339_2372 : Positive step802 2339 2372 := by decide +kernel

private theorem step802_2373_2499 : Positive step802 2373 2499 := by decide +kernel

theorem step802_cover : ∃ ends, Cover step802 firstHeight ends := by
  exact ⟨[2338, 2372, 2499],
    ⟨(by decide), (by decide), step802_2330_2338,
      (by decide), (by decide), step802_2339_2372,
      (by decide), (by decide), step802_2373_2499, rfl⟩⟩

theorem step802_verified : Checked step802 :=
  ⟨step802_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step802_cover⟩

def step803 : Request :=
  ⟨⟨⟨210, 293, 62, 2377⟩, 279710269440, 204151930⟩, 1, 7, 51, 900003⟩

theorem step803_nodes : P1_7_1.nodeRows step803.bank.shape = step803.bank.nodeRows :=
  node_check step803.bank (by decide) (by decide) (by decide)

private theorem step803_2330_2330 : Positive step803 2330 2330 := by decide +kernel

private theorem step803_2331_2333 : Positive step803 2331 2333 := by decide +kernel

private theorem step803_2334_2345 : Positive step803 2334 2345 := by decide +kernel

private theorem step803_2346_2392 : Positive step803 2346 2392 := by decide +kernel

private theorem step803_2393_2499 : Positive step803 2393 2499 := by decide +kernel

theorem step803_cover : ∃ ends, Cover step803 firstHeight ends := by
  exact ⟨[2330, 2333, 2345, 2392, 2499],
    ⟨(by decide), (by decide), step803_2330_2330,
      (by decide), (by decide), step803_2331_2333,
      (by decide), (by decide), step803_2334_2345,
      (by decide), (by decide), step803_2346_2392,
      (by decide), (by decide), step803_2393_2499, rfl⟩⟩

theorem step803_verified : Checked step803 :=
  ⟨step803_nodes, Research6966.HelperWindowCatalogue.moment293_62,
    (by decide), (by decide), (by decide), step803_cover⟩

def step804 : Request :=
  ⟨⟨⟨210, 293, 65, 2674⟩, 289785774080, 211692234⟩, 2, 7, 51, 900003⟩

theorem step804_nodes : P1_7_1.nodeRows step804.bank.shape = step804.bank.nodeRows :=
  node_check step804.bank (by decide) (by decide) (by decide)

private theorem step804_2330_2354 : Positive step804 2330 2354 := by decide +kernel

private theorem step804_2355_2451 : Positive step804 2355 2451 := by decide +kernel

private theorem step804_2452_2499 : Positive step804 2452 2499 := by decide +kernel

theorem step804_cover : ∃ ends, Cover step804 firstHeight ends := by
  exact ⟨[2354, 2451, 2499],
    ⟨(by decide), (by decide), step804_2330_2354,
      (by decide), (by decide), step804_2355_2451,
      (by decide), (by decide), step804_2452_2499, rfl⟩⟩

theorem step804_verified : Checked step804 :=
  ⟨step804_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step804_cover⟩

def step805 : Request :=
  ⟨⟨⟨250, 348, 76, 2674⟩, 480667500544, 414368386⟩, 3, 7, 51, 900003⟩

theorem step805_nodes : P1_7_1.nodeRows step805.bank.shape = step805.bank.nodeRows :=
  node_check step805.bank (by decide) (by decide) (by decide)

private theorem step805_2330_2369 : Positive step805 2330 2369 := by decide +kernel

private theorem step805_2370_2499 : Positive step805 2370 2499 := by decide +kernel

theorem step805_cover : ∃ ends, Cover step805 firstHeight ends := by
  exact ⟨[2369, 2499],
    ⟨(by decide), (by decide), step805_2330_2369,
      (by decide), (by decide), step805_2370_2499, rfl⟩⟩

theorem step805_verified : Checked step805 :=
  ⟨step805_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step805_cover⟩

def step806 : Request :=
  ⟨⟨⟨250, 348, 76, 3008⟩, 480667500544, 414368386⟩, 4, 7, 51, 900003⟩

theorem step806_nodes : P1_7_1.nodeRows step806.bank.shape = step806.bank.nodeRows :=
  node_check step806.bank (by decide) (by decide) (by decide)

private theorem step806_2330_2347 : Positive step806 2330 2347 := by decide +kernel

private theorem step806_2348_2412 : Positive step806 2348 2412 := by decide +kernel

private theorem step806_2413_2499 : Positive step806 2413 2499 := by decide +kernel

theorem step806_cover : ∃ ends, Cover step806 firstHeight ends := by
  exact ⟨[2347, 2412, 2499],
    ⟨(by decide), (by decide), step806_2330_2347,
      (by decide), (by decide), step806_2348_2412,
      (by decide), (by decide), step806_2413_2499, rfl⟩⟩

theorem step806_verified : Checked step806 :=
  ⟨step806_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step806_cover⟩

def step807 : Request :=
  ⟨⟨⟨250, 348, 78, 3384⟩, 490108092416, 422716393⟩, 5, 7, 51, 900003⟩

theorem step807_nodes : P1_7_1.nodeRows step807.bank.shape = step807.bank.nodeRows :=
  node_check step807.bank (by decide) (by decide) (by decide)

private theorem step807_2330_2331 : Positive step807 2330 2331 := by decide +kernel

private theorem step807_2332_2339 : Positive step807 2332 2339 := by decide +kernel

private theorem step807_2340_2367 : Positive step807 2340 2367 := by decide +kernel

private theorem step807_2368_2467 : Positive step807 2368 2467 := by decide +kernel

private theorem step807_2468_2499 : Positive step807 2468 2499 := by decide +kernel

theorem step807_cover : ∃ ends, Cover step807 firstHeight ends := by
  exact ⟨[2331, 2339, 2367, 2467, 2499],
    ⟨(by decide), (by decide), step807_2330_2331,
      (by decide), (by decide), step807_2332_2339,
      (by decide), (by decide), step807_2340_2367,
      (by decide), (by decide), step807_2368_2467,
      (by decide), (by decide), step807_2468_2499, rfl⟩⟩

theorem step807_verified : Checked step807 :=
  ⟨step807_nodes, Research6966.HelperWindowCatalogue.moment348_78,
    (by decide), (by decide), (by decide), step807_cover⟩

def step808 : Request :=
  ⟨⟨⟨294, 410, 89, 3807⟩, 777085255680, 791788817⟩, 7, 7, 51, 900003⟩

theorem step808_nodes : P1_7_1.nodeRows step808.bank.shape = step808.bank.nodeRows :=
  node_check step808.bank (by decide) (by decide) (by decide)

private theorem step808_2330_2334 : Positive step808 2330 2334 := by decide +kernel

private theorem step808_2335_2351 : Positive step808 2335 2351 := by decide +kernel

private theorem step808_2352_2408 : Positive step808 2352 2408 := by decide +kernel

private theorem step808_2409_2499 : Positive step808 2409 2499 := by decide +kernel

theorem step808_cover : ∃ ends, Cover step808 firstHeight ends := by
  exact ⟨[2334, 2351, 2408, 2499],
    ⟨(by decide), (by decide), step808_2330_2334,
      (by decide), (by decide), step808_2335_2351,
      (by decide), (by decide), step808_2352_2408,
      (by decide), (by decide), step808_2409_2499, rfl⟩⟩

theorem step808_verified : Checked step808 :=
  ⟨step808_nodes, Research6966.HelperWindowCatalogue.moment410_89,
    (by decide), (by decide), (by decide), step808_cover⟩

def step809 : Request :=
  ⟨⟨⟨350, 488, 108, 4282⟩, 1326705278976, 1607754763⟩, 10, 7, 51, 900003⟩

theorem step809_nodes : P1_7_1.nodeRows step809.bank.shape = step809.bank.nodeRows :=
  node_check step809.bank (by decide) (by decide) (by decide)

private theorem step809_2330_2344 : Positive step809 2330 2344 := by decide +kernel

private theorem step809_2345_2392 : Positive step809 2345 2392 := by decide +kernel

private theorem step809_2393_2499 : Positive step809 2393 2499 := by decide +kernel

theorem step809_cover : ∃ ends, Cover step809 firstHeight ends := by
  exact ⟨[2344, 2392, 2499],
    ⟨(by decide), (by decide), step809_2330_2344,
      (by decide), (by decide), step809_2345_2392,
      (by decide), (by decide), step809_2393_2499, rfl⟩⟩

theorem step809_verified : Checked step809 :=
  ⟨step809_nodes, Research6966.HelperWindowCatalogue.moment488_108,
    (by decide), (by decide), (by decide), step809_cover⟩

def step810 : Request :=
  ⟨⟨⟨520, 725, 161, 4817⟩, 4343013310464, 7809559934⟩, 16, 7, 51, 900003⟩

theorem step810_nodes : P1_7_1.nodeRows step810.bank.shape = step810.bank.nodeRows :=
  node_check step810.bank (by decide) (by decide) (by decide)

private theorem step810_2330_2335 : Positive step810 2330 2335 := by decide +kernel

private theorem step810_2336_2352 : Positive step810 2336 2352 := by decide +kernel

private theorem step810_2353_2403 : Positive step810 2353 2403 := by decide +kernel

private theorem step810_2404_2499 : Positive step810 2404 2499 := by decide +kernel

theorem step810_cover : ∃ ends, Cover step810 firstHeight ends := by
  exact ⟨[2335, 2352, 2403, 2499],
    ⟨(by decide), (by decide), step810_2330_2335,
      (by decide), (by decide), step810_2336_2352,
      (by decide), (by decide), step810_2353_2403,
      (by decide), (by decide), step810_2404_2499, rfl⟩⟩

theorem step810_verified : Checked step810 :=
  ⟨step810_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step810_cover⟩

def step811 : Request :=
  ⟨⟨⟨630, 878, 195, 5419⟩, 7709474160640, 16765904450⟩, 20, 7, 51, 900003⟩

theorem step811_nodes : P1_7_1.nodeRows step811.bank.shape = step811.bank.nodeRows :=
  node_check step811.bank (by decide) (by decide) (by decide)

private theorem step811_2330_2331 : Positive step811 2330 2331 := by decide +kernel

private theorem step811_2332_2336 : Positive step811 2332 2336 := by decide +kernel

private theorem step811_2337_2351 : Positive step811 2337 2351 := by decide +kernel

private theorem step811_2352_2394 : Positive step811 2352 2394 := by decide +kernel

private theorem step811_2395_2499 : Positive step811 2395 2499 := by decide +kernel

theorem step811_cover : ∃ ends, Cover step811 firstHeight ends := by
  exact ⟨[2331, 2336, 2351, 2394, 2499],
    ⟨(by decide), (by decide), step811_2330_2331,
      (by decide), (by decide), step811_2332_2336,
      (by decide), (by decide), step811_2337_2351,
      (by decide), (by decide), step811_2352_2394,
      (by decide), (by decide), step811_2395_2499, rfl⟩⟩

theorem step811_verified : Checked step811 :=
  ⟨step811_nodes, Research6966.HelperWindowCatalogue.moment878_195,
    (by decide), (by decide), (by decide), step811_cover⟩

def step812 : Request :=
  ⟨⟨⟨750, 1046, 226, 8679⟩, 12730741817344, 33009058589⟩, 31, 7, 51, 900003⟩

theorem step812_nodes : P1_7_1.nodeRows step812.bank.shape = step812.bank.nodeRows :=
  node_check step812.bank (by decide) (by decide) (by decide)

private theorem step812_2330_2343 : Positive step812 2330 2343 := by decide +kernel

private theorem step812_2344_2383 : Positive step812 2344 2383 := by decide +kernel

private theorem step812_2384_2497 : Positive step812 2384 2497 := by decide +kernel

private theorem step812_2498_2499 : Positive step812 2498 2499 := by decide +kernel

theorem step812_cover : ∃ ends, Cover step812 firstHeight ends := by
  exact ⟨[2343, 2383, 2497, 2499],
    ⟨(by decide), (by decide), step812_2330_2343,
      (by decide), (by decide), step812_2344_2383,
      (by decide), (by decide), step812_2384_2497,
      (by decide), (by decide), step812_2498_2499, rfl⟩⟩

theorem step812_verified : Checked step812 :=
  ⟨step812_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step812_cover⟩

def step813 : Request :=
  ⟨⟨⟨750, 1046, 232, 8679⟩, 12985818152960, 33687112323⟩, 32, 7, 51, 900003⟩

theorem step813_nodes : P1_7_1.nodeRows step813.bank.shape = step813.bank.nodeRows :=
  node_check step813.bank (by decide) (by decide) (by decide)

private theorem step813_2330_2347 : Positive step813 2330 2347 := by decide +kernel

private theorem step813_2348_2398 : Positive step813 2348 2398 := by decide +kernel

private theorem step813_2399_2499 : Positive step813 2399 2499 := by decide +kernel

theorem step813_cover : ∃ ends, Cover step813 firstHeight ends := by
  exact ⟨[2347, 2398, 2499],
    ⟨(by decide), (by decide), step813_2330_2347,
      (by decide), (by decide), step813_2348_2398,
      (by decide), (by decide), step813_2399_2499, rfl⟩⟩

theorem step813_verified : Checked step813 :=
  ⟨step813_nodes, Research6966.HelperWindowCatalogue.moment1046_232,
    (by decide), (by decide), (by decide), step813_cover⟩

def step814 : Request :=
  ⟨⟨⟨900, 1255, 279, 12355⟩, 22452680785920, 69841856233⟩, 44, 7, 51, 900003⟩

theorem step814_nodes : P1_7_1.nodeRows step814.bank.shape = step814.bank.nodeRows :=
  node_check step814.bank (by decide) (by decide) (by decide)

private theorem step814_2330_2346 : Positive step814 2330 2346 := by decide +kernel

private theorem step814_2347_2393 : Positive step814 2347 2393 := by decide +kernel

private theorem step814_2394_2499 : Positive step814 2394 2499 := by decide +kernel

theorem step814_cover : ∃ ends, Cover step814 firstHeight ends := by
  exact ⟨[2346, 2393, 2499],
    ⟨(by decide), (by decide), step814_2330_2346,
      (by decide), (by decide), step814_2347_2393,
      (by decide), (by decide), step814_2394_2499, rfl⟩⟩

theorem step814_verified : Checked step814 :=
  ⟨step814_nodes, Research6966.HelperWindowCatalogue.moment1255_279,
    (by decide), (by decide), (by decide), step814_cover⟩

def step815 : Request :=
  ⟨⟨⟨1650, 2301, 512, 15636⟩, 138129879859200, 787417379725⟩, 73, 7, 51, 900003⟩

theorem step815_nodes : P1_7_1.nodeRows step815.bank.shape = step815.bank.nodeRows :=
  node_check step815.bank (by decide) (by decide) (by decide)

private theorem step815_2330_2350 : Positive step815 2330 2350 := by decide +kernel

private theorem step815_2351_2406 : Positive step815 2351 2406 := by decide +kernel

private theorem step815_2407_2499 : Positive step815 2407 2499 := by decide +kernel

theorem step815_cover : ∃ ends, Cover step815 firstHeight ends := by
  exact ⟨[2350, 2406, 2499],
    ⟨(by decide), (by decide), step815_2330_2350,
      (by decide), (by decide), step815_2351_2406,
      (by decide), (by decide), step815_2407_2499, rfl⟩⟩

theorem step815_verified : Checked step815 :=
  ⟨step815_nodes, Research6966.HelperWindowCatalogue.moment2301_512,
    (by decide), (by decide), (by decide), step815_cover⟩

def step816 : Request :=
  ⟨⟨⟨1650, 2301, 498, 17590⟩, 135254251667456, 770619519922⟩, 76, 7, 51, 900003⟩

theorem step816_nodes : P1_7_1.nodeRows step816.bank.shape = step816.bank.nodeRows :=
  node_check step816.bank (by decide) (by decide) (by decide)

private theorem step816_2330_2353 : Positive step816 2330 2353 := by decide +kernel

private theorem step816_2354_2418 : Positive step816 2354 2418 := by decide +kernel

private theorem step816_2419_2499 : Positive step816 2419 2499 := by decide +kernel

theorem step816_cover : ∃ ends, Cover step816 firstHeight ends := by
  exact ⟨[2353, 2418, 2499],
    ⟨(by decide), (by decide), step816_2330_2353,
      (by decide), (by decide), step816_2354_2418,
      (by decide), (by decide), step816_2419_2499, rfl⟩⟩

theorem step816_verified : Checked step816 :=
  ⟨step816_nodes, Research6966.HelperWindowCatalogue.moment2301_498,
    (by decide), (by decide), (by decide), step816_cover⟩

def step817 : Request :=
  ⟨⟨⟨2000, 2788, 604, 25043⟩, 240862397726720, 1661128510194⟩, 103, 7, 51, 900003⟩

theorem step817_nodes : P1_7_1.nodeRows step817.bank.shape = step817.bank.nodeRows :=
  node_check step817.bank (by decide) (by decide) (by decide)

private theorem step817_2330_2350 : Positive step817 2330 2350 := by decide +kernel

private theorem step817_2351_2406 : Positive step817 2351 2406 := by decide +kernel

private theorem step817_2407_2499 : Positive step817 2407 2499 := by decide +kernel

theorem step817_cover : ∃ ends, Cover step817 firstHeight ends := by
  exact ⟨[2350, 2406, 2499],
    ⟨(by decide), (by decide), step817_2330_2350,
      (by decide), (by decide), step817_2351_2406,
      (by decide), (by decide), step817_2407_2499, rfl⟩⟩

theorem step817_verified : Checked step817 :=
  ⟨step817_nodes, Research6966.HelperWindowCatalogue.moment2788_604,
    (by decide), (by decide), (by decide), step817_cover⟩

def step818 : Request :=
  ⟨⟨⟨170, 237, 53, 1671⟩, 155362000896, 91783289⟩, 0, 7, 71, 900003⟩

theorem step818_nodes : P1_7_1.nodeRows step818.bank.shape = step818.bank.nodeRows :=
  node_check step818.bank (by decide) (by decide) (by decide)

private theorem step818_2330_2338 : Positive step818 2330 2338 := by decide +kernel

private theorem step818_2339_2377 : Positive step818 2339 2377 := by decide +kernel

private theorem step818_2378_2499 : Positive step818 2378 2499 := by decide +kernel

theorem step818_cover : ∃ ends, Cover step818 firstHeight ends := by
  exact ⟨[2338, 2377, 2499],
    ⟨(by decide), (by decide), step818_2330_2338,
      (by decide), (by decide), step818_2339_2377,
      (by decide), (by decide), step818_2378_2499, rfl⟩⟩

theorem step818_verified : Checked step818 :=
  ⟨step818_nodes, Research6966.HelperWindowCatalogue.moment237_53,
    (by decide), (by decide), (by decide), step818_cover⟩

def step819 : Request :=
  ⟨⟨⟨170, 237, 53, 2113⟩, 155362000896, 91783289⟩, 1, 7, 71, 900003⟩

theorem step819_nodes : P1_7_1.nodeRows step819.bank.shape = step819.bank.nodeRows :=
  node_check step819.bank (by decide) (by decide) (by decide)

private theorem step819_2330_2345 : Positive step819 2330 2345 := by decide +kernel

private theorem step819_2346_2416 : Positive step819 2346 2416 := by decide +kernel

private theorem step819_2417_2499 : Positive step819 2417 2499 := by decide +kernel

theorem step819_cover : ∃ ends, Cover step819 firstHeight ends := by
  exact ⟨[2345, 2416, 2499],
    ⟨(by decide), (by decide), step819_2330_2345,
      (by decide), (by decide), step819_2346_2416,
      (by decide), (by decide), step819_2417_2499, rfl⟩⟩

theorem step819_verified : Checked step819 :=
  ⟨step819_nodes, Research6966.HelperWindowCatalogue.moment237_53,
    (by decide), (by decide), (by decide), step819_cover⟩

def step820 : Request :=
  ⟨⟨⟨210, 293, 63, 2113⟩, 283090354176, 206678784⟩, 2, 7, 71, 900003⟩

theorem step820_nodes : P1_7_1.nodeRows step820.bank.shape = step820.bank.nodeRows :=
  node_check step820.bank (by decide) (by decide) (by decide)

private theorem step820_2330_2360 : Positive step820 2330 2360 := by decide +kernel

private theorem step820_2361_2481 : Positive step820 2361 2481 := by decide +kernel

private theorem step820_2482_2499 : Positive step820 2482 2499 := by decide +kernel

theorem step820_cover : ∃ ends, Cover step820 firstHeight ends := by
  exact ⟨[2360, 2481, 2499],
    ⟨(by decide), (by decide), step820_2330_2360,
      (by decide), (by decide), step820_2361_2481,
      (by decide), (by decide), step820_2482_2499, rfl⟩⟩

theorem step820_verified : Checked step820 :=
  ⟨step820_nodes, Research6966.HelperWindowCatalogue.moment293_63,
    (by decide), (by decide), (by decide), step820_cover⟩

def step821 : Request :=
  ⟨⟨⟨210, 293, 65, 2377⟩, 289785774080, 211692234⟩, 3, 7, 71, 900003⟩

theorem step821_nodes : P1_7_1.nodeRows step821.bank.shape = step821.bank.nodeRows :=
  node_check step821.bank (by decide) (by decide) (by decide)

private theorem step821_2330_2363 : Positive step821 2330 2363 := by decide +kernel

private theorem step821_2364_2495 : Positive step821 2364 2495 := by decide +kernel

private theorem step821_2496_2499 : Positive step821 2496 2499 := by decide +kernel

theorem step821_cover : ∃ ends, Cover step821 firstHeight ends := by
  exact ⟨[2363, 2495, 2499],
    ⟨(by decide), (by decide), step821_2330_2363,
      (by decide), (by decide), step821_2364_2495,
      (by decide), (by decide), step821_2496_2499, rfl⟩⟩

theorem step821_verified : Checked step821 :=
  ⟨step821_nodes, Research6966.HelperWindowCatalogue.moment293_65,
    (by decide), (by decide), (by decide), step821_cover⟩

def step822 : Request :=
  ⟨⟨⟨250, 348, 76, 2377⟩, 480667500544, 414368386⟩, 4, 7, 71, 900003⟩

theorem step822_nodes : P1_7_1.nodeRows step822.bank.shape = step822.bank.nodeRows :=
  node_check step822.bank (by decide) (by decide) (by decide)

private theorem step822_2330_2375 : Positive step822 2330 2375 := by decide +kernel

private theorem step822_2376_2499 : Positive step822 2376 2499 := by decide +kernel

theorem step822_cover : ∃ ends, Cover step822 firstHeight ends := by
  exact ⟨[2375, 2499],
    ⟨(by decide), (by decide), step822_2330_2375,
      (by decide), (by decide), step822_2376_2499, rfl⟩⟩

theorem step822_verified : Checked step822 :=
  ⟨step822_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step822_cover⟩

def step823 : Request :=
  ⟨⟨⟨250, 348, 76, 2674⟩, 480667500544, 414368386⟩, 5, 7, 71, 900003⟩

theorem step823_nodes : P1_7_1.nodeRows step823.bank.shape = step823.bank.nodeRows :=
  node_check step823.bank (by decide) (by decide) (by decide)

private theorem step823_2330_2367 : Positive step823 2330 2367 := by decide +kernel

private theorem step823_2368_2499 : Positive step823 2368 2499 := by decide +kernel

theorem step823_cover : ∃ ends, Cover step823 firstHeight ends := by
  exact ⟨[2367, 2499],
    ⟨(by decide), (by decide), step823_2330_2367,
      (by decide), (by decide), step823_2368_2499, rfl⟩⟩

theorem step823_verified : Checked step823 :=
  ⟨step823_nodes, Research6966.HelperWindowCatalogue.moment348_76,
    (by decide), (by decide), (by decide), step823_cover⟩

def step824 : Request :=
  ⟨⟨⟨294, 410, 87, 3008⟩, 763884470272, 778016029⟩, 7, 7, 71, 900003⟩

theorem step824_nodes : P1_7_1.nodeRows step824.bank.shape = step824.bank.nodeRows :=
  node_check step824.bank (by decide) (by decide) (by decide)

private theorem step824_2330_2330 : Positive step824 2330 2330 := by decide +kernel

private theorem step824_2331_2333 : Positive step824 2331 2333 := by decide +kernel

private theorem step824_2334_2343 : Positive step824 2334 2343 := by decide +kernel

private theorem step824_2344_2377 : Positive step824 2344 2377 := by decide +kernel

private theorem step824_2378_2494 : Positive step824 2378 2494 := by decide +kernel

private theorem step824_2495_2499 : Positive step824 2495 2499 := by decide +kernel

theorem step824_cover : ∃ ends, Cover step824 firstHeight ends := by
  exact ⟨[2330, 2333, 2343, 2377, 2494, 2499],
    ⟨(by decide), (by decide), step824_2330_2330,
      (by decide), (by decide), step824_2331_2333,
      (by decide), (by decide), step824_2334_2343,
      (by decide), (by decide), step824_2344_2377,
      (by decide), (by decide), step824_2378_2494,
      (by decide), (by decide), step824_2495_2499, rfl⟩⟩

theorem step824_verified : Checked step824 :=
  ⟨step824_nodes, Research6966.HelperWindowCatalogue.moment410_87,
    (by decide), (by decide), (by decide), step824_cover⟩

def step825 : Request :=
  ⟨⟨⟨350, 488, 106, 3384⟩, 1308168290304, 1584729438⟩, 10, 7, 71, 900003⟩

theorem step825_nodes : P1_7_1.nodeRows step825.bank.shape = step825.bank.nodeRows :=
  node_check step825.bank (by decide) (by decide) (by decide)

private theorem step825_2330_2352 : Positive step825 2330 2352 := by decide +kernel

private theorem step825_2353_2427 : Positive step825 2353 2427 := by decide +kernel

private theorem step825_2428_2499 : Positive step825 2428 2499 := by decide +kernel

theorem step825_cover : ∃ ends, Cover step825 firstHeight ends := by
  exact ⟨[2352, 2427, 2499],
    ⟨(by decide), (by decide), step825_2330_2352,
      (by decide), (by decide), step825_2353_2427,
      (by decide), (by decide), step825_2428_2499, rfl⟩⟩

theorem step825_verified : Checked step825 :=
  ⟨step825_nodes, Research6966.HelperWindowCatalogue.moment488_106,
    (by decide), (by decide), (by decide), step825_cover⟩

def step826 : Request :=
  ⟨⟨⟨420, 585, 127, 4817⟩, 2252760678400, 3261978232⟩, 16, 7, 71, 900003⟩

theorem step826_nodes : P1_7_1.nodeRows step826.bank.shape = step826.bank.nodeRows :=
  node_check step826.bank (by decide) (by decide) (by decide)

private theorem step826_2330_2357 : Positive step826 2330 2357 := by decide +kernel

private theorem step826_2358_2445 : Positive step826 2358 2445 := by decide +kernel

private theorem step826_2446_2499 : Positive step826 2446 2499 := by decide +kernel

theorem step826_cover : ∃ ends, Cover step826 firstHeight ends := by
  exact ⟨[2357, 2445, 2499],
    ⟨(by decide), (by decide), step826_2330_2357,
      (by decide), (by decide), step826_2358_2445,
      (by decide), (by decide), step826_2446_2499, rfl⟩⟩

theorem step826_verified : Checked step826 :=
  ⟨step826_nodes, Research6966.HelperWindowCatalogue.moment585_127,
    (by decide), (by decide), (by decide), step826_cover⟩

def step827 : Request :=
  ⟨⟨⟨520, 725, 161, 4817⟩, 4343013310464, 7809559934⟩, 20, 7, 71, 900003⟩

theorem step827_nodes : P1_7_1.nodeRows step827.bank.shape = step827.bank.nodeRows :=
  node_check step827.bank (by decide) (by decide) (by decide)

private theorem step827_2330_2339 : Positive step827 2330 2339 := by decide +kernel

private theorem step827_2340_2368 : Positive step827 2340 2368 := by decide +kernel

private theorem step827_2369_2454 : Positive step827 2369 2454 := by decide +kernel

private theorem step827_2455_2499 : Positive step827 2455 2499 := by decide +kernel

theorem step827_cover : ∃ ends, Cover step827 firstHeight ends := by
  exact ⟨[2339, 2368, 2454, 2499],
    ⟨(by decide), (by decide), step827_2330_2339,
      (by decide), (by decide), step827_2340_2368,
      (by decide), (by decide), step827_2369_2454,
      (by decide), (by decide), step827_2455_2499, rfl⟩⟩

theorem step827_verified : Checked step827 :=
  ⟨step827_nodes, Research6966.HelperWindowCatalogue.moment725_161,
    (by decide), (by decide), (by decide), step827_cover⟩

def step828 : Request :=
  ⟨⟨⟨630, 878, 195, 7715⟩, 7709474160640, 16765904450⟩, 31, 7, 71, 900003⟩

theorem step828_nodes : P1_7_1.nodeRows step828.bank.shape = step828.bank.nodeRows :=
  node_check step828.bank (by decide) (by decide) (by decide)

private theorem step828_2330_2350 : Positive step828 2330 2350 := by decide +kernel

private theorem step828_2351_2410 : Positive step828 2351 2410 := by decide +kernel

private theorem step828_2411_2499 : Positive step828 2411 2499 := by decide +kernel

theorem step828_cover : ∃ ends, Cover step828 firstHeight ends := by
  exact ⟨[2350, 2410, 2499],
    ⟨(by decide), (by decide), step828_2330_2350,
      (by decide), (by decide), step828_2351_2410,
      (by decide), (by decide), step828_2411_2499, rfl⟩⟩

theorem step828_verified : Checked step828 :=
  ⟨step828_nodes, Research6966.HelperWindowCatalogue.moment878_195,
    (by decide), (by decide), (by decide), step828_cover⟩

def step829 : Request :=
  ⟨⟨⟨750, 1046, 226, 6858⟩, 12730741817344, 33009058589⟩, 32, 7, 71, 900003⟩

theorem step829_nodes : P1_7_1.nodeRows step829.bank.shape = step829.bank.nodeRows :=
  node_check step829.bank (by decide) (by decide) (by decide)

private theorem step829_2330_2332 : Positive step829 2330 2332 := by decide +kernel

private theorem step829_2333_2340 : Positive step829 2333 2340 := by decide +kernel

private theorem step829_2341_2363 : Positive step829 2341 2363 := by decide +kernel

private theorem step829_2364_2428 : Positive step829 2364 2428 := by decide +kernel

private theorem step829_2429_2499 : Positive step829 2429 2499 := by decide +kernel

theorem step829_cover : ∃ ends, Cover step829 firstHeight ends := by
  exact ⟨[2332, 2340, 2363, 2428, 2499],
    ⟨(by decide), (by decide), step829_2330_2332,
      (by decide), (by decide), step829_2333_2340,
      (by decide), (by decide), step829_2341_2363,
      (by decide), (by decide), step829_2364_2428,
      (by decide), (by decide), step829_2429_2499, rfl⟩⟩

theorem step829_verified : Checked step829 :=
  ⟨step829_nodes, Research6966.HelperWindowCatalogue.moment1046_226,
    (by decide), (by decide), (by decide), step829_cover⟩

def step830 : Request :=
  ⟨⟨⟨900, 1255, 272, 9763⟩, 22024701870080, 68477558806⟩, 44, 7, 71, 900003⟩

theorem step830_nodes : P1_7_1.nodeRows step830.bank.shape = step830.bank.nodeRows :=
  node_check step830.bank (by decide) (by decide) (by decide)

private theorem step830_2330_2363 : Positive step830 2330 2363 := by decide +kernel

private theorem step830_2364_2459 : Positive step830 2364 2459 := by decide +kernel

private theorem step830_2460_2499 : Positive step830 2460 2499 := by decide +kernel

theorem step830_cover : ∃ ends, Cover step830 firstHeight ends := by
  exact ⟨[2363, 2459, 2499],
    ⟨(by decide), (by decide), step830_2330_2363,
      (by decide), (by decide), step830_2364_2459,
      (by decide), (by decide), step830_2460_2499, rfl⟩⟩

theorem step830_verified : Checked step830 :=
  ⟨step830_nodes, Research6966.HelperWindowCatalogue.moment1255_272,
    (by decide), (by decide), (by decide), step830_cover⟩

def step831 : Request :=
  ⟨⟨⟨1350, 1882, 418, 13899⟩, 75578221264896, 352166349574⟩, 73, 7, 71, 900003⟩

theorem step831_nodes : P1_7_1.nodeRows step831.bank.shape = step831.bank.nodeRows :=
  node_check step831.bank (by decide) (by decide) (by decide)

private theorem step831_2330_2340 : Positive step831 2330 2340 := by decide +kernel

private theorem step831_2341_2369 : Positive step831 2341 2369 := by decide +kernel

private theorem step831_2370_2448 : Positive step831 2370 2448 := by decide +kernel

private theorem step831_2449_2499 : Positive step831 2449 2499 := by decide +kernel

theorem step831_cover : ∃ ends, Cover step831 firstHeight ends := by
  exact ⟨[2340, 2369, 2448, 2499],
    ⟨(by decide), (by decide), step831_2330_2340,
      (by decide), (by decide), step831_2341_2369,
      (by decide), (by decide), step831_2370_2448,
      (by decide), (by decide), step831_2449_2499, rfl⟩⟩

theorem step831_verified : Checked step831 :=
  ⟨step831_nodes, Research6966.HelperWindowCatalogue.moment1882_418,
    (by decide), (by decide), (by decide), step831_cover⟩

def step832 : Request :=
  ⟨⟨⟨1350, 1882, 408, 15636⟩, 74202776600576, 345598963978⟩, 76, 7, 71, 900003⟩

theorem step832_nodes : P1_7_1.nodeRows step832.bank.shape = step832.bank.nodeRows :=
  node_check step832.bank (by decide) (by decide) (by decide)

private theorem step832_2330_2330 : Positive step832 2330 2330 := by decide +kernel

private theorem step832_2331_2333 : Positive step832 2331 2333 := by decide +kernel

private theorem step832_2334_2341 : Positive step832 2334 2341 := by decide +kernel

private theorem step832_2342_2363 : Positive step832 2342 2363 := by decide +kernel

private theorem step832_2364_2422 : Positive step832 2364 2422 := by decide +kernel

private theorem step832_2423_2499 : Positive step832 2423 2499 := by decide +kernel

theorem step832_cover : ∃ ends, Cover step832 firstHeight ends := by
  exact ⟨[2330, 2333, 2341, 2363, 2422, 2499],
    ⟨(by decide), (by decide), step832_2330_2330,
      (by decide), (by decide), step832_2331_2333,
      (by decide), (by decide), step832_2334_2341,
      (by decide), (by decide), step832_2342_2363,
      (by decide), (by decide), step832_2364_2422,
      (by decide), (by decide), step832_2423_2499, rfl⟩⟩

theorem step832_verified : Checked step832 :=
  ⟨step832_nodes, Research6966.HelperWindowCatalogue.moment1882_408,
    (by decide), (by decide), (by decide), step832_cover⟩

def step833 : Request :=
  ⟨⟨⟨2000, 2788, 620, 17590⟩, 245690786119680, 1695265997069⟩, 103, 7, 71, 900003⟩

theorem step833_nodes : P1_7_1.nodeRows step833.bank.shape = step833.bank.nodeRows :=
  node_check step833.bank (by decide) (by decide) (by decide)

private theorem step833_2330_2334 : Positive step833 2330 2334 := by decide +kernel

private theorem step833_2335_2347 : Positive step833 2335 2347 := by decide +kernel

private theorem step833_2348_2382 : Positive step833 2348 2382 := by decide +kernel

private theorem step833_2383_2474 : Positive step833 2383 2474 := by decide +kernel

private theorem step833_2475_2499 : Positive step833 2475 2499 := by decide +kernel

theorem step833_cover : ∃ ends, Cover step833 firstHeight ends := by
  exact ⟨[2334, 2347, 2382, 2474, 2499],
    ⟨(by decide), (by decide), step833_2330_2334,
      (by decide), (by decide), step833_2335_2347,
      (by decide), (by decide), step833_2348_2382,
      (by decide), (by decide), step833_2383_2474,
      (by decide), (by decide), step833_2475_2499, rfl⟩⟩

theorem step833_verified : Checked step833 :=
  ⟨step833_nodes, Research6966.HelperWindowCatalogue.moment2788_620,
    (by decide), (by decide), (by decide), step833_cover⟩

end Research6966.HelperRescueCatalogue
