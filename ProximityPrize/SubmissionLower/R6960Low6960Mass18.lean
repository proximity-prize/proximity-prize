import ProximityPrize.SubmissionLower.R6960Low6960Rectangle

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group18

private def m0 : MassCell 18 :=
  ⟨⟨1,3,7⟩,mass_cell 18 1 3 7 281 (by decide)
    (by decide +kernel) [4521096949118, 3699767134972, 2970330478012, 2352481584508, 1834394215996, 1404896064508, 1053468752572, 770247833212, 546022789948, 372237036796, 240987918268, 145026709372, 77758615612, 33292803772, 7782751612, 253552877, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 18 :=
  ⟨⟨19,4,47⟩,mass_cell 18 19 4 47 281 (by decide)
    (by decide +kernel) [4562199382878, 3963267012546, 3417499517094, 2911643298339, 2164288709316, 1441317697840, 886685633364, 474488194015, 182571285352, 23689873711, 49709946, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 18 :=
  ⟨⟨6,14,56⟩,mass_cell 18 6 14 56 152 (by decide)
    (by decide +kernel) [4562199382878, 3963267012546, 3417499517094, 2921889652938, 2394165327129, 1472795993492, 787911035312, 374147069556, 148872698336, 44296456436, 7466811312, 272418379, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 18 :=
  ⟨⟨6,18,60⟩,mass_cell 18 6 18 60 137 (by decide)
    (by decide +kernel) [4562199382878, 3963267012546, 3417499517094, 2921889652938, 2466824297208, 1577814498651, 759417967731, 306053374179, 91569767979, 14972927691, 431471547, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 18) := [m0, m1, m2, m3]

end Low6960Allocation.Group18
