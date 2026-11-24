import ProximityPrize.SubmissionLower.R6960Low6960Rectangle

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group27

private def m0 : MassCell 27 :=
  ⟨⟨1,3,34⟩,mass_cell 27 1 3 34 198 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3240995387441, 2554253280047, 1927222873963, 1411659219079, 996922155395, 672274754911, 426883321627, 249817391543, 130049732659, 56456344975, 17816460491, 2812543207, 47589622, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 27 :=
  ⟨⟨4,6,56⟩,mass_cell 27 4 6 56 181 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2206169782549, 1528328598195, 972016663691, 571401200819, 300286063083, 132854745587, 43670385035, 7675759731, 204316690, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 27 :=
  ⟨⟨3,8,61⟩,mass_cell 27 3 8 61 170 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1610073834217, 965097727657, 520128315817, 238551913897, 83264949097, 16673960617, 697454785, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 27) := [m0, m1, m2]

end Low6960Allocation.Group27
