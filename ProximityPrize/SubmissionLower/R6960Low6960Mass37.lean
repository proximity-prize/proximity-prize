import ProximityPrize.SubmissionLower.R6960Low6960Rectangle

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group37

private def m0 : MassCell 37 :=
  ⟨⟨1,3,34⟩,mass_cell 37 1 3 34 198 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3240995387441, 2554253280047, 1927222873963, 1411659219079, 996922155395, 672274754911, 426883321627, 249817391543, 130049732659, 56456344975, 17816460491, 2812543207, 47589622, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 37 :=
  ⟨⟨9,8,63⟩,mass_cell 37 9 8 63 172 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1662103704360, 984124237241, 524450357057, 239324934233, 84281301569, 17722135865, 919546249, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 37 :=
  ⟨⟨95,31,81⟩,mass_cell 37 95 31 81 123 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1359776296335, 317996829311, 15044267587, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 37 :=
  ⟨⟨15,45,82⟩,mass_cell 37 15 45 82 112 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1394550371248, 293022453668, 2738552598, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 37) := [m0, m1, m2, m3]

end Low6960Allocation.Group37
