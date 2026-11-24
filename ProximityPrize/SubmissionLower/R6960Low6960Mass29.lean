import ProximityPrize.SubmissionLower.R6960Low6960Rectangle

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group29

private def m0 : MassCell 29 :=
  ⟨⟨1,3,74⟩,mass_cell 29 1 3 74 223 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1138422911309, 751365998725, 463315354117, 260013963725, 126974816989, 49480906549, 12585228245, 1110781117, 228157, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 29) := [m0]

end Low6960Allocation.Group29
