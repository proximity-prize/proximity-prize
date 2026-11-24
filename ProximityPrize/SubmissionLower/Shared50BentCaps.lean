import ProximityPrize.SubmissionLower.Final50ActiveCyclePrice

-- merged module Final50ActiveCycleChart
section Merged_Final50ActiveCycleChart

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle

noncomputable section

open Polynomial
open P3 (K)
open Final50Price (physicalDegree taylorLength)
open K1_13 (Row shape extend InBox Shape)
open Low48BentCycle (Family rawFamily)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5 actualPoint)
open K1_13_6_2_2 (generic5 rawGraph numerator denominator padded padded_last)
open Final50GeometryCut_2 (Branch branch_box)
open MvPolynomial








end

end Final50ActiveCycle

end Merged_Final50ActiveCycleChart

-- merged module Shared50BentCaps
section Merged_Shared50BentCaps
set_option Elab.async false
namespace Shared50BentCaps
noncomputable section

open K1_13 (Shape Row shape)
open K1_13_6 (GeoField)
open Final50Price (taylorLength)
open Low48BentLattice (Cap Allowed Chamber latticePoints)
open Low48BentSupport (graph lifted)
open Low48BentCycle (Family rawFamily capFamily capSum ambient_cap integral mixedDegree)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators
open Low48BentCycle (slots ambient_list)














end
end Shared50BentCaps

end Merged_Shared50BentCaps
