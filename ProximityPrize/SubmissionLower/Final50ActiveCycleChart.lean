import ProximityPrize.SubmissionLower.Final50ActiveCycleCaps
import ProximityPrize.SubmissionLower.Final50GeometryCut

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
