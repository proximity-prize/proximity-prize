import ProximityPrize.SubmissionLower.Final50ActiveCyclePrice
import ProximityPrize.SubmissionLower.Final50ActiveCycleChart
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
open private slots ambient_list from ProximityPrize.SubmissionLower.Low48BentCyclePrice














end
end Shared50BentCaps
