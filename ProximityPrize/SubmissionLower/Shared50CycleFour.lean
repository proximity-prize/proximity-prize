import ProximityPrize.SubmissionLower.Final50ActiveCyclePrice
set_option Elab.async false

namespace Shared50CycleFour
noncomputable section
open Final50Price (SmallFactor primaryBox taylorLength)
open Final50GeometryCut (membershipTest)
open Final50GeometryCut_2 (Branch Slice4 )
open K1_13 (Row Shape shape InBox chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators


end
end Shared50CycleFour
