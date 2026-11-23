import ProximityPrize.SubmissionLower.Low48BentCycle
import ProximityPrize.SubmissionLower.Final50GeometryCut

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle

noncomputable section

open Low48BentCycle (Family mixedDegree properCut cycleComparison divisorBound diagonalExponents)

open Final50Price (SmallFactor)
open Final50GeometryCut_2 (Branch)
open P0_9_6_2_3 (cylinder_comparison)
open K1_13 (Row)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5)
open K1_13_6_2_4 (Exponent Component DimLE OfDim LengthAt ambient_dim cylinder cylinder_injective
  dim_le_after_section oldEmbedding pointIdeal sectionIdeal)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators Pointwise

open private eval_surjective pointIdeal_injective point_component exists_coordinate_cut
  from ProximityPrize.SubmissionLower.Fast054











end

end Final50ActiveCycle
