import ProximityPrize.SubmissionLower.Final50GeometryCut
set_option Elab.async false

namespace Shared50CycleLegacy
noncomputable section
open Final50Price (SmallFactor primaryBox taylorLength)
open Final50GeometryCut_2 (Branch  )
open P0_9_6_2_3 (cylinder_comparison cycle_comparison divisor_comparison proper_cut_comparison)
open K1_13 (Row Shape shape InBox liftedChart)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5 Box5 graphBox)
open K1_13_6_2_4 (Admissible Chamber Component DimLE DivisorBound OfDim LengthAt
  ambient_dim cylinder cylinder_injective dim_le_after_section mixedDegree oldEmbedding
  old_section_box point_bound pointIdeal sectionIdeal)
open scoped BigOperators


end
end Shared50CycleLegacy
