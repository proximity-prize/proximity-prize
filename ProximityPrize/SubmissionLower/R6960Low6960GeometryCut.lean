import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.R6960Low6960FatPad

set_option Elab.async false
set_option autoImplicit true
section
namespace Low6960GeometryCut
noncomputable section
open Polynomial
open P3 (K)

open K1_13 (Geom Row Shape shape extend InBox OnFactor OrderAt chart mixed32)
open K1_13_6 (HighChart toGeneric markIdeal separant jetNumerator divisorIdeal cycleLength)





































end
end Low6960GeometryCut
end
section
namespace Low6960GeometryCut_1
noncomputable section
open Polynomial
open scoped Polynomial
open K1_13 (Row Geom Shape shape InBox extend atJet OnFactor)
open K1_13_6 (GeoJets CanonicalChart HighMark Invariant separant toGeneric
  markIdeal intersectionIdeal cycleLength)
open K1_13_6_1 (HasMark anchorBox tangentCut DerivativeWeight
  mem_markIdeal orderAt_vanishes tangentCut_vanishes)
open K1_13_6_1_3 (tangent_box anchor_fits derivative_fits)


open P0_9_6_1 (SurfaceCut canonicalChart)
open P0_9_6_1 (lowHasse chart_cut derivative_proper box_charge box_cutter_charge)














































open K1_13_7_1 (topAt topAt_coeff eval_topAt topView_separant)


































































































end
end Low6960GeometryCut_1
end
section
namespace Low6960GeometryCut_1
noncomputable section
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength divisorIdeal separant)
open K1_13_6_1 (anchorBox DerivativeWeight CurveOnFactor sectionDegree)
open K1_13_6_1_4 (FullChamber pair_dimension curve_of_proper_cut surfaceDegree)
open K1_13_7_1 (toGeneric_fits proper_generic shape_chamber)


open P0_9_6_1 (SurfaceCut)
open scoped BigOperators
open P0_9_6_1_1 (proper_divisor additive_sections weighted_pair full_chart full_plus chamber_scale full_scale supported_charge sum_biUnion_bound toGeneric_ne_zero)




















































































































































end
end Low6960GeometryCut_1
end
section
namespace Low6960GeometryCut_1
noncomputable section
open Polynomial
open P3 (K)

open K1_13 (InBox chart extend shape atJet)
open K1_13_6 (CanonicalChart CurveSections evalGeneric markIdeal separant)
open K1_13_6_1 (CurveOnFactor anchorBox sectionDegree mem_markIdeal)
open K1_13_6_1_5 (coordinate_cut)
open K1_13_7 (RegularAt)
open K1_13_7_1 (Chamber GeoFits derivative_in_box shape_chamber toGeneric_fits)
open P0_9_6_1_2 (exists_value_cut)
open P0_9_6_1_2 (count_points count_marks chart_has_simplex)




































































end
end Low6960GeometryCut_1
end
namespace Low6960GeometryCut


end Low6960GeometryCut

section
namespace Low6960GeometryCut
noncomputable section
open Polynomial
open P3 (K)


open K1_13 (Row Shape Geom extend atJet shape ceilDiv)
open K1_13_6 (Pieces toGeneric
  separant jetNumerator HighMark divisorIdeal cycleLength eval_jetNumerator)
open K1_13_6_1 (mem_markIdeal mark_curve)
open scoped BigOperators

































































































































































































end
end Low6960GeometryCut
end
section
namespace Low6960GeometryCut_1
noncomputable section
open P3 (K)


open K1_13 (Row shape extend chart atJet)
open K1_13_6 (Pieces GeoJets CurveSections HighMark intersectionIdeal markIdeal)
open K1_13_6_1 (HasMark anchorBox sectionDegree mark_surface mark_curve)
open P0_9_6_1 (SurfaceCut canonicalChart)
open scoped BigOperators






































































































end
end Low6960GeometryCut_1
end
section
namespace Low6960GeometryCut_2
noncomputable section
open Polynomial
open P3 (K)


open K1_13 (Row Shape Geom shape extend chart liftedChart mixed32)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength CanonicalChart
  Invariant separant divisorIdeal partialFlow)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint Box4 Box5 graphBox)
open scoped BigOperators














namespace Branch



























end Branch
































end
end Low6960GeometryCut_2
end
section
namespace Low6960GeometryCut_2
noncomputable section
open Polynomial


open K1_13 (Geom Row Shape shape InBox atJet jet indexDegree)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GenericField GeoField genericCoeffs toGeneric separant)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open scoped BigOperators


















namespace Branch
variable {f Q : Row 4} {l : ℕ}






























































end Branch

















end
end Low6960GeometryCut_2
end
section
namespace Low6960GeometryCut_2
noncomputable section
open Polynomial MvPolynomial
open P3 (K)

open K1_13 (Row Shape Geom InBox embed extend shape chart atJet jet)
open K1_13_6 (GeoJets GeoField GenericField genericCoeffs evalGeneric toGeneric
  separant jetNumerator eval_jetNumerator)
open K1_13_6_2_1 (jet_fits oldBox_of_fits three_weights separant_pow_bound jet_bound)
open K1_13_7_1 (Chamber GeoFits shape_chamber weight_X_le weight_const_mul_le)
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree

























































































































































































end
end Low6960GeometryCut_2
end
section
namespace Low6960GeometryCut_2
noncomputable section
open Polynomial
open P3 (K)


open K1_13 (Row Shape shape extend embed InBox chart liftedChart)
open K1_13_6 (Pieces CurveSections)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand Box4 Box5 graphBox)
open scoped BigOperators


























































































































































end
end Low6960GeometryCut_2
end
section
namespace Low6960GeometryCut_2_1
noncomputable section
open Polynomial MvPolynomial


open K1_13 (Geom Row Shape InBox shape indexDegree liftedChart)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GeoField genericCoeffs toGeneric separant partialFlow jetNumerator)
open K1_13_6_2 (GeoJets5 Box5 graphBox)
open K1_13_6_2_2 (lift4 generic5 rawGraph numerator denominator padded)
open K1_13_6_2_2_2 (Chart incl S invS S_mul_invS negQuarter q constants W
  graphMap graphMap_lift graphMap_X_last)
open scoped BigOperators
open K1_13_6_2_2_2 (compare_numerators)
open K1_13_6_2_2_1 (support_bounds topWeight fifthWeight box_of_weights)
variable {f Q : Row 4} {l : ℕ}




























































local notation "wtDegree" => MvPolynomial.weightedTotalDegree














































































end
end Low6960GeometryCut_2_1
end
section
namespace Low6960GeometryCut_2_1
noncomputable section
open Polynomial
open P3 (K)


open K1_13 (Geom Row embed extend atJet jet)
open K1_13_6 (GeoField genericCoeffs toGeneric separant jetNumerator eval_jetNumerator)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open K1_13_6_2_2 (lift4 generic5 numerator denominator padded padded_last)
open scoped BigOperators
open K1_13_6_2_2 (ordinary ordinary_eq_hasse const centre taylorScalar factorial_ne_zero box_C_mul box_sum box_sub)
variable {f Q : Row 4} {l : ℕ}













































































































































end
end Low6960GeometryCut_2_1
end
section
namespace Low6960GeometryCut_2_2
noncomputable section



open K1_13 (Row Shape shape chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators





























































































































































































































































end
end Low6960GeometryCut_2_2
end
section
namespace Low6960GeometryCut_2_3
noncomputable section


open K1_13 (Shape liftedChart)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5 graphBox)
open K1_13_6_2_4 (Boxes)








end
end Low6960GeometryCut_2_3
end
section
namespace Low6960GeometryCut_2_3
noncomputable section


open K1_13 (Shape liftedChart mixed32)
open K1_13_6 (GeoField)
open K1_13_6_2 (graphBox)
open K1_13_6_2_4 (Boxes Chamber Allowed Admissible allowed_coordinate
  mixedDegree diagonalExponents)
open K1_13_6_2_4_3 (volumeProduct sumCap diagonal)
open MvPolynomial
open scoped BigOperators
open K1_13_6_2_4 (chart_chamber)
open K1_13_6_2_4_3 (diagonal_coeff)
open K1_13_6_2_4_3 (alt alt_insert alt_empty capDiff five_differences signed4_le)
























































end
end Low6960GeometryCut_2_3
end
section
namespace Low6960GeometryCut_2_3
noncomputable section

open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (oldEmbedding)





















































end
end Low6960GeometryCut_2_3
end
section
namespace Low6960GeometryCut_2_3
noncomputable section


open P0_9_6_2_3 (cylinder_comparison cycle_comparison divisor_comparison proper_cut_comparison)
open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5 Box5)
open K1_13_6_2_4 (Admissible Chamber Component DimLE DivisorBound OfDim LengthAt
  ambient_dim cylinder cylinder_injective dim_le_after_section mixedDegree oldEmbedding
  old_section_box point_bound pointIdeal sectionIdeal)
open scoped BigOperators















































































































































































end
end Low6960GeometryCut_2_3
end
section
namespace Low6960GeometryCut_2_3_1
noncomputable section


open K1_13_6 (GeoField GeoJets partialFlow toGeneric)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (OfDim cylinder oldEmbedding one_le_length sectionIdeal)
open K1_13_6_2_4_5 (four_ne_zero substituteLast substituteLast_old)
open K1_13_6_2_4_5 (dim_after_proper_cut)










































































































































end
end Low6960GeometryCut_2_3_1
end
section
namespace Low6960GeometryCut_2_3_2
noncomputable section



open K1_13_6 (GeoField GeoJets toGeneric partialFlow divisorIdeal cycleLength)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_3 (localWeight weight_cast weight_pos)
open K1_13_6_2_4 (OfDim LengthAt sectionIdeal oldEmbedding)
open K1_13_6_2_4_5 (four_ne_zero)
open K1_13_6_2_4_5 (length_le_of_surjection dim_after_proper_cut)






































































































































































































































end
end Low6960GeometryCut_2_3_2
end
section
set_option autoImplicit false
namespace Low6960GeometryCut_3
noncomputable section
open K1_13 (Row)
open K1_13_6 (toGeneric divisorIdeal cycleLength)
open K1_13_6_3 (CoeffIdeal JetIdeal)







end
end Low6960GeometryCut_3
end
section
set_option autoImplicit false
namespace Low6960GeometryCut_3
noncomputable section
open K1_13 K1_13_6 MvPolynomial
open P0_9_6_3 (iterate_separant_degree jetNumerator_degree)












end
end Low6960GeometryCut_3
end
section
set_option autoImplicit false
namespace Low6960GeometryCut_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal)
open K1_13_6_3_1
attribute [local instance] MvPolynomial.algebraMvPolynomial
open P0_9_6_3 (flat_sepToGeo map_eq_maximal_of_length_one step_in_sep sep_sq_dvd_jet nonvanishing_of_simple_cut stable_of_simple_cut)



















































































end
end Low6960GeometryCut_3
end
section
set_option autoImplicit false
namespace Low6960GeometryCut_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal dimension cycleWeight)
open K1_13_6_3_6 MvPolynomial
open P0_9_6_3 (CutCycle)
open scoped BigOperators
open P0_9_6_2_3 (geometric_regular)
open P0_9_6_3 (coefficient_budget)




































































































end
end Low6960GeometryCut_3
end
section
set_option autoImplicit false
namespace Low6960GeometryCut_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial
open P0_9_6_3 (fresh_prime fresh_birational dim_fresh_of_recovery dim_lt_of_prime_lt)

































































end
end Low6960GeometryCut_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Low6960GeometryCut_3
noncomputable section
open K1 K1_13 K1_13_6 Polynomial MvPolynomial
open K1_13_6_3

open P0_9_6_3 (freshImage_injective)
open P0_9_6_3 (curve_degree markPoint_inj canonical_unique cycleWeight_ge surface_sum)
open scoped BigOperators















































































































































































































































end
end Low6960GeometryCut_3
end
section
set_option autoImplicit false
set_option maxRecDepth 200000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Low6960GeometryCut_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_2 Polynomial




















open P0_9_6_3_1 (iterate_zero_of_le differentialTaylor_degree rowAt_eval initial_dividedIterate chartTaylor_toComponent)









































































end
end Low6960GeometryCut_3_1
end
namespace Low6960GeometryCut_3_2

end Low6960GeometryCut_3_2

namespace Low6960GeometryCut















end Low6960GeometryCut

