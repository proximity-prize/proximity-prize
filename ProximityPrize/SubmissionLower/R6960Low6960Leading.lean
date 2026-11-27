import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.FrontBranch3

set_option Elab.async false
set_option autoImplicit true

section
namespace Low6960Leading_1
noncomputable section
variable {top : Fin 15}
open P3 (I K)


open K1_13 (Row Geom atJet extend)
open K1_13_5 (RegularAt NodeFamily separant)
open K1_13_5_4 (GeometricX GeoRow genericRow genericCoeff genericCoeff_injective
  jetPoint regularLocus eval_genericRow_at_point jetPoint_injOn)
open Polynomial
open scoped BigOperators




























































































































































































end
end Low6960Leading_1
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1
noncomputable section
variable {top : Fin 15}
open K1_13 (Row)
open K1_13_5 (separant)

open K1_13_5_4 (InLiftedBox GeoRow GeometricX genericRow)
open K1_13_5_4_2 (JetPoint ExponentSpace boxExponents graphLocus graphCurve capBody mixedVolume4)



open MvPolynomial




























end
end Low6960Leading_1_1
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1
noncomputable section
variable {top : Fin 15}
open K1_13 (Row Geom Shape)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericCoeff_injective genericRow
  liftRow regularLocus graphPoint)
open K1_13_5_4_2 (boxExponents graphCurve eval_represents_iff)




open MvPolynomial RingTheory.Sequence
open scoped BigOperators Polynomial
open K1_13_5_4_2_1 (quotient_regular_iff graph_dimension)
open K1_13_5_4_2 (graphPoint_injective)
attribute [local instance] MvPolynomial.algebraMvPolynomial









































































































































































































end
end Low6960Leading_1_1
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1
noncomputable section
variable {top : Fin 15}

open K1_13_5_4 (InLiftedBox GeoRow)
open K1_13_5_4_2 (JetPoint fourCutIdeal pointIdeal pointLength downBody capBody)
open K1_13_5_4_2_4 (Exponent Downward cutIdeal downSupport capSupport mem_downSupport mem_capSupport
  latticeBody latticeBody_downSupport latticeBody_capSupport)

open MvPolynomial
open scoped BigOperators Pointwise
open K1_13_5_4_2_4 (mixed_eq_generic downSupport_downward capSupport_downward zero_mem_capSupport)

































































end
end Low6960Leading_1_1
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1
noncomputable section
variable {top : Fin 15}
open K1_13 (Row Shape indexDegree)
open K1_13_5 (separant)

open K1_13_5_4 (InLiftedBox GeometricX GeoRow genericRow liftRow graphPoint regularLocus)
open K1_13_5_4_2 (graphLocus JetPoint eval_liftRow_graphPoint)



open MvPolynomial
open scoped BigOperators Pointwise
open K1_13_5_4_2 (ratio_image_degree box_mono)







































































































end
end Low6960Leading_1_1
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1
noncomputable section
variable {top : Fin 15}
open K1_13 (Row)
open K1_13_5_4 (GeoRow genericRow liftRow graph)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal pointLength downBody
  localLength_lt_top)


open MvPolynomial
open scoped BigOperators
open K1_13_5_4_2 (lift_generic_ne_zero)


















































































end
end Low6960Leading_1_1
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1_1
noncomputable section
variable {top : Fin 15}
open K1_13 (Row)
open K1_13_5 (separant lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow regularLocus graph graphPoint)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve eval_liftRow_graphPoint eval_graph_graphPoint)



open MvPolynomial
open K1_13_5_4_2 (three_ne_zero)
open K1_13_5_4_2_3 (graphCurve_comap)



























































































































end
end Low6960Leading_1_1_1
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1_1
noncomputable section
variable {top : Fin 15}
open K1_13_5_4 (GeoRow GeometricX InLiftedBox)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve)
open K1_13_5_4_2_2 (linearForm fiberIdeal totalDegree_hyperplane_le_one zeroLocus_fiber_iff
  ncard_eq_affineDegree_of_radical)


open MvPolynomial
open scoped Pointwise
































































































end
end Low6960Leading_1_1_1
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1_2
noncomputable section
variable {top : Fin 15}
open K1_13 (Row)
open K1_13_5 (lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow graph graphIdeal)

open K1_13_5_4_2_3 (OpenRing onOpen onOpen_kills onOpen_isUnit onOpen_hom_ext
  openLift openLift_onOpen sep liftedSep)
open MvPolynomial
open K1_13_5_4_2_3 (three_isUnit graph_coord_unique represents_vanish)










































































































end
end Low6960Leading_1_1_2
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1_2
noncomputable section
variable {top : Fin 15}
open K1_13 (Row)
open K1_13_5_4 (GeoRow GeometricX genericRow regularLocus liftRow graph graphIdeal graphPoint)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal
  eval_liftRow_graphPoint eval_graph_graphPoint eval_represents_iff)
open K1_13_5_4_2_3 (sep liftedSep openLift openLift_onOpen onOpen_kills
  length_atPrime_le_length_principalCut)


open MvPolynomial
open K1_13_5_4_2_1 (graph_dimension)
open K1_13_5_4_2_3 (graphCurve_comap graphCurve_le_point sep_notMem_point)

open K1_13_5_4_2_3_1 (mem_iff_vanishes_regular)
open K1_13_5_4_2_3_2 (exists_open_prime openAtPrimeEquivQuotient colength_eq_of_quotient_equiv)



































































































































































end
end Low6960Leading_1_1_2
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1_3
noncomputable section
variable {top : Fin 15}
open K1_13 (Shape)

open K1_13_5_4_2 K1_13_5_4_2_5 K1_13_5_4_2_5_2
open MeasureTheory Set Filter
open scoped Topology Pointwise ENNReal BigOperators
open K1_13_5_4_2_5_2_2 (realCap shiftedCap shiftedCap_tendsto form form_apply form_fun bounds mem_realCap support support_attains Pair nonparallel remaining slabMatrix slabRegion volume_slabRegion slabMatrix_invertible slabMap_apply)




































































































































































































end
end Low6960Leading_1_1_3
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1_3
noncomputable section
variable {top : Fin 15}
open K1_13 (Shape)

open K1_13_5_4_2 (ExponentSpace capBody mixedVolume4)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation
  volumeQuotient rest univ_eq_insert zero_notMem_rest)
open K1_13_5_4_2_5_2_1 (cap_polytope closedOrthant)


open MeasureTheory Filter MvPolynomial
open scoped BigOperators Pointwise Topology
open K1_13_5_4_2_5 (sumShape sumChamber sum_capBody capBody_zero)
open K1_13_5_4_2_5_2_1 (labelHull_eq positivePolynomial)
open K1_13_5_4_2_5_2 (weights polar_linear)
open K1_13_5_4_2_5_2 (volume_zero_height)
















































































































































end
end Low6960Leading_1_1_3
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1_3
noncomputable section
variable {top : Fin 15}
open K1_13 (Shape)

open K1_13_5_4_2 (ExponentSpace capBody)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation rest)


open scoped BigOperators



















































































end
end Low6960Leading_1_1_3
end
section
set_option autoImplicit false
namespace Low6960Leading_1_1_3
noncomputable section
variable {top : Fin 15}
open K1_13 (Row indexDegree)

open K1_13_5_4 (genericRow liftRow)
open K1_13_5_4_2 (ExponentSpace downBody capBody)
open K1_13_5_4_2_5 (FirstBody firstBody_zero firstBody_row)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport)


open MvPolynomial
open scoped BigOperators Pointwise
open K1_13_5_4_2_5 (rowShape row_support downBody_subset)

























































































end
end Low6960Leading_1_1_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Low6960Leading_1_2
noncomputable section
variable {top : Fin 15}
open K1_13 (Row)
open K1_13_5 (compatibilityNumerator separant tangentNumerator)
open K1_13_5_4 (GeoRow genericRow genericCoeff genericCoeff_injective)
open K1_13_5_4_3 (TangentStable)
open K1_13_5_4_3_1 (tangentNumerator_add tangentNumerator_mul)



open Polynomial
open K1_13_5_4_3_1 (flat_rowToGeo rowToGeo_eq tangent_self)
open K1_13_5_4_3_3 (generic_cut_regular)
attribute [local instance] MvPolynomial.algebraMvPolynomial












































































































































end
end Low6960Leading_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Low6960Leading_1_2
noncomputable section
variable {top : Fin 15}
open K1_13 (Row Geom)
open K1_13_5 (separant)
open K1_13_5_4 (GeoRow GeometricX genericRow regularLocus extendedAtJet)
open K1_13_5_4_3 (TangentStable trajectory pointEval taylorAt)
open K1_13_5_4_3_2


open Polynomial
open K1_13_5_4_3_2 (fresh_identity initial_residual)
open K1_13_5_4_3_2 (specialize specialize_trajectory specialize_taylor)
























































end
end Low6960Leading_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Low6960Leading_1_2
noncomputable section
variable {top : Fin 15}
open K1_13 (Geom)
open K1_13_5 (RegularAt separant)
open K1_13_5_4 (GeoRow GeometricX extendedAtJet genericCoeff genericCoeff_injective
  genericRow jetPoint regularLocus eval_genericRow_at_point)
open K1_13_5_4_3 (coefficientImage coefficientPolynomial_reconstructAt curveIdeal
  eval_trajectory_at_centre pointEval reconstructAt reconstructAt_mark regularLocus_nonempty
  solves_on_closure taylorAt)
open K1_13_5_4_3_2 (jetPolynomial coeff_jetPolynomial)


open Polynomial MvPolynomial





































































































































end
end Low6960Leading_1_2
end
section
set_option autoImplicit false
namespace Low6960Leading_1_3
noncomputable section
variable {top : Fin 15}
open K1_13_5_4 (GeometricX)
open MvPolynomial
open scoped BigOperators
open P0_9_5_1_4 (restrictVariables restrict_rename padded_hilbert sum_monomial_eq_of_tail_zero)
































































end
end Low6960Leading_1_3
end
section
set_option autoImplicit false
namespace Low6960Leading_1_3
noncomputable section
variable {top : Fin 15}
open K1_13 (Geom Row embed)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX extendedAtJet)
open K1_13_5_4_4



open MvPolynomial Finset
open scoped BigOperators Polynomial
open K1_13_5_4_4 (flat_of_injective regular_cut_of_flat_map)
open K1_13_5_4_4 (curve_minimal)


























































































































































































end
end Low6960Leading_1_3
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace Low6960Leading_2
noncomputable section
variable {top : Fin 15}
open P3 (K I node)

open K1_13 (Geom embed extend taylorLength)
open K1_13_5 (NodeCapacity)
open K1_13_5_5 (CoeffRing CoeffIndex coeffPoint)
open Finset MvPolynomial
open scoped BigOperators Polynomial
open K1_13_5_5 (valueCut valueCut_degree valueCut_eval nodeCapacity_of_sections curve_degree_nat)











































































































end
end Low6960Leading_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Low6960Leading_2
noncomputable section
variable {top : Fin 15}
open K1_13 (Geom embed Row atJet)
open K1_13_5 (RegularAt separant compatibilityNumerator)
open K1_13_5_5 K1_13_5_5_1


open scoped Polynomial
open P0_9_5_2 (chart_trajectory)













































































































































end
end Low6960Leading_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Low6960Leading_2
noncomputable section
variable {top : Fin 15}
open K1_13 (Geom)
open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1

open MvPolynomial
open scoped BigOperators Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_5_5_2_1 (monic_chart_aux)
open K1_13_5_5_2_1 (commonFactor_monic trimmedValue_monic trimmedValue_dvd)
open P0_9_5_2 (eval_divisions)





































































































end
end Low6960Leading_2
end
section
set_option maxHeartbeats 1000000
namespace Low6960Leading_2
noncomputable section
variable {top : Fin 15}
open P3 (K)

open K1_13 (Row Geom extend)
open K1_13_5 (RegularAt NodeCapacity NodeFamily)
open K1_13_5_5 (freshRow FreshField)
open Finset MvPolynomial
open scoped BigOperators Polynomial











































end
end Low6960Leading_2
end

namespace Low6960Leading
variable {top : Fin 15}











end Low6960Leading
