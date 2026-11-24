import ProximityPrize.SubmissionLower.Final50ActiveCycleCaps
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import ProximityPrize.SubmissionLower.Low49ActiveVolume
import Mathlib.Algebra.MvPolynomial.Coeff

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle
noncomputable section

open Low48BentLattice (Cap Chamber Scale latticePoints)
open Low49ActiveLattice (Fits points)
open K1_13 (Shape)
open K1_13_6 (GeoField)
open K1_13_6_2_4_1 (Grade Form unitGrade positiveDiagonal positiveDiagonal_apply
  cube_extract line_coeff squarefree squarefree_apply)
open Low48BentCycle (Family capFamily capSum ambient_cap integral mixedDegree diagonalExponents
  diagonal_nsmul diagonal_add)
open MvPolynomial
open scoped BigOperators Pointwise

open Low48BentCycle (diagonal_unit grade_sum diagonal_sum coeff_congr)
open Low48BentCycle (ambient_list)
open Low49ActiveVolume (fits_scale point_scale point_zero)














end
end Final50ActiveCycle
