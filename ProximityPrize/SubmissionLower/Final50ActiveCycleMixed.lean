import ProximityPrize.SubmissionLower.Final50ActiveCycleChart
import ProximityPrize.SubmissionLower.Final50ActiveCyclePrice

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle

noncomputable section

open Polynomial MvPolynomial
open P3 (K)
open Final50GeometryCut ( CutInput )
open Final50GeometryCut_2 (Branch )
open Final50Price (primaryBox tiltedSurface)
open K1_13 (Row extend embed shape)
open Low48BentCycle (Family mixedDegree rawFamily capFamily)
open K1_13_6 (Pieces CurveSections toGeneric)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand)
open K1_13_6_2_4 (oldEmbedding)
open scoped BigOperators





end

end Final50ActiveCycle

