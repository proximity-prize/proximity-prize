import ProximityPrize.SubmissionLower.R6966ProofNativeMarkedTariff
import ProximityPrize.SubmissionLower.R6966ProofFarChart
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceClass
import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift
import ProximityPrize.SubmissionLower.R6960MarkedProtocol
import ProximityPrize.SubmissionLower.R6960RetainedCompressionPureNodes
import ProximityPrize.SubmissionLower.R6960ExceptionalStage
import ProximityPrize.SubmissionLower.HighCore82258PrefixProcess

set_option Elab.async false

namespace Research6966.NearBook
open Finset
open K1 (K)
open K1_14 (Jet Equation)
open K1_14_1 (CRTLift PoleData)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (Active mass mass_mono sectionDegree)
open K1_14_3 (Surface Parent ProjectedProduct)

open KoalaRect (axisDegree axisDegree_le_iff)
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

















































def owning (G:Jet) (S:Finset Surface) := S.filter (fun q=>G∈q.asIdeal)
def outside (G:Jet) (S:Finset Surface) := S.filter (fun q=>G∉q.asIdeal)
def ownerSources (G:Jet) (J:Finset (Ideal Ambient)) := J.filter (fun j=>toJet G∈j)
def otherSources (G:Jet) (J:Finset (Ideal Ambient)) := J.filter (fun j=>toJet G∉j)

theorem split_mass (G:Jet) (J:Finset (Ideal Ambient)) (k:Fin 4) :
    mass (ownerSources G J) k+mass (otherSources G J) k=mass J k :=
  sum_filter_add_sum_filter_not .. 























theorem axis_total {f:Equation} {d:ℕ} (cap:∀ i,(f.coeff i).totalDegree≤d) (z:Fin 2) :
    axisDegree f z≤d := (axisDegree_le_iff ..).mpr (fun i=>(MvPolynomial.degreeOf_le_totalDegree ..).trans (cap i))









end
end Research6966.NearBook
