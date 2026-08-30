import ProximityPrize.SubmissionLower.ContactFlagGlobalPoleProjection
import ProximityPrize.SubmissionLower.ContactFlagTrapezoidCaps
namespace ProximityPrize.SubmissionLower.ContactFlagPrincipalCycles

open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers ActualCurveZeroCount
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactLocalPoleBound
open ContactSparsePoleSupport
open ContactFlagBezout ContactFlagPoleInequality
open ContactFlagTriangularProjection
open ContactFlagAffineFamilyDegree
open ContactFlagExactSeparableProjection
open ContactFlagGlobalPoleProjection
open ContactFlagTrapezoidCaps
open ContactResidualSparseComponentAdapter
open TrivariateRationalCollection ActualPlaneCoordinateKernel
  ArbitraryRationalProjection

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}
variable {hseparator : ∀ C : RegularComponent Omega G T H,
  Transcendental Omega (coordinate Omega C.1 2)}
variable {hproj : ∀ C : RegularComponent Omega G T H,
  ProjectionsFiniteSeparable Omega C.1}

omit [IsAlgClosed Omega] in
theorem elementEmbedding_congr
    {L : Type} [Field L] [Algebra Omega L]
    {s t : L} (hs : Transcendental Omega s)
    (ht : Transcendental Omega t) (h : s = t) :
    elementEmbedding Omega L s hs = elementEmbedding Omega L t ht := by
  subst t
  rfl

end

end ProximityPrize.SubmissionLower.ContactFlagPrincipalCycles
