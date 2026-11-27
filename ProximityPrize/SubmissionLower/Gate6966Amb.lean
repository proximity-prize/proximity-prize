import ProximityPrize.SubmissionLower.Low6966Order
import Mathlib.RingTheory.Localization.Integer
import ProximityPrize.SubmissionLower.Low6966Monotone
import ProximityPrize.SubmissionLower.Shared50ShapeRankBase
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleCaps
import ProximityPrize.SubmissionLower.Low49ActiveLattice
import ProximityPrize.SubmissionLower.Low48BentCycle
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import Mathlib.Algebra.MvPolynomial.Coeff
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.R6960Anchor6966Local
import ProximityPrize.SubmissionLower.Low50Euler2367JetDegree
import ProximityPrize.SubmissionLower.Low6966Retained
import ProximityPrize.SubmissionLower.R6966ProofLowTierWeight

set_option Elab.async false

-- merged module Gate6966Box
section Merged_Gate6966Box

set_option autoImplicit false
set_option Elab.async false

namespace Gate6966Box

open K1_13_6 (GenericField)
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetColumns jetExponents)
open MvPolynomial Finset















































end Gate6966Box

end Merged_Gate6966Box

-- merged module Gate6966Amb
section Merged_Gate6966Amb

set_option autoImplicit false

namespace Gate6966Amb
open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeExponents mem_cumulativeColumns)
open TaperColumns (jetColumns jetExponents)
open TaperMoments (gradeCap)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open TaperColumns (sumGrade sumOld)

def bound (b : ℕ) : ℕ := min 4013 (b + 1)
def start (k : ℕ) : ℕ := 16 * k
def stop (b k : ℕ) : ℕ := min (bound b) (start (k + 1))
def chunks (b : ℕ) : ℕ := (bound b + 15) / 16
def padGrade (b k : ℕ) : ℕ := min (gradeCap (start k)) (gradeCap (stop b k - 1))
def index (j : ℕ) : ℕ := min 1650 j
































































































































end Gate6966Amb

end Merged_Gate6966Amb
