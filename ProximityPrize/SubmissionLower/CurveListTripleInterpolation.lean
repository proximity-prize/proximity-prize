import ProximityPrize.SubmissionLower.CurveListTripleSupport
import ProximityPrize.SubmissionLower.CurveListPairResultant -- serialize candidate build

set_option maxRecDepth 8000
set_option maxHeartbeats 3000000

namespace CurveListTripleInterpolation
open CJ0 CJ0_3 MvPolynomial PolynomialDifferential CurveListJointWeight CurveListTripleSupport
open scoped Polynomial
open private jetView jet_degree jet_mul from ProximityPrize.SubmissionLower.CurveListPairInterpolation

noncomputable section

private abbrev lead (Q : Equation) : JetExponent := MonomialOrder.degLex.degree (jetView Q)

private theorem lead_degree (Q : Equation) : (lead Q).degree = jetTotalDegree Q :=
  MvPolynomial.degree_degLexDegree.trans (jet_degree Q)

private theorem jetView_ne_zero {Q : Equation} (hq : Q ≠ 0) : jetView Q ≠ 0 := by
  intro hz
  apply hq (jetView.injective _)
  exact hz.trans (show jetView (0 : Equation) = 0 from jetView.map_zero).symm

private theorem lead_mul {P Q : Equation} (hp : P ≠ 0) (hq : Q ≠ 0) :
    lead (P*Q) = lead P+lead Q := by
  unfold lead
  rw [map_mul]
  exact MonomialOrder.degLex.degree_mul (jetView_ne_zero hp) (jetView_ne_zero hq)

end
end CurveListTripleInterpolation
