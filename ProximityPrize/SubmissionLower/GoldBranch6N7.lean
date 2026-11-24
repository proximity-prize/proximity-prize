import ProximityPrize.SubmissionLower.GoldBranch6N5
import ProximityPrize.SubmissionLower.GoldBranch6N6
set_option maxRecDepth 200000
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_7
noncomputable section
open K1_13 (Shape chart ceilDiv mixed32 Row)
open K1_13_7 (LowerPoint pointIdeal pairIdeal tripleIdeal localColength)
open P3_6 (commonBox resultantBox fatOrder divisorOrder isolatedOrder taylorLength
  linearChart incidenceGap physicalDegree)
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
end
end P3_6_7
end
section
namespace P3_6_7_2
noncomputable section
open Polynomial
open K1_13 (Geom Row Shape InBox shape mixed32 atJet)
open K1_13_6 (GeoJets toGeneric separant cycleLength intersectionIdeal Invariant)
open K1_13_7 (LowerCaps genericRow)
open K1_13_7_2 (evalTrajectory LiftedSurface lowerFlow liftLower)
open P3_6 (taylorLength physicalDegree)
open P3_6_7 (fatChart )
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (P3_6_6.membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : (Polynomial L)),
    S.natDegree ≤ physicalDegree → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
end
end P3_6_7_2
end
section
namespace P3_6_7_2
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open K1_13_7_2_2 (stride raw topLinear denominator numerator hasseNumerator)
open K1_13_7_1 (weight_const_mul_le top_le_index shape_chamber Chamber)
open K1_13_1 (indexDegree_eq)
open K1_13_7_2_2 (raw_false raw_true_compare)
open K1_13_7_2_2 (raw_bound sep_pow_bound)
open K1_13_7_2_2 (specializes topLinear_regular)
local notation "W" => MvPolynomial.weightedTotalDegree
end
end P3_6_7_2
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace P3_6_7_2_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_3 K1_13_7
open K1_13_7_2_4 K1_13_7_2_4_2
open P3_6 (physicalDegree )
open K1_13_7_2_4_2 (intDerivation coeffDeriv coeffDeriv_zero_of_shift zero_of_stationary_eval rowTrajectory rowTrajectory_stationary eval_chartTrajectory)
open K1_13_7_2_4 (sum_monomial_eq_of_coeffs)
open K1_13_7_2_4 (trajectory_at_component component_ne_zero)
end
end P3_6_7_2_2
end
section
set_option autoImplicit false
namespace P3_6_7_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row)
open K1_13_6 (GeoField GeoJets toGeneric separant)
open K1_13_6_3 (JetIdeal dimension geomConstants genericArgument)
open P3_6 (taylorLength)
open P3_6_7_2 ( FatTaylor)
end
end P3_6_7_2_3
end
section
namespace P3_6_7_3
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open K1_13_1 (indexDegree_eq)
open P3_6 (physicalDegree)
section
open K1_13_7_5_2 (denominator)
open P0_9_7_3_1 (numerator numerator_bound denominator_bound coefficients_recover)
local notation "W" => MvPolynomial.weightedTotalDegree
end
section
open K1_13_7_1 (denominator)
open P0_9_7_3_2 (coefficientNumerator coefficients_fit coefficients_recover)
end
end
end P3_6_7_3
end
