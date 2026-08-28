import ProximityPrize.SubmissionLower.BCHKSMultiplierDefectAbstract6400
import ProximityPrize.SubmissionLower.BCHKSMappedBilinearNode6400
import ProximityPrize.SubmissionLower.BCHKSNormalizedAffineMultiplierNodes6400

/-!
# Exact affine-lane compatibility for bounded rank-one multipliers

The locator pair attached to a second Cramer vector may be a rational
polynomial multiple of a normalized primitive pair.  Its affine lane is
defined by interpolation, so compatibility with that multiplier is not a
formal module law: a priori interpolation could reduce the product modulo the
full-domain locator.

For the score-64 parameters there is ample degree room.  Both candidate
affine lanes have degree below the number of coordinates outside the fixed
primitive-factor defect.  Their equality on those coordinates therefore
upgrades to an exact polynomial identity over the challenge fraction field.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSLocatorAffineMultiplierCompatibility6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSPrimitiveTripleRelation6400
open BCHKSMultiplierDefectAbstract6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- A bounded integral Cramer relation whose two homogeneous lanes are a
rational multiplier of the normalized primitive pair has affine lane exactly
the same multiplier times the normalized affine lane. -/
theorem score6400_affineLane_map_eq_multiplier
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q₀ q₁ : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (M : Score6400ChallengeFraction[X])
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q₀).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q₀).2.1 = H * B)
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q₀ = H * C)
    (hFixed : Fixed = fixedCoordinateDefect H)
    (hFixedCard : Fixed.card ≤ 22488)
    (hq₁ker : q₁ ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (D : Nat) (hq₁degree : ∀ k, (q₁ k).natDegree ≤ D)
    (hfield : D + 2130706433 < Fintype.card IRSProfile.Field)
    (hA₁ :
      (score6400PolynomialLocatorRelationPair q₁).1.1.map
          score6400ChallengeIota =
        M * A.map score6400ChallengeIota)
    (hB₁ :
      (score6400PolynomialLocatorRelationPair q₁).2.1.map
          score6400ChallengeIota =
        M * B.map score6400ChallengeIota)
    (hMdegree : M.natDegree < 22489)
    (hCdegree : C.natDegree < 185363) :
    (score6400PolynomialLocatorPairToCode f₀ f₁ q₁).map
        score6400ChallengeIota =
      M * C.map score6400ChallengeIota := by
  have hiota : Function.Injective score6400ChallengeIota :=
    IsFractionRing.injective IRSProfile.Field[X]
      Score6400ChallengeFraction
  have hcard : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have hC₁degreeBase :
      (score6400PolynomialLocatorPairToCode f₀ f₁ q₁).natDegree <
        185363 :=
    score6400PolynomialLocatorPairToCode_natDegree_lt
      f₀ f₁ q₁ hq₁ker D hq₁degree hfield
  have hC₁degree :
      ((score6400PolynomialLocatorPairToCode f₀ f₁ q₁).map
          score6400ChallengeIota).natDegree <
        Fintype.card IRSProfile.Index - Fixed.card := by
    rw [Polynomial.natDegree_map_eq_of_injective hiota]
    rw [hcard]
    omega
  have hCmapDegree : (C.map score6400ChallengeIota).natDegree < 185363 := by
    rw [Polynomial.natDegree_map_eq_of_injective hiota]
    exact hCdegree
  have hproductDegree :
      (M * C.map score6400ChallengeIota).natDegree <
        Fintype.card IRSProfile.Index - Fixed.card := by
    apply Polynomial.natDegree_mul_le.trans_lt
    rw [hcard]
    omega
  apply polynomial_eq_mul_of_eval_eq_outside
    score6400ChallengeFractionDomain Fixed
    ((score6400PolynomialLocatorPairToCode f₀ f₁ q₁).map
      score6400ChallengeIota)
    M (C.map score6400ChallengeIota) hC₁degree hproductDegree
  intro i hi
  have hiDefect : i ∉ fixedCoordinateDefect H := by
    simpa only [hFixed] using hi
  exact bilinear_node_eq_multiplier
    ((score6400PolynomialLocatorPairToCode f₀ f₁ q₁).map
      score6400ChallengeIota)
    ((score6400PolynomialLocatorRelationPair q₁).1.1.map
      score6400ChallengeIota)
    ((score6400PolynomialLocatorRelationPair q₁).2.1.map
      score6400ChallengeIota)
    M (A.map score6400ChallengeIota) (B.map score6400ChallengeIota)
    (C.map score6400ChallengeIota)
    (score6400ChallengeFractionDomain i)
    (score6400ChallengeIota (score6400ReceivedPolynomial f₀ f₁ i))
    (score6400ChallengeIota
      (score6400FrobeniusReceivedPolynomial f₀ f₁ i))
    (score6400_affineLane_fraction_eval_coordinate f₀ f₁ q₁ i)
    (score6400_normalizedAffineLane_fraction_eval_coordinate
      f₀ f₁ q₀ H A B C hAfactor hBfactor hCfactor i hiDefect)
    hA₁ hB₁

end BCHKSLocatorAffineMultiplierCompatibility6400
end ProximityPrize.SubmissionLower
