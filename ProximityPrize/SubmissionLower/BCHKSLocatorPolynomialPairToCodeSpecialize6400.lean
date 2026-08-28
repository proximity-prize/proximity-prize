import ProximityPrize.SubmissionLower.BCHKSLocatorPolynomialPairToCode6400

/-!
# Challenge specialization of the bivariate affine code component

Kept separate from construction and degree control so Lean elaborates the
large production objects through opaque checked interfaces.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open ProximityPrize.Benchmark

/-- Challenge specialization of the bivariate affine component is exactly
the previously checked concrete affine component. -/
theorem score6400PolynomialLocatorPairToCode_map_eval
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (z : IRSProfile.Field) :
    (score6400PolynomialLocatorPairToCode f₀ f₁ q).map
        (Polynomial.evalRingHom z) =
      score6400LocatorPairToCode f₀ f₁ z
        (score6400LocatorRelationPair (fun k => (q k).eval z)) := by
  classical
  let concrete : IRSProfile.Index → IRSProfile.Field := fun i =>
    (score6400LocatorRelationPair (fun k => (q k).eval z)).1.1.eval
          (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
      (score6400LocatorRelationPair (fun k => (q k).eval z)).2.1.eval
          (IRSProfile.domain i) *
        koalaSexticFrobenius (f₀ i + z * f₁ i)
  have hvalues :
      (fun i : IRSProfile.Index =>
        (score6400PolynomialPairRelationWord f₀ f₁ q i).eval z) =
        concrete := by
    funext i
    exact score6400PolynomialPairRelationWord_eval f₀ f₁ q i z
  have hmap := algebraLagrangeInterpolate_map_eval
    Finset.univ (fun i : IRSProfile.Index => IRSProfile.domain i)
    (score6400PolynomialPairRelationWord f₀ f₁ q) z
    IRSProfile.domain.injective.injOn Finset.univ_nonempty
  have hinterpolate := congrArg
    (fun values : IRSProfile.Index → IRSProfile.Field =>
      Lagrange.interpolate Finset.univ
        (fun i : IRSProfile.Index => IRSProfile.domain i) values)
    hvalues
  have hconcrete :
      score6400LocatorPairToCode f₀ f₁ z
          (score6400LocatorRelationPair (fun k => (q k).eval z)) =
        Lagrange.interpolate Finset.univ
          (fun i : IRSProfile.Index => IRSProfile.domain i) concrete := rfl
  rw [score6400PolynomialLocatorPairToCode_eq_interpolate]
  rw [hmap, hinterpolate]
  exact hconcrete.symm

end ProximityPrize.SubmissionLower
