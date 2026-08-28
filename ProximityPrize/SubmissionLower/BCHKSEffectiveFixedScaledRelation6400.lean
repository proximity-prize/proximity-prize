import ProximityPrize.SubmissionLower.BCHKSEffectiveFixedRelation6400
import ProximityPrize.SubmissionLower.BCHKSGlobalQuotientSpecialization6400

/-! # Scaling away the effective fixed defect -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSEffectiveFixedRelation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSGlobalInhomogeneousKeyEquation6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable def score6400EffectiveFixedLocatorLift
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    IRSProfile.Field[X][X] :=
  (score6400EffectiveFixedLocator Fixed K).map
    (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X])

@[simp]
theorem score6400EffectiveFixedLocatorLift_map_eval
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X])
    (z : IRSProfile.Field) :
    (score6400EffectiveFixedLocatorLift Fixed K).map
        (Polynomial.evalRingHom z) =
      score6400EffectiveFixedLocator Fixed K := by
  exact map_C_map_eval (score6400EffectiveFixedLocator Fixed K) z

@[simp]
theorem score6400EffectiveFixedLocatorLift_natDegree
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    (score6400EffectiveFixedLocatorLift Fixed K).natDegree =
      (score6400EffectiveFixedDefect Fixed K).card := by
  rw [score6400EffectiveFixedLocatorLift,
    Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective,
    score6400EffectiveFixedLocator_natDegree]

theorem score6400EffectiveFixedLocator_eval_zero_of_mem
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X])
    (i : IRSProfile.Index)
    (hi : i ∈ score6400EffectiveFixedDefect Fixed K) :
    (score6400EffectiveFixedLocator Fixed K).eval
        (IRSProfile.domain i) = 0 := by
  apply Lagrange.eval_nodal_at_node
  exact hi

/-- Multiplying both homogeneous lanes by the effective-set locator turns a
relation valid outside that set into a relation valid at every source node. -/
theorem score6400_effectiveLocator_scaled_relation_everywhere
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (Fixed : Finset IRSProfile.Index) (K A B : IRSProfile.Field[X][X])
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (hrelation : ∀ i,
      i ∉ score6400EffectiveFixedDefect Fixed K →
      (A.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
          (B.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            (koalaSexticFrobenius (f₀ i + z * f₁ i) -
              (P.map koalaSexticFrobenius.toRingHom).eval
                (IRSProfile.domain i)) = 0)
    (i : IRSProfile.Index) :
    ((score6400EffectiveFixedLocatorLift Fixed K * A).map
        (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
          ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
      ((score6400EffectiveFixedLocatorLift Fixed K * B).map
        (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
          (koalaSexticFrobenius (f₀ i + z * f₁ i) -
            (P.map koalaSexticFrobenius.toRingHom).eval
              (IRSProfile.domain i)) = 0 := by
  let R := score6400EffectiveFixedLocator Fixed K
  let Az := A.map (Polynomial.evalRingHom z)
  let Bz := B.map (Polynomial.evalRingHom z)
  let e := (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)
  let g := koalaSexticFrobenius (f₀ i + z * f₁ i) -
    (P.map koalaSexticFrobenius.toRingHom).eval (IRSProfile.domain i)
  have hshape :
      ((score6400EffectiveFixedLocatorLift Fixed K * A).map
          (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) =
        R.eval (IRSProfile.domain i) * Az.eval (IRSProfile.domain i) := by
    rw [Polynomial.map_mul, Polynomial.eval_mul,
      score6400EffectiveFixedLocatorLift_map_eval]
  have hshapeB :
      ((score6400EffectiveFixedLocatorLift Fixed K * B).map
          (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) =
        R.eval (IRSProfile.domain i) * Bz.eval (IRSProfile.domain i) := by
    rw [Polynomial.map_mul, Polynomial.eval_mul,
      score6400EffectiveFixedLocatorLift_map_eval]
  rw [hshape, hshapeB]
  by_cases hi : i ∈ score6400EffectiveFixedDefect Fixed K
  · have hRzero : R.eval (IRSProfile.domain i) = 0 := by
      simpa only [R] using
        score6400EffectiveFixedLocator_eval_zero_of_mem Fixed K i hi
    simp only [hRzero, zero_mul, add_zero]
  · apply scaled_bilinear_error_eq_zero
    simpa only [Az, Bz, e, g] using hrelation i hi

theorem score6400_effectiveLocatorLift_mul_natDegree_le
    (Fixed : Finset IRSProfile.Index) (K P : IRSProfile.Field[X][X]) :
    (score6400EffectiveFixedLocatorLift Fixed K * P).natDegree ≤
      (score6400EffectiveFixedDefect Fixed K).card + P.natDegree := by
  exact Polynomial.natDegree_mul_le.trans_eq (by
    rw [score6400EffectiveFixedLocatorLift_natDegree])

end BCHKSEffectiveFixedRelation6400
end ProximityPrize.SubmissionLower
