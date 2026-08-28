import ProximityPrize.SubmissionLower.BCHKSLocatorRelationProduction6400
import ProximityPrize.SubmissionLower.BCHKSSyndromeInterpolationDegree6400

/-!
# The affine code component of a production locator relation

The production locator pencil was originally consumed only through its
pointwise error relation.  This file retains the affine component that is
lost in that formulation.  Lagrange interpolation is linear in the pair of
locator multipliers, and the zero syndrome prefix lowers its degree from the
full domain size to `185363`.

For every close owner polynomial `P`, the resulting code polynomial is
exactly

`A * P + B * P.map sigma`.

This is the interface needed to principalize the full triple `(C,A,B)` in
the remaining rational-rank-one branch.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- Interpolation of the received-word relation attached to a pair of
locator multipliers at one challenge. -/
noncomputable def score6400LocatorPairToCode
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (u : PolynomialPairSpace IRSProfile.Field locatorOrdinaryRows6400
      locatorFrobeniusRows6400) : IRSProfile.Field[X] :=
  Lagrange.interpolate Finset.univ
    (fun i : IRSProfile.Index => IRSProfile.domain i)
    (fun i =>
      u.1.1.eval (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
        u.2.1.eval (IRSProfile.domain i) *
          koalaSexticFrobenius (f₀ i + z * f₁ i))

@[simp]
theorem score6400LocatorPairToCode_eval
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (u : PolynomialPairSpace IRSProfile.Field locatorOrdinaryRows6400
      locatorFrobeniusRows6400)
    (i : IRSProfile.Index) :
    (score6400LocatorPairToCode f₀ f₁ z u).eval (IRSProfile.domain i) =
      u.1.1.eval (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
        u.2.1.eval (IRSProfile.domain i) *
          koalaSexticFrobenius (f₀ i + z * f₁ i) := by
  exact Lagrange.eval_interpolate_at_node
    (fun i =>
      u.1.1.eval (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
        u.2.1.eval (IRSProfile.domain i) *
          koalaSexticFrobenius (f₀ i + z * f₁ i))
    IRSProfile.domain.injective.injOn (Finset.mem_univ i)

/-- A production-pencil kernel pair has an affine code component of degree
strictly below `185363`. -/
theorem score6400LocatorPairToCode_natDegree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq : q ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin) :
    (score6400LocatorPairToCode f₀ f₁ z
      (score6400LocatorRelationPair q)).natDegree < 185363 := by
  have hcard : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have hcolumns : locatorColumns6400 = 76781 := by
    norm_num [locatorColumns6400]
  have hraw :
      (Lagrange.interpolate Finset.univ
        (fun i : IRSProfile.Index => IRSProfile.domain i)
        (fun i =>
          (score6400LocatorRelationPair q).1.1.eval
                (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
            (score6400LocatorRelationPair q).2.1.eval
                (IRSProfile.domain i) *
              koalaSexticFrobenius (f₀ i + z * f₁ i))).natDegree <
        Fintype.card IRSProfile.Index - locatorColumns6400 :=
    rsSyndromeInterpolation_natDegree_lt_card_sub_of_zero_prefix
      IRSProfile.domain
      (fun i =>
        (score6400LocatorRelationPair q).1.1.eval
              (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
          (score6400LocatorRelationPair q).2.1.eval
              (IRSProfile.domain i) *
            koalaSexticFrobenius (f₀ i + z * f₁ i))
      locatorColumns6400
      (by rw [hcard, hcolumns]; norm_num)
      (fun t ht => by
        exact score6400_locatorKernel_received_relation_moment
          f₀ f₁ z q hq t ht)
  rw [hcard, hcolumns] at hraw
  change
    (Lagrange.interpolate Finset.univ
      (fun i : IRSProfile.Index => IRSProfile.domain i)
      (fun i =>
        (score6400LocatorRelationPair q).1.1.eval
              (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
          (score6400LocatorRelationPair q).2.1.eval
              (IRSProfile.domain i) *
            koalaSexticFrobenius (f₀ i + z * f₁ i))).natDegree < 185363
  exact hraw

end ProximityPrize.SubmissionLower
