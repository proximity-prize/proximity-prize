/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# The first exact-parameter fold frontier

Optimizing the integer parameters in Corvaja--Zannier Proposition 2 rules out
the useful alternative for a full irreducible collision curve through map
degree fourteen.  Degree fifteen is the first numerical survivor.  It is
exceptionally narrow: 34 full fibres cover 510 of the 512 subgroup points and
give 7140 ordered collisions, while the maximal bidegree `(14,14)` Euler
characteristic gives the cleared estimate

`18 * G <= 128576`,

only 56 above `18 * 7140 = 128520`.  Reducing the Euler-characteristic cap
from 392 to 391 changes the right side by 72 and closes the case with margin
16.  Consequently any survivor must simultaneously have maximal genus 169
and all 56 possible boundary punctures.

There is a second useful normalization.  For a monic odd-degree fibre
`A - t B` with roots in `mu_512`, its constant coefficient is the negative of
the root product.  Dividing that product by any root gives the product of the
other fourteen roots, again in `mu_512`.  Algebraically this is the value of

`(B(0) A(x) - A(0) B(x)) / (x B(x))`.

The numerator vanishes at zero, so after cancelling `x` this is a rational
map of degree at most fourteen.  Thus a degree-fifteen survivor induces a
degree-fourteen map carrying the same 510 subgroup inputs back into the
subgroup.  This is the concrete next target for a stability theorem or an
exact search.  The geometric subgroup-curve estimate remains an explicit
hypothesis of the numerical consumer; the arithmetic is independently
audited by `scripts/upper-fifteenth-fold-frontier-audit.py`.
-/

namespace ProximityPrize.SubmissionUpper.FifteenthFoldFrontier

open Polynomial
open scoped BigOperators

def subgroupOrder : Nat := 512
def baseCharacteristic : Nat := 2130706433
def mapDegree : Nat := 15
def collisionCoordinateDegree : Nat := 14
def powerCoordinateDegree : Nat := 7168
def fullFibres : Nat := 34
def usedSubgroupPoints : Nat := 510
def requiredCollisions : Nat := 7140

def parameterH : Nat := 4
def parameterK : Nat := 1
def parameterN : Nat := 9
def maximalGenus : Nat := 169
def maximalBoundary : Nat := 56
def maximalEulerCharacteristic : Nat := 392
def improvedEulerCharacteristic : Nat := 391
def maximalClearedCap : Nat := 128576
def improvedClearedCap : Nat := 128504

theorem fibre_count_receipt : fullFibres * mapDegree = usedSubgroupPoints := by
  norm_num [fullFibres, mapDegree, usedSubgroupPoints]

theorem collision_count_receipt :
    fullFibres * mapDegree * collisionCoordinateDegree = requiredCollisions := by
  norm_num [fullFibres, mapDegree, collisionCoordinateDegree, requiredCollisions]

theorem parameter_denominator_receipt :
    parameterH * parameterK + parameterH + parameterK = parameterN := by
  norm_num [parameterH, parameterK, parameterN]

theorem proposition_characteristic_condition_receipt :
    powerCoordinateDegree * parameterH + powerCoordinateDegree * parameterK <
      baseCharacteristic := by
  norm_num [powerCoordinateDegree, parameterH, parameterK, baseCharacteristic]

theorem maximal_geometry_receipt :
    (collisionCoordinateDegree - 1) ^ 2 = maximalGenus ∧
      4 * collisionCoordinateDegree = maximalBoundary ∧
      2 * maximalGenus - 2 + maximalBoundary = maximalEulerCharacteristic := by
  norm_num [collisionCoordinateDegree, maximalGenus, maximalBoundary,
    maximalEulerCharacteristic]

theorem maximal_parameterized_cap_receipt :
    2 * (parameterH + 2 * parameterK) * powerCoordinateDegree +
        2 * parameterK * powerCoordinateDegree +
        (parameterN - 1) * parameterN * maximalEulerCharacteristic =
      maximalClearedCap := by
  norm_num [parameterH, parameterK, parameterN, powerCoordinateDegree,
    maximalEulerCharacteristic, maximalClearedCap]

theorem improved_parameterized_cap_receipt :
    2 * (parameterH + 2 * parameterK) * powerCoordinateDegree +
        2 * parameterK * powerCoordinateDegree +
        (parameterN - 1) * parameterN * improvedEulerCharacteristic =
      improvedClearedCap := by
  norm_num [parameterH, parameterK, parameterN, powerCoordinateDegree,
    improvedEulerCharacteristic, improvedClearedCap]

/-- The completely generic bound misses by exactly 56 after denominators are
cleared. -/
theorem maximal_cap_deficit_receipt :
    maximalClearedCap - 2 * parameterN * requiredCollisions = 56 := by
  norm_num [maximalClearedCap, parameterN, requiredCollisions]

/-- Saving one unit of affine Euler characteristic closes the degree-fifteen
collision count with an exact cleared margin of 16. -/
theorem one_euler_unit_closes_receipt :
    2 * parameterN * requiredCollisions - improvedClearedCap = 16 := by
  norm_num [parameterN, requiredCollisions, improvedClearedCap]

theorem no_full_fibres_of_improved_parameterized_cap
    (collisionGcd : Nat)
    (hfull : requiredCollisions ≤ collisionGcd)
    (hparameterized : 2 * parameterN * collisionGcd ≤ improvedClearedCap) : False := by
  have hrequired : 2 * parameterN * requiredCollisions ≤
      2 * parameterN * collisionGcd := Nat.mul_le_mul_left _ hfull
  have := hrequired.trans hparameterized
  norm_num [parameterN, requiredCollisions, improvedClearedCap] at this

section ProductCofactor

variable {F : Type*} [Field F]

def productLabel (a0 b0 t : F) : F := -(a0 - t * b0)

/-- For an odd monic split fibre, the negative constant coefficient is the
product of all fifteen roots. -/
theorem product_label_eq_of_split_fifteen
    (A B : Polynomial F) (a0 b0 t : F) (roots : Fin 15 → F)
    (hA0 : A.eval 0 = a0) (hB0 : B.eval 0 = b0)
    (hsplit : A - Polynomial.C t * B =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) :
    productLabel a0 b0 t = ∏ i, roots i := by
  have hzero := congrArg (fun P : Polynomial F => P.eval 0) hsplit
  have hsign : (-1 : F) ^ 15 = -1 := by ring
  simpa [productLabel, hA0, hB0, Polynomial.eval_prod, Finset.prod_neg, hsign]
    using congrArg Neg.neg hzero

theorem product_label_mem_subgroup
    (a0 b0 t : F) (roots : Fin 15 → F)
    (hroots : ∀ i, roots i ^ subgroupOrder = 1)
    (hconstant : productLabel a0 b0 t = ∏ i, roots i) :
    productLabel a0 b0 t ^ subgroupOrder = 1 := by
  rw [hconstant, ← Finset.prod_pow]
  simp [hroots]

/-- Dividing the fibre product by one nonzero root leaves the product of the
other fourteen roots, hence another subgroup element. -/
theorem cofactor_label_mem_subgroup
    (label root : F) (hlabel : label ^ subgroupOrder = 1)
    (hroot : root ^ subgroupOrder = 1) :
    (label / root) ^ subgroupOrder = 1 := by
  have hroot0 : root ≠ 0 := by
    intro hz
    subst root
    norm_num [subgroupOrder] at hroot
  rw [div_pow, hlabel, hroot, div_one]

/-- The normalized cofactor value is represented by a numerator vanishing at
zero.  After cancelling `x`, both numerator and denominator have degree at
most fourteen in the extremal degree-fifteen normalization. -/
theorem normalized_cofactor_identity
    (A B : Polynomial F) (a0 b0 x : F)
    (hx : x ≠ 0) (hBx : B.eval x ≠ 0) :
    productLabel a0 b0 (A.eval x / B.eval x) / x =
      (b0 * A.eval x - a0 * B.eval x) / (x * B.eval x) := by
  simp only [productLabel]
  field_simp [hx, hBx]
  ring

theorem normalized_numerator_vanishes_at_zero
    (A B : Polynomial F) (a0 b0 : F)
    (hA0 : A.eval 0 = a0) (hB0 : B.eval 0 = b0) :
    (Polynomial.C b0 * A - Polynomial.C a0 * B).eval 0 = 0 := by
  simp [hA0, hB0]
  ring

theorem X_dvd_normalized_numerator
    (A B : Polynomial F) (a0 b0 : F)
    (hA0 : A.eval 0 = a0) (hB0 : B.eval 0 = b0) :
    (Polynomial.X : Polynomial F) ∣
      Polynomial.C b0 * A - Polynomial.C a0 * B := by
  rw [show (Polynomial.X : Polynomial F) = Polynomial.X - Polynomial.C 0 by simp,
    Polynomial.dvd_iff_isRoot]
  exact normalized_numerator_vanishes_at_zero A B a0 b0 hA0 hB0

end ProductCofactor

end ProximityPrize.SubmissionUpper.FifteenthFoldFrontier

#print axioms ProximityPrize.SubmissionUpper.FifteenthFoldFrontier.no_full_fibres_of_improved_parameterized_cap
#print axioms ProximityPrize.SubmissionUpper.FifteenthFoldFrontier.product_label_mem_subgroup
#print axioms ProximityPrize.SubmissionUpper.FifteenthFoldFrontier.normalized_cofactor_identity
#print axioms ProximityPrize.SubmissionUpper.FifteenthFoldFrontier.X_dvd_normalized_numerator
