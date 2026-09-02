/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Exact-parameter multiplicative-subgroup collision gate

Corollary 2 of Corvaja--Zannier, JEMS 15 (2013), is convenient but loses
useful slack when its two integer parameters are optimized and rounded into
a cube-root expression.  Proposition 2 of the same paper exposes the exact
parameters.  For rational functions `u,v` of degrees `a,b`, integers `h,k`
with `a*h + b*k < p`, and `n = h*k+h+k`, it gives either

`deg(v) <= k` and `deg(u) <= h`,

or the gcd bound

`G <= (h+2*k)/n*a + k/n*b + (n-1)/2*chi`.

Apply this after descending a collision curve through
`(x,y) |-> (x^512,y^512)`.  If the descent degree is `e`, pullback gives
`G_X=e*G_Y`, the coordinate degrees satisfy `e*a=e*b=512*s`, and affine
Riemann--Hurwitz gives `e*chi_Y <= chi_X`.  Thus the denominator `e`
cancels from the useful alternative.

For the first surviving fold degree, `d=6`, the irreducible off-diagonal
collision curve has `s=5`, coordinate-power degree `2560`, and
`chi_X <= 50`.  Taking `h=k=4`, so `n=24`, clears denominators to

`48*G_X <= 2*12*2560 + 2*4*2560 + 23*24*50 = 109520`.

But 85 full sextic fibres contribute 2550 ordered collisions, for which the
left side is 122400.  The degree alternative is also impossible once the
power-map descent has degree at most 512: its quotient coordinate degree is
at least five, not at most four.

The algebraic-geometry inputs (descent degree, affine Riemann--Hurwitz, and
the proposition itself) are deliberately hypotheses of the numerical
consumer.  The exact application ledger is independently executable in
`scripts/upper-parameterized-subgroup-curve-audit.py`.
-/

namespace ProximityPrize.SubmissionUpper.ParameterizedSubgroupCurveGate

def subgroupOrder : Nat := 512
def baseCharacteristic : Nat := 2130706433

def sexticCollisionCoordinateDegree : Nat := 5
def sexticPowerCoordinateDegree : Nat := 2560
def sexticEulerCharacteristicCap : Nat := 50
def sexticFullFibres : Nat := 85
def sexticRequiredCollisions : Nat := 2550

def parameterH : Nat := 4
def parameterK : Nat := 4
def parameterN : Nat := 24
def clearedParameterizedCap : Nat := 109520

theorem parameter_denominator_receipt :
    parameterH * parameterK + parameterH + parameterK = parameterN := by
  norm_num [parameterH, parameterK, parameterN]

theorem proposition_characteristic_condition_receipt :
    sexticPowerCoordinateDegree * parameterH +
        sexticPowerCoordinateDegree * parameterK < baseCharacteristic := by
  norm_num [sexticPowerCoordinateDegree, parameterH, parameterK,
    baseCharacteristic]

theorem parameterized_cap_receipt :
    2 * (parameterH + 2 * parameterK) * sexticPowerCoordinateDegree +
        2 * parameterK * sexticPowerCoordinateDegree +
        (parameterN - 1) * parameterN * sexticEulerCharacteristicCap =
      clearedParameterizedCap := by
  norm_num [parameterH, parameterK, parameterN,
    sexticPowerCoordinateDegree, sexticEulerCharacteristicCap,
    clearedParameterizedCap]

theorem sextic_collision_receipt :
    sexticFullFibres * 6 * 5 = sexticRequiredCollisions := by
  norm_num [sexticFullFibres, sexticRequiredCollisions]

theorem required_collisions_break_parameterized_cap :
    2 * parameterN * sexticRequiredCollisions > clearedParameterizedCap := by
  norm_num [parameterN, sexticRequiredCollisions, clearedParameterizedCap]

/-- The low-degree alternative of Proposition 2 cannot occur when the
descent degree is at most 512. -/
theorem quotient_coordinate_degree_not_le_four
    (descentDegree quotientCoordinateDegree : Nat)
    (hdegree : descentDegree * quotientCoordinateDegree =
      sexticPowerCoordinateDegree)
    (hdescent : descentDegree ≤ subgroupOrder)
    (hlow : quotientCoordinateDegree ≤ parameterK) : False := by
  have hmul : descentDegree * quotientCoordinateDegree ≤
      subgroupOrder * parameterK := Nat.mul_le_mul hdescent hlow
  norm_num [hdegree, sexticPowerCoordinateDegree, subgroupOrder, parameterK] at hmul

/-- A scaling kernel acting freely on a generic five-point coordinate fibre
cannot have nontrivial dyadic order. -/
theorem dyadic_kernel_on_five_points_trivial
    (kernelOrder : Nat) (hfibre : kernelOrder ∣ 5)
    (hdyadic : kernelOrder ∣ subgroupOrder) : kernelOrder = 1 := by
  exact Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 5 512)
    hfibre (by simpa [subgroupOrder] using hdyadic)

/-- Numerical consumer for the useful alternative of the exact-parameter
subgroup-curve proposition. -/
theorem no_85_full_sextic_fibres_of_parameterized_cap
    (collisionGcd : Nat)
    (hfull : sexticRequiredCollisions ≤ collisionGcd)
    (hparameterized : 2 * parameterN * collisionGcd ≤
      clearedParameterizedCap) : False := by
  have hrequired : 2 * parameterN * sexticRequiredCollisions ≤
      2 * parameterN * collisionGcd := Nat.mul_le_mul_left _ hfull
  have := hrequired.trans hparameterized
  norm_num [parameterN, sexticRequiredCollisions, clearedParameterizedCap] at this

end ProximityPrize.SubmissionUpper.ParameterizedSubgroupCurveGate

#print axioms ProximityPrize.SubmissionUpper.ParameterizedSubgroupCurveGate.quotient_coordinate_degree_not_le_four
#print axioms ProximityPrize.SubmissionUpper.ParameterizedSubgroupCurveGate.dyadic_kernel_on_five_points_trivial
#print axioms ProximityPrize.SubmissionUpper.ParameterizedSubgroupCurveGate.no_85_full_sextic_fibres_of_parameterized_cap
