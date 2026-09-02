/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Multiplicative-subgroup obstruction for cubic folds

A degree-three rational map with 170 full fibres on the 512-point inner
domain would create `170 * 3 * 2 = 1020` ordered off-diagonal collisions.
After writing its monic fibre pencil as `A + t B`, with `A` cubic and `B`
quadratic, the off-diagonal collision equation has bidegree at most `(2,2)`.
The first theorem below verifies that factorization coefficient by
coefficient.

Corollary 2 of Corvaja--Zannier, JEMS 15 (2013), DOI 10.4171/JEMS/409,
bounds the intersection of a non-toric absolutely irreducible curve of
bidegree `(d₁,d₂)` and Euler characteristic `χ` with
`μ_m₁ × μ_m₂` by

`max (3 * ∛(2*m₁*m₂*d₁*d₂*χ),
      12*m₁*m₂*d₁*d₂/p)`.

The coordinate degrees are at most two and `p` does not divide 512, so the
nonzero-differential hypothesis behind the corollary is automatic here.

For `(m₁,m₂,d₁,d₂,χ) = (512,512,2,2,8)`, the first
branch is exactly 768 and the second is smaller.  Thus an irreducible
non-toric collision curve cannot supply 1020 collisions.

The exceptional cases need separate bookkeeping.  If the whole collision
curve is an irreducible torus translate, symmetry forces it to be a graph
`xy = c` or `x/y = c` (in the second case symmetry also gives `c² = 1`).
Such a graph contains at most 512 points of `μ_512 × μ_512`, already
fewer than 1020.

If the collision curve is geometrically reducible, coprimality of `A,B` and
separability of the degree-three map make its two `(1,1)` components the
graphs of the two nonidentity deck transformations.  Each graph contains
`170 * 3 = 510` of the ordered collisions.  A non-toric `(1,1)` graph has
genus zero and at most four punctures, so Corvaja--Zannier with `χ ≤ 2`
bounds its subgroup points by less than 305 (after a finite extension of the
field of definition if necessary).  A toric `(1,1)` graph is a scaling or an
inversion.  For a scaling, even one subgroup collision puts its scalar in
`μ_512`, incompatible with nontrivial order three; an inversion has order
two.

For completeness, the Möbius lemmas below record the stronger fact that a
transformation preserving all 512 roots must be diagonal or anti-diagonal.
That stronger premise is not used in the reducible-case argument: the 170
full fibres account for only 510 of the 512 roots.

The algebraic-geometry point-count inputs are deliberately exposed as
hypotheses in the final numerical consumers; the component/deck reductions
above are audit notes rather than Lean formalizations.  This keeps the upper
submission self-contained; `scripts/upper-cubic-collision-curve-audit.py`
records the exact application ledger.
-/

namespace ProximityPrize.SubmissionUpper.CubicCollisionCurveGate

variable {F : Type*} [Field F]

def cubicEval (a₀ a₁ a₂ a₃ x : F) : F :=
  a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3

def quadraticEval (b₀ b₁ b₂ x : F) : F :=
  b₀ + b₁ * x + b₂ * x ^ 2

/-- The quotient after removing the diagonal from equality of two values of
the cubic-over-quadratic rational map. -/
def collisionQuotient
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ x y : F) : F :=
  (a₁ * b₀ - a₀ * b₁) +
    (a₂ * b₀ - a₀ * b₂) * (x + y) +
    (a₂ * b₁ - a₁ * b₂) * x * y +
    (a₃ * b₀) * (x ^ 2 + x * y + y ^ 2) +
    (a₃ * b₁) * x * y * (x + y) +
    (a₃ * b₂) * x ^ 2 * y ^ 2

/-- Removing the diagonal leaves a polynomial of degree at most two in each
coordinate. -/
theorem cubic_quadratic_collision_factorization
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ x y : F) :
    cubicEval a₀ a₁ a₂ a₃ x * quadraticEval b₀ b₁ b₂ y -
        cubicEval a₀ a₁ a₂ a₃ y * quadraticEval b₀ b₁ b₂ x =
      (x - y) * collisionQuotient a₀ a₁ a₂ a₃ b₀ b₁ b₂ x y := by
  simp only [cubicEval, quadraticEval, collisionQuotient]
  ring

/-- If all four entries of a Möbius matrix are nonzero, equality of the
first two interior binomial coefficients already makes its determinant
zero. -/
theorem interior_coefficients_force_singular
    {a b c d : F} (hc : c ≠ 0) (hd : d ≠ 0)
    (h₁ : a * b ^ 511 = c * d ^ 511)
    (h₂ : a ^ 2 * b ^ 510 = c ^ 2 * d ^ 510) :
    a * d - b * c = 0 := by
  have hproduct : c * d ^ 510 * (a * d - b * c) = 0 := by
    calc
      c * d ^ 510 * (a * d - b * c) =
          a * (c * d ^ 511) - b * (c ^ 2 * d ^ 510) := by ring
      _ = a * (a * b ^ 511) - b * (a ^ 2 * b ^ 510) := by rw [← h₁, ← h₂]
      _ = 0 := by ring
  have hleft : c * d ^ 510 ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hd)
  exact (mul_eq_zero.mp hproduct).resolve_left hleft

/-- The two coefficient comparisons and a nonzero determinant force a
Möbius matrix to be diagonal or anti-diagonal. -/
theorem mobius_matrix_sparse
    [DecidableEq F] {a b c d : F} (hdet : a * d - b * c ≠ 0)
    (h₁ : a * b ^ 511 = c * d ^ 511)
    (h₂ : a ^ 2 * b ^ 510 = c ^ 2 * d ^ 510) :
    (b = 0 ∧ c = 0) ∨ (a = 0 ∧ d = 0) := by
  by_cases ha : a = 0
  · right
    refine ⟨ha, ?_⟩
    subst a
    have hbc : b * c ≠ 0 := by simpa using hdet
    have hc : c ≠ 0 := (mul_ne_zero_iff.mp hbc).2
    have hdPow : d ^ 511 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hc
      simpa using h₁
    exact eq_zero_of_pow_eq_zero hdPow
  by_cases hb : b = 0
  · left
    refine ⟨hb, ?_⟩
    subst b
    have hd : d ≠ 0 := by
      intro hd
      subst d
      simp at hdet
    have hcPow : c * d ^ 511 = 0 := by simpa using h₁.symm
    exact (mul_eq_zero.mp hcPow).resolve_right (pow_ne_zero _ hd)
  by_cases hc : c = 0
  · left
    exact ⟨by
      subst c
      have hab : a * b ^ 511 = 0 := by simpa using h₁
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hab).resolve_left ha), hc⟩
  by_cases hd : d = 0
  · right
    exact ⟨by
      subst d
      have hab : a * b ^ 511 = 0 := by simpa using h₁
      exact (mul_eq_zero.mp hab).resolve_right (pow_ne_zero _ hb), hd⟩
  · exact False.elim (hdet (interior_coefficients_force_singular hc hd h₁ h₂))

/-- A diagonal stabilizer cannot have nontrivial order three when its scalar
also has order dividing 512. -/
theorem no_nontrivial_diagonal_order_three {r : F}
    (hthree : r ^ 3 = 1) (hsubgroup : r ^ 512 = 1) : r = 1 := by
  exact (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 3 512)).mp
    ⟨hthree, hsubgroup⟩

/-- An anti-diagonal fractional-linear map is an involution. -/
theorem antidiagonal_is_involution (r x : F) (hr : r ≠ 0) (hx : x ≠ 0) :
    r / (r / x) = x := by
  field_simp

def fullCubicFibres : ℕ := 170
def subgroupOrder : ℕ := 512
def collisionBidegree : ℕ := 2
def eulerCharacteristicCap : ℕ := 8
def nonToricCollisionCap : ℕ := 768
def requiredOrderedCollisions : ℕ := 1020
def toricGraphCollisionCap : ℕ := 512
def reducibleComponentCollisions : ℕ := 510
def graphBidegree : ℕ := 1
def graphEulerCharacteristicCap : ℕ := 2
def nonToricGraphCap : ℕ := 305
def baseCharacteristic : ℕ := 2130706433

theorem full_fibre_collision_receipt :
    fullCubicFibres * 3 * 2 = requiredOrderedCollisions := by
  norm_num [fullCubicFibres, requiredOrderedCollisions]

/-- A generator of a cyclic cubic deck group contributes one directed
collision from each point in every full fibre. -/
theorem full_fibre_component_collision_receipt :
    fullCubicFibres * 3 = reducibleComponentCollisions := by
  norm_num [fullCubicFibres, reducibleComponentCollisions]

/-- Cubing the first Corvaja--Zannier branch gives an exact integer
identity, avoiding any formal real cube roots. -/
theorem subgroup_curve_first_branch_receipt :
    54 * subgroupOrder ^ 2 * collisionBidegree ^ 2 * eulerCharacteristicCap =
      nonToricCollisionCap ^ 3 := by
  norm_num [subgroupOrder, collisionBidegree, eulerCharacteristicCap,
    nonToricCollisionCap]

theorem subgroup_curve_second_branch_receipt :
    12 * subgroupOrder ^ 2 * collisionBidegree ^ 2 <
      nonToricCollisionCap * baseCharacteristic := by
  norm_num [subgroupOrder, collisionBidegree, nonToricCollisionCap,
    baseCharacteristic]

/-- The first Corvaja--Zannier branch for a non-toric `(1,1)` deck graph is
strictly below the convenient integral cap 305. -/
theorem subgroup_graph_first_branch_receipt :
    54 * subgroupOrder ^ 2 * graphBidegree ^ 2 * graphEulerCharacteristicCap <
      nonToricGraphCap ^ 3 := by
  norm_num [subgroupOrder, graphBidegree, graphEulerCharacteristicCap,
    nonToricGraphCap]

theorem subgroup_graph_second_branch_receipt :
    12 * subgroupOrder ^ 2 * graphBidegree ^ 2 <
      nonToricGraphCap * baseCharacteristic := by
  norm_num [subgroupOrder, graphBidegree, nonToricGraphCap, baseCharacteristic]

/-- Numerical consumer for the cited subgroup-curve theorem. -/
theorem no_170_full_fibres_of_collision_cap
    (collisionPoints : ℕ)
    (hfull : requiredOrderedCollisions ≤ collisionPoints)
    (hCZ : collisionPoints ≤ nonToricCollisionCap) : False := by
  norm_num [requiredOrderedCollisions, nonToricCollisionCap] at hfull hCZ
  omega

/-- Numerical consumer for the irreducible toric-graph case. -/
theorem no_170_full_fibres_of_toric_graph_cap
    (collisionPoints : ℕ)
    (hfull : requiredOrderedCollisions ≤ collisionPoints)
    (htoric : collisionPoints ≤ toricGraphCollisionCap) : False := by
  norm_num [requiredOrderedCollisions, toricGraphCollisionCap] at hfull htoric
  omega

/-- Numerical consumer for one non-toric graph component in the geometrically
reducible case. -/
theorem no_170_full_fibres_of_graph_cap
    (componentPoints : ℕ)
    (hfull : reducibleComponentCollisions ≤ componentPoints)
    (hCZ : componentPoints ≤ nonToricGraphCap) : False := by
  norm_num [reducibleComponentCollisions, nonToricGraphCap] at hfull hCZ
  omega

end ProximityPrize.SubmissionUpper.CubicCollisionCurveGate

#print axioms ProximityPrize.SubmissionUpper.CubicCollisionCurveGate.cubic_quadratic_collision_factorization
#print axioms ProximityPrize.SubmissionUpper.CubicCollisionCurveGate.mobius_matrix_sparse
#print axioms ProximityPrize.SubmissionUpper.CubicCollisionCurveGate.no_170_full_fibres_of_collision_cap
#print axioms ProximityPrize.SubmissionUpper.CubicCollisionCurveGate.no_170_full_fibres_of_graph_cap
