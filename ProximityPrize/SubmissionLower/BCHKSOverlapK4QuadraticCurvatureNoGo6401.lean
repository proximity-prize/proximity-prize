import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401

/-!
# A rich-K4 quadratic-curvature obstruction at score 6401

The clean-overlap graph joins two polynomial owners when they have at least
`131072` simultaneous literal agreements with the received affine row.  It
is tempting to use a triangle, a four-cycle, or a Pluecker/octahedral
curvature identity to propagate the two-owner affine charts carried by its
edges.

This file records a sharp local obstruction.  Four owners of the form

`P_z(X) = z^2 G(X)`

can realize a complete rich `K4` at the exact benchmark agreement count,
while every three distinct owners have nonzero affine curvature.  The
received row is allowed to vary with the coordinate, as it does in the
benchmark.  On a block labelled by a pair `{a,b}`, use the affine line

`-a*b*G(x) + z*(a+b)*G(x)`.

It agrees with the quadratic owner exactly at `z=a,b` whenever `G(x) != 0`.
The exact block ledger is

* common zero block: `108564`;
* four cycle-pair blocks: `22508` each;
* two diagonal-pair blocks: `31774` each.

Thus every owner has `185354` agreements; cycle pairs have exactly `131072`
common agreements, and diagonal pairs have `140338`.  A locator `G` for the
common block has degree `108564 <= 131071`.  Triangle curvature is a nonzero
scalar multiple of `G`, leaving a root deficit of `22507` rather than an
identity.  A normalized octahedral comparison does vanish on this family,
but only because it detects quadratic (not affine) challenge dependence.

No production theorem imports this audit.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSOverlapK4QuadraticCurvatureNoGo6401

open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def richK4CommonZero6401 : Nat := 108564
def richK4CyclePairBlock6401 : Nat := 22508
def richK4DiagonalPairBlock6401 : Nat := 31774

/-- The complete exact support/agreement ledger for the rich `K4`. -/
theorem richK4_block_ledger6401 :
    richK4CommonZero6401 + 4 * richK4CyclePairBlock6401 +
        2 * richK4DiagonalPairBlock6401 = n6401 /\
      richK4CommonZero6401 + 2 * richK4CyclePairBlock6401 +
        richK4DiagonalPairBlock6401 = a6401 /\
      richK4CommonZero6401 + richK4CyclePairBlock6401 =
        ownerDegreeCap6401 + 1 /\
      richK4CommonZero6401 + richK4DiagonalPairBlock6401 = 140338 /\
      richK4CommonZero6401 <= ownerDegreeCap6401 /\
      ownerDegreeCap6401 - richK4CommonZero6401 = 22507 := by
  norm_num [richK4CommonZero6401, richK4CyclePairBlock6401,
    richK4DiagonalPairBlock6401, n6401, a6401, ownerDegreeCap6401]

/-- Quadratic challenge dependence times one common locator. -/
noncomputable def quadraticOwner
    {F : Type*} [Field F] (z : F) (G : F[X]) : F[X] :=
  C (z ^ 2) * G

/-- The coordinatewise affine intercept selecting the pair `a,b`. -/
noncomputable def quadraticPairIntercept
    {F : Type*} [Field F] (a b : F) (G : F[X]) : F[X] :=
  C (-(a * b)) * G

/-- The coordinatewise affine slope selecting the pair `a,b`. -/
noncomputable def quadraticPairSlope
    {F : Type*} [Field F] (a b : F) (G : F[X]) : F[X] :=
  C (a + b) * G

/-- The pair-block interpolation identity.  Away from a zero of `G`, the
quadratic owner meets this affine challenge line precisely at `z=a` or
`z=b`. -/
theorem quadraticOwner_sub_pairLine
    {F : Type*} [Field F] (z a b : F) (G : F[X]) :
    quadraticOwner z G -
        (quadraticPairIntercept a b G +
          C z * quadraticPairSlope a b G) =
      C ((z - a) * (z - b)) * G := by
  simp only [quadraticOwner, quadraticPairIntercept, quadraticPairSlope]
  calc
    C (z ^ 2) * G -
          (C (-(a * b)) * G + C z * (C (a + b) * G)) =
        (C (z ^ 2) - (C (-(a * b)) + C z * C (a + b))) * G := by
          ring_nf
    _ = C (z ^ 2 - (-(a * b) + z * (a + b))) * G := by
      rw [← C_mul, ← C_add, ← C_sub]
    _ = C ((z - a) * (z - b)) * G := by
      congr 1
      ring

theorem quadraticOwner_eq_pairLine_left
    {F : Type*} [Field F] (a b : F) (G : F[X]) :
    quadraticOwner a G =
      quadraticPairIntercept a b G + C a * quadraticPairSlope a b G := by
  have h := quadraticOwner_sub_pairLine a a b G
  simpa using sub_eq_zero.mp (by simpa using h)

theorem quadraticOwner_eq_pairLine_right
    {F : Type*} [Field F] (a b : F) (G : F[X]) :
    quadraticOwner b G =
      quadraticPairIntercept a b G + C b * quadraticPairSlope a b G := by
  have h := quadraticOwner_sub_pairLine b a b G
  simpa using sub_eq_zero.mp (by simpa using h)

/-- No third distinct owner lies on the pair-selected affine line at a
coordinate where the locator is nonzero. -/
theorem eval_quadraticOwner_ne_pairLine_of_distinct
    {F : Type*} [Field F]
    (z a b x : F) (G : F[X])
    (hza : z ≠ a) (hzb : z ≠ b) (hG : eval x G ≠ 0) :
    eval x (quadraticOwner z G) ≠
      eval x (quadraticPairIntercept a b G +
        C z * quadraticPairSlope a b G) := by
  intro heq
  have hdiff := congrArg (eval x) (quadraticOwner_sub_pairLine z a b G)
  simp only [eval_sub, eval_mul, eval_C] at hdiff
  rw [heq, sub_self] at hdiff
  have hzprod : (z - a) * (z - b) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb)
  exact (mul_ne_zero hzprod hG) hdiff.symm

/-- Division-free affine curvature of three challenge-labelled owners. -/
noncomputable def triangleCurvature
    {F : Type*} [Field F]
    (a b c : F) (Pa Pb Pc : F[X]) : F[X] :=
  C (c - b) * Pa + C (a - c) * Pb + C (b - a) * Pc

/-- An actually affine owner triple has zero curvature. -/
theorem triangleCurvature_eq_zero_of_affine
    {F : Type*} [Field F]
    (a b c : F) (p0 p1 : F[X]) :
    triangleCurvature a b c
        (p0 + C a * p1) (p0 + C b * p1) (p0 + C c * p1) = 0 := by
  simp only [triangleCurvature]
  calc
    C (c - b) * (p0 + C a * p1) +
          C (a - c) * (p0 + C b * p1) +
          C (b - a) * (p0 + C c * p1) =
        (C (c - b) + C (a - c) + C (b - a)) * p0 +
          (C (c - b) * C a + C (a - c) * C b +
            C (b - a) * C c) * p1 := by ring
    _ = C ((c - b) + (a - c) + (b - a)) * p0 +
          C ((c - b) * a + (a - c) * b + (b - a) * c) * p1 := by
      rw [← C_add, ← C_add, ← C_mul, ← C_mul, ← C_add, ← C_mul, ← C_add]
    _ = 0 := by
      have h0 : (c - b) + (a - c) + (b - a) = 0 := by ring
      have h1 : (c - b) * a + (a - c) * b + (b - a) * c = 0 := by ring
      rw [h0, h1]
      simp

/-- Quadratic challenge dependence makes the triangle curvature a
Vandermonde scalar times the common locator.  It is therefore genuinely
non-tautological. -/
theorem triangleCurvature_quadraticOwner
    {F : Type*} [Field F]
    (a b c : F) (G : F[X]) :
    triangleCurvature a b c
        (quadraticOwner a G) (quadraticOwner b G) (quadraticOwner c G) =
      C ((a - b) * (b - c) * (c - a)) * G := by
  simp only [triangleCurvature, quadraticOwner]
  repeat' rw [← mul_assoc, ← C_mul]
  calc
    C ((c - b) * a ^ 2) * G + C ((a - c) * b ^ 2) * G +
          C ((b - a) * c ^ 2) * G =
        (C ((c - b) * a ^ 2) + C ((a - c) * b ^ 2) +
          C ((b - a) * c ^ 2)) * G := by ring
    _ = C ((c - b) * a ^ 2 + (a - c) * b ^ 2 +
          (b - a) * c ^ 2) * G := by
      rw [← C_add, ← C_add]
    _ = C ((a - b) * (b - c) * (c - a)) * G := by
      congr 1
      ring

theorem triangleCurvature_quadraticOwner_ne_zero
    {F : Type*} [Field F]
    (a b c : F) (G : F[X])
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (hG : G ≠ 0) :
    triangleCurvature a b c
        (quadraticOwner a G) (quadraticOwner b G) (quadraticOwner c G) ≠ 0 := by
  rw [triangleCurvature_quadraticOwner]
  apply mul_ne_zero
  · exact C_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hbc))
      (sub_ne_zero.mpr hca))
  · exact hG

/-- On one literal coordinate, simultaneous agreement of all three owners
with the same received affine row kills the curvature evaluation. -/
theorem eval_triangleCurvature_eq_zero_of_three_agreements
    {F : Type*} [Field F]
    (a b c u0 u1 x : F) (Pa Pb Pc : F[X])
    (ha : eval x Pa = u0 + a * u1)
    (hb : eval x Pb = u0 + b * u1)
    (hc : eval x Pc = u0 + c * u1) :
    eval x (triangleCurvature a b c Pa Pb Pc) = 0 := by
  simp only [triangleCurvature, eval_add, eval_mul, eval_C]
  rw [ha, hb, hc]
  ring

/-- Every triangle curvature of degree-bounded owners still has degree up to
the full owner cap.  The `108564` forced common roots of the rich-K4 model
therefore miss polynomial identity by exactly `22507`. -/
theorem triangleCurvature_natDegree_le
    {F : Type*} [Field F]
    (a b c : F) (Pa Pb Pc : F[X]) (k : Nat)
    (ha : Pa.natDegree <= k) (hb : Pb.natDegree <= k)
    (hc : Pc.natDegree <= k) :
    (triangleCurvature a b c Pa Pb Pc).natDegree <= k := by
  simp only [triangleCurvature]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le ((natDegree_C_mul_le _ _).trans ha)
      ((natDegree_C_mul_le _ _).trans hb)
  · exact (natDegree_C_mul_le _ _).trans hc

/-- Closed form of a quadratic secant; this is the edge chart in the rich
overlap graph. -/
noncomputable def quadraticSecant
    {F : Type*} [Field F] (a b : F) (G : F[X]) : F[X] :=
  C (a + b) * G

/-- The basic four-edge Pluecker numerator is non-tautological on the
quadratic family. -/
theorem quadraticSecant_plucker
    {F : Type*} [Field F]
    (a b c d : F) (G : F[X]) :
    quadraticSecant a b G * quadraticSecant c d G -
        quadraticSecant a c G * quadraticSecant b d G =
      C ((a + b) * (c + d) - (a + c) * (b + d)) * G ^ 2 := by
  simp only [quadraticSecant, pow_two]
  calc
    C (a + b) * G * (C (c + d) * G) -
          C (a + c) * G * (C (b + d) * G) =
        (C (a + b) * C (c + d) -
          C (a + c) * C (b + d)) * (G * G) := by ring
    _ = C ((a + b) * (c + d) - (a + c) * (b + d)) *
          (G * G) := by
      rw [← C_mul, ← C_mul, ← C_sub]

/-- Conversely, comparing normalized triangle curvatures around an
octahedron is identically zero on every quadratic challenge family.  Such an
identity detects degree at most two in the challenge, not the affine curve
required by the benchmark. -/
theorem quadratic_octahedral_curvature_tautology
    {F : Type*} [Field F]
    (a b c d : F) (G : F[X]) :
    C ((a - b) * (b - d) * (d - a)) *
        triangleCurvature a b c
          (quadraticOwner a G) (quadraticOwner b G) (quadraticOwner c G) -
      C ((a - b) * (b - c) * (c - a)) *
        triangleCurvature a b d
          (quadraticOwner a G) (quadraticOwner b G) (quadraticOwner d G) = 0 := by
  rw [triangleCurvature_quadraticOwner,
    triangleCurvature_quadraticOwner]
  ring

end BCHKSOverlapK4QuadraticCurvatureNoGo6401
end ProximityPrize.SubmissionLower
