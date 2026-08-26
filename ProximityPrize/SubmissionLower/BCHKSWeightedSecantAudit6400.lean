import ProximityPrize.SubmissionLower.BCHKSDeepHigherDegreeAudit6400
import ProximityPrize.SubmissionLower.BCHKSWeightedSubstitution

namespace ProximityPrize.SubmissionLower
namespace BCHKSWeightedSecantAudit6400

open BCHKSWeightedSubstitution

/-!
The weighted-secant constraint for a repeated nonlinear owner.

For two challenges `z != w`, coefficientwise affine interpolation between
their degree-`k` root polynomials gives a polynomial `P_zw(X,Z)` of `X`
degree at most `k`.  At every coordinate where both challenges use an
identity section of an irreducible factor `R`, substituting `P_zw` into `R`
has `X`-root order at least the local identity order `nu_i`.  Its `X` degree
is at most the `(1,k)` weight `weight(R)`.  If the sum of the common orders
were larger than that weight, the substitution would vanish identically;
then `P_zw` would be a root of `R` over the coefficient fraction field,
contradicting irreducibility when `deg_Y R >= 2`.

The polynomial shift-to-root transfer is kept as an explicit hypothesis in
`weightedSecantIntersection_le`; the root count, irreducibility finish, and
the exact weighted-Cauchy arithmetic are unconditional.
-/

/-- An irreducible polynomial of degree other than one has no root in its
coefficient field.  This is the final algebraic step of the secant argument. -/
theorem irreducible_eval_ne_zero_of_two_le_natDegree
    {K : Type*} [Field K] (R : Polynomial K) (p : K)
    (hirr : Irreducible R) (hdeg : 2 <= R.natDegree) :
    R.eval p ≠ 0 := by
  intro hroot
  exact hirr.not_isRoot_of_natDegree_ne_one (by omega) hroot

/-- Root counting for the substituted secant.  The injective locator map
ensures that the coordinate roots are distinct. -/
theorem weightedSecantIntersection_le
    {F iota : Type*} [Field F] [DecidableEq F] [DecidableEq iota]
    (substitution : Polynomial F) (omega : iota ↪ F)
    (C : Finset iota) (nu : iota -> Nat) (weight : Nat)
    (hdegree : substitution.natDegree <= weight)
    (hmult : ∀ i ∈ C,
      nu i <= substitution.rootMultiplicity (omega i)) :
    (∑ i ∈ C, nu i) <= weight := by
  exact (sum_le_natDegree_of_rootMultiplicity
    substitution omega C nu hmult).trans hdegree

/-- Convenient contradiction form: it is enough to know that an identically
zero secant substitution would give a forbidden root of a nonlinear
irreducible factor. -/
theorem weightedSecantIntersection_le_of_zero_forces_irreducible_root
    {F K iota : Type*} [Field F] [Field K]
    [DecidableEq F] [DecidableEq iota]
    (substitution : Polynomial F) (omega : iota ↪ F)
    (C : Finset iota) (nu : iota -> Nat) (weight : Nat)
    (R : Polynomial K) (p : K)
    (hirr : Irreducible R) (hdegR : 2 <= R.natDegree)
    (hzero : substitution = 0 -> R.eval p = 0)
    (hdegree : substitution.natDegree <= weight)
    (hmult : substitution ≠ 0 -> ∀ i ∈ C,
      nu i <= substitution.rootMultiplicity (omega i)) :
    (∑ i ∈ C, nu i) <= weight := by
  have hsubstitution : substitution ≠ 0 := by
    intro hz
    exact irreducible_eval_ne_zero_of_two_le_natDegree R p hirr hdegR
      (hzero hz)
  exact weightedSecantIntersection_le substitution omega C nu weight
    hdegree (hmult hsubstitution)

/-- Scalar weighted-Johnson calculation after deleting a mandatory core.

`L` owners each have residual incidence mass at least `s`; the residual
universe has mass `W`; and every ordered pair has common residual mass at
most `w`.  Cauchy and pair counting give `hcauchy`.  The conclusion is the
division-free list bound

`L * (s^2 - W*w) <= W * (s-w)`.

It is useful exactly when the parenthesized Johnson denominator is positive.
-/
theorem weightedJohnson_scalar
    (L W s w : Real) (hL : 0 < L)
    (hcauchy : (L * s) ^ 2 <=
      W * (L * s + L * (L - 1) * w)) :
    L * (s ^ 2 - W * w) <= W * (s - w) := by
  nlinarith [sq_nonneg (L * s)]

/-- A positive Johnson denominator turns the preceding inequality into an
explicit owner-count bound. -/
theorem weightedJohnson_card_bound
    (L W s w B : Real) (hL : 0 < L)
    (hcauchy : (L * s) ^ 2 <=
      W * (L * s + L * (L - 1) * w))
    (hden : 0 < s ^ 2 - W * w)
    (hB : W * (s - w) <= B * (s ^ 2 - W * w)) :
    L <= B := by
  have hmain := weightedJohnson_scalar L W s w hL hcauchy
  nlinarith

/-- In a cubic identity profile, `b3` full-multiplicity coordinates account
for three units each and are a mandatory common core. -/
theorem cubic_fullMultiplicity_core_lower
    (b1 b2 b3 b t : Nat)
    (hb : b1 + b2 + b3 = b)
    (ht : b2 + 2 * b3 = t) :
    t - b <= b3 := by
  omega

/-- A nonzero cubic slice with a triple received root has no other root.
This is why all full-multiplicity coordinates belong to every owner away
from the leading-coefficient exceptional fibres. -/
theorem eq_received_of_cubic_triple_root
    {A : Type*} [CommRing A] [IsDomain A]
    (c p u : A) (hc : c ≠ 0)
    (hroot : c * (p - u) ^ 3 = 0) :
    p = u := by
  have hpow : (p - u) ^ 3 = 0 := (mul_eq_zero.mp hroot).resolve_left hc
  have hsub : p - u = 0 := (pow_eq_zero_iff (by norm_num : (3 : Nat) ≠ 0)).mp hpow
  exact sub_eq_zero.mp hsub

def cubicWorstB6400 : Nat := 262121
def cubicWorstT6400 : Nat := 326758
def cubicWorstB3Core6400 : Nat := 64637
def cubicWorstWeightedCore6400 : Nat := 193911
def cubicWorstResidualMass6400 : Nat := 394968
def cubicWorstOwnerScore6400 : Nat := 444313
def cubicWorstResidualScore6400 : Nat := 250402
def cubicWorstWeight6400 : Nat := 393213
def cubicWorstResidualPairCap6400 : Nat := 199302
def cubicWorstCauchyGapNumerator6400 : Nat := 16016750732

/-- Exact arithmetic at the worst coarse cubic profile found by the integer
scan.  The full-multiplicity core improves the asymptotic common-order lower
bound from inclusion-exclusion to

`193911 + 250402^2 / 394968`,

but this remains below the secant cap `393213` by
`16016750732 / 394968 = 40552.02...`.  Thus weighted Cauchy is a major
reduction, not yet a complete cubic closure. -/
lemma cubicWorstProfile_exact6400 :
    cubicWorstB3Core6400 = cubicWorstT6400 - cubicWorstB6400 ∧
    cubicWorstWeightedCore6400 = 3 * cubicWorstB3Core6400 ∧
    cubicWorstResidualMass6400 =
      cubicWorstB6400 + cubicWorstT6400 - cubicWorstWeightedCore6400 ∧
    cubicWorstOwnerScore6400 =
      cubicWorstWeight6400 +
        (868689 + 17 - 1) / 17 ∧
    cubicWorstResidualScore6400 =
      cubicWorstOwnerScore6400 - cubicWorstWeightedCore6400 ∧
    cubicWorstResidualPairCap6400 =
      cubicWorstWeight6400 - cubicWorstWeightedCore6400 ∧
    cubicWorstCauchyGapNumerator6400 =
      cubicWorstWeight6400 * cubicWorstResidualMass6400 -
        (cubicWorstWeightedCore6400 * cubicWorstResidualMass6400 +
          cubicWorstResidualScore6400 ^ 2) := by
  norm_num [cubicWorstB3Core6400, cubicWorstT6400, cubicWorstB6400,
    cubicWorstWeightedCore6400, cubicWorstResidualMass6400,
    cubicWorstOwnerScore6400, cubicWorstWeight6400,
    cubicWorstResidualScore6400, cubicWorstResidualPairCap6400,
    cubicWorstCauchyGapNumerator6400]

lemma cubicWorstProfile_cauchy_still_below_cap6400 :
    cubicWorstWeightedCore6400 * cubicWorstResidualMass6400 +
        cubicWorstResidualScore6400 ^ 2 <
      cubicWorstWeight6400 * cubicWorstResidualMass6400 := by
  norm_num [cubicWorstWeightedCore6400, cubicWorstResidualMass6400,
    cubicWorstResidualScore6400, cubicWorstWeight6400]

end BCHKSWeightedSecantAudit6400
end ProximityPrize.SubmissionLower
