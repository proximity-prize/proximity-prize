import ProximityPrize.SubmissionLower.BCHKSDeepHigherDegreeAudit6400
import ProximityPrize.SubmissionLower.BCHKSWeightedSubstitution
namespace ProximityPrize.SubmissionLower
namespace BCHKSWeightedSecantAudit6400
open BCHKSWeightedSubstitution
theorem irreducible_eval_ne_zero_of_two_le_natDegree
    {K : Type*} [Field K] (R : Polynomial K) (p : K)
    (hirr : Irreducible R) (hdeg : 2 <= R.natDegree) :
    R.eval p ≠ 0 := by
  intro hroot
  exact hirr.not_isRoot_of_natDegree_ne_one (by omega) hroot
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
theorem weightedJohnson_scalar
    (L W s w : Real) (hL : 0 < L)
    (hcauchy : (L * s) ^ 2 <=
      W * (L * s + L * (L - 1) * w)) :
    L * (s ^ 2 - W * w) <= W * (s - w) := by
  nlinarith [sq_nonneg (L * s)]
theorem weightedJohnson_card_bound
    (L W s w B : Real) (hL : 0 < L)
    (hcauchy : (L * s) ^ 2 <=
      W * (L * s + L * (L - 1) * w))
    (hden : 0 < s ^ 2 - W * w)
    (hB : W * (s - w) <= B * (s ^ 2 - W * w)) :
    L <= B := by
  have hmain := weightedJohnson_scalar L W s w hL hcauchy
  nlinarith
theorem cubic_fullMultiplicity_core_lower
    (b1 b2 b3 b t : Nat)
    (hb : b1 + b2 + b3 = b)
    (ht : b2 + 2 * b3 = t) :
    t - b <= b3 := by
  omega
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
