import ProximityPrize.SubmissionLower.BCHKSMixedJetAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSMixedJetRankBridge6400

open Polynomial

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
Core rank facts for the unrestricted-Gao mixed-jet lane.

The first theorem is the reusable block-triangular step.  Apply it from low
`Y` layer to high `Y` layer: restriction to a pure layer kills every higher
mixed derivative row, and the surviving diagonal block is an ordinary
confluent Hermite family in `X`.
-/

/-- Two-block triangular linear independence.  The map `L` is restriction
to the current pure `Y` layer.  The current block stays independent after
restriction, while every later block restricts to zero. -/
theorem linearIndependent_sum_of_triangular_restriction
    {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    {I J : Type*} [Fintype I] [Fintype J]
    (current : I → M) (later : J → M) (L : M →ₗ[K] N)
    (hcurrent : LinearIndependent K (fun i ↦ L (current i)))
    (hlater : LinearIndependent K later)
    (hzero : ∀ j, L (later j) = 0) :
    LinearIndependent K (Sum.elim current later) := by
  classical
  rw [Fintype.linearIndependent_iff] at hcurrent hlater ⊢
  intro c hrelation
  have hmapped := congrArg L hrelation
  have hcurrentRelation :
      (∑ i : I, c (Sum.inl i) • L (current i)) = 0 := by
    simpa [Fintype.sum_sum_type, hzero] using hmapped
  have hcCurrent : ∀ i, c (Sum.inl i) = 0 :=
    hcurrent (fun i ↦ c (Sum.inl i)) hcurrentRelation
  have hlaterRelation :
      (∑ j : J, c (Sum.inr j) • later j) = 0 := by
    simpa [Fintype.sum_sum_type, hcCurrent] using hrelation
  have hcLater : ∀ j, c (Sum.inr j) = 0 :=
    hlater (fun j ↦ c (Sum.inr j)) hlaterRelation
  intro ij
  cases ij with
  | inl i => exact hcCurrent i
  | inr j => exact hcLater j

/-- Hasse mixed jet at `(omega,u)`.  This is the coefficient extracted after
translating by that point, but unlike ordinary iterated derivatives it has
diagonal scalar one in every characteristic. -/
noncomputable def mixedHasseJet
    {K : Type*} [Field K] (omega u : K) (s b : ℕ)
    (T : Polynomial (Polynomial K)) : K :=
  Polynomial.eval omega
    (Polynomial.hasseDeriv s
      (Polynomial.eval (Polynomial.C u) (Polynomial.hasseDeriv b T)))

/-- On the matching pure `Y^b` layer, a mixed jet is exactly the usual
univariate Hasse-Hermite functional in `X`; the received value `u` drops
out of the diagonal block. -/
theorem mixedHasseJet_pureLayer_same
    {K : Type*} [Field K] (omega u : K) (s b : ℕ)
    (A : Polynomial K) :
    mixedHasseJet omega u s b (Polynomial.monomial b A) =
      Polynomial.eval omega (Polynomial.hasseDeriv s A) := by
  simp [mixedHasseJet, Polynomial.hasseDeriv_monomial]

/-- A derivative row from a strictly higher `Y` layer kills a pure lower
layer.  Together with `mixedHasseJet_pureLayer_same`, this is the exact
block-triangular pattern used by the preceding theorem. -/
theorem mixedHasseJet_pureLayer_higher_zero
    {K : Type*} [Field K] (omega u : K) (s b c : ℕ)
    (A : Polynomial K) (hbc : b < c) :
    mixedHasseJet omega u s c (Polynomial.monomial b A) = 0 := by
  simp [mixedHasseJet, Polynomial.hasseDeriv_monomial,
    Nat.choose_eq_zero_of_lt hbc]

/-- Factor-aggregate degree ledger for the cheap mixed-jet rows.  The rows
are factor-specific, so their `Z`-degree cost must be summed over owners;
it is not sound to charge the endpoint cost only once. -/
theorem aggregate_two_mul_jetRank_mul_degree_le
    {I : Type*} [DecidableEq I]
    (S : Finset I) (jetRank degree : I → ℕ) (Tmax DY : ℕ)
    (hjet : ∀ i ∈ S, jetRank i ≤ Tmax)
    (hdegreeMass : (∑ i ∈ S, degree i) ≤ DY) :
    (∑ i ∈ S, 2 * jetRank i * degree i) ≤ 2 * Tmax * DY := by
  calc
    (∑ i ∈ S, 2 * jetRank i * degree i) ≤
        ∑ i ∈ S, 2 * Tmax * degree i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_right (degree i)
        (Nat.mul_le_mul_left 2 (hjet i hi))
    _ = 2 * Tmax * (∑ i ∈ S, degree i) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * Tmax * DY := Nat.mul_le_mul_left _ hdegreeMass

def bchksMixed52JetRankOneComponent6400 : ℕ := 243023721
def bchksMixed52FactorDegreeMass6400 : ℕ := 84607
def bchksMixed52AggregateCheapCover6400 : ℕ := 41123015925294

lemma bchksMixed52_aggregateCheapCover_exact6400 :
    bchksMixed52AggregateCheapCover6400 =
      2 * bchksMixed52JetRankOneComponent6400 *
        bchksMixed52FactorDegreeMass6400 := by
  norm_num [bchksMixed52AggregateCheapCover6400,
    bchksMixed52JetRankOneComponent6400,
    bchksMixed52FactorDegreeMass6400]

/-- Benchmark specialization of the factor-aggregate ledger. -/
theorem bchksMixed52_aggregateCheapCover_le6400
    {I : Type*} [DecidableEq I]
    (S : Finset I) (jetRank degree : I → ℕ)
    (hjet : ∀ i ∈ S,
      jetRank i ≤ bchksMixed52JetRankOneComponent6400)
    (hmass : (∑ i ∈ S, degree i) ≤
      bchksMixed52FactorDegreeMass6400) :
    (∑ i ∈ S, 2 * jetRank i * degree i) ≤
      bchksMixed52AggregateCheapCover6400 := by
  rw [bchksMixed52_aggregateCheapCover_exact6400]
  exact aggregate_two_mul_jetRank_mul_degree_le S jetRank degree
    bchksMixed52JetRankOneComponent6400
    bchksMixed52FactorDegreeMass6400 hjet hmass

def bchksMixed52Weight6400 : ℕ := 9584634
def bchksMixed52LatticePoints6400 : ℕ := 327369817
def bchksMixed52UnrestrictedColumns6400 : ℕ := 645154946
def bchksMixed52ExpensiveRows6400 : ℕ := 159107504
def bchksMixed52ExpensiveCover6400 : ℕ := 268728664666411712
def bchksMixed52MinorCover6400 : ℕ := 268769787682337006
def bchksMixed52TotalCover6400 : ℕ := 269276963357709414

/-! Exact unrestricted-source endpoint.  `UnrestrictedColumns` is
`2|P∩Z²|-bottom-left edges`; its generic Gao rank is one less.  The
conservative expensive-row count keeps one full `DZ-1` block for the
normalization row, hence it is `columns-2T`, not `rank-2T`. -/
lemma bchksMixed52_exactLedger6400 :
    bchksMixed52Weight6400 = 52 * 185364 - 54293 - 1 ∧
      bchksMixed52LatticePoints6400 =
        (52 + 1) * (bchksMixed52Weight6400 + 1) -
          131071 * 52 * (52 + 1) / 2 ∧
      bchksMixed52UnrestrictedColumns6400 =
        2 * bchksMixed52LatticePoints6400 -
          (bchksMixed52Weight6400 + 1) - (52 + 1) ∧
      bchksMixed52JetRankOneComponent6400 =
        185364 * (52 * 51 / 2) - 54293 * 51 ∧
      bchksMixed52ExpensiveRows6400 =
        bchksMixed52UnrestrictedColumns6400 -
          2 * bchksMixed52JetRankOneComponent6400 ∧
      bchksMixed52ExpensiveCover6400 =
        bchksMixed52ExpensiveRows6400 *
          (bchksCofactorZCap6400 - 1) ∧
      bchksMixed52MinorCover6400 =
        bchksMixed52ExpensiveCover6400 +
          bchksMixed52AggregateCheapCover6400 ∧
      bchksMixed52TotalCover6400 =
        bchksMixed52MinorCover6400 +
          BCHKSAugmentedSparseAudit6400.bchksAugmentedPureRadicalCover6400 +
          BCHKSAugmentedSparseAudit6400.bchksAugmentedFullCoreBadCover6400 ∧
      bchksMixed52TotalCover6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksMixed52TotalCover6400 =
        5702036642290586 ∧
      (2 * 52 - 1) * bchksMixed52Weight6400 < 2130706433 := by
  norm_num [bchksMixed52Weight6400, bchksMixed52LatticePoints6400,
    bchksMixed52UnrestrictedColumns6400,
    bchksMixed52JetRankOneComponent6400,
    bchksMixed52ExpensiveRows6400, bchksMixed52ExpensiveCover6400,
    bchksMixed52AggregateCheapCover6400, bchksMixed52MinorCover6400,
    bchksMixed52TotalCover6400, bchksCofactorZCap6400,
    BCHKSAugmentedSparseAudit6400.bchksAugmentedPureRadicalCover6400,
    BCHKSAugmentedSparseAudit6400.bchksAugmentedFullCoreBadCover6400,
    bchksWeightedNumerator6400]

/-!
The global order constraints alone do not improve the degree-53 endpoint.
Here is the exact numerical obstruction.  Give the prospective degree-53
owner order 53 on 131071 coordinates of its agreement row, order 52 on the
remaining 54293 coordinates, and order zero off that row.  A second,
zero-`Z`-degree carrier of `Y`-degree 59826 can supply the complementary
order at every coordinate.  The carrier may have enormous convex jet mass,
but its Gao matrix is constant in `Z`, so that mass cannot lower the
`Z`-degree charged to the owner.  Notice that this obstruction does not use
factor multiplicities: both abstract factors can have exponent one.

Thus a degree-53 improvement needs an additional structural statement tying
order mass to the same factor's positive `Z`-degree (or an alignment theorem
that rules out this carrier); Jensen/convexity plus the displayed global
support budgets is insufficient.
-/
def bchksMixed53OwnerWeight6400 : ℕ := 9769998
def bchksMixed53CarrierDegree6400 : ℕ := 59826
def bchksMixed53CarrierWeight6400 : ℕ := 7841453646
def bchksMixed53OwnerJetRank6400 : ℕ := 252608356

lemma bchksMixed53_aggregateOrderCounterprofile6400 :
    131071 + 54293 = 185364 ∧
      bchksMixed53OwnerJetRank6400 =
        131071 * (53 * 52 / 2) + 54293 * (52 * 51 / 2) ∧
      bchksMixed53OwnerJetRank6400 =
        185364 * (53 * 52 / 2) - 54293 * 52 ∧
      53 + (bchksMixed53CarrierDegree6400 - 53) = 59826 ∧
      52 + (bchksMixed53CarrierDegree6400 - 52) = 59826 ∧
      0 + bchksMixed53CarrierDegree6400 = 59826 ∧
      53 + bchksMixed53CarrierDegree6400 ≤
        bchksCofactorYCap6400 - 1 ∧
      bchksMixed53CarrierWeight6400 =
        131071 * bchksMixed53CarrierDegree6400 ∧
      bchksMixed53OwnerWeight6400 +
          bchksMixed53CarrierWeight6400 ≤ bchksCofactorXCap6400 ∧
      (bchksCofactorZCap6400 - 1) + 0 ≤
        bchksCofactorZCap6400 - 1 := by
  norm_num [bchksMixed53OwnerWeight6400,
    bchksMixed53CarrierDegree6400, bchksMixed53CarrierWeight6400,
    bchksMixed53OwnerJetRank6400, bchksCofactorYCap6400,
    bchksCofactorXCap6400, bchksCofactorZCap6400]

end BCHKSMixedJetRankBridge6400
end ProximityPrize.SubmissionLower
