import ProximityPrize.SubmissionLower.BCHKSCoreVandermonde6400
import ProximityPrize.SubmissionLower.BCHKSBoundaryCoreArrangement6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSCodimTupleCount6400

open scoped BigOperators
open BCHKSBoundaryCoreArrangement6400

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
The finite double count needed by the codimension-`s` core route.

For each challenge `z`, let `A z` be its off-core agreement coordinates in
the finite ambient set `U`.  If `|A z| >= r` and every fixed unordered
`t`-subset is contained in at most `e` of the `A z`, then

`|S| * (r)_t <= e * (|U|)_t`.

Counting unordered subsets is equivalent to counting ordered distinct
tuples: both sides are multiplied by `t!`.  The last two theorems specialize
the result to the exact codimension-24 parameters and aggregate over every
factor of degree at least 129.

The only application-specific hypothesis left here is `hfiber`.  The
Vandermonde file proves that one shared 25-set puts all owners in its fibre
on one affine polynomial line; the eventual assembly must combine that fact
with nonalignment to prove that such a fibre has at most 76780 challenges.
-/

/-- Swap the challenge and coordinate-subset sums. -/
theorem card_mul_choose_le_of_subsetFibers
    {I Challenge : Type*} [DecidableEq I] [DecidableEq Challenge]
    (U : Finset I) (S : Finset Challenge) (A : Challenge → Finset I)
    (r t e : ℕ)
    (hsub : ∀ z ∈ S, A z ⊆ U)
    (hrow : ∀ z ∈ S, r ≤ (A z).card)
    (hfiber : ∀ T ∈ U.powersetCard t,
      (S.filter fun z ↦ T ⊆ A z).card ≤ e) :
    S.card * r.choose t ≤ e * U.card.choose t := by
  classical
  have hlower : S.card * r.choose t ≤
      ∑ z ∈ S, (A z).card.choose t := by
    calc
      S.card * r.choose t = ∑ _z ∈ S, r.choose t := by simp
      _ ≤ ∑ z ∈ S, (A z).card.choose t := by
        apply Finset.sum_le_sum
        intro z hz
        exact Nat.choose_le_choose t (hrow z hz)
  have hswap : (∑ z ∈ S, (A z).card.choose t) =
      ∑ T ∈ U.powersetCard t,
        (S.filter fun z ↦ T ⊆ A z).card := by
    calc
      (∑ z ∈ S, (A z).card.choose t) =
          ∑ z ∈ S, ((A z).powersetCard t).card := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Finset.card_powersetCard]
      _ = ∑ z ∈ S, ∑ T ∈ U.powersetCard t,
          if T ⊆ A z then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Finset.card_filter]
        congr 1
        ext T
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor <;> grind [hsub z hz]
      _ = ∑ T ∈ U.powersetCard t, ∑ z ∈ S,
          if T ⊆ A z then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ T ∈ U.powersetCard t,
          (S.filter fun z ↦ T ⊆ A z).card := by
        apply Finset.sum_congr rfl
        intro T hT
        simp
  calc
    S.card * r.choose t ≤ ∑ z ∈ S, (A z).card.choose t := hlower
    _ = ∑ T ∈ U.powersetCard t,
        (S.filter fun z ↦ T ⊆ A z).card := hswap
    _ ≤ ∑ _T ∈ U.powersetCard t, e :=
      Finset.sum_le_sum hfiber
    _ = e * U.card.choose t := by
      simp [Finset.card_powersetCard, Nat.mul_comm]

/-- The falling-factorial form, equivalently the ordered-distinct-tuple
double count. -/
theorem card_mul_fallingFactorial_le_of_tupleFibers
    {I Challenge : Type*} [DecidableEq I] [DecidableEq Challenge]
    (U : Finset I) (S : Finset Challenge) (A : Challenge → Finset I)
    (r t e : ℕ)
    (hsub : ∀ z ∈ S, A z ⊆ U)
    (hrow : ∀ z ∈ S, r ≤ (A z).card)
    (hfiber : ∀ T ∈ U.powersetCard t,
      (S.filter fun z ↦ T ⊆ A z).card ≤ e) :
    S.card * fallingFactorial6400 r t ≤
      e * fallingFactorial6400 U.card t := by
  have hchoose :=
    card_mul_choose_le_of_subsetFibers U S A r t e hsub hrow hfiber
  have hfall (n : ℕ) :
      fallingFactorial6400 n t = t.factorial * n.choose t := by
    rw [fallingFactorial6400, ← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_eq_factorial_mul_choose]
  rw [hfall r, hfall U.card]
  calc
    S.card * (t.factorial * r.choose t) =
        t.factorial * (S.card * r.choose t) := by ring
    _ ≤ t.factorial * (e * U.card.choose t) :=
      Nat.mul_le_mul_left t.factorial hchoose
    _ = e * (t.factorial * U.card.choose t) := by ring

/-- Exact per-factor consequence at core codimension 24. -/
theorem card_le_codim24PerFactorCap_of_tupleFibers
    {I Challenge : Type*} [DecidableEq I] [DecidableEq Challenge]
    (U : Finset I) (S : Finset Challenge) (A : Challenge → Finset I)
    (hUcard : U.card = bchksBoundaryTupleAmbient6400)
    (hsub : ∀ z ∈ S, A z ⊆ U)
    (hrow : ∀ z ∈ S,
      bchksBoundaryTupleIncidences6400 ≤ (A z).card)
    (hfiber : ∀ T ∈ U.powersetCard bchksBoundaryTupleSize6400,
      (S.filter fun z ↦ T ⊆ A z).card ≤ bchksBoundaryErrors6400) :
    S.card ≤ bchksBoundaryCodim24PerFactorCap6400 := by
  have hcount := card_mul_fallingFactorial_le_of_tupleFibers
    U S A bchksBoundaryTupleIncidences6400
      bchksBoundaryTupleSize6400 bchksBoundaryErrors6400
      hsub hrow hfiber
  have hpos : 0 < fallingFactorial6400
      bchksBoundaryTupleIncidences6400 bchksBoundaryTupleSize6400 := by
    norm_num [fallingFactorial6400, bchksBoundaryTupleIncidences6400,
      bchksBoundaryTupleSize6400, Finset.prod_range_succ]
  have hcapacity := card_le_tupleCapacity
    S.card U.card bchksBoundaryTupleIncidences6400
      bchksBoundaryTupleSize6400 bchksBoundaryErrors6400 hpos hcount
  rw [hUcard] at hcapacity
  simpa only [bchksBoundary_codim24_tupleCapacity6400] using hcapacity

/-- Aggregating the exact tuple bound over all degree-at-least-129 factors
stays strictly below the available weighted challenge numerator. -/
theorem sum_ownerCard_lt_weightedNumerator_of_codim24_tupleFibers
    {R I Challenge : Type*} [DecidableEq R] [DecidableEq I]
      [DecidableEq Challenge]
    (Rs : Finset R) (degree : R → ℕ)
    (U : Finset I) (owner : R → Finset Challenge)
    (A : R → Challenge → Finset I)
    (hUcard : U.card = bchksBoundaryTupleAmbient6400)
    (hdegree : ∀ q ∈ Rs, 129 ≤ degree q)
    (hmass : (∑ q ∈ Rs, degree q) ≤ 84607)
    (hsub : ∀ q ∈ Rs, ∀ z ∈ owner q, A q z ⊆ U)
    (hrow : ∀ q ∈ Rs, ∀ z ∈ owner q,
      bchksBoundaryTupleIncidences6400 ≤ (A q z).card)
    (hfiber : ∀ q ∈ Rs,
      ∀ T ∈ U.powersetCard bchksBoundaryTupleSize6400,
        ((owner q).filter fun z ↦ T ⊆ A q z).card ≤
          bchksBoundaryErrors6400) :
    (∑ q ∈ Rs, (owner q).card) < bchksWeightedNumerator6400 := by
  have howner : ∀ q ∈ Rs,
      (owner q).card ≤ bchksBoundaryCodim24PerFactorCap6400 := by
    intro q hq
    exact card_le_codim24PerFactorCap_of_tupleFibers U (owner q) (A q)
      hUcard (hsub q hq) (hrow q hq) (hfiber q hq)
  have haggregate := aggregate_ownerCard_le_of_minDegree
    Rs degree (fun q ↦ (owner q).card) 129 84607
      bchksBoundaryCodim24PerFactorCap6400 (by norm_num)
      hdegree hmass howner
  have hnumeric :
      (84607 / 129) * bchksBoundaryCodim24PerFactorCap6400 <
        bchksWeightedNumerator6400 := by
    obtain ⟨hcount, hlt, hgap⟩ :=
      bchksBoundary_codim24_highFactorAggregate6400
    have hfactorCount : bchksBoundaryHighFactorCount6400 = 84607 / 129 :=
      bchksBoundary_exactCore_highFactorAggregate6400.1
    rw [← hfactorCount, ← hcount]
    exact hlt
  exact haggregate.trans_lt hnumeric

end BCHKSCodimTupleCount6400
end ProximityPrize.SubmissionLower
