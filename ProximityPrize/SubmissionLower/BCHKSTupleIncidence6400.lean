import ProximityPrize.SubmissionLower.BCHKSCoreVandermonde6400
import ProximityPrize.SubmissionLower.BCHKSBoundaryCoreArrangement6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSTupleIncidence6400

open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
The exact double count for the codimension-`s` core route.

Each challenge supplies at least `r.choose t` coordinate tuples.  If every
fixed tuple belongs to at most `e` challenges, swapping the two finite sums
gives `|S| * choose r t <= e * choose N t`.  Unlike the earlier arithmetic
audit, this theorem constructs and counts the incidence set itself.
-/

theorem card_mul_choose_le_of_tupleFibers
    {Ι Ζ : Type*} [Fintype Ι] [DecidableEq Ι] [DecidableEq Ζ]
    (U : Finset Ι) (S : Finset Ζ) (A : Ζ → Finset Ι)
    (r t e : ℕ)
    (hsub : ∀ z ∈ S, A z ⊆ U)
    (hrow : ∀ z ∈ S, r ≤ (A z).card)
    (hfiber : ∀ B ∈ U.powersetCard t,
      (S.filter fun z ↦ B ⊆ A z).card ≤ e) :
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
  have hincidence : (∑ z ∈ S, (A z).card.choose t) =
      ∑ B ∈ U.powersetCard t,
        (S.filter fun z ↦ B ⊆ A z).card := by
    calc
      (∑ z ∈ S, (A z).card.choose t) =
          ∑ z ∈ S, ((A z).powersetCard t).card := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Finset.card_powersetCard]
      _ = ∑ z ∈ S, ∑ B ∈ U.powersetCard t,
          if B ⊆ A z then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Finset.card_filter]
        congr 1
        ext B
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor <;> grind [hsub z hz]
      _ = ∑ B ∈ U.powersetCard t, ∑ z ∈ S,
          if B ⊆ A z then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ B ∈ U.powersetCard t,
          (S.filter fun z ↦ B ⊆ A z).card := by
        apply Finset.sum_congr rfl
        intro B hB
        simp
  calc
    S.card * r.choose t ≤ ∑ z ∈ S, (A z).card.choose t := hlower
    _ = ∑ B ∈ U.powersetCard t,
        (S.filter fun z ↦ B ⊆ A z).card := hincidence
    _ ≤ ∑ _B ∈ U.powersetCard t, e := by
      exact Finset.sum_le_sum hfiber
    _ = e * U.card.choose t := by
      simp [Finset.card_powersetCard, Nat.mul_comm]

/-- Division-free form matching the falling-factorial arithmetic helper. -/
lemma fallingFactorial_eq_factorial_mul_choose (n t : ℕ) :
    BCHKSBoundaryCoreArrangement6400.fallingFactorial6400 n t =
      t.factorial * n.choose t := by
  rw [BCHKSBoundaryCoreArrangement6400.fallingFactorial6400,
    ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose]

theorem card_mul_fallingFactorial_le_of_tupleFibers
    {Ι Ζ : Type*} [Fintype Ι] [DecidableEq Ι] [DecidableEq Ζ]
    (U : Finset Ι) (S : Finset Ζ) (A : Ζ → Finset Ι)
    (r t e : ℕ)
    (hsub : ∀ z ∈ S, A z ⊆ U)
    (hrow : ∀ z ∈ S, r ≤ (A z).card)
    (hfiber : ∀ B ∈ U.powersetCard t,
      (S.filter fun z ↦ B ⊆ A z).card ≤ e) :
    S.card * BCHKSBoundaryCoreArrangement6400.fallingFactorial6400 r t ≤
      e * BCHKSBoundaryCoreArrangement6400.fallingFactorial6400 U.card t := by
  have h := card_mul_choose_le_of_tupleFibers U S A r t e hsub hrow hfiber
  rw [fallingFactorial_eq_factorial_mul_choose,
    fallingFactorial_eq_factorial_mul_choose]
  calc
    S.card * (t.factorial * r.choose t) =
        t.factorial * (S.card * r.choose t) := by ring
    _ ≤ t.factorial * (e * U.card.choose t) :=
      Nat.mul_le_mul_left t.factorial h
    _ = e * (t.factorial * U.card.choose t) := by ring

end BCHKSTupleIncidence6400
end ProximityPrize.SubmissionLower
