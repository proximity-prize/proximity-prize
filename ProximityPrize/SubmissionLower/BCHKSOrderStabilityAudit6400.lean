import ProximityPrize.SubmissionLower.BCHKSUnrestrictedMixedJetAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSOrderStabilityAudit6400

open Polynomial

/-!
Order-stability cover for the unrestricted mixed-jet lane.

The mixed rows used in a fixed Gao minor must come from the generic local
orders of a factor at the received coordinate lines.  The owner cofactor
argument initially sees the possibly larger local orders after specializing
`Z=z`.  For every factor-coordinate pair, choose one nonzero coefficient on
the first nonzero diagonal of the generically shifted factor.  A strict
increase of local order at `z` forces that witness coefficient to vanish at
`z`.

If a factor has `Z`-degree `e` and `Y`-degree `d`, shifting `Y` by the
received affine value increases the witness's `Z`-degree by at most `d`.
Consequently all order jumps cost at most

`n * (sumFactorZDegree + sumFactorYDegree)`.

This is an ordinary nonzero-polynomial root cover.  It requires neither the
pure-slice hypothesis nor the conditional stable-cover theorem.
-/

/-- Union of the roots of one order witness for every factor-coordinate
pair. -/
noncomputable def orderWitnessBadValues
    {F R I : Type*} [Field F] [DecidableEq F]
    (Rs : Finset R) (coords : Finset I)
    (witness : R → I → Polynomial F) : Finset F :=
  (Rs ×ˢ coords).biUnion fun ri ↦
    (witness ri.1 ri.2).roots.toFinset

/-- The order-jump cover costs at most the sum of the witness degrees. -/
theorem orderWitnessBadValues_card_le_sum_natDegree
    {F R I : Type*} [Field F] [DecidableEq F]
    [DecidableEq R] [DecidableEq I]
    (Rs : Finset R) (coords : Finset I)
    (witness : R → I → Polynomial F)
    (hne : ∀ r ∈ Rs, ∀ i ∈ coords, witness r i ≠ 0) :
    (orderWitnessBadValues Rs coords witness).card ≤
      ∑ r ∈ Rs, ∑ i ∈ coords, (witness r i).natDegree := by
  classical
  calc
    (orderWitnessBadValues Rs coords witness).card ≤
        ∑ ri ∈ Rs ×ˢ coords,
          (witness ri.1 ri.2).roots.toFinset.card := by
      unfold orderWitnessBadValues
      exact Finset.card_biUnion_le
    _ ≤ ∑ ri ∈ Rs ×ˢ coords,
          (witness ri.1 ri.2).roots.card := by
      apply Finset.sum_le_sum
      intro ri hri
      exact Multiset.toFinset_card_le _
    _ ≤ ∑ ri ∈ Rs ×ˢ coords,
          (witness ri.1 ri.2).natDegree := by
      apply Finset.sum_le_sum
      intro ri hri
      exact Polynomial.card_roots' _
    _ = ∑ r ∈ Rs, ∑ i ∈ coords,
          (witness r i).natDegree := by
      rw [Finset.sum_product]

/-- Outside the cover, every selected lowest-order coefficient survives. -/
theorem orderWitness_eval_ne_zero_of_not_mem
    {F R I : Type*} [Field F] [DecidableEq F]
    [DecidableEq R] [DecidableEq I]
    (Rs : Finset R) (coords : Finset I)
    (witness : R → I → Polynomial F)
    (hne : ∀ r ∈ Rs, ∀ i ∈ coords, witness r i ≠ 0)
    {z : F} (hz : z ∉ orderWitnessBadValues Rs coords witness) :
    ∀ r ∈ Rs, ∀ i ∈ coords,
      Polynomial.eval z (witness r i) ≠ 0 := by
  intro r hr i hi heval
  apply hz
  unfold orderWitnessBadValues
  rw [Finset.mem_biUnion]
  refine ⟨(r, i), Finset.mem_product.mpr ⟨hr, hi⟩, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hne r hr i hi)]
  exact heval

/-- Abstract coefficient-level form of local-order stability.  The actual
application takes `coeff s t` to be the `(X-ω)^s(Y-U)^t` coefficient of
the shifted factor. -/
theorem localOrderProfile_stable_of_witness_eval_ne_zero
    {F : Type*} [Field F]
    (coeff : ℕ → ℕ → Polynomial F) (z : F)
    (nu s₀ t₀ : ℕ)
    (hlow : ∀ s t, s + t < nu → coeff s t = 0)
    (hdiag : s₀ + t₀ = nu)
    (hwitness : Polynomial.eval z (coeff s₀ t₀) ≠ 0) :
    (∀ s t, s + t < nu → Polynomial.eval z (coeff s t) = 0) ∧
      ∃ s t, s + t = nu ∧ Polynomial.eval z (coeff s t) ≠ 0 := by
  constructor
  · intro s t hst
    rw [hlow s t hst]
    simp
  · exact ⟨s₀, t₀, hdiag, hwitness⟩

/-- Generic aggregate ledger: one witness of degree at most `zDegree r +
yDegree r` for each of at most `n` coordinates. -/
theorem orderWitnessBadValues_card_le_aggregate
    {F R I : Type*} [Field F] [DecidableEq F]
    [DecidableEq R] [DecidableEq I]
    (Rs : Finset R) (coords : Finset I)
    (witness : R → I → Polynomial F)
    (zDegree yDegree : R → ℕ) (n zCap yCap : ℕ)
    (hne : ∀ r ∈ Rs, ∀ i ∈ coords, witness r i ≠ 0)
    (hdegree : ∀ r ∈ Rs, ∀ i ∈ coords,
      (witness r i).natDegree ≤ zDegree r + yDegree r)
    (hcoords : coords.card ≤ n)
    (hzMass : (∑ r ∈ Rs, zDegree r) ≤ zCap)
    (hyMass : (∑ r ∈ Rs, yDegree r) ≤ yCap) :
    (orderWitnessBadValues Rs coords witness).card ≤
      n * (zCap + yCap) := by
  have hroot := orderWitnessBadValues_card_le_sum_natDegree
    Rs coords witness hne
  calc
    (orderWitnessBadValues Rs coords witness).card ≤
        ∑ r ∈ Rs, ∑ i ∈ coords,
          (witness r i).natDegree := hroot
    _ ≤ ∑ r ∈ Rs, ∑ _i ∈ coords,
          (zDegree r + yDegree r) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro i hi
      exact hdegree r hr i hi
    _ = ∑ r ∈ Rs, coords.card * (zDegree r + yDegree r) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_const_nat (fun _i _hi ↦ rfl)
    _ = coords.card * ∑ r ∈ Rs, (zDegree r + yDegree r) := by
      rw [Finset.mul_sum]
    _ = coords.card *
        ((∑ r ∈ Rs, zDegree r) + ∑ r ∈ Rs, yDegree r) := by
      rw [Finset.sum_add_distrib]
    _ ≤ n * (zCap + yCap) := by
      apply Nat.mul_le_mul hcoords
      exact Nat.add_le_add hzMass hyMass

def bchksOrderStabilityCover6400 : ℕ := 442776953815040
def bchksUnrestrictedStableTotalCover6400 : ℕ := 269719740311524454

lemma bchksOrderStabilityCover_exact6400 :
    bchksOrderStabilityCover6400 =
      262144 *
        ((BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedZCap6400 - 1) +
          (BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedYCap6400 - 1)) := by
  norm_num [bchksOrderStabilityCover6400,
    BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedZCap6400,
    BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedYCap6400]

lemma bchksUnrestrictedStableTotalCover_exact6400 :
    bchksUnrestrictedStableTotalCover6400 =
      BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedTotalCover6400 +
        bchksOrderStabilityCover6400 := by
  norm_num [bchksUnrestrictedStableTotalCover6400,
    BCHKSUnrestrictedMixedJetAudit6400.bchksUnrestrictedTotalCover6400,
    bchksOrderStabilityCover6400]

lemma bchksUnrestrictedStable_fieldBudget6400 :
    bchksUnrestrictedStableTotalCover6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksUnrestrictedStableTotalCover6400 =
        5259259688475546 ∧
      2 ^ (128 : ℕ) *
          (bchksUnrestrictedStableTotalCover6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksUnrestrictedStableTotalCover6400,
    bchksWeightedNumerator6400, bchksListBound6400]

end BCHKSOrderStabilityAudit6400
end ProximityPrize.SubmissionLower
