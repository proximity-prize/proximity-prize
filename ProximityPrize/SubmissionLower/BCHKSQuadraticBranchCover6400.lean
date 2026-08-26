import ProximityPrize.SubmissionLower.BCHKSStableCoverAudit6400

namespace ProximityPrize.SubmissionLower

open scoped BigOperators

set_option maxRecDepth 100000

/-!
Exact arithmetic for a conditional two-global-branch extension of the stable
cover.  This file deliberately does not infer two global branches from
quadratic coordinate slices: coordinatewise choices can have exponentially
many sign patterns.  It only records that, if the missing algebraic theorem
produces one global bit per challenge, the counting budget is already ample.
-/

def bchksStableQuadraticCoverCap6400 : ℕ := 19161843228

/-- Sum over owner/branch fibres when every challenge has one of two global
branch labels. -/
theorem bchksStable_quadratic_branch_card_le6400
    {ζ γ : Type*} [DecidableEq ζ] [Fintype γ] [DecidableEq γ]
    (Branched : Finset ζ) (owner : ζ → γ) (branch : ζ → Fin 2)
    (hfactor : Fintype.card γ ≤ bchksStableFactorCount6400)
    (hfibre : ∀ q : γ, ∀ b : Fin 2,
      (Branched.filter fun z => owner z = q ∧ branch z = b).card ≤
        bchksStableFiberCap6400) :
    Branched.card ≤
      bchksStableFactorCount6400 * 2 * bchksStableFiberCap6400 := by
  let key : ζ → γ × Fin 2 := fun z => (owner z, branch z)
  have hpartition :=
    Finset.sum_card_fiberwise_eq_card_filter Branched Finset.univ key
  have hsum :
      (∑ qb : γ × Fin 2,
        (Branched.filter fun z => key z = qb).card) = Branched.card := by
    simpa using hpartition
  calc
    Branched.card = ∑ qb : γ × Fin 2,
        (Branched.filter fun z => key z = qb).card := hsum.symm
    _ ≤ ∑ _qb : γ × Fin 2, bchksStableFiberCap6400 := by
      apply Finset.sum_le_sum
      intro qb _hqb
      rcases qb with ⟨q, b⟩
      simpa [key] using hfibre q b
    _ = Fintype.card (γ × Fin 2) * bchksStableFiberCap6400 := by simp
    _ = Fintype.card γ * 2 * bchksStableFiberCap6400 := by simp
    _ ≤ bchksStableFactorCount6400 * 2 * bchksStableFiberCap6400 := by
      simpa [Nat.mul_assoc] using
        Nat.mul_le_mul_right (2 * bchksStableFiberCap6400) hfactor

lemma bchksStableQuadraticCoverCap_eq6400 :
    bchksStableQuadraticCoverCap6400 =
      bchksStableFactorCount6400 * 2 * bchksStableFiberCap6400 +
        bchksStableChargedChallengeCap6400 := by
  norm_num [bchksStableQuadraticCoverCap6400,
    bchksStableFactorCount6400, bchksStableFiberCap6400,
    bchksStableChargedChallengeCap6400]

/-- Conditional quadratic stable-cover finish.  The nonbranch charge is
identical to the pure-cover theorem; only the fibre term is doubled. -/
theorem bchksStable_card_le_of_quadratic_branch_nonroot_cover6400
    {ζ ι γ : Type*}
    [DecidableEq ζ] [DecidableEq ι] [Fintype γ] [DecidableEq γ]
    (S Branched : Finset ζ) (A : ζ → Finset ι) (B : γ → Finset ι)
    (owner : ζ → γ) (branch : ζ → Fin 2)
    (hBranched : Branched ⊆ S)
    (hfactor : Fintype.card γ ≤ bchksStableFactorCount6400)
    (hfibre : ∀ q : γ, ∀ b : Fin 2,
      (Branched.filter fun z => owner z = q ∧ branch z = b).card ≤
        bchksStableFiberCap6400)
    (hA : ∀ z ∈ S, 185364 ≤ (A z).card)
    (hsmall : ∀ z ∈ S \ Branched, (B (owner z)).card < 131072)
    (hrootMass :
      (∑ z ∈ S \ Branched, (A z \ B (owner z)).card) ≤
        262144 * bchksStableRootMass6400) :
    S.card ≤ bchksStableQuadraticCoverCap6400 := by
  have hbranchCap :
      Branched.card ≤
        bchksStableFactorCount6400 * 2 * bchksStableFiberCap6400 :=
    bchksStable_quadratic_branch_card_le6400
      Branched owner branch hfactor hfibre
  have hrow : ∀ z ∈ S \ Branched,
      bchksStableChargeGap6400 ≤ (A z \ B (owner z)).card := by
    intro z hz
    exact bchksStable_sdiff_card_ge_gap6400 (A z) (B (owner z))
      (hA z (Finset.mem_sdiff.mp hz).1) (hsmall z hz)
  have hchargeLower :
      (S \ Branched).card * bchksStableChargeGap6400 ≤
        ∑ z ∈ S \ Branched, (A z \ B (owner z)).card := by
    calc
      (S \ Branched).card * bchksStableChargeGap6400 =
          ∑ _z ∈ S \ Branched, bchksStableChargeGap6400 := by simp
      _ ≤ ∑ z ∈ S \ Branched, (A z \ B (owner z)).card :=
        Finset.sum_le_sum hrow
  have hcharged :
      (S \ Branched).card ≤ bchksStableChargedChallengeCap6400 := by
    norm_num [bchksStableChargeGap6400, bchksStableRootMass6400,
      bchksStableChargedChallengeCap6400] at hchargeLower hrootMass ⊢
    omega
  have hsplit := Finset.card_sdiff_add_card_eq_card hBranched
  rw [bchksStableQuadraticCoverCap_eq6400]
  omega

lemma bchksStableQuadraticCoverCap_lt_numerator6400 :
    bchksStableQuadraticCoverCap6400 < bchksNumerator6400 := by
  norm_num [bchksStableQuadraticCoverCap6400, bchksNumerator6400]

lemma bchksStableQuadraticCoverFieldBudget6400 :
    2 ^ (128 : ℕ) *
        (bchksStableQuadraticCoverCap6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksStableQuadraticCoverCap6400, bchksListBound6400]

end ProximityPrize.SubmissionLower
