import ProximityPrize.SubmissionLower.BCHKSExactSparsification6400
import ProximityPrize.SubmissionLower.BCHKSParameters6400

/-!
# The ten-level score-64 shell

The accepted score-63.99 alignment theorem controls every MCA-bad challenge
which already has `185374` agreements.  At score 64 the threshold is
`185364`.  This file records the exact set difference and its available
cardinality budget, without making any algebraic assumption about how the new
shell is eventually controlled.
-/

open scoped BigOperators Classical

noncomputable section

namespace ProximityPrize.SubmissionLower.BCHKSShellDecomposition6400

open BCHKSExactSparsification6400

set_option autoImplicit false

universe u v

variable {F : Type u} {D : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype D] [Nonempty D] [DecidableEq D]

local notation "Word" => D → F

/-- Raising the agreement threshold can only remove MCA-bad challenges. -/
theorem mcaBad_mono_threshold
    (C : Submodule F Word) (f₀ f₁ : Word) {a b : ℕ} (hab : a ≤ b)
    (z : F) :
    MCABad C f₀ f₁ b z → MCABad C f₀ f₁ a z := by
  rintro ⟨S, hS, hline, hpair⟩
  exact ⟨S, hab.trans hS, hline, hpair⟩

/-- The genuinely new challenges at score 64: bad at `185364`, but not
already bad at the accepted `185374` threshold. -/
def newShellSlopes (Gamma : Finset F) (C : Submodule F Word)
    (f₀ f₁ : Word) : Finset F :=
  restrictedMCABadSlopes Gamma C f₀ f₁ 185364 \
    restrictedMCABadSlopes Gamma C f₀ f₁ 185374

theorem oldBadSlopes_subset_newBadSlopes
    (Gamma : Finset F) (C : Submodule F Word) (f₀ f₁ : Word) :
    restrictedMCABadSlopes Gamma C f₀ f₁ 185374 ⊆
      restrictedMCABadSlopes Gamma C f₀ f₁ 185364 := by
  intro z hz
  simp only [restrictedMCABadSlopes, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, mcaBad_mono_threshold C f₀ f₁ (by omega) z hz.2⟩

theorem card_newShellSlopes
    (Gamma : Finset F) (C : Submodule F Word) (f₀ f₁ : Word) :
    (newShellSlopes Gamma C f₀ f₁).card =
      (restrictedMCABadSlopes Gamma C f₀ f₁ 185364).card -
        (restrictedMCABadSlopes Gamma C f₀ f₁ 185374).card := by
  exact Finset.card_sdiff_of_subset
    (oldBadSlopes_subset_newBadSlopes Gamma C f₀ f₁)

/-- Every member of the shell carries the two predicates used by the later
exact-error and locator arguments. -/
theorem mem_newShellSlopes_iff
    (Gamma : Finset F) (C : Submodule F Word) (f₀ f₁ : Word) (z : F) :
    z ∈ newShellSlopes Gamma C f₀ f₁ ↔
      z ∈ Gamma ∧ MCABad C f₀ f₁ 185364 z ∧
        ¬ MCABad C f₀ f₁ 185374 z := by
  simp only [newShellSlopes, restrictedMCABadSlopes,
    Finset.mem_sdiff, Finset.mem_filter]
  tauto

/-- A chosen witness for a shell challenge necessarily has one of the ten
cardinalities `185364, ..., 185373`.  Otherwise the same witness would make
the challenge old-bad. -/
theorem shell_witness_card_lt_old_threshold
    (C : Submodule F Word) (f₀ f₁ : Word) (z : F)
    (hnotOld : ¬ MCABad C f₀ f₁ 185374 z)
    (S : Finset D) (hS : 185364 ≤ S.card)
    (hline : Explained C (fun x ↦ f₀ x + z * f₁ x) S)
    (hpair : ¬ ExplainedPair C f₀ f₁ S) :
    185364 ≤ S.card ∧ S.card < 185374 := by
  refine ⟨hS, ?_⟩
  by_contra hnot
  apply hnotOld
  exact ⟨S, Nat.le_of_not_gt hnot, hline, hpair⟩

/-- Exact arithmetic behind the shell budget. -/
theorem score6400_shell_floor_arithmetic :
    ProximityPrize.SubmissionLower.bchksNumerator6400 + 1 -
        ProximityPrize.SubmissionLower.bchksNumerator6399 =
      174972148031419761 := by
  norm_num [ProximityPrize.SubmissionLower.bchksNumerator6400,
    ProximityPrize.SubmissionLower.bchksNumerator6399]

/-- Once the accepted theorem bounds the old set by its `10^17` numerator,
any violation of the proposed score-64 numerator leaves at least the stated
number of genuinely new challenges. -/
theorem score6400_shell_card_lower
    (Gamma : Finset F) (C : Submodule F Word) (f₀ f₁ : Word)
    (hnew : ProximityPrize.SubmissionLower.bchksNumerator6400 <
      (restrictedMCABadSlopes Gamma C f₀ f₁ 185364).card)
    (hold :
      (restrictedMCABadSlopes Gamma C f₀ f₁ 185374).card ≤
        ProximityPrize.SubmissionLower.bchksNumerator6399) :
    174972148031419761 ≤ (newShellSlopes Gamma C f₀ f₁).card := by
  rw [card_newShellSlopes]
  norm_num [ProximityPrize.SubmissionLower.bchksNumerator6400,
    ProximityPrize.SubmissionLower.bchksNumerator6399] at hnew hold ⊢
  omega

end ProximityPrize.SubmissionLower.BCHKSShellDecomposition6400
