import ProximityPrize.SubmissionLower.CyclicFourIncidence

namespace ProximityPrize.SubmissionLower.CyclicFourRankBridge

open ProximityPrize.Benchmark
open CyclicFourFibre CyclicFourIncidence
open scoped BigOperators

set_option autoImplicit false

section AbstractRankSaving

variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W]

/-- A rank-saving interface for interpolation.  The usual argument bounds the
range by `localBudget`.  It is enough instead to save `saving` dimensions in
the actual global range, provided that the same saving closes the source gate. -/
theorem exists_nonzero_kernel_of_rank_saving
    (f : V →ₗ[K] W) (sourceRank localBudget saving : ℕ)
    (hsource : Module.finrank K V = sourceRank)
    (hsaved : Module.finrank K (LinearMap.range f) + saving ≤ localBudget)
    (hgate : localBudget < sourceRank + saving) :
    ∃ v : V, v ≠ 0 ∧ f v = 0 := by
  have hrange : Module.finrank K (LinearMap.range f) < sourceRank := by omega
  have hsum := f.finrank_range_add_finrank_ker
  rw [hsource] at hsum
  have hker : 0 < Module.finrank K (LinearMap.ker f) := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hker
  refine ⟨v.1, ?_, LinearMap.mem_ker.mp v.2⟩
  intro hz
  apply hv
  apply Subtype.ext
  exact hz

end AbstractRankSaving

/-! The exact 68.03 interpolation gates.  These constants are the dimensions
of the three source coefficient boxes and their old coordinatewise local-rank
budgets after lowering the weighted cutoffs to `m * 181363`. -/

def sourceRankA6803 : ℕ := 3627053099058455
def localBudgetA : ℕ := 3627373728890880
def requiredSavingA6803 : ℕ := 320629832426

def sourceRankB6803 : ℕ := 546926355561905
def localBudgetB : ℕ := 546993139875840
def requiredSavingB6803 : ℕ := 66784313936

def sourceRankT6803 : ℕ := 1179105412859268
def localBudgetT : ℕ := 1179249335599104
def requiredSavingT6803 : ℕ := 143922739837

def sourceRankC6803 : ℕ := 78049579997465428
def localBudgetC : ℕ := 77755877446385664

theorem rankGateA6803 :
    localBudgetA < sourceRankA6803 + requiredSavingA6803 := by
  norm_num [localBudgetA, sourceRankA6803, requiredSavingA6803]

theorem rankGateB6803 :
    localBudgetB < sourceRankB6803 + requiredSavingB6803 := by
  norm_num [localBudgetB, sourceRankB6803, requiredSavingB6803]

theorem rankGateT6803 :
    localBudgetT < sourceRankT6803 + requiredSavingT6803 := by
  norm_num [localBudgetT, sourceRankT6803, requiredSavingT6803]

/-- The fourth kernel already passes at 68.03 without a geometric rank saving. -/
theorem rankGateC6803 : localBudgetC < sourceRankC6803 := by
  norm_num [localBudgetC, sourceRankC6803]

/-! A sufficient per-excess-unit target.  These are ceilings of the three
required savings divided by the 50,291 excess agreements certified by
`bundleExcess_sum_ge_6803`. -/

def savingPerExcessA : ℕ := 6375492
def savingPerExcessB : ℕ := 1327958
def savingPerExcessT : ℕ := 2861800

theorem excess_covers_requiredSavingA (S : Finset IRSProfile.Index)
    (hS : 181363 ≤ S.card) :
    requiredSavingA6803 ≤
      savingPerExcessA * ∑ j : Fin quarterSize, bundleExcess S j := by
  calc
    requiredSavingA6803 ≤ savingPerExcessA * 50291 := by
      norm_num [requiredSavingA6803, savingPerExcessA]
    _ ≤ savingPerExcessA * ∑ j : Fin quarterSize, bundleExcess S j :=
      Nat.mul_le_mul_left savingPerExcessA (bundleExcess_sum_ge_6803 S hS)

theorem excess_covers_requiredSavingB (S : Finset IRSProfile.Index)
    (hS : 181363 ≤ S.card) :
    requiredSavingB6803 ≤
      savingPerExcessB * ∑ j : Fin quarterSize, bundleExcess S j := by
  calc
    requiredSavingB6803 ≤ savingPerExcessB * 50291 := by
      norm_num [requiredSavingB6803, savingPerExcessB]
    _ ≤ savingPerExcessB * ∑ j : Fin quarterSize, bundleExcess S j :=
      Nat.mul_le_mul_left savingPerExcessB (bundleExcess_sum_ge_6803 S hS)

theorem excess_covers_requiredSavingT (S : Finset IRSProfile.Index)
    (hS : 181363 ≤ S.card) :
    requiredSavingT6803 ≤
      savingPerExcessT * ∑ j : Fin quarterSize, bundleExcess S j := by
  calc
    requiredSavingT6803 ≤ savingPerExcessT * 50291 := by
      norm_num [requiredSavingT6803, savingPerExcessT]
    _ ≤ savingPerExcessT * ∑ j : Fin quarterSize, bundleExcess S j :=
      Nat.mul_le_mul_left savingPerExcessT (bundleExcess_sum_ge_6803 S hS)

end ProximityPrize.SubmissionLower.CyclicFourRankBridge
