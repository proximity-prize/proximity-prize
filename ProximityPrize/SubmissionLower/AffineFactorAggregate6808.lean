import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! A finite max-plus receipt carries affine single-factor bounds to an entire
factor family. No convexity or monotonicity of the single-factor cost is assumed.
The theorem has no mathematical source assumptions beyond its explicit inputs. -/
namespace ProximityPrize.SubmissionLower.AffineFactorAggregate6808
open scoped BigOperators
set_option autoImplicit false

/-- Each row absorbs one factor into the remaining coordinate budgets. -/
def BellmanRows (Rcap Ycap : ℕ) (b B : ℕ → ℕ → ℕ) : Prop :=
  ∀ r v R V, 1 ≤ r → r + R ≤ Rcap → r + v + R + V ≤ Ycap →
    b r v + B R V ≤ B (r + R) (v + V)

theorem sum_intercepts_le {ι : Type*} [DecidableEq ι]
    (Rcap Ycap : ℕ) (b B : ℕ → ℕ → ℕ)
    (hrows : BellmanRows Rcap Ycap b B)
    (s : Finset ι) (r v : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i)
    (hR : (∑ i ∈ s, r i) ≤ Rcap)
    (hY : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ Ycap) :
    (∑ i ∈ s, b (r i) (v i)) ≤ B (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hRi : r a + (∑ i ∈ s, r i) ≤ Rcap := by
      simpa only [Finset.sum_insert ha] using hR
    have hYi : (r a + ∑ i ∈ s, r i) + (v a + ∑ i ∈ s, v i) ≤ Ycap := by
      simpa only [Finset.sum_insert ha] using hY
    have hrec := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
      (by omega) (by omega)
    have hrow := hrows (r a) (v a) (∑ i ∈ s, r i) (∑ i ∈ s, v i)
      (hr a (Finset.mem_insert_self a s)) hRi (by omega)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Nat.add_le_add_left hrec _).trans hrow

/-- Single-factor affine receipts imply a bound for every finite factor family. -/
theorem sum_count_le {ι : Type*} [DecidableEq ι]
    (Rcap Ycap slope : ℕ) (b B : ℕ → ℕ → ℕ)
    (hrows : BellmanRows Rcap Ycap b B)
    (s : Finset ι) (r v z count : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i)
    (hR : (∑ i ∈ s, r i) ≤ Rcap)
    (hY : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ Ycap)
    (hcost : ∀ i ∈ s, count i ≤ slope * z i + b (r i) (v i)) :
    (∑ i ∈ s, count i) ≤ slope * (∑ i ∈ s, z i) +
      B (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  calc
    (∑ i ∈ s, count i) ≤ ∑ i ∈ s, (slope * z i + b (r i) (v i)) :=
      Finset.sum_le_sum hcost
    _ = slope * (∑ i ∈ s, z i) + ∑ i ∈ s, b (r i) (v i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := Nat.add_le_add_left (sum_intercepts_le Rcap Ycap b B hrows s r v hr hR hY) _

/-- A finite collection of proved aggregate bounds may be combined pointwise. -/
theorem combine_bounds {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (count : ι → ℕ) (choices : Finset κ)
    (cost : κ → ℕ) (bound : ℕ)
    (hcost : ∀ k ∈ choices, (∑ i ∈ s, count i) ≤ cost k)
    (hchoice : ∃ k ∈ choices, cost k ≤ bound) :
    (∑ i ∈ s, count i) ≤ bound := by
  obtain ⟨k, hk, hle⟩ := hchoice
  exact (hcost k hk).trans hle

/-- A coordinatewise monotone rate produces superadditive total intercepts. -/
theorem rate_bellman (Rcap Ycap : ℕ) (rate : ℕ → ℕ → ℕ)
    (hmono : ∀ r v R V, r ≤ R → v ≤ V → R ≤ Rcap → R + V ≤ Ycap →
      rate r v ≤ rate R V) :
    BellmanRows Rcap Ycap (fun r v => r * rate r v) (fun r v => r * rate r v) := by
  intro r v R V hr hR hY
  have h1 := hmono r v (r+R) (v+V) (by omega) (by omega) hR (by omega)
  have h2 := hmono R V (r+R) (v+V) (by omega) (by omega) hR (by omega)
  calc
    r * rate r v + R * rate R V ≤ r * rate (r+R) (v+V) + R * rate (r+R) (v+V) :=
      Nat.add_le_add (Nat.mul_le_mul_left r h1) (Nat.mul_le_mul_left R h2)
    _ = (r+R) * rate (r+R) (v+V) := (Nat.add_mul _ _ _).symm

/-- On a singleton, a strict helper split charges the only factor directly. -/
theorem singleton_helper {ι : Type*} [DecidableEq ι] (a : ι)
    (count helper : ι → ℕ)
    (hsplit : ∃ U : Finset ι, U ⊂ {a} ∧ ∀ i ∈ ({a} : Finset ι) \ U,
      count i ≤ helper i) : count a ≤ helper a := by
  obtain ⟨U, hU, hcount⟩ := hsplit
  have ha : a ∉ U := by
    intro ha
    apply hU.2
    exact Finset.singleton_subset_iff.mpr ha
  exact hcount a (Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self a, ha⟩)

#print axioms sum_intercepts_le
#print axioms sum_count_le
#print axioms combine_bounds
#print axioms rate_bellman
#print axioms singleton_helper
end ProximityPrize.SubmissionLower.AffineFactorAggregate6808
