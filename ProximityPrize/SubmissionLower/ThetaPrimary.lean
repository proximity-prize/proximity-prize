import ProximityPrize.SubmissionLower.ThetaSum
import ProximityPrize.SubmissionLower.Fast072

/-!
The rank of the primary interpolation with the theta bound on the grades below 3012.
-/

set_option Elab.async false

namespace K1_13_2
noncomputable section
open K1 K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open K1_13_2 (finrank_of_column_cover)
open private high_monomial_vanishes from ProximityPrize.SubmissionLower.Fast017

end
end K1_13_2

namespace ThetaPrimary
open K1_13 K1_13_2 K1_13_2_3 ThetaBlock ThetaSum
open scoped BigOperators
open K1_13_2_3 (savings_parts bound_le_baseline)
open private combine baseline_budget_on from ProximityPrize.SubmissionLower.Fast022

def zeroPowers : BlockIndex → Powers := fun _ => ⟨0, 0, 0⟩

theorem expand_zero : (⟨0, 0, 0⟩ : Powers).expand = fun _ => 0 := by
  funext j
  fin_cases j <;> rfl

/-- The block bound: theta and the plain bound below grade 3012, the product bound above. -/
def bound (p : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if i.1.val < 3012 then min (baseline i) (thetaBound i) else blockBound i (p i).expand

theorem block_le (hblock : K1_13_2.c2) (p : BlockIndex → Powers) (i : BlockIndex) :
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤ bound p i := by
  unfold bound
  by_cases hs : i.1.val < 3012
  · rw [if_pos hs]
    refine le_min (hblock i _) ?_
    unfold thetaBound
    by_cases hc : 2999 ≤ i.1.val + i.2.val ∧ i.1.val + i.2.val ≤ 4650
    · rw [if_pos hc]
      have h := block_rank i hc.1 hc.2
      omega
    · rw [if_neg hc]
      exact hblock i _
  · rw [if_neg hs]
    exact hblock i _

end ThetaPrimary
