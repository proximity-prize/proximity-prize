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
open private finrank_of_column_cover high_monomial_vanishes
  from ProximityPrize.SubmissionLower.Fast017

/-- The column cover of the origin map with any family of block bounds. -/
theorem origin_rank_le_bound (bound : BlockIndex → ℕ)
    (h : ∀ i, Module.finrank Geom (LinearMap.range (originBlock i)) ≤ bound i) :
    Module.finrank Geom (LinearMap.range (nodeMap 0 0)) ≤ ∑ i, bound i := by
  classical
  let ranges : BlockIndex → Submodule Geom Local := fun i => LinearMap.range (originBlock i)
  refine finrank_of_column_cover (localConstraintAt 3000 0 0) ranges bound ?_ h
  intro e he c
  by_cases hx : e none < 3000
  · have he' : SourceEligible e := he
    let grade := e.weight jetDegreeWeight
    let idx := e.weight jetDerivativeWeight
    have hb : grade ≤ 4012 := he'.1
    have hj : idx ≤ 1650 := he'.2.1
    let i : BlockIndex := (⟨grade, by omega⟩, ⟨e none + (1650 - idx), by omega⟩)
    have hi : e ∈ blockExponents i := by
      refine ⟨he', hx, rfl, ?_⟩
      change (e none : ℤ) - idx = ((e none + (1650 - idx) : ℕ) : ℤ) - 1650
      omega
    refine Or.inr ⟨i, ?_⟩
    have hm : MvPolynomial.monomial e c ∈ BlockSpace i := by
      unfold BlockSpace
      exact (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hi)
    exact ⟨⟨MvPolynomial.monomial e c, hm⟩, rfl⟩
  · exact Or.inl (high_monomial_vanishes e _ (Nat.le_of_not_gt hx))

end
end K1_13_2

namespace ThetaPrimary
open K1_13 K1_13_2 K1_13_2_3 ThetaBlock ThetaSum
open scoped BigOperators
open private combine baseline_budget_on savings_parts bound_le_baseline
  from ProximityPrize.SubmissionLower.Fast022

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

theorem sum_bound (p : BlockIndex → Powers)
    (hzero : ∀ i : BlockIndex, i.1.val < 3012 → p i = ⟨0, 0, 0⟩)
    (hsave : 277923269377 ≤ ∑ i : BlockIndex, savings i (p i)) :
    (∑ i : BlockIndex, bound p i) ≤ 344003309486625 := by
  have hstatic := baseline_budget_on (Finset.univ : Finset BlockIndex) baseline_low
    K1_13_2_3_1.proof K1_13_2_3_2.proof K1_13_2_3_3.proof
  have htheta := total_le
  have hpoint : ∀ i ∈ (Finset.univ : Finset BlockIndex),
      bound p i + (savings i (p i) + stripSave i) ≤ baseline i := by
    intro i _
    unfold bound stripSave thetaSave savings
    by_cases hs : i.1.val < 3012
    · have hb : blockBound i (p i).expand = baseline i := by
        rw [hzero i hs, expand_zero]
        rfl
      simp only [if_pos hs]
      rw [hb]
      omega
    · have hle := bound_le_baseline i (p i).expand
      simp only [if_neg hs]
      omega
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  omega

/-- The rank of the primary interpolation at the origin, with the theta bound. -/
theorem origin_rank :
    Module.finrank Geom (LinearMap.range (K1_13_2.nodeMap 0 0)) ≤ 344003309486625 := by
  have hblock := K1_13_2_2.of_children K1_13_2_2_1.proof K1_13_2_2_2.proof
    K1_13_2_2_3.proof K1_13_2_2_4.proof K1_13_2_2_5.proof
  obtain ⟨p₃, hp₃⟩ := K1_13_2_3_6.proof
  have hp₄ : 177382348097 ≤ savingsSum w4 K1_13_2_3_7.witness :=
    K1_13_2_3_7.numeric_total ▸ K1_13_2_3_7.numeric_le_savings
  have hparts := savings_parts zeroPowers zeroPowers p₃ K1_13_2_3_7.witness
  have hzero : ∀ i : BlockIndex, i.1.val < 3012 →
      combine zeroPowers zeroPowers p₃ K1_13_2_3_7.witness i = ⟨0, 0, 0⟩ := by
    intro i hi
    unfold combine zeroPowers
    split_ifs <;> first | rfl | omega
  have hsave : 277923269377 ≤ ∑ i : BlockIndex,
      savings i (combine zeroPowers zeroPowers p₃ K1_13_2_3_7.witness i) := by
    omega
  exact (K1_13_2.origin_rank_le_bound _ (block_le hblock _)).trans (sum_bound _ hzero hsave)

#print axioms origin_rank

end ThetaPrimary
