import ProximityPrize.SubmissionLower.Final50PriceTotal

namespace Final50PriceActiveAllocation

open K1_13 (Row shape indexDegree extend OnFactor)
open Final50Price (Messages SmallFactor ActiveFits Fits LayerBudget ProperCut FatEquations Holds c6 c7)
open Final50PriceCaps (Band Admits start activeCap factorCap)
open Final50PriceTotal (retainedShape)
open P3 (K)
open MvPolynomial
open scoped BigOperators Polynomial

noncomputable def activeDegree (f : Row 4) : ℕ :=
  f.weightedTotalDegree (![1, 2, 2, 2] : Fin 4 → ℕ)

private theorem active_monomial (m : Fin 4 →₀ ℕ) :
    m.weight (![1, 2, 2, 2] : Fin 4 → ℕ) =
      m 0 + 2 * m 1 + 2 * m 2 + 2 * m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, Nat.mul_comm]

theorem activeFits_iff (f : Row 4) (cap : ℕ) : ActiveFits f cap ↔ activeDegree f ≤ cap := by
  unfold ActiveFits activeDegree weightedTotalDegree
  rw [Finset.sup_le_iff]
  simp only [active_monomial]

theorem degree_le_active (f : Row 4) : (shape f).b ≤ activeDegree f := by
  change f.totalDegree ≤ _
  rw [← weightedTotalDegree_one, weightedTotalDegree, Finset.sup_le_iff]
  intro m hm
  have hm' := le_weightedTotalDegree (![1, 2, 2, 2] : Fin 4 → ℕ) hm
  rw [active_monomial] at hm'
  simp only [Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, Pi.one_apply, Nat.mul_one]
  change _ ≤ f.weightedTotalDegree (![1, 2, 2, 2] : Fin 4 → ℕ)
  omega

theorem index_credit_le_active (f : Row 4) : 2 * (((shape f).j + 2) / 3) ≤ activeDegree f := by
  have h : indexDegree f ≤ 3 * (activeDegree f / 2) := by
    rw [K1_13_1.indexDegree_eq, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    have hm' := le_weightedTotalDegree (![1, 2, 2, 2] : Fin 4 → ℕ) hm
    rw [active_monomial] at hm'
    change m 0 + 2 * m 1 + 2 * m 2 + 2 * m 3 ≤ activeDegree f at hm'
    simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul]
    omega
  change 2 * ((indexDegree f + 2) / 3) ≤ activeDegree f
  omega

/-- A positive-order factor has the active degree left after the retained factors. -/
theorem factor_fits {n : ℕ} (f : Fin n → Row 4) (l : Fin n → ℕ)
    (hactive : (∑ j, activeDegree (f j)) ≤ 165) {i : Fin n} (hi : 0 < l i)
    {k : Band} (hk : Admits k (retainedShape (fun j => shape (f j)) l)) :
    ActiveFits (f i) (activeCap k) := by
  let z := Finset.univ.filter fun j => l j = 0
  let degree (j : Fin n) := activeDegree (f j)
  let a (j : Fin n) := shape (f j)
  let credit (j : Fin n) := (((a j).j + 2) / 3)
  have hb : (start k).b ≤ ∑ j ∈ z, (a j).b := hk.1.1
  have hj : (start k).j ≤ ∑ j ∈ z, (a j).j := hk.1.2.1
  have hsB : (start k).b ≤ ∑ j ∈ z, degree j :=
    hb.trans (Finset.sum_le_sum fun j _ => degree_le_active (f j))
  have hJ : (start k).j ≤ 3 * (∑ j ∈ z, credit j) := by
    apply hj.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    change (a j).j ≤ 3 * (((a j).j + 2) / 3)
    omega
  have hC : 2 * (∑ j ∈ z, credit j) ≤ ∑ j ∈ z, degree j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => index_credit_le_active (f j)
  have hsJ : 2 * (((start k).j + 2) / 3) ≤ ∑ j ∈ z, degree j := by omega
  have hspent := max_le hsB hsJ
  have hnz : i ∉ z := by simp [z, Nat.ne_of_gt hi]
  have hroom : degree i + (∑ j ∈ z, degree j) ≤ 165 := by
    rw [← Finset.sum_insert hnz]
    exact (Finset.sum_le_sum_of_subset (Finset.subset_univ (insert i z))).trans hactive
  apply (activeFits_iff _ _).mpr
  change degree i ≤ 165 - max (start k).b (2 * (((start k).j + 2) / 3))
  omega

end Final50PriceActiveAllocation
