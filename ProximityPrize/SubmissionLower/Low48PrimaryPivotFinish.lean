import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBaseline

set_option Elab.async false
set_option maxHeartbeats 2500000

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_2 K1_13_2_3
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open private finrank_of_column_cover high_monomial_vanishes from ProximityPrize.SubmissionLower.Fast017

noncomputable def blockRank (i : BlockIndex) :=
  Module.finrank Geom (LinearMap.range (originBlock i))

private theorem full_blocks :
    Module.finrank Geom (LinearMap.range (nodeMap 0 0)) ≤ ∑ i, blockRank i := by
  classical
  let ranges : BlockIndex → Submodule Geom Local := fun i => LinearMap.range (originBlock i)
  refine finrank_of_column_cover (localConstraintAt 3000 0 0) ranges blockRank ?_ (fun i => le_rfl)
  intro e he c
  by_cases hx : e none < 3000
  · have he' : SourceEligible e := he
    let grade := e.weight jetDegreeWeight
    let idx := e.weight jetDerivativeWeight
    have hb : grade ≤ 4012 := he'.1
    have hj : idx ≤ 1650 := he'.2.1
    let i : BlockIndex := (⟨grade, by omega⟩, ⟨e none+(1650-idx),by omega⟩)
    have hi : e ∈ blockExponents i := by
      refine ⟨he',hx,rfl,?_⟩
      change (e none : ℤ)-idx = ((e none+(1650-idx) : ℕ) : ℤ)-1650
      omega
    refine Or.inr ⟨i,?_⟩
    have hm : MvPolynomial.monomial e c ∈ BlockSpace i := by
      unfold BlockSpace
      exact (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hi)
    exact ⟨⟨MvPolynomial.monomial e c,hm⟩,rfl⟩
  · exact Or.inl (high_monomial_vanishes e _ (Nat.le_of_not_gt hx))

open private baseline_budget_on bound_le_baseline from ProximityPrize.SubmissionLower.Fast022

private theorem local_invoice (S : Finset BlockIndex) (p₁ p₄ : BlockIndex → Powers)
    (hblock : K1_13_2.c2) :
    (∑ i ∈ S, blockRank i) +
      (∑ i ∈ S, if w1.Contains i then savings i (p₁ i) else 0) +
      (∑ i ∈ S, if w4.Contains i then savings i (p₄ i) else 0) +
      (∑ i ∈ S, if w2.Contains i then baseline i else 0) +
      (∑ i ∈ S, if w3.Contains i then baseline i else 0) ≤
    (∑ i ∈ S, baseline i) +
      (∑ i ∈ S, if w2.Contains i then ∑ q : Column, charge i q else 0) +
      (∑ i ∈ S, if w3.Contains i then ∑ q : Column, charge i q else 0) := by
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hb : blockRank i ≤ baseline i := hblock i (fun _ => 0)
  have h1 : blockRank i + savings i (p₁ i) ≤ baseline i := by
    unfold savings
    have h : blockRank i ≤ blockBound i (p₁ i).expand := hblock i (p₁ i).expand
    have hle := bound_le_baseline i (p₁ i).expand
    exact (Nat.add_le_add_right h _).trans_eq (Nat.add_sub_of_le hle)
  have h4 : blockRank i + savings i (p₄ i) ≤ baseline i := by
    unfold savings
    have h : blockRank i ≤ blockBound i (p₄ i).expand := hblock i (p₄ i).expand
    have hle := bound_le_baseline i (p₄ i).expand
    exact (Nat.add_le_add_right h _).trans_eq (Nat.add_sub_of_le hle)
  have distinctWindows :
      (w1.Contains i → ¬w2.Contains i ∧ ¬w3.Contains i ∧ ¬w4.Contains i) ∧
      (w2.Contains i → ¬w1.Contains i ∧ ¬w3.Contains i ∧ ¬w4.Contains i) ∧
      (w3.Contains i → ¬w1.Contains i ∧ ¬w2.Contains i ∧ ¬w4.Contains i) ∧
      (w4.Contains i → ¬w1.Contains i ∧ ¬w2.Contains i ∧ ¬w3.Contains i) := by
    simp only [w1, w2, w3, w4, Window.Contains]
    omega
  by_cases hw1 : w1.Contains i
  · obtain ⟨hn2,hn3,hn4⟩ := distinctWindows.1 hw1
    simpa [hw1,hn2,hn3,hn4] using h1
  by_cases hw2 : w2.Contains i
  · obtain ⟨_,hn3,hn4⟩ := distinctWindows.2.1 hw2
    have hpow := block_le_charge i (by
      have := hw2.1
      change 2008 ≤ i.1.val at this
      omega)
    change blockRank i ≤ _ at hpow
    simp only [hw1, hw2, hn3, hn4, ite_true, ite_false, zero_add, add_zero]
    exact (Nat.add_le_add_right hpow _).trans_eq (Nat.add_comm _ _)
  by_cases hw3 : w3.Contains i
  · obtain ⟨_,_,hn4⟩ := distinctWindows.2.2.1 hw3
    have hpow := block_le_charge i (by
      have := hw3.1
      change 3012 ≤ i.1.val at this
      omega)
    change blockRank i ≤ _ at hpow
    simp only [hw1, hw2, hw3, hn4, ite_true, ite_false, zero_add, add_zero]
    exact (Nat.add_le_add_right hpow _).trans_eq (Nat.add_comm _ _)
  by_cases hw4 : w4.Contains i
  · simpa [hw1,hw2,hw3,hw4] using h4
  · simpa [hw1,hw2,hw3,hw4] using hb

private theorem rank_budget {r h1 h4 b2 b3 b d2 d3 : ℕ}
    (hs : r+h1+h4+b2+b3 ≤ b+d2+d3) (h₁ : 9573892230 ≤ h1)
    (h₄ : 177382348097 ≤ h4) (hb : b ≤ 344569599740461)
    (hraw : 28571050105634 ≤ b2+b3) (hfee : d2+d3 ≤ 28152494316297) :
    r ≤ 343964087710797 := by omega

attribute [local irreducible] Finset.univ

private theorem savings_def (w : Window) (p : BlockIndex → Powers) :
    savingsSum w p = ∑ i : BlockIndex, if w.Contains i then savings i (p i) else 0 := rfl

private theorem raw_def (w : Window) :
    rawWindow w = ∑ i : BlockIndex, if w.Contains i then baseline i else 0 := rfl

private theorem debit_def (w : Window) :
    debit w = ∑ i : BlockIndex, if w.Contains i then ∑ q : Column, charge i q else 0 := rfl

private theorem invoice_body (p₁ p₄ : BlockIndex → Powers) (hblock : K1_13_2.c2) :
    (∑ i : BlockIndex, blockRank i) +
      (∑ i : BlockIndex, if w1.Contains i then savings i (p₁ i) else 0) +
      (∑ i : BlockIndex, if w4.Contains i then savings i (p₄ i) else 0) +
      (∑ i : BlockIndex, if w2.Contains i then baseline i else 0) +
      (∑ i : BlockIndex, if w3.Contains i then baseline i else 0) ≤
      (∑ i : BlockIndex, baseline i) +
      (∑ i : BlockIndex, if w2.Contains i then ∑ q : Column, charge i q else 0) +
      (∑ i : BlockIndex, if w3.Contains i then ∑ q : Column, charge i q else 0) :=
  local_invoice (Finset.univ : Finset BlockIndex) p₁ p₄ hblock

private theorem invoice_univ (p₁ p₄ : BlockIndex → Powers) (hblock : K1_13_2.c2) :
    (∑ i : BlockIndex, blockRank i) + savingsSum w1 p₁ + savingsSum w4 p₄ +
      rawWindow w2 + rawWindow w3 ≤ (∑ i : BlockIndex, baseline i) + debit w2 + debit w3 := by
  rw [savings_def, savings_def, raw_def, raw_def, debit_def, debit_def]
  exact invoice_body p₁ p₄ hblock

theorem origin_rank_of_receipts
    (hraw : 28571050105634 ≤ rawWindow w2 + rawWindow w3)
    (hfee : debit w2 + debit w3 ≤ 28152494316297) :
    Module.finrank Geom (LinearMap.range (nodeMap 0 0)) ≤ 343964087710797 := by
  obtain ⟨p₁, hp₁⟩ := K1_13_2_3_4.proof
  let p₄ := K1_13_2_3_7.witness
  have hp₄ : 177382348097 ≤ savingsSum w4 p₄ :=
    K1_13_2_3_7.numeric_total ▸ K1_13_2_3_7.numeric_le_savings
  have hblock := K1_13_2_2.of_children K1_13_2_2_1.proof K1_13_2_2_2.proof
    K1_13_2_2_3.proof K1_13_2_2_4.proof K1_13_2_2_5.proof
  have hstatic := baseline_budget_on (Finset.univ : Finset BlockIndex) baseline_low
    K1_13_2_3_1.proof K1_13_2_3_2.proof K1_13_2_3_3.proof
  have hRank := rank_budget
    (r := ∑ i : BlockIndex, blockRank i)
    (h1 := savingsSum w1 p₁) (h4 := savingsSum w4 p₄)
    (b2 := rawWindow w2) (b3 := rawWindow w3)
    (b := ∑ i : BlockIndex, baseline i) (d2 := debit w2) (d3 := debit w3)
    (invoice_univ p₁ p₄ hblock) hp₁ hp₄ hstatic hraw hfee
  exact Nat.le_trans full_blocks hRank

#print axioms origin_rank_of_receipts
end Low48PrimaryPivot
