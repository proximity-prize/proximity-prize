import ProximityPrize.SubmissionLower.Peer653High53FamilyPersistentCount

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
noncomputable section
open Finset Polynomial MvPolynomial
open Peer653High53 (agreement)
open K1_14 (Shape shapeSum Banks Equation FX Jet slots triangle SeedBound)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth seedDegree seedDegree_pow)
open P1_7_5 (kept)
open private position_sum from ProximityPrize.SubmissionLower.UpperBranch5
open private rank_joint_multiples_le gradeCapacity_eq from ProximityPrize.SubmissionLower.UpperBranch5
open private shapeSum_swap from ProximityPrize.SubmissionLower.Fast072
open private finrank_le_grades mem_filtered from ProximityPrize.SubmissionLower.Fast069
def cutoffCapacity (h : ℕ) (s : Shape) (E v W : ℕ) : ℕ :=
  shapeSum s fun q j =>
    if q*(131071-h) ≤ W+j then
      kept s.U v ((q-j)/E) (contactPower h s W - j)
    else 0
private def gradeCapacity (h : ℕ) (s : Shape) (E v W j : ℕ) : ℕ :=
  let r := contactPower h s W - j
  (gradeWidth (131071-h) s.B W j - r*E) * slots s.U (r*v)
private theorem cutoffCapacity_eq (h : ℕ) (s : Shape) (E v W : ℕ)
    (hk : 0 < 131071-h) (he : 0 < E) :
    (∑ j ∈ range (s.J+1), gradeCapacity h s E v W j) = cutoffCapacity h s E v W := by
  rw [cutoffCapacity, ← shapeSum_swap]
  apply sum_congr rfl
  intro j _
  exact gradeCapacity_eq _ _ _ _ _ _ _ _ hk he
set_option backward.isDefEq.respectTransparency false in
theorem cutoff_finrank_le (h : ℕ) (s : Shape) (E v W : ℕ) (V : Submodule FX Jet)
    {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree) (hv : v ≤ seedDegree f)
    (hk : 0 < 131071-h) (he : 0 < E)
    (hcaps : ∀ P ∈ V, RowCaps P s)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree) * (131071-h) ≤ W + P.natDegree)
    (hdvd : ∀ P ∈ V, P ≠ 0 → f ^ (contactPower h s W - P.natDegree) ∣ P.leadingCoeff) :
    Module.finrank FX V ≤ cutoffCapacity h s E v W := by
  have hrow {P : Jet} (hP : P ∈ V) (hn : P ≠ 0) :
      P.leadingCoeff.natDegree + P.natDegree ≤ s.B ∧ P.natDegree ≤ s.J ∧
      SeedBound P.leadingCoeff s.U := by
    have ha : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hB, hJ, _⟩ := hcaps P hP _ _ ha
    refine ⟨hB, hJ, fun i => ?_⟩
    by_cases hi : P.leadingCoeff.coeff i = 0
    · simp [hi]
    · rw [← coeff_natDegree] at hi ⊢
      exact (hcaps P hP _ _ hi).2.2
  rw [← cutoffCapacity_eq h s E v W hk he]
  refine finrank_le_grades (F := FX) (A := Equation) V (gradeCapacity h s E v W)
    (s.J+1) ?_ ?_
  · intro j
    let r := contactPower h s W - j
    apply rank_joint_multiples_le _ (g := f^r) (pow_ne_zero r hf)
    · rw [Polynomial.natDegree_pow]
      exact Nat.mul_le_mul_left _ hE
    · rw [seedDegree_pow hf]
      exact Nat.mul_le_mul_left _ hv
    · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
      change P.coeff j ≠ 0 at hc
      obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
      have hn : P ≠ 0 := by
        intro hz
        exact hc (by simp [hz])
      have hj : P.natDegree = j :=
        le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB, _, hseed⟩ := hrow hpV hn
      have hwidth := hlead P hpV hn
      have hdiv := hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree < _ ∧ SeedBound (P.coeff j) _ ∧ _ ∣ P.coeff j
      rw [← hj, coeff_natDegree, hj]
      refine ⟨?_, hseed, hdiv⟩
      have hd := (Nat.le_div_iff_mul_le hk).2 hwidth
      unfold gradeWidth
      omega
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2.1)
end
end Peer653High53
end
