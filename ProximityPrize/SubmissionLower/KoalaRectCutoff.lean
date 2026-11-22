import ProximityPrize.SubmissionLower.KoalaRectPosition
import ProximityPrize.SubmissionLower.KoalaRectQuotient

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaRect
noncomputable section
open Finset Polynomial
open K1_14 (FX Jet Equation Shape)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth)
open private gradeMap mem_filtered finrank_le_grades from ProximityPrize.SubmissionLower.Fast069
open scoped BigOperators

theorem rectCutoff_finrank_le (A h : ℕ) (s : Shape) (E W : ℕ) (U d : Fin 2 → ℕ)
    (V : Submodule FX Jet) {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree)
    (hk : 0 < 131071-h) (he : 0 < E)
    (hsupport : ∀ P ∈ V, RowCaps P s)
    (haxis : ∀ P ∈ V, ∀ j i z, ((P.coeff j).coeff i).degreeOf z ≤ U z)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree)*(131071-h) ≤ W+P.natDegree)
    (hdvd : ∀ P ∈ V, P ≠ 0 → f ^ (rectPower A h s W-P.natDegree) ∣ P.leadingCoeff)
    (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r) :
    Module.finrank FX V ≤ rectCapacity A h s E U d W := by
  have hrow {P : Jet} (hP : P ∈ V) (hn : P ≠ 0) :
      P.leadingCoeff.natDegree + P.natDegree ≤ s.B ∧ P.natDegree ≤ s.J := by
    have hn' : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    exact ⟨(hsupport P hP _ _ hn').1, (hsupport P hP _ _ hn').2.1⟩
  rw [← rectCapacity_eq _ _ _ _ _ _ _ hk he]
  refine finrank_le_grades (F := FX) (A := Equation) V (rectGrade A h s E U d W)
    (s.J+1) ?_ ?_
  · intro j
    let r := rectPower A h s W-j
    have hmul := rank_rect_multiples_le (gradeMap (F := FX) (A := Equation) V j).range
      (g := f^r) (pow_ne_zero r hf)
      (a := gradeWidth (131071-h) s.B W j) (yspent := r*E)
      (U := U) (spent := fun z => r*axisDegree f z)
      (by rw [Polynomial.natDegree_pow]; exact Nat.mul_le_mul_left _ hE)
      (fun z => by rw [axisDegree_pow hf]) ?_
    · apply hmul.trans
      rw [Nat.mul_assoc]
      change (↑((gradeWidth (131071-h) s.B W j-r*E)*rectSlots U (axisDegree f) r) : Cardinal) ≤
        ↑((gradeWidth (131071-h) s.B W j-r*E)*rectSlots U d r)
      exact_mod_cast Nat.mul_le_mul_left (gradeWidth (131071-h) s.B W j-r*E) (hslots r)
    · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
      change P.coeff j ≠ 0 at hc
      obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
      have hn : P ≠ 0 := by
        intro hz
        exact hc (by simp [hz])
      have hj : P.natDegree = j :=
        le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB, _⟩ := hrow hpV hn
      have hwidth := hlead P hpV hn
      have hdiv := hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree < _ ∧ (∀ i z, ((P.coeff j).coeff i).degreeOf z ≤ U z) ∧
        f^r ∣ P.coeff j
      refine ⟨?_, haxis P hpV j, ?_⟩
      · rw [← hj, coeff_natDegree, hj]
        have hle := (Nat.le_div_iff_mul_le hk).2 hwidth
        unfold gradeWidth
        omega
      · rwa [← hj, coeff_natDegree]
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2)

#print axioms rectCutoff_finrank_le
end
end KoalaRect
