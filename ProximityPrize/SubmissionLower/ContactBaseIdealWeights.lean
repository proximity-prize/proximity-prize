import ProximityPrize.SubmissionLower.ContactBaseIdealCoefficients
import ProximityPrize.SubmissionLower.ContactPost6464MinkowskiRecurrence

namespace ProximityPrize.SubmissionLower.ContactBaseIdealWeights

open ContactTaylorNumerators ContactBaseIdealAlgebra
open ContactBaseIdealCoefficients ContactPost6464MinkowskiRecurrence

noncomputable section

variable {K : Type*} [Field K]

abbrev Poly (K : Type*) [Field K] := MvPolynomial (Fin 4) K

def WeightBound (w : Fin 4 → ℕ) (P : Poly K) (c : ℤ) : Prop :=
  P = 0 ∨ (wt w P : ℤ) ≤ c

namespace WeightBound

variable {w : Fin 4 → ℕ} {P Q : Poly K} {a b : ℤ}

theorem mono (h : WeightBound w P a) (hab : a ≤ b) : WeightBound w P b :=
  h.imp_right (fun hp => hp.trans hab)

theorem add (hP : WeightBound w P a) (hQ : WeightBound w Q a) :
    WeightBound w (P + Q) a := by
  rcases hP with rfl | hp
  · simpa only [zero_add] using hQ
  rcases hQ with rfl | hq
  · rw [add_zero]
    exact Or.inr hp
  right
  have h : (wt w (P + Q) : ℤ) ≤ max (wt w P : ℤ) (wt w Q : ℤ) := by
    exact_mod_cast wt_add_le w P Q
  exact h.trans (max_le hp hq)

theorem neg (hP : WeightBound w P a) : WeightBound w (-P) a := by
  rcases hP with rfl | hp
  · exact Or.inl neg_zero
  exact Or.inr (by simpa only [wt_neg] using hp)

theorem sub (hP : WeightBound w P a) (hQ : WeightBound w Q a) :
    WeightBound w (P - Q) a := by
  simpa only [sub_eq_add_neg] using hP.add hQ.neg

theorem mul (hP : WeightBound w P a) (hQ : WeightBound w Q b) :
    WeightBound w (P * Q) (a + b) := by
  rcases hP with rfl | hp
  · exact Or.inl (zero_mul _)
  rcases hQ with rfl | hq
  · exact Or.inl (mul_zero _)
  right
  have h : (wt w (P * Q) : ℤ) ≤ (wt w P : ℤ) + (wt w Q : ℤ) := by
    exact_mod_cast wt_mul_le w P Q
  linarith

theorem natCast (n : ℕ) : WeightBound w (n : Poly K) 0 :=
  Or.inr (by simp only [wt_natCast, Nat.cast_zero, le_refl])

theorem scale (n : ℕ) (hP : WeightBound w P a) : WeightBound w ((n : Poly K) * P) a := by
  simpa only [zero_add] using (natCast n).mul hP

theorem pderiv (hP : WeightBound w P a) (i : Fin 4) :
    WeightBound w (MvPolynomial.pderiv i P) (a - w i) := by
  by_cases hz : MvPolynomial.pderiv i P = 0
  · exact Or.inl hz
  rcases hP with rfl | hp
  · exact (hz (map_zero _)).elim
  right
  have hi : w i ≤ wt w P := by
    by_contra hh
    exact hz (ContactPost6464MinkowskiRecurrence.pderiv_eq_zero_of_wt_lt w P i (by omega))
  have hd := wt_pderiv_le w P i (wt w P) le_rfl
  have hsum : wt w (MvPolynomial.pderiv i P) + w i ≤ wt w P := by omega
  have hsum' : (wt w (MvPolynomial.pderiv i P) : ℤ) + w i ≤ wt w P := by
    exact_mod_cast hsum
  linarith

theorem horizontal (hP : WeightBound w P a) (t : ℕ)
    (hX : w 0 = 0) (hY : w 1 = t) (hR : w 2 = 1) (ht : t ≤ 1) :
    WeightBound w (horizontalDerivation P) (a + 1 - t) := by
  have hx := hP.pderiv (0 : Fin 4)
  have hy := hP.pderiv (1 : Fin 4)
  have hr : WeightBound w (MvPolynomial.X (2 : Fin 4) : Poly K) 1 :=
    Or.inr (by simp only [wt_X, hR, Nat.cast_one, le_refl])
  simp only [hX, Nat.cast_zero, sub_zero] at hx
  rw [hY] at hy
  have hxy : WeightBound w (MvPolynomial.X (2 : Fin 4) * MvPolynomial.pderiv (1 : Fin 4) P)
      (a + 1 - t) := by convert hr.mul hy using 1; ring
  have ht' : (t : ℤ) ≤ 1 := by exact_mod_cast ht
  simpa only [horizontalDerivation, Derivation.add_apply, Derivation.smul_apply,
    smul_eq_mul] using (hx.mono (by linarith)).add hxy

end WeightBound

theorem contribution_bounds (w : Fin 4 → ℕ) (t : ℕ)
    (hX : w 0 = 0) (hY : w 1 = t) (hR : w 2 = 1) (ht : t ≤ 1)
    (F P : Poly K) (C a : ℤ) (hF : WeightBound w F C) (hP : WeightBound w P a)
    (n j : ℕ) :
    WeightBound w (sameContribution F n j P) (a + C - t) ∧
    WeightBound w (downContribution F j P) (a + C + 2 - 2 * t) ∧
    WeightBound w (upContribution F n j P) (a + C - 2) := by
  have hH : WeightBound w (polyH K F) (C - 1) := by
    simpa only [polyH, hR, Nat.cast_one] using hF.pderiv (2 : Fin 4)
  have hG : WeightBound w (polyG K F) (C + 1 - t) := by
    simpa only [polyG, horizontalDerivation, Derivation.add_apply,
      Derivation.smul_apply, smul_eq_mul] using (hF.horizontal t hX hY hR ht).neg
  have hDH := hH.horizontal t hX hY hR ht
  have hDG := hG.horizontal t hX hY hR ht
  have hDP := hP.horizontal t hX hY hR ht
  have hGR := hG.pderiv (2 : Fin 4)
  have hHR := hH.pderiv (2 : Fin 4)
  have hPR := hP.pderiv (2 : Fin 4)
  simp only [hR, Nat.cast_one] at hGR hHR hPR
  refine ⟨?_, ?_, ?_⟩
  · unfold sameContribution
    apply WeightBound.add
    · apply WeightBound.sub
      · convert hH.mul hDP using 1; ring
      · convert (hP.scale (n + j)).mul hDH using 1; ring
    · convert (hP.scale j).mul hGR using 1; ring
  · unfold downContribution
    convert (hP.scale j).mul hDG using 1; ring
  · unfold upContribution
    apply WeightBound.sub
    · convert hH.mul hPR using 1; ring
    · convert (hP.scale (n + j)).mul hHR using 1; ring

theorem baseCoefficients_weightBound (w : Fin 4 → ℕ) (t : ℕ)
    (hX : w 0 = 0) (hY : w 1 = t) (hR : w 2 = 1) (ht : t ≤ 1)
    (F : Poly K) (C : ℤ) (hF : WeightBound w F C) (n j : ℕ) :
    WeightBound w (baseCoefficients F n j)
      (2 - t + n * (C - t) - j * (2 - t)) := by
  induction n generalizing j with
  | zero =>
    by_cases hj : j = 1
    · subst j
      simp only [baseCoefficients, ↓reduceIte]
      convert WeightBound.natCast (w := w) (K := K) 1 using 1 <;> push_cast <;> ring
    · exact Or.inl (by simp [baseCoefficients, hj])
  | succ n ih =>
    rw [baseCoefficients, coefficientStep]
    apply WeightBound.add
    · apply WeightBound.add
      · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih j) n j).1 using 1
        push_cast
        ring
      · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j + 1)) n (j + 1)).2.1
          using 1
        push_cast
        ring
    · by_cases hj : j = 0
      · rw [if_pos hj]
        exact Or.inl rfl
      · rw [if_neg hj]
        have hj1 : 1 ≤ j := by omega
        convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j - 1)) n (j - 1)).2.2
          using 1
        simp only [Nat.cast_sub hj1, Nat.cast_one, Nat.cast_add]
        ring

end

end ProximityPrize.SubmissionLower.ContactBaseIdealWeights
