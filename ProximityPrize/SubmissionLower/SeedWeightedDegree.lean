import ProximityPrize.SubmissionLower.ContactFactorCaps
import ProximityPrize.SubmissionLower.ContactTaylorNumerators

/-!
# Weighted-degree analogues of the Taylor-numerator degree bounds

`ContactTaylorNumerators` bounds `degreeOf i` of every stage of the agreement
numerator.  The projection gate for the `unitR` pair needs one more quantity:
the *joint* `Y + Z` degree, i.e. `weightedTotalDegree seedWeights`, because the
coefficient box couples those two exponents (`d 1 + d 3 ≤ seedTotalCap`, since
the surface's `Y` variable is evaluated on the affine seed line).

Every lemma here mirrors one in `ContactTaylorNumerators.DegreeBounds`, with
`degreeOf i` replaced by `MvPolynomial.weightedTotalDegree weights`.  The
replacements are all support-level, so the proofs are shorter than the originals.
-/

namespace ProximityPrize.SubmissionLower.SeedWeightedDegree

open ContactDifferentialRing ContactTaylorNumerators ContactFactorCaps

noncomputable section

variable {K : Type*} [Field K]

/-- Abbreviation for the weighted total degree used throughout. -/
abbrev wdeg (weights : Fin 4 → ℕ) (P : Poly4 K) : ℕ :=
  MvPolynomial.weightedTotalDegree weights P

theorem wdeg_le_iff (weights : Fin 4 → ℕ) (P : Poly4 K) (a : ℕ) :
    wdeg weights P ≤ a ↔ ∀ d ∈ P.support, Finsupp.weight weights d ≤ a :=
  weightedTotalDegree_le_iff weights P a

theorem wdeg_le_of_support (weights : Fin 4 → ℕ) (P : Poly4 K) (a : ℕ)
    (h : ∀ d ∈ P.support, Finsupp.weight weights d ≤ a) : wdeg weights P ≤ a :=
  (wdeg_le_iff weights P a).mpr h

theorem wdeg_C_le (weights : Fin 4 → ℕ) (c : K) (a : ℕ) : wdeg weights (MvPolynomial.C c) ≤ a := by
  classical
  apply wdeg_le_of_support
  intro d hd
  have hd0 : d = 0 := by
    by_contra hne
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hd
    simp [Ne.symm hne] at hd
  subst hd0
  simp [weight_fin4]

theorem wdeg_natCast_le (weights : Fin 4 → ℕ) (k a : ℕ) :
    wdeg weights ((k : Poly4 K)) ≤ a := by
  rw [← map_natCast (MvPolynomial.C : K →+* Poly4 K) k]
  exact wdeg_C_le weights _ a

theorem wdeg_X_le (weights : Fin 4 → ℕ) (i : Fin 4) (a : ℕ) (h : weights i ≤ a) :
    wdeg weights (MvPolynomial.X i : Poly4 K) ≤ a := by
  classical
  apply wdeg_le_of_support
  intro d hd
  have hd1 : d = Finsupp.single i 1 := by
    by_contra hne
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X'] at hd
    simp [Ne.symm hne] at hd
  subst hd1
  rw [weight_fin4]
  fin_cases i <;> simpa using h

theorem wdeg_add_le (weights : Fin 4 → ℕ) {P Q : Poly4 K} {a : ℕ}
    (hP : wdeg weights P ≤ a) (hQ : wdeg weights Q ≤ a) : wdeg weights (P + Q) ≤ a := by
  apply wdeg_le_of_support
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact (wdeg_le_iff weights P a).mp hP d h
  · exact (wdeg_le_iff weights Q a).mp hQ d h

theorem wdeg_neg_le (weights : Fin 4 → ℕ) {P : Poly4 K} {a : ℕ}
    (hP : wdeg weights P ≤ a) : wdeg weights (-P) ≤ a := by
  apply wdeg_le_of_support
  intro d hd
  rw [MvPolynomial.support_neg] at hd
  exact (wdeg_le_iff weights P a).mp hP d hd

theorem wdeg_sub_le (weights : Fin 4 → ℕ) {P Q : Poly4 K} {a : ℕ}
    (hP : wdeg weights P ≤ a) (hQ : wdeg weights Q ≤ a) : wdeg weights (P - Q) ≤ a := by
  rw [sub_eq_add_neg]
  exact wdeg_add_le weights hP (wdeg_neg_le weights hQ)

theorem wdeg_mul_le (weights : Fin 4 → ℕ) {P Q : Poly4 K} {a b : ℕ}
    (hP : wdeg weights P ≤ a) (hQ : wdeg weights Q ≤ b) : wdeg weights (P * Q) ≤ a + b := by
  apply wdeg_le_of_support
  intro d hd
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  have h₁ := (wdeg_le_iff weights P a).mp hP d₁ hd₁
  have h₂ := (wdeg_le_iff weights Q b).mp hQ d₂ hd₂
  rw [map_add]
  exact Nat.add_le_add h₁ h₂

theorem wdeg_pow_le (weights : Fin 4 → ℕ) {P : Poly4 K} {a : ℕ} (k : ℕ)
    (hP : wdeg weights P ≤ a) : wdeg weights (P ^ k) ≤ k * a := by
  induction k with
  | zero => simpa using wdeg_natCast_le weights 1 0
  | succ k ih =>
      have := wdeg_mul_le weights ih hP
      calc wdeg weights (P ^ (k + 1)) = wdeg weights (P ^ k * P) := by rw [pow_succ]
        _ ≤ k * a + a := this
        _ = (k + 1) * a := by ring

theorem wdeg_sum_le (weights : Fin 4 → ℕ) (I : Finset ℕ) (f : ℕ → Poly4 K) (a : ℕ)
    (hf : ∀ j ∈ I, wdeg weights (f j) ≤ a) : wdeg weights (∑ j ∈ I, f j) ≤ a := by
  classical
  induction I using Finset.induction with
  | empty => simpa using wdeg_natCast_le weights 0 a
  | insert j I hj ih =>
      rw [Finset.sum_insert hj]
      exact wdeg_add_le weights (hf j (Finset.mem_insert_self j I))
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

/-- Differentiation never raises a weighted degree: the support moves down by
one unit of the differentiated variable's weight. -/
theorem wdeg_pderiv_le (weights : Fin 4 → ℕ) (i : Fin 4) {P : Poly4 K} {a : ℕ}
    (hP : wdeg weights P ≤ a) : wdeg weights (MvPolynomial.pderiv i P) ≤ a := by
  apply wdeg_le_of_support
  intro d hd
  have hmem := support_before_pderiv i P d hd
  have hle := (wdeg_le_iff weights P a).mp hP _ hmem
  rw [map_add] at hle
  omega

end

end ProximityPrize.SubmissionLower.SeedWeightedDegree
