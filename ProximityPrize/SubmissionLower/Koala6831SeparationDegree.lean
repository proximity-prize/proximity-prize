import ProximityPrize.SubmissionLower.Koala6831SeparationTensor
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.FieldDivision

namespace ProximityPrize.SubmissionLower.Koala6831Separation

open Polynomial

variable {K : Type*} [Field K]

def pairDegree (A : Fin 2 → K[X]) : ℕ := max (A 0).natDegree (A 1).natDegree

theorem natDegree_le_pairDegree (A : Fin 2 → K[X]) (i : Fin 2) :
    (A i).natDegree ≤ pairDegree A := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

private theorem pairDegree_le_iff (A : Fin 2 → K[X]) (n : ℕ) :
    pairDegree A ≤ n ↔ ∀ i, (A i).natDegree ≤ n := by
  constructor
  · exact fun h i ↦ (natDegree_le_pairDegree A i).trans h
  · exact fun h ↦ max_le (h 0) (h 1)

private theorem coprime_of_nonzero_pair {a b : K} (h : a ≠ 0 ∨ b ≠ 0) :
    IsCoprime a b := by
  rcases h with ha | hb
  · exact ⟨a⁻¹, 0, by simp [ha]⟩
  · exact ⟨0, b⁻¹, by simp [hb]⟩

private theorem pair_top_coprime (A : Fin 2 → K[X]) (hn : A 0 ≠ 0 ∨ A 1 ≠ 0) :
    IsCoprime ((A 0).coeff (pairDegree A)) ((A 1).coeff (pairDegree A)) := by
  apply coprime_of_nonzero_pair
  by_cases h : (A 0).natDegree ≤ (A 1).natDegree
  · have he : pairDegree A = (A 1).natDegree := max_eq_right h
    by_cases h1 : A 1 = 0
    · have h0 : A 0 ≠ 0 := hn.resolve_right (fun h ↦ h h1)
      have hh : (A 0).natDegree = (A 1).natDegree := by simpa [h1] using h
      exact Or.inl (by simpa only [he, ← hh, leadingCoeff] using leadingCoeff_ne_zero.mpr h0)
    · exact Or.inr (by simpa only [he, leadingCoeff] using leadingCoeff_ne_zero.mpr h1)
  · have hh : (A 1).natDegree < (A 0).natDegree := Nat.lt_of_not_ge h
    have he : pairDegree A = (A 0).natDegree := max_eq_left hh.le
    have h0 : A 0 ≠ 0 := by
      intro h0
      simp [h0] at hh
    exact Or.inl (by simpa only [he, leadingCoeff] using leadingCoeff_ne_zero.mpr h0)

private theorem degree_drop_of_top_cancel {P F : K[X]} {r a q : ℕ} {t : K}
    (hr : 0 < r) (hqa : q + a = r) (hP : P.natDegree ≤ r) (hF : F.natDegree ≤ a)
    (hcoeff : P.coeff r = t * F.coeff a) :
    (P - monomial q t * F).natDegree < r := by
  have hq : (monomial q t).natDegree ≤ q := natDegree_monomial_le _
  have hbound : (P - monomial q t * F).natDegree ≤ r :=
    (natDegree_sub_le _ _).trans (max_le hP (hqa ▸ natDegree_mul_le_of_le hq hF))
  have htop : (monomial q t * F).coeff r = t * F.coeff a := by
    rw [← hqa, coeff_mul_add_eq_of_natDegree_le hq hF, coeff_monomial]
    simp
  have hzero : (P - monomial q t * F).coeff r = 0 := by rw [coeff_sub, hcoeff, htop, sub_self]
  by_contra hc
  have heq := Nat.le_antisymm hbound (Nat.le_of_not_gt hc)
  have hpzero : P - monomial q t * F = 0 := leadingCoeff_eq_zero.mp (by
    unfold leadingCoeff
    rw [heq]
    exact hzero)
  exact hc (by simpa [hpzero] using hr)

theorem exists_decomposition_with_degree (A B : Fin 2 → K[X]) (β : Fin 2 → Fin 2 → K[X])
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (lim : ℕ) (hlim : pairDegree A + pairDegree B ≤ lim)
    (hβ : ∀ i j, (β i j).natDegree ≤ lim) (hw : wedge A B β = 0) :
    ∃ C D : Fin 2 → K[X], pairDegree B + pairDegree C ≤ lim ∧
      pairDegree A + pairDegree D ≤ lim ∧ ∀ i j, β i j = C i * B j + A i * D j := by
  obtain ⟨C, D, hCD⟩ := exists_integral_decomposition A B β hA hB hw
  have hAn : A 0 ≠ 0 ∨ A 1 ≠ 0 := by
    by_contra! hn
    obtain ⟨u, v, h⟩ := hA
    simp [hn.1, hn.2] at h
  have hBn : B 0 ≠ 0 ∨ B 1 ≠ 0 := by
    by_contra! hn
    obtain ⟨u, v, h⟩ := hB
    simp [hn.1, hn.2] at h
  let a := pairDegree A
  let b := pairDegree B
  have hnormalize (n : ℕ) : ∀ C D : Fin 2 → K[X],
      (∀ i j, β i j = C i * B j + A i * D j) →
      b + pairDegree C ≤ n → a + pairDegree D ≤ n →
      ∃ C' D' : Fin 2 → K[X], b + pairDegree C' ≤ lim ∧
        a + pairDegree D' ≤ lim ∧ ∀ i j, β i j = C' i * B j + A i * D' j := by
    induction n with
    | zero =>
        intro C D h hC hD
        exact ⟨C, D, hC.trans (Nat.zero_le _), hD.trans (Nat.zero_le _), h⟩
    | succ n ih =>
        intro C D h hC hD
        by_cases hl : n.succ ≤ lim
        · exact ⟨C, D, hC.trans hl, hD.trans hl, h⟩
        let c := n.succ - b
        let d := n.succ - a
        let shift := n.succ - (a + b)
        have hab : a + b ≤ lim := hlim
        have hrc : c + b = n.succ := by dsimp [c]; omega
        have hsd : a + d = n.succ := by dsimp [d]; omega
        have hc : ∀ i, (C i).natDegree ≤ c := (pairDegree_le_iff _ _).mp (by dsimp [c]; omega)
        have hd : ∀ i, (D i).natDegree ≤ d := (pairDegree_le_iff _ _).mp (by dsimp [d]; omega)
        have ha : ∀ i, (A i).natDegree ≤ a := natDegree_le_pairDegree A
        have hb : ∀ j, (B j).natDegree ≤ b := natDegree_le_pairDegree B
        have htop (i j : Fin 2) :
            (C i).coeff c * (B j).coeff b + (A i).coeff a * (D j).coeff d = 0 := by
          have hzero := coeff_eq_zero_of_natDegree_lt ((hβ i j).trans_lt (Nat.lt_of_not_ge hl))
          rw [h i j, coeff_add] at hzero
          have hCtop : (C i * B j).coeff n.succ = (C i).coeff c * (B j).coeff b := by
            rw [← hrc, coeff_mul_add_eq_of_natDegree_le (hc i) (hb j)]
          have hDtop : (A i * D j).coeff n.succ = (A i).coeff a * (D j).coeff d := by
            rw [← hsd, coeff_mul_add_eq_of_natDegree_le (ha i) (hd j)]
          rwa [hCtop, hDtop] at hzero
        obtain ⟨t, hCt, hDt⟩ := exists_scalar_of_tensor_zero
          (fun i ↦ (A i).coeff a) (fun i ↦ (B i).coeff b)
          (fun i ↦ (C i).coeff c) (fun i ↦ (D i).coeff d)
          (pair_top_coprime A hAn) (pair_top_coprime B hBn) htop
        let C' (i : Fin 2) := C i - monomial shift t * A i
        let D' (j : Fin 2) := D j - monomial shift (-t) * B j
        have hC' (i : Fin 2) : (C' i).natDegree < c :=
          degree_drop_of_top_cancel (by dsimp [c]; omega) (by dsimp [shift,c]; omega)
            (hc i) (ha i) (hCt i)
        have hD' (j : Fin 2) : (D' j).natDegree < d :=
          degree_drop_of_top_cancel (by dsimp [d]; omega) (by dsimp [shift,d]; omega)
            (hd j) (hb j) (by simpa only [neg_mul] using hDt j)
        have hCd : b + pairDegree C' ≤ n := by
          have hdeg := (pairDegree_le_iff C' (c - 1)).mpr fun i ↦ by have hi := hC' i; omega
          have hcpos : 0 < c := by dsimp [c]; omega
          omega
        have hDd : a + pairDegree D' ≤ n := by
          have hdeg := (pairDegree_le_iff D' (d - 1)).mpr fun i ↦ by have hi := hD' i; omega
          have hdpos : 0 < d := by dsimp [d]; omega
          omega
        apply ih C' D' (fun i j ↦ ?_) hCd hDd
        rw [h i j]
        dsimp only [C', D']
        rw [monomial_neg]
        ring
  exact hnormalize (max (b + pairDegree C) (a + pairDegree D)) C D hCD
    (le_max_left _ _) (le_max_right _ _)

end ProximityPrize.SubmissionLower.Koala6831Separation
