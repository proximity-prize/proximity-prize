import ProximityPrize.SubmissionLower.ContactBaseIdealAgreement6676Research
import ProximityPrize.SubmissionLower.ContactBaseIdealWeights6676Research
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research
import ProximityPrize.SubmissionLower.ContactGenericSurface

/-! .




 -/

namespace ProximityPrize.SubmissionLower.ContactBaseIdealAgreementFlags6676Research

open ContactTaylorNumerators ContactBaseIdealAlgebra6676Research
open ContactBaseIdealCoefficients6676Research ContactBaseIdealWeights6676Research
open ContactBaseIdealAgreement6676Research ContactPost6464MinkowskiRecurrenceResearch
open ContactFlagBezout6543Research

noncomputable section

variable {K : Type*} [Field K]

theorem weightBound_C (w : Fin 4 → ℕ) (c : K) :
    WeightBound w (MvPolynomial.C c : Poly K) 0 :=
  Or.inr (by simp only [wt_C, Nat.cast_zero, le_refl])

theorem weightBound_pow {w : Fin 4 → ℕ} {P : Poly K} {a : ℤ}
    (hP : WeightBound w P a) (n : ℕ) : WeightBound w (P ^ n) (n * a) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul, Nat.cast_one] using
      (WeightBound.natCast (w := w) (K := K) 1)
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hP using 1
    push_cast
    ring

theorem weightBound_sum {w : Fin 4 → ℕ} {a : ℤ} (I : Finset ℕ) (P : ℕ → Poly K)
    (hP : ∀ i ∈ I, WeightBound w (P i) a) : WeightBound w (∑ i ∈ I, P i) a := by
  classical
  induction I using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact (hP i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem weightBound_shift (w : Fin 4 → ℕ) (hX : w 0 = 0) (x : K) :
    WeightBound w (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly K) 0 :=
  (weightBound_C w x).sub (Or.inr (by simp only [wt_X, hX, Nat.cast_zero, le_refl]))

theorem agreementLow_weightBound (w : Fin 4 → ℕ) (hX : w 0 = 0)
    (hY : w 1 ≤ 1) (hR : w 2 = 1) (hZ : w 3 ≤ 1)
    (c : ℕ → K) (x u₀ u₁ : K) : WeightBound w (agreementLow c x u₀ u₁) 1 := by
  have hvar (i : Fin 4) (hi : w i ≤ 1) :
      WeightBound w (MvPolynomial.X i : Poly K) 1 := by
    right
    rw [wt_X]
    exact_mod_cast hi
  have h₀ := (weightBound_C w (c 0)).mul (hvar 1 hY)
  have h₁ := ((weightBound_C w (c 1)).mul (hvar 2 (by omega))).mul (weightBound_shift w hX x)
  have hseed := ((weightBound_C w u₀).mono (by norm_num : (0 : ℤ) ≤ 1)).add
    (by simpa only [add_zero] using (hvar 3 hZ).mul (weightBound_C w u₁))
  simpa only [agreementLow, affineSeedPolynomial, zero_add, add_zero] using (h₀.add h₁).sub hseed

/-- . -/
theorem agreementCoefficients_weightBound (w : Fin 4 → ℕ) (t : ℕ)
    (hX : w 0 = 0) (hY : w 1 = t) (hR : w 2 = 1) (hZ : w 3 ≤ 1) (ht : t ≤ 1)
    (F : Poly K) (C : ℤ) (hF : WeightBound w F C) (d : ℕ) (hd : 2 ≤ d)
    (c : ℕ → K) (x u₀ u₁ : K) (j : ℕ) :
    WeightBound w (agreementCoefficients F d c x u₀ u₁ j)
      ((d + 1 : ℕ) * (C - 1) + 1 + (d - 1 : ℕ) * (1 - (t : ℤ)) - j * (2 - (t : ℤ))) := by
  have ht' : (t : ℤ) ≤ 1 := by exact_mod_cast ht
  have hH : WeightBound w (polyH K F) (C - 1) := by
    simpa only [polyH, hR, Nat.cast_one] using hF.pderiv (2 : Fin 4)
  unfold agreementCoefficients
  apply WeightBound.add
  · by_cases hj : j = 0
    · subst j
      rw [if_pos rfl]
      apply ((weightBound_pow hH (d + 1)).mul
        (agreementLow_weightBound w hX (by omega) hR hZ c x u₀ u₁)).mono
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      have hn : (0 : ℤ) ≤ (d - 1 : ℕ) := Nat.cast_nonneg _
      nlinarith
    · rw [if_neg hj]
      exact Or.inl rfl
  · apply weightBound_sum
    intro n hn
    have hn' : n + 2 ≤ d := by have := Finset.mem_range.mp hn; omega
    have he : ((d - (n + 2) + 3 : ℕ) : ℤ) = (d : ℤ) - n + 1 := by
      push_cast [Nat.cast_sub hn']
      ring
    have hn'' : (n : ℤ) + 2 ≤ d := by exact_mod_cast hn'
    have hd' : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
    have hterm := (((weightBound_C w (c (n + 2))).mul
      (weightBound_pow hH (d - (n + 2) + 3))).mul
        (baseCoefficients_weightBound w t hX hY hR ht F C hF n j)).mul
          (weightBound_pow (weightBound_shift w hX x) (n + 2))
    apply hterm.mono
    rw [he, hd']
    push_cast
    nlinarith

theorem agreementCoefficients_support_bounds (F : Poly K) (s M L : ℕ)
    (hR : F.degreeOf (2 : Fin 4) ≤ s) (hYR : wt ![0, 1, 1, 0] F ≤ M)
    (hAll : wt ![0, 1, 1, 1] F ≤ L) (d : ℕ) (hd : 2 ≤ d)
    (c : ℕ → K) (x u₀ u₁ : K) (j : ℕ) :
    (agreementCoefficients F d c x u₀ u₁ j).degreeOf (2 : Fin 4) ≤ (d + 1) * s - 1 - 2 * j ∧
    wt ![0, 1, 1, 0] (agreementCoefficients F d c x u₀ u₁ j) ≤ (d + 1) * M - d - j ∧
    wt ![0, 1, 1, 1] (agreementCoefficients F d c x u₀ u₁ j) ≤ (d + 1) * L - d - j := by
  have hcoord (P : Poly K) : wt (Pi.single (2 : Fin 4) 1) P = P.degreeOf (2 : Fin 4) := by
    rw [wt, MvPolynomial.weightedTotalDegree, MvPolynomial.degreeOf_eq_sup]
    apply congrArg (fun f : (Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
    funext e
    exact Finsupp.weight_single_one_apply _ e
  have hbound (w : Fin 4 → ℕ) (t : ℕ) (hX : w 0 = 0) (hY : w 1 = t)
      (hR' : w 2 = 1) (hZ : w 3 ≤ 1) (ht : t ≤ 1) (N : ℕ) (hF : wt w F ≤ N) :=
    agreementCoefficients_weightBound w t hX hY hR' hZ ht F N
      (Or.inr (by exact_mod_cast hF)) d hd c x u₀ u₁ j
  constructor
  · have h := hbound (Pi.single (2 : Fin 4) 1) 0 (by simp) (by simp) (by simp)
      (by simp) (by omega) s (by simpa only [hcoord] using hR)
    rcases h with hz | hb
    · simp [hz]
    · rw [hcoord] at hb
      have he : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
      rw [he] at hb
      push_cast at hb
      have hh : ((agreementCoefficients F d c x u₀ u₁ j).degreeOf (2 : Fin 4) : ℤ) + 1 +
          2 * j ≤ (d + 1 : ℕ) * s := by push_cast; nlinarith
      have hn : (agreementCoefficients F d c x u₀ u₁ j).degreeOf (2 : Fin 4) + 1 +
          2 * j ≤ (d + 1) * s := by exact_mod_cast hh
      omega
  · have cumulative (w : Fin 4 → ℕ) (hX : w 0 = 0) (hY : w 1 = 1)
        (hR' : w 2 = 1) (hZ : w 3 ≤ 1) (N : ℕ) (hF : wt w F ≤ N) :
        wt w (agreementCoefficients F d c x u₀ u₁ j) ≤ (d + 1) * N - d - j := by
      rcases hbound w 1 hX hY hR' hZ le_rfl N hF with hz | hb
      · simp [hz, wt, MvPolynomial.weightedTotalDegree]
      · have hh : (wt w (agreementCoefficients F d c x u₀ u₁ j) : ℤ) + d + j ≤
            (d + 1 : ℕ) * N := by push_cast at hb ⊢; nlinarith
        have hn : wt w (agreementCoefficients F d c x u₀ u₁ j) + d + j ≤
            (d + 1) * N := by exact_mod_cast hh
        omega
    exact ⟨cumulative _ rfl rfl rfl (by decide) M hYR,
      cumulative _ rfl rfl rfl (by decide) L hAll⟩

/-- . -/
def coefficientFlag (a b s d j : ℕ) : FlagDegree :=
  ⟨(d + 1) * a, 1 + (d + 1) * b - d + j, (d + 1) * s - 1 - 2 * j⟩

def hFlag (a b s : ℕ) : FlagDegree := ⟨a, b, s - 1⟩
def gFlag (a b s : ℕ) : FlagDegree := ⟨a, b - 1, s + 1⟩
def directionFlag (a b s : ℕ) : FlagDegree := ⟨2 * a, 2 * b - 1, 2 * s - 1⟩

theorem coefficientFlag_cumulative (a b s d j : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s)
    (hj : j < d) :
    (coefficientFlag a b s d j).all = (d + 1) * s - 1 - 2 * j ∧
    (coefficientFlag a b s d j).yz + (coefficientFlag a b s d j).all =
      (d + 1) * (b + s) - d - j ∧
    (coefficientFlag a b s d j).zOnly + (coefficientFlag a b s d j).yz +
      (coefficientFlag a b s d j).all = (d + 1) * (a + b + s) - d - j := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
  simp only [coefficientFlag, Nat.succ_eq_add_one, Nat.mul_add, Nat.add_mul,
    Nat.mul_one, Nat.one_mul]
  exact ⟨trivial, by omega, by omega⟩

theorem coefficientFlag_nonnegative_form (a b s d j : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s)
    (hj : j < d) : coefficientFlag a b s d j =
      ⟨(d + 1) * a, (d + 1) * (b - 1) + 2 + j,
        (d + 1) * (s - 2) + 3 + 2 * (d - 1 - j)⟩ := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
  dsimp only [coefficientFlag]
  congr 1 <;> simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_mul, Nat.mul_one,
    Nat.one_mul, Nat.add_sub_cancel_left] <;> omega

/-- . -/
theorem coefficientFlag_add_baseMonomial (a b s d j : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s)
    (hj : j < d) :
    coefficientFlag a b s d j + (d - 1 - j) • hFlag a b s + j • gFlag a b s =
      unitYZFlag + d • directionFlag a b s := by
  rw [coefficientFlag_nonnegative_form a b s d j hb hs hj]
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
  have hk : j + 1 + k - 1 - j = k := by omega
  have hs' : 2 + s - 1 = 1 + s := by omega
  have hb' : 2 * (1 + b) - 1 = 1 + 2 * b := by omega
  have hs'' : 2 * (2 + s) - 1 = 3 + 2 * s := by omega
  simp only [hk, hFlag, gFlag, directionFlag, unitYZFlag, Nat.add_sub_cancel_left,
    hs', hb', hs'']
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  congr 1 <;> simp only [add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
    <;> dsimp <;> ring

/-- . -/
theorem agreementCoefficients_in_flag (F : Poly K) (a b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s)
    (hR : F.degreeOf (2 : Fin 4) ≤ s) (hYR : wt ![0, 1, 1, 0] F ≤ b + s)
    (hAll : wt ![0, 1, 1, 1] F ≤ a + b + s) (d : ℕ) (hd : 2 ≤ d)
    (c : ℕ → K) (x u₀ u₁ : K) (j : ℕ) (hj : j < d) :
    ∀ e ∈ (agreementCoefficients F d c x u₀ u₁ j).support,
      e 2 ≤ (coefficientFlag a b s d j).all ∧
      e 1 + e 2 ≤ (coefficientFlag a b s d j).yz + (coefficientFlag a b s d j).all ∧
      e 1 + e 2 + e 3 ≤ (coefficientFlag a b s d j).zOnly +
        (coefficientFlag a b s d j).yz + (coefficientFlag a b s d j).all := by
  intro e he
  obtain ⟨hr, hyr, ht⟩ := agreementCoefficients_support_bounds F s (b + s) (a + b + s)
    hR hYR hAll d hd c x u₀ u₁ j
  obtain ⟨fr, fyr, ft⟩ := coefficientFlag_cumulative a b s d j hb hs hj
  rw [ft, fyr, fr]
  have heR := (MvPolynomial.le_degreeOf_of_mem_support (2 : Fin 4) he).trans hr
  have heYR := (MvPolynomial.le_weightedTotalDegree ![0, 1, 1, 0] he).trans hyr
  have heT := (MvPolynomial.le_weightedTotalDegree ![0, 1, 1, 1] he).trans ht
  rw [ContactFactorCaps.weight_fin4] at heYR heT
  change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 0 ≤ _ at heYR
  change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 1 ≤ _ at heT
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add] at heYR heT
  exact ⟨heR, heYR, heT⟩

/-- . -/
theorem surfaceMap_agreementCoefficients_in_flag {Ω : Type*} [Field Ω]
    (φ : Polynomial K →+* Ω) (F : Poly K) (a b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s)
    (hR : F.degreeOf (2 : Fin 4) ≤ s) (hYR : wt ![0, 1, 1, 0] F ≤ b + s)
    (hAll : wt ![0, 1, 1, 1] F ≤ a + b + s) (d : ℕ) (hd : 2 ≤ d)
    (c : ℕ → K) (x u₀ u₁ : K) (j : ℕ) (hj : j < d) :
    PolynomialInFlag (coefficientFlag a b s d j)
      (ContactGenericSurface.surfaceMap φ (agreementCoefficients F d c x u₀ u₁ j)) := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (ContactGenericSurface.support_surfaceMap_subset φ _ he)
  exact agreementCoefficients_in_flag F a b s hb hs hR hYR hAll d hd c x u₀ u₁ j hj q hq

/-- . -/
theorem surfaceMap_agreementNumerator_eq_coefficient_sum {Ω : Type*} [Field Ω]
    (φ : Polynomial K →+* Ω) (F : Poly K) (d : ℕ) (hd : 2 ≤ d)
    (c : ℕ → K) (x u₀ u₁ : K) :
    ContactGenericSurface.surfaceMap φ (agreementNumerator F d c x u₀ u₁) =
      ∑ j ∈ Finset.range d, ContactGenericSurface.surfaceMap φ (polyH K F) ^ (d - 1 - j) *
        ContactGenericSurface.surfaceMap φ (polyG K F) ^ j *
          ContactGenericSurface.surfaceMap φ (agreementCoefficients F d c x u₀ u₁ j) := by
  rw [agreementNumerator_eq_coefficient_sum F d hd c x u₀ u₁]
  simp only [map_sum, map_mul, map_pow]

end

end ProximityPrize.SubmissionLower.ContactBaseIdealAgreementFlags6676Research
