import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp

/-! The mixed seed degree charged when removing genuine polynomial multiples
in the 6402 interpolation. Scaling R by Z^q reduces additivity to the
promoted weighted degree on Y and Z. -/

namespace ProximityPrize.SubmissionBinaryLower.B6402MixedDegree
open Polynomial B6401ContactKerD B6401QuotInterp
set_option autoImplicit false

variable {K : Type*} [Field K]
local notation "CP" => ContactPoly (Polynomial K)

noncomputable def slopeScale (q : ℕ) : BiPoly (Polynomial K) :=
  C (C ((Polynomial.X : Polynomial K)^q))

noncomputable def tilt (q : ℕ) (f : CP) : CP :=
  f.comp (C (slopeScale q)*Polynomial.X)

noncomputable def mixed (q : ℕ) (f : CP) : ℕ := wYZ q (tilt q f)

theorem coeff_tilt (q : ℕ) (f : CP) (k j i : ℕ) :
    ((((tilt q f).coeff k).coeff j).coeff i) =
      (((f.coeff k).coeff j).coeff i) * (Polynomial.X : Polynomial K)^(q*k) := by
  unfold tilt slopeScale
  rw [comp_C_mul_X_coeff,← C_pow,← C_pow,coeff_mul_C,coeff_mul_C,←pow_mul]

theorem tilt_ne_zero (q : ℕ) {f : CP} (hf : f≠0) : tilt q f ≠ 0 := by
  have hs : slopeScale (K:=K) q ≠ 0 := by
    unfold slopeScale; exact C_ne_zero.mpr (C_ne_zero.mpr (pow_ne_zero _ X_ne_zero))
  intro h
  apply hf
  exact (Polynomial.comp_C_mul_X_eq_zero_iff (p:=f) (mem_nonZeroDivisors_of_ne_zero hs)).mp h

theorem mixed_mul (q : ℕ) {f g : CP} (hf : f≠0) (hg : g≠0) :
    mixed q (f*g) = mixed q f + mixed q g := by
  unfold mixed tilt
  rw [mul_comp]
  exact wYZ_mul q (tilt_ne_zero q hf) (tilt_ne_zero q hg)

theorem mixed_le_iff (q bound : ℕ) (f : CP) :
    mixed q f ≤ bound ↔
      ∀ k j i, ((f.coeff k).coeff j).coeff i ≠ 0 →
        (((f.coeff k).coeff j).coeff i).natDegree + q*(j+k) ≤ bound := by
  unfold mixed
  rw [wYZ_le_iff]
  constructor
  · intro h k j i hn
    have hc : (((tilt q f).coeff k).coeff j).coeff i ≠ 0 := by
      rw [coeff_tilt]; exact mul_ne_zero hn (pow_ne_zero _ X_ne_zero)
    specialize h k j i hc
    rw [coeff_tilt,natDegree_mul hn (pow_ne_zero _ X_ne_zero),natDegree_X_pow] at h
    simpa only [Nat.mul_add,Nat.add_assoc,Nat.add_comm (q*j) (q*k)] using h
  · intro h k j i hn
    rw [coeff_tilt] at hn ⊢
    have hc := left_ne_zero_of_mul hn
    specialize h k j i hc
    rw [natDegree_mul hc (pow_ne_zero _ X_ne_zero),natDegree_X_pow]
    simpa only [Nat.mul_add,Nat.add_assoc,Nat.add_comm (q*j) (q*k)] using h

theorem at_most_input (q : ℕ) (f : CP) :
    mixed q f ≤ wYZ q f + q*f.natDegree := by
  rw [mixed_le_iff]
  intro k j i hn
  have hcoeff : f.coeff k ≠ 0 := by intro h; simp [h] at hn
  have hk := le_natDegree_of_ne_zero hcoeff
  have hseed := (wYZ_le_iff q _ f).mp le_rfl k j i hn
  rw [Nat.mul_add]
  have hkr := Nat.mul_le_mul_left q hk
  omega

/-- The hard coefficient of Y^4 R supplies the lower endpoint of the price test. -/
theorem quartic_lower (q : ℕ) (f : CP) (hd : (f.coeff 1).natDegree=4) :
    5*q ≤ mixed q f := by
  have ha : f.coeff 1 ≠ 0 := by intro he; simp [he] at hd
  have hc : (f.coeff 1).coeff 4 ≠ 0 := by
    simpa only [←hd,coeff_natDegree] using leadingCoeff_ne_zero.mpr ha
  let a := (f.coeff 1).coeff 4
  have hz : a.coeff a.natDegree ≠ 0 := by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hc
  have h := (mixed_le_iff q _ f).mp le_rfl 1 4 a.natDegree hz
  omega

theorem cofactor_cap (q T : ℕ) {f g : CP} (hf : f≠0) (hg : g≠0)
    (h : mixed q (f*g) ≤ T) : mixed q g ≤ T-mixed q f := by
  rw [mixed_mul q hf hg] at h; omega

lemma coordinate_bound {F : Type*} [Field F] [CharP F 2] {wY W s dy D : ℕ} (hwY : 0 < wY)
    (c : KerDIdx wY W s → Polynomial F)
    (hw : mixed dy (∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1) ≤ D) :
    ∀ e : KerDIdx wY W s, c e ≠ 0 → (c e).natDegree + dy * (2 * e.1.2.2.1 + e.1.2.1 + e.1.1) ≤ D := by
  intro ⟨⟨k, r, b, a⟩, he⟩ hne
  have hr := ((mem_kerDIdxFinset_iff wY W s hwY k r b a).mp he).1
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · have hcoeff : (((∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1).coeff k).coeff (2 * b)).coeff (2 * a) =
        c ⟨(k, 0, b, a), he⟩ := by
      rw [coeff_sum_kerDBasisPoly hwY]; simp [he]
    have hle := (mixed_le_iff dy D _).mp hw k (2 * b) (2 * a) (hcoeff.symm ▸ hne)
    rw [hcoeff] at hle; simpa using hle
  · have hcoeff : (((∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1).coeff k).coeff (2 * b + 1)).coeff (2 * a) =
        c ⟨(k, 1, b, a), he⟩ := by
      rw [coeff_sum_kerDBasisPoly hwY]
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simp [h1, h2, h3, h4, he]
    have hle := (mixed_le_iff dy D _).mp hw k (2 * b + 1) (2 * a) (hcoeff.symm ▸ hne)
    rw [hcoeff] at hle; simpa using hle

lemma sum_bound {F : Type*} [Field F] [CharP F 2] {wY W s dy D : ℕ} (hwY : 0 < wY)
    (c : KerDIdx wY W s → Polynomial F)
    (hc : ∀ e : KerDIdx wY W s, c e ≠ 0 → (c e).natDegree + dy * (2 * e.1.2.2.1 + e.1.2.1 + e.1.1) ≤ D) :
    mixed dy (∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1) ≤ D := by
  rw [mixed_le_iff]
  intro k j i hnz
  rw [coeff_sum_kerDBasisPoly hwY] at hnz ⊢
  by_cases h00 : j % 2 = 0 ∧ i % 2 = 0
  · simp only [h00, and_self, ↓reduceIte] at hnz ⊢
    split_ifs at hnz ⊢ with hm1
    · have hle := hc ⟨(k, 0, j / 2, i / 2), hm1⟩ hnz
      dsimp only at hle
      have hj : 2 * (j / 2) + 0 = j := by omega
      rw [hj] at hle; exact hle
    · exact absurd rfl hnz
  · simp only [h00, ↓reduceIte] at hnz ⊢
    by_cases h10 : j % 2 = 1 ∧ i % 2 = 0
    · simp only [h10, and_self, ↓reduceIte] at hnz ⊢
      split_ifs at hnz ⊢ with hm2
      · have hle := hc ⟨(k, 1, j / 2, i / 2), hm2⟩ hnz
        dsimp only at hle
        have hj : 2 * (j / 2) + 1 = j := by omega
        rw [hj] at hle; exact hle
      · exact absurd rfl hnz
    · simp only [h10, ↓reduceIte] at hnz ⊢
      by_cases h01 : j % 2 = 0 ∧ i % 2 = 1 ∧ 0 < k
      · simp only [h01, and_self, ↓reduceIte] at hnz ⊢
        split_ifs at hnz ⊢ with hm3
        · have hle := hc ⟨(k - 1, 1, j / 2, i / 2), hm3⟩ hnz
          dsimp only at hle
          have hj : 2 * (j / 2) + 1 + (k-1) = j+k := by omega
          rw [hj] at hle; exact hle
        · exact absurd rfl hnz
      · simp only [h01, ↓reduceIte] at hnz; exact absurd rfl hnz

#print axioms coordinate_bound
#print axioms sum_bound
#print axioms mixed_mul
#print axioms mixed_le_iff
end ProximityPrize.SubmissionBinaryLower.B6402MixedDegree
