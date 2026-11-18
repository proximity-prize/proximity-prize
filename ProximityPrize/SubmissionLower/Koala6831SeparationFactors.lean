import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.PrincipalIdealDomain

namespace ProximityPrize.SubmissionLower.Koala6831SeparationFactors

open MvPolynomial
open scoped Polynomial nonZeroDivisors

variable {F : Type*} [Field F]

abbrev SeedPolynomial (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R

noncomputable def affine {R : Type*} [CommRing R] (i : Fin 2) (c d : R) :
    SeedPolynomial R := C c + C d * X i

theorem affine_eq_zero_iff (i : Fin 2) (c d : F) : affine i c d = 0 ↔ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have hc : c = 0 := by
      simpa [affine] using congrArg (MvPolynomial.eval fun _ : Fin 2 ↦ (0 : F)) h
    have hd : d = 0 := by
      simpa [affine, hc] using congrArg (MvPolynomial.eval fun _ : Fin 2 ↦ (1 : F)) h
    exact ⟨hc, hd⟩
  · rintro ⟨rfl, rfl⟩
    simp [affine]

private theorem affine_left_dvd_of_relation (a₀ a₁ b₀ b₁ : F)
    (first second : SeedPolynomial F) (hA : affine 0 a₀ a₁ ≠ 0)
    (hB : affine 1 b₀ b₁ ≠ 0)
    (rel : affine 0 a₀ a₁ * first + affine 1 b₀ b₁ * second = 0) :
    affine 0 a₀ a₁ ∣ second := by
  by_cases h₁ : a₁ = 0
  · have h₀ : a₀ ≠ 0 := fun ha ↦ hA ((affine_eq_zero_iff _ _ _).mpr ⟨ha, h₁⟩)
    refine ⟨C a₀⁻¹ * second, ?_⟩
    simp only [affine, h₁, map_zero, zero_mul, add_zero]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ h₀, map_one, one_mul]
  · let e := finSuccEquiv F 1
    let r : MvPolynomial (Fin 1) F := C (-a₀ / a₁)
    let cF : F →+* (MvPolynomial (Fin 1) F)[X] := Polynomial.C.comp MvPolynomial.C
    have ha : e (affine 0 a₀ a₁) = Polynomial.C (C a₁) * (Polynomial.X - Polynomial.C r) := by
      simp only [e, affine, map_add, map_mul,
        finSuccEquiv_apply, eval₂Hom_C, RingHom.comp_apply]
      rw [mul_sub, ← map_mul, ← map_mul, mul_div_cancel₀ _ h₁]
      simp [add_comm]
    have hb : e (affine 1 b₀ b₁) = Polynomial.C (C b₀ + C b₁ * X 0) := by
      have h' : (1 : Fin 2) = Fin.succ (0 : Fin 1) := rfl
      have hx : e (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) := by
        rw [h']
        exact finSuccEquiv_X_succ
      have hc (c : F) : e (C c) = Polynomial.C (C c) := by
        rw [show e (C c) = finSuccEquiv F 1 (C c) from rfl, finSuccEquiv_apply, eval₂Hom_C]
        rfl
      simp only [affine, map_add, map_mul, hx, hc]
    have hb₀ : C b₀ + C b₁ * (X 0 : MvPolynomial (Fin 1) F) ≠ 0 := by
      intro hz
      apply hB
      apply e.injective
      simp [hb, hz]
    have hroot : Polynomial.IsRoot (e second) r := by
      have hrel := congrArg (fun t ↦ (e t).eval r) rel
      simp only [map_add, map_mul, map_zero, ha, hb, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero,
        sub_self, mul_zero, zero_mul, zero_add] at hrel
      exact (mul_eq_zero.mp hrel).resolve_left hb₀
    obtain ⟨D, hD⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    have hinv : cF a₁ * cF a₁⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h₁, map_one]
    refine ⟨e.symm (cF a₁⁻¹ * D), e.injective ?_⟩
    rw [map_mul, ha, AlgEquiv.apply_symm_apply, hD]
    calc
      (Polynomial.X - Polynomial.C r) * D =
          (cF a₁ * cF a₁⁻¹) * ((Polynomial.X - Polynomial.C r) * D) := by rw [hinv, one_mul]
      _ = (cF a₁ * (Polynomial.X - Polynomial.C r)) * (cF a₁⁻¹ * D) := by ac_rfl

theorem factor_of_relation (a₀ a₁ b₀ b₁ : F) (first second : SeedPolynomial F)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hnonzero : a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ b₀ ≠ 0 ∨ b₁ ≠ 0)
    (rel : affine 0 a₀ a₁ * first + affine 1 b₀ b₁ * second = 0) :
    ∃ G : SeedPolynomial F, G ≠ 0 ∧
      first = affine 1 b₀ b₁ * G ∧ second = -(affine 0 a₀ a₁ * G) := by
  have impossible (hA : affine 0 a₀ a₁ = 0) (hB : affine 1 b₀ b₁ = 0) : False := by
    rcases (affine_eq_zero_iff _ _ _).mp hA with ⟨rfl, rfl⟩
    rcases (affine_eq_zero_iff _ _ _).mp hB with ⟨rfl, rfl⟩
    simp at hnonzero
  have hA : affine 0 a₀ a₁ ≠ 0 := by
    intro hz
    apply impossible hz
    rw [hz, zero_mul, zero_add] at rel
    exact (mul_eq_zero.mp rel).resolve_right hsecond
  have hB : affine 1 b₀ b₁ ≠ 0 := by
    intro hz
    refine impossible ?_ hz
    rw [hz, zero_mul, add_zero] at rel
    exact (mul_eq_zero.mp rel).resolve_right hfirst
  obtain ⟨D, hD⟩ := affine_left_dvd_of_relation a₀ a₁ b₀ b₁ first second hA hB rel
  have hfirst' : first = affine 1 b₀ b₁ * (-D) := by
    apply mul_left_cancel₀ hA
    calc
      _ = -(affine 1 b₀ b₁ * second) := eq_neg_of_add_eq_zero_left rel
      _ = _ := by rw [hD]; ring
  refine ⟨-D, ?_, hfirst', ?_⟩
  · intro h
    exact hfirst (by simpa [h] using hfirst')
  · simpa using hD

theorem separate_of_primitive_relation (a₀ a₁ b₀ b₁ : F)
    (beta first second left right : SeedPolynomial F)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hnonzero : a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ b₀ ≠ 0 ∨ b₁ ≠ 0)
    (rel : affine 0 a₀ a₁ * first + affine 1 b₀ b₁ * second = 0)
    (hbeta : beta = left * first + right * second)
    (hprimitive : ∀ G : SeedPolynomial F, G ∣ beta → G ∣ first → G ∣ second → IsUnit G) :
    ∃ c : F, c ≠ 0 ∧ first = affine 1 b₀ b₁ * C c ∧
      second = -(affine 0 a₀ a₁ * C c) := by
  obtain ⟨G, hG, h₁, h₂⟩ := factor_of_relation a₀ a₁ b₀ b₁ first second
    hfirst hsecond hnonzero rel
  have hd₁ : G ∣ first := by rw [h₁]; exact dvd_mul_left _ _
  have hd₂ : G ∣ second := by rw [h₂, dvd_neg]; exact dvd_mul_left _ _
  have hdβ : G ∣ beta := by
    rw [hbeta]
    exact dvd_add (dvd_mul_of_dvd_right hd₁ left) (dvd_mul_of_dvd_right hd₂ right)
  obtain ⟨c, hc, rfl⟩ := isUnit_iff_eq_C_of_isReduced.mp (hprimitive G hdβ hd₁ hd₂)
  exact ⟨c, hc.ne_zero, h₁, h₂⟩

section Integral

variable {R : Type*} [CommRing R] [IsDomain R] [Algebra R F] [IsFractionRing R F]

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable abbrev fractionMap : SeedPolynomial R →+* SeedPolynomial F :=
  MvPolynomial.map (algebraMap R F)

omit [IsDomain R] in
private theorem fractionMap_injective :
    Function.Injective (fractionMap (R := R) (F := F)) :=
  MvPolynomial.map_injective _ (IsFractionRing.injective R F)

private theorem clear_denominator (P : SeedPolynomial F) :
    ∃ (N : SeedPolynomial R) (d : R), d ≠ 0 ∧
      P * fractionMap (C d) = fractionMap N := by
  obtain ⟨⟨N, m⟩, h⟩ := IsLocalization.surj
    ((nonZeroDivisors R).map (C (σ := Fin 2))) P
  obtain ⟨d, hd, hdm⟩ := m.property
  refine ⟨N, d, nonZeroDivisors.ne_zero hd, ?_⟩
  simpa only [MvPolynomial.algebraMap_def, ← hdm] using h

private theorem clear_fraction_divisibility {H P : SeedPolynomial R}
    (h : fractionMap (F := F) H ∣ fractionMap P) :
    ∃ d : R, d ≠ 0 ∧ H ∣ C d * P := by
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨N, d, hd, hN⟩ := clear_denominator (R := R) Q
  refine ⟨d, hd, N, fractionMap_injective (F := F) ?_⟩
  simp only [map_mul, hQ, ← hN, mul_left_comm, mul_comm]

set_option maxHeartbeats 1200000 in

theorem primitive_fractionMap [GCDMonoid (SeedPolynomial R)]
    {beta first second : SeedPolynomial R}
    (hprimitive : ∀ D : SeedPolynomial R, D ∣ beta → D ∣ first → D ∣ second → IsUnit D)
    (G : SeedPolynomial F) (hβ : G ∣ fractionMap beta)
    (h₁ : G ∣ fractionMap first) (h₂ : G ∣ fractionMap second) : IsUnit G := by
  obtain ⟨H, m, hm, hH⟩ := clear_denominator (R := R) G
  have hmUnit : IsUnit (fractionMap (F := F) (C m)) := by
    rw [fractionMap, MvPolynomial.map_C]
    apply IsUnit.map C
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hm
  have hHG : fractionMap H ∣ G := by
    rw [← hH]
    simpa using mul_dvd_mul (dvd_refl G) (isUnit_iff_dvd_one.mp hmUnit)
  obtain ⟨dβ, hdβ, h'β⟩ := clear_fraction_divisibility (hHG.trans hβ)
  obtain ⟨d₁, hd₁, h'₁⟩ := clear_fraction_divisibility (hHG.trans h₁)
  obtain ⟨d₂, hd₂, h'₂⟩ := clear_fraction_divisibility (hHG.trans h₂)
  let d := dβ * d₁ * d₂
  have hd : d ≠ 0 := mul_ne_zero (mul_ne_zero hdβ hd₁) hd₂
  have scale (P : SeedPolynomial R) (q r s : R) (hdiv : H ∣ C q * P) :
      H ∣ C (q * r * s) * P := by
    calc
      H ∣ C (r * s) * (C q * P) := dvd_mul_of_dvd_right hdiv _
      _ = _ := by simp only [map_mul, mul_left_comm, mul_comm]
  obtain ⟨H', D', hH', hD', hcoprime⟩ := extract_gcd H (C d)
  let M := gcd H (C d)
  have hCd : (C d : SeedPolynomial R) ≠ 0 := by simpa using hd
  have hM : M ≠ 0 := gcd_ne_zero_of_right hCd
  have cancel {P : SeedPolynomial R} (h : H ∣ C d * P) : H' ∣ P := by
    have hscaled : M * H' ∣ M * (D' * P) := by
      calc
        M * H' = H := hH'.symm
        _ ∣ C d * P := h
        _ = (M * D') * P := congrArg (· * P) hD'
        _ = _ := mul_assoc _ _ _
    exact (gcd_isUnit_iff_isRelPrime.mp hcoprime).dvd_of_dvd_mul_left
      ((mul_dvd_mul_iff_left hM).mp hscaled)
  have hH'Unit : IsUnit H' := hprimitive H'
    (cancel (scale beta dβ d₁ d₂ h'β))
    (cancel (by simpa only [d, mul_left_comm, mul_comm, mul_assoc] using scale first d₁ dβ d₂ h'₁))
    (cancel (by simpa only [d, mul_left_comm, mul_comm, mul_assoc] using scale second d₂ dβ d₁ h'₂))
  obtain ⟨c, _, hc⟩ := (dvd_C_iff_exists hd).mp (gcd_dvd_right H (C d))
  have hc₀ : c ≠ 0 := by
    intro hz
    apply hM
    exact hc.trans (by simp [hz])
  have hMUnit : IsUnit (fractionMap (F := F) M) := by
    rw [show M = C c from hc, fractionMap, MvPolynomial.map_C]
    apply IsUnit.map C
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hc₀
  have hHUnit : IsUnit (fractionMap (F := F) H) := by
    rw [hH', map_mul]
    exact hMUnit.mul (hH'Unit.map fractionMap)
  exact isUnit_of_mul_isUnit_left (hH.symm ▸ hHUnit)

omit [IsDomain R] in
theorem coeff_affine_zero (i : Fin 2) (c d : R) :
    (affine i c d).coeff 0 = c := by simp [affine, coeff_X]

omit [IsDomain R] in
theorem coeff_affine_one (i : Fin 2) (c d : R) :
    (affine i c d).coeff (Finsupp.single i 1) = d := by
  have hi : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro h
    simpa using congrArg (fun x : Fin 2 →₀ ℕ ↦ x i) h
  simp [affine, coeff_X, hi]

omit [IsDomain R] in
private theorem affine_of_fractionMap_eq_affine (i : Fin 2)
    {P : SeedPolynomial R} {a b : F} (h : fractionMap P = affine i a b) :
    P = affine i (P.coeff 0) (P.coeff (Finsupp.single i 1)) := by
  have h₀ := congrArg (fun Q : SeedPolynomial F ↦ Q.coeff 0) h
  have h₁ := congrArg (fun Q : SeedPolynomial F ↦ Q.coeff (Finsupp.single i 1)) h
  simp only [fractionMap, coeff_map, coeff_affine_zero] at h₀
  simp only [fractionMap, coeff_map, coeff_affine_one] at h₁
  apply fractionMap_injective (F := F)
  simpa only [fractionMap, affine, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, h₀, h₁]
    using h

private theorem affine_mul_C {i : Fin 2} (a b c : F) :
    affine i a b * C c = affine i (a * c) (b * c) := by
  simp only [affine, map_mul]
  ring

omit [IsDomain R] in
private theorem normalize_affine [GCDMonoid R] [IsBezout R]
    (i : Fin 2) (a b : R) (h : affine i a b ≠ 0) :
    ∃ (A : Fin 2 → R) (d : R), d ≠ 0 ∧ IsCoprime (A 0) (A 1) ∧
      affine i a b = C d * affine i (A 0) (A 1) := by
  obtain ⟨a', b', ha, hb, hcoprime⟩ := extract_gcd a b
  have hg : gcd a b ≠ 0 := by
    intro hz
    apply h
    have ha₀ : a = 0 := by rw [ha, hz, zero_mul]
    have hb₀ : b = 0 := by rw [hb, hz, zero_mul]
    simp [affine, ha₀, hb₀]
  refine ⟨![a', b'], gcd a b, hg, ?_, ?_⟩
  · simpa using (gcd_isUnit_iff_isRelPrime.mp hcoprime).isCoprime
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, affine, mul_add, ← mul_assoc, ← map_mul]
    rw [← ha, ← hb]

theorem integral_separation [GCDMonoid R] [IsBezout R] [GCDMonoid (SeedPolynomial R)]
    (a₀ a₁ b₀ b₁ : F) (beta first second : SeedPolynomial R) (left right : SeedPolynomial F)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hnonzero : a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ b₀ ≠ 0 ∨ b₁ ≠ 0)
    (rel : affine 0 a₀ a₁ * fractionMap first + affine 1 b₀ b₁ * fractionMap second = 0)
    (hbeta : fractionMap beta = left * fractionMap first + right * fractionMap second)
    (hprimitive : ∀ D : SeedPolynomial R, D ∣ beta → D ∣ first → D ∣ second → IsUnit D) :
    ∃ (A B : Fin 2 → R) (d₀ d₁ : R), d₀ ≠ 0 ∧ d₁ ≠ 0 ∧
      IsCoprime (A 0) (A 1) ∧ IsCoprime (B 0) (B 1) ∧
      first = C d₀ * affine 1 (B 0) (B 1) ∧ second = -(C d₁ * affine 0 (A 0) (A 1)) := by
  have hfirst' : fractionMap (F := F) first ≠ 0 :=
    fun h ↦ hfirst (fractionMap_injective (F := F) (by simpa using h))
  have hsecond' : fractionMap (F := F) second ≠ 0 :=
    fun h ↦ hsecond (fractionMap_injective (F := F) (by simpa using h))
  obtain ⟨c, _, h₁, h₂⟩ := separate_of_primitive_relation a₀ a₁ b₀ b₁
    (fractionMap beta) (fractionMap first) (fractionMap second) left right
    hfirst' hsecond' hnonzero rel hbeta (primitive_fractionMap hprimitive)
  have h₁' := affine_of_fractionMap_eq_affine 1 (h₁.trans (affine_mul_C _ _ _))
  have h₂' := affine_of_fractionMap_eq_affine 0
    (show fractionMap (-second) = affine 0 (a₀ * c) (a₁ * c) by
      rw [map_neg, h₂, neg_neg, affine_mul_C])
  obtain ⟨B, d₀, hd₀, hB, he₀⟩ := normalize_affine 1 _ _ (h₁' ▸ hfirst)
  obtain ⟨A, d₁, hd₁, hA, he₁⟩ := normalize_affine 0 _ _
    (h₂' ▸ (neg_ne_zero.mpr hsecond))
  refine ⟨A, B, d₀, d₁, hd₀, hd₁, hA, hB, h₁'.trans he₀, ?_⟩
  simpa only [neg_neg] using congrArg Neg.neg (h₂'.trans he₁)

end Integral

end ProximityPrize.SubmissionLower.Koala6831SeparationFactors
