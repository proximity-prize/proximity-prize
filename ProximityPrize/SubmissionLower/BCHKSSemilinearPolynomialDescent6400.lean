import ProximityPrize.SubmissionLower.BCHKSScalarCyclicCompatibilityExact6400

/-!
# Semilinear polynomial division by cyclic compatibility

Exact scalar compatibility is lifted coefficient by coefficient.  At every
step the top polynomial compatibility coefficient supplies the scalar needed
to cancel the current leading term.  Compatibility survives subtraction and
the residual degree strictly drops, so well-founded recursion produces a
remainder below the common degree of the two semilinear coefficient lanes.
-/

open scoped BigOperators

namespace ProximityPrize.SubmissionLower.BCHKSSemilinearPolynomialDescent6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSInhomogeneousCyclicCompatibility6400
open BCHKSScalarCyclicCompatibilityExact6400
open BCHKSHilbert90FiniteSeeds6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem coeff_mul_six_at_natDegree_sum
    (P₀ P₁ P₂ P₃ P₄ P₅ : IRSProfile.Field[X])
    (h₀ : P₀ ≠ 0) (h₁ : P₁ ≠ 0) (h₂ : P₂ ≠ 0)
    (h₃ : P₃ ≠ 0) (h₄ : P₄ ≠ 0) (h₅ : P₅ ≠ 0) :
    (P₀ * P₁ * P₂ * P₃ * P₄ * P₅).coeff
        (P₀.natDegree + P₁.natDegree + P₂.natDegree +
          P₃.natDegree + P₄.natDegree + P₅.natDegree) =
      P₀.leadingCoeff * P₁.leadingCoeff * P₂.leadingCoeff *
        P₃.leadingCoeff * P₄.leadingCoeff * P₅.leadingCoeff := by
  have h₀₁ : P₀ * P₁ ≠ 0 := mul_ne_zero h₀ h₁
  have h₀₁₂ : P₀ * P₁ * P₂ ≠ 0 := mul_ne_zero h₀₁ h₂
  have h₀₁₂₃ : P₀ * P₁ * P₂ * P₃ ≠ 0 := mul_ne_zero h₀₁₂ h₃
  have h₀₁₂₃₄ : P₀ * P₁ * P₂ * P₃ * P₄ ≠ 0 :=
    mul_ne_zero h₀₁₂₃ h₄
  have hdegree :
      (P₀ * P₁ * P₂ * P₃ * P₄ * P₅).natDegree =
        P₀.natDegree + P₁.natDegree + P₂.natDegree +
          P₃.natDegree + P₄.natDegree + P₅.natDegree := by
    rw [Polynomial.natDegree_mul h₀₁₂₃₄ h₅,
      Polynomial.natDegree_mul h₀₁₂₃ h₄,
      Polynomial.natDegree_mul h₀₁₂ h₃,
      Polynomial.natDegree_mul h₀₁ h₂,
      Polynomial.natDegree_mul h₀ h₁]
  rw [← hdegree, Polynomial.coeff_natDegree]
  simp only [Polynomial.leadingCoeff_mul]

theorem coeff_mul_six_at_five_mul_add
    (P₀ P₁ P₂ P₃ P₄ P₅ : IRSProfile.Field[X]) (d n : Nat)
    (h₀ : P₀ ≠ 0) (h₁ : P₁ ≠ 0) (h₂ : P₂ ≠ 0)
    (h₃ : P₃ ≠ 0) (h₄ : P₄ ≠ 0) (h₅ : P₅ ≠ 0)
    (hd₀ : P₀.natDegree = d) (hd₁ : P₁.natDegree = d)
    (hd₂ : P₂.natDegree = d) (hd₃ : P₃.natDegree = d)
    (hd₄ : P₄.natDegree = d) (hn₅ : P₅.natDegree = n) :
    (P₀ * P₁ * P₂ * P₃ * P₄ * P₅).coeff (5 * d + n) =
      P₀.leadingCoeff * P₁.leadingCoeff * P₂.leadingCoeff *
        P₃.leadingCoeff * P₄.leadingCoeff * P₅.leadingCoeff := by
  have h := coeff_mul_six_at_natDegree_sum
    P₀ P₁ P₂ P₃ P₄ P₅ h₀ h₁ h₂ h₃ h₄ h₅
  rw [hd₀, hd₁, hd₂, hd₃, hd₄, hn₅] at h
  have hindex : d + d + d + d + d + n = 5 * d + n := by omega
  rw [hindex] at h
  exact h

theorem koalaFrobeniusConjugate_leadingCoeff_iterate6400
    (P : IRSProfile.Field[X]) (n : Nat) :
    (koalaFrobeniusConjugate n P).leadingCoeff =
      (koalaSexticFrobenius^[n]) P.leadingCoeff := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [koalaFrobeniusConjugate, Polynomial.leadingCoeff_map, ih]
      simp only [Function.iterate_succ_apply']
      rfl

theorem koalaFrobeniusConjugate_leadingCoeff_scalar6400
    (P : IRSProfile.Field[X]) (i : Fin 6) :
    (koalaFrobeniusConjugate i.1 P).leadingCoeff =
      koalaScalarConjugate6400 i P.leadingCoeff := by
  rw [koalaFrobeniusConjugate_leadingCoeff_iterate6400]
  have h := koalaFrobeniusMonoidCharacter6400_eq_iterate i P.leadingCoeff
  change koalaFrobeniusAlgCharacter6400 i P.leadingCoeff =
    (koalaSexticFrobenius^[i.1]) P.leadingCoeff at h
  simpa only [koalaScalarConjugate6400] using h.symm

@[simp] theorem koalaFrobeniusConjugate_leadingCoeff_zero6400
    (P : IRSProfile.Field[X]) :
    (koalaFrobeniusConjugate 0 P).leadingCoeff =
      koalaScalarConjugate6400 0 P.leadingCoeff := by
  simpa using koalaFrobeniusConjugate_leadingCoeff_scalar6400 P (0 : Fin 6)

@[simp] theorem koalaFrobeniusConjugate_leadingCoeff_one6400
    (P : IRSProfile.Field[X]) :
    (koalaFrobeniusConjugate 1 P).leadingCoeff =
      koalaScalarConjugate6400 1 P.leadingCoeff := by
  simpa using koalaFrobeniusConjugate_leadingCoeff_scalar6400 P (1 : Fin 6)

@[simp] theorem koalaFrobeniusConjugate_leadingCoeff_two6400
    (P : IRSProfile.Field[X]) :
    (koalaFrobeniusConjugate 2 P).leadingCoeff =
      koalaScalarConjugate6400 2 P.leadingCoeff := by
  simpa using koalaFrobeniusConjugate_leadingCoeff_scalar6400 P (2 : Fin 6)

@[simp] theorem koalaFrobeniusConjugate_leadingCoeff_three6400
    (P : IRSProfile.Field[X]) :
    (koalaFrobeniusConjugate 3 P).leadingCoeff =
      koalaScalarConjugate6400 3 P.leadingCoeff := by
  simpa using koalaFrobeniusConjugate_leadingCoeff_scalar6400 P (3 : Fin 6)

@[simp] theorem koalaFrobeniusConjugate_leadingCoeff_four6400
    (P : IRSProfile.Field[X]) :
    (koalaFrobeniusConjugate 4 P).leadingCoeff =
      koalaScalarConjugate6400 4 P.leadingCoeff := by
  simpa using koalaFrobeniusConjugate_leadingCoeff_scalar6400 P (4 : Fin 6)

@[simp] theorem koalaFrobeniusConjugate_leadingCoeff_five6400
    (P : IRSProfile.Field[X]) :
    (koalaFrobeniusConjugate 5 P).leadingCoeff =
      koalaScalarConjugate6400 5 P.leadingCoeff := by
  simpa using koalaFrobeniusConjugate_leadingCoeff_scalar6400 P (5 : Fin 6)

theorem koalaCyclicCompatibilitySix_coeff_top6400
    (A B R : IRSProfile.Field[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hdegree : A.natDegree = B.natDegree) :
    (koalaCyclicCompatibilitySix A B R).coeff
        (5 * A.natDegree + R.natDegree) =
      koalaScalarCompatibilityLinear6400
        A.leadingCoeff B.leadingCoeff R.leadingCoeff := by
  have hAn (i : Nat) : koalaFrobeniusConjugate i A ≠ 0 :=
    koalaFrobeniusConjugate_ne_zero A hA i
  have hBn (i : Nat) : koalaFrobeniusConjugate i B ≠ 0 :=
    koalaFrobeniusConjugate_ne_zero B hB i
  have hRn (i : Nat) : koalaFrobeniusConjugate i R ≠ 0 :=
    koalaFrobeniusConjugate_ne_zero R hR i
  have hAd (i : Nat) :
      (koalaFrobeniusConjugate i A).natDegree = A.natDegree :=
    koalaFrobeniusConjugate_natDegree A i
  have hBd (i : Nat) :
      (koalaFrobeniusConjugate i B).natDegree = A.natDegree := by
    rw [koalaFrobeniusConjugate_natDegree, ← hdegree]
  have hRd (i : Nat) :
      (koalaFrobeniusConjugate i R).natDegree = R.natDegree :=
    koalaFrobeniusConjugate_natDegree R i
  have ht₀ := coeff_mul_six_at_five_mul_add
    (koalaFrobeniusConjugate 0 B) (koalaFrobeniusConjugate 1 B)
    (koalaFrobeniusConjugate 2 B) (koalaFrobeniusConjugate 3 B)
    (koalaFrobeniusConjugate 4 B) (koalaFrobeniusConjugate 5 R)
    A.natDegree R.natDegree (hBn 0) (hBn 1) (hBn 2) (hBn 3)
    (hBn 4) (hRn 5) (hBd 0) (hBd 1) (hBd 2) (hBd 3) (hBd 4) (hRd 5)
  have ht₁ := coeff_mul_six_at_five_mul_add
    (koalaFrobeniusConjugate 5 A) (koalaFrobeniusConjugate 0 B)
    (koalaFrobeniusConjugate 1 B) (koalaFrobeniusConjugate 2 B)
    (koalaFrobeniusConjugate 3 B) (koalaFrobeniusConjugate 4 R)
    A.natDegree R.natDegree (hAn 5) (hBn 0) (hBn 1) (hBn 2)
    (hBn 3) (hRn 4) (hAd 5) (hBd 0) (hBd 1) (hBd 2) (hBd 3) (hRd 4)
  have ht₂ := coeff_mul_six_at_five_mul_add
    (koalaFrobeniusConjugate 5 A) (koalaFrobeniusConjugate 4 A)
    (koalaFrobeniusConjugate 0 B) (koalaFrobeniusConjugate 1 B)
    (koalaFrobeniusConjugate 2 B) (koalaFrobeniusConjugate 3 R)
    A.natDegree R.natDegree (hAn 5) (hAn 4) (hBn 0) (hBn 1)
    (hBn 2) (hRn 3) (hAd 5) (hAd 4) (hBd 0) (hBd 1) (hBd 2) (hRd 3)
  have ht₃ := coeff_mul_six_at_five_mul_add
    (koalaFrobeniusConjugate 5 A) (koalaFrobeniusConjugate 4 A)
    (koalaFrobeniusConjugate 3 A) (koalaFrobeniusConjugate 0 B)
    (koalaFrobeniusConjugate 1 B) (koalaFrobeniusConjugate 2 R)
    A.natDegree R.natDegree (hAn 5) (hAn 4) (hAn 3) (hBn 0)
    (hBn 1) (hRn 2) (hAd 5) (hAd 4) (hAd 3) (hBd 0) (hBd 1) (hRd 2)
  have ht₄ := coeff_mul_six_at_five_mul_add
    (koalaFrobeniusConjugate 5 A) (koalaFrobeniusConjugate 4 A)
    (koalaFrobeniusConjugate 3 A) (koalaFrobeniusConjugate 2 A)
    (koalaFrobeniusConjugate 0 B) (koalaFrobeniusConjugate 1 R)
    A.natDegree R.natDegree (hAn 5) (hAn 4) (hAn 3) (hAn 2)
    (hBn 0) (hRn 1) (hAd 5) (hAd 4) (hAd 3) (hAd 2) (hBd 0) (hRd 1)
  have ht₅ := coeff_mul_six_at_five_mul_add
    (koalaFrobeniusConjugate 5 A) (koalaFrobeniusConjugate 4 A)
    (koalaFrobeniusConjugate 3 A) (koalaFrobeniusConjugate 2 A)
    (koalaFrobeniusConjugate 1 A) (koalaFrobeniusConjugate 0 R)
    A.natDegree R.natDegree (hAn 5) (hAn 4) (hAn 3) (hAn 2)
    (hAn 1) (hRn 0) (hAd 5) (hAd 4) (hAd 3) (hAd 2) (hAd 1) (hRd 0)
  rw [koalaScalarCompatibilityLinear6400_apply]
  simp only [koalaCyclicCompatibilitySix, Polynomial.coeff_sub,
    Polynomial.coeff_add, ht₀, ht₁, ht₂, ht₃, ht₄, ht₅,
    koalaFrobeniusConjugate_leadingCoeff_zero6400,
    koalaFrobeniusConjugate_leadingCoeff_one6400,
    koalaFrobeniusConjugate_leadingCoeff_two6400,
    koalaFrobeniusConjugate_leadingCoeff_three6400,
    koalaFrobeniusConjugate_leadingCoeff_four6400,
    koalaFrobeniusConjugate_leadingCoeff_five6400]

theorem koalaCyclicNormSix_leadingCoeff6400
    (P : IRSProfile.Field[X]) :
    (koalaCyclicNormSix P).leadingCoeff =
      koalaScalarCyclicNormSix6400 P.leadingCoeff := by
  simp only [koalaCyclicNormSix, koalaScalarCyclicNormSix6400,
    Polynomial.leadingCoeff_mul,
    koalaFrobeniusConjugate_leadingCoeff_zero6400,
    koalaFrobeniusConjugate_leadingCoeff_one6400,
    koalaFrobeniusConjugate_leadingCoeff_two6400,
    koalaFrobeniusConjugate_leadingCoeff_three6400,
    koalaFrobeniusConjugate_leadingCoeff_four6400,
    koalaFrobeniusConjugate_leadingCoeff_five6400]

theorem koalaScalarCyclicNormSix_leadingCoeff_eq_of_norm_eq6400
    (A B : IRSProfile.Field[X])
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B) :
    koalaScalarCyclicNormSix6400 A.leadingCoeff =
      koalaScalarCyclicNormSix6400 B.leadingCoeff := by
  have h := congrArg Polynomial.leadingCoeff hnorm
  simpa only [koalaCyclicNormSix_leadingCoeff6400] using h

theorem koalaFrobeniusConjugate_sub6400
    (P Q : IRSProfile.Field[X]) (n : Nat) :
    koalaFrobeniusConjugate n (P - Q) =
      koalaFrobeniusConjugate n P - koalaFrobeniusConjugate n Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [koalaFrobeniusConjugate, koalaFrobeniusConjugate,
        koalaFrobeniusConjugate, ih, Polynomial.map_sub]

theorem koalaCyclicCompatibilitySix_sub6400
    (A B R S : IRSProfile.Field[X]) :
    koalaCyclicCompatibilitySix A B (R - S) =
      koalaCyclicCompatibilitySix A B R -
        koalaCyclicCompatibilitySix A B S := by
  simp only [koalaCyclicCompatibilitySix,
    koalaFrobeniusConjugate_sub6400]
  ring

theorem koalaScalarCompatibilityLeadingCoeff_eq_zero6400
    (A B R : IRSProfile.Field[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hdegree : A.natDegree = B.natDegree)
    (hcompat : koalaCyclicCompatibilitySix A B R = 0) :
    koalaScalarCompatibilityLinear6400
      A.leadingCoeff B.leadingCoeff R.leadingCoeff = 0 := by
  have htop := koalaCyclicCompatibilitySix_coeff_top6400
    A B R hA hB hR hdegree
  rw [hcompat, Polynomial.coeff_zero] at htop
  exact htop.symm

theorem exists_leadingCoeff_semilinear_solution6400
    (A B R : IRSProfile.Field[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hdegree : A.natDegree = B.natDegree)
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B)
    (hcompat : koalaCyclicCompatibilitySix A B R = 0) :
    ∃ q : IRSProfile.Field,
      A.leadingCoeff * q +
        B.leadingCoeff * koalaSexticFrobenius q = R.leadingCoeff := by
  apply (koalaScalarCompatibilityLinear6400_eq_zero_iff_exists
    A.leadingCoeff B.leadingCoeff R.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hB)
    (koalaScalarCyclicNormSix_leadingCoeff_eq_of_norm_eq6400
      A B hnorm)).mp
  exact koalaScalarCompatibilityLeadingCoeff_eq_zero6400
    A B R hA hB hR hdegree hcompat

noncomputable def koalaLeadingCorrection6400
    (A R : IRSProfile.Field[X]) (q : IRSProfile.Field) :
    IRSProfile.Field[X] :=
  Polynomial.C q * Polynomial.X ^ (R.natDegree - A.natDegree)

noncomputable def koalaPolynomialSemilinear6400
    (A B Q : IRSProfile.Field[X]) : IRSProfile.Field[X] :=
  A * Q + B * Q.map koalaSexticFrobenius.toRingHom

theorem koalaPolynomialSemilinear6400_add
    (A B Q₀ Q₁ : IRSProfile.Field[X]) :
    koalaPolynomialSemilinear6400 A B (Q₀ + Q₁) =
      koalaPolynomialSemilinear6400 A B Q₀ +
        koalaPolynomialSemilinear6400 A B Q₁ := by
  simp only [koalaPolynomialSemilinear6400, Polynomial.map_add]
  ring

@[simp]
theorem koalaPolynomialSemilinear6400_zero
    (A B : IRSProfile.Field[X]) :
    koalaPolynomialSemilinear6400 A B 0 = 0 := by
  simp only [koalaPolynomialSemilinear6400, Polynomial.map_zero,
    mul_zero, add_zero]

@[simp]
theorem koalaCyclicCompatibilitySix_zero6400
    (A B : IRSProfile.Field[X]) :
    koalaCyclicCompatibilitySix A B 0 = 0 := by
  have hsub := koalaCyclicCompatibilitySix_sub6400 A B 0 0
  simpa only [sub_self] using hsub

theorem koalaLeadingCorrection6400_map
    (A R : IRSProfile.Field[X]) (q : IRSProfile.Field) :
    (koalaLeadingCorrection6400 A R q).map
        koalaSexticFrobenius.toRingHom =
      Polynomial.C (koalaSexticFrobenius q) *
        Polynomial.X ^ (R.natDegree - A.natDegree) := by
  simp only [koalaLeadingCorrection6400, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  rfl

theorem exists_koalaSemilinear_leadingCorrection_degree_lt6400
    (A B R : IRSProfile.Field[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hdegree : A.natDegree = B.natDegree)
    (hle : A.natDegree ≤ R.natDegree)
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B)
    (hcompat : koalaCyclicCompatibilitySix A B R = 0) :
    ∃ Q : IRSProfile.Field[X],
      koalaCyclicCompatibilitySix A B
          (R - (A * Q + B * Q.map koalaSexticFrobenius.toRingHom)) = 0 ∧
        ((R - (A * Q + B * Q.map
            koalaSexticFrobenius.toRingHom)) = 0 ∨
          (R - (A * Q + B * Q.map
            koalaSexticFrobenius.toRingHom)).natDegree < R.natDegree) := by
  obtain ⟨q, hq⟩ := exists_leadingCoeff_semilinear_solution6400
    A B R hA hB hR hdegree hnorm hcompat
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, map_zero, mul_zero, mul_zero, add_zero] at hq
    exact (Polynomial.leadingCoeff_ne_zero.mpr hR) hq.symm
  let Q := koalaLeadingCorrection6400 A R q
  let S := A * Q + B * Q.map koalaSexticFrobenius.toRingHom
  have hQ : Q ≠ 0 := by
    dsimp only [Q, koalaLeadingCorrection6400]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hq0)
      (pow_ne_zero _ Polynomial.X_ne_zero)
  have hQmap : Q.map koalaSexticFrobenius.toRingHom ≠ 0 :=
    Polynomial.map_ne_zero hQ
  have hQdegree : Q.natDegree = R.natDegree - A.natDegree := by
    exact Polynomial.natDegree_C_mul_X_pow _ q hq0
  have hQmapDegree :
      (Q.map koalaSexticFrobenius.toRingHom).natDegree =
        R.natDegree - A.natDegree := by
    rw [Polynomial.natDegree_map, hQdegree]
  have hAQ : A * Q ≠ 0 := mul_ne_zero hA hQ
  have hBQ : B * Q.map koalaSexticFrobenius.toRingHom ≠ 0 :=
    mul_ne_zero hB hQmap
  have hAQdegree : (A * Q).natDegree = R.natDegree := by
    rw [Polynomial.natDegree_mul hA hQ, hQdegree]
    omega
  have hBQdegree :
      (B * Q.map koalaSexticFrobenius.toRingHom).natDegree =
        R.natDegree := by
    rw [Polynomial.natDegree_mul hB hQmap, hQmapDegree, ← hdegree]
    omega
  have hQleading : Q.leadingCoeff = q := by
    exact Polynomial.leadingCoeff_C_mul_X_pow q _
  have hQmapLeading :
      (Q.map koalaSexticFrobenius.toRingHom).leadingCoeff =
        koalaSexticFrobenius q := by
    rw [Polynomial.leadingCoeff_map, hQleading]
    rfl
  have hAQcoeff :
      (A * Q).coeff R.natDegree = (A * Q).leadingCoeff := by
    rw [← hAQdegree, Polynomial.coeff_natDegree]
  have hBQcoeff :
      (B * Q.map koalaSexticFrobenius.toRingHom).coeff R.natDegree =
        (B * Q.map koalaSexticFrobenius.toRingHom).leadingCoeff := by
    rw [← hBQdegree, Polynomial.coeff_natDegree]
  have hScoeff : S.coeff R.natDegree = R.leadingCoeff := by
    dsimp only [S]
    rw [Polynomial.coeff_add, hAQcoeff, hBQcoeff,
      Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
      hQleading, hQmapLeading]
    exact hq
  have hSdegree_le : S.natDegree ≤ R.natDegree := by
    dsimp only [S]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le hAQdegree.le hBQdegree.le)
  have hScoeff0 : S.coeff R.natDegree ≠ 0 := by
    rw [hScoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hR
  have hSdegree : S.natDegree = R.natDegree :=
    le_antisymm hSdegree_le (Polynomial.le_natDegree_of_ne_zero hScoeff0)
  have hS : S ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.coeff_zero] at hScoeff0
    exact hScoeff0 rfl
  have hSleading : S.leadingCoeff = R.leadingCoeff := by
    rw [← Polynomial.coeff_natDegree, hSdegree, hScoeff]
  have hdegreeRS : R.degree = S.degree := by
    rw [Polynomial.degree_eq_natDegree hR,
      Polynomial.degree_eq_natDegree hS, hSdegree]
  have hdegreeDrop : (R - S).degree < R.degree :=
    Polynomial.degree_sub_lt hdegreeRS hR hSleading.symm
  have hdrop : (R - S) = 0 ∨ (R - S).natDegree < R.natDegree := by
    by_cases hRS : R - S = 0
    · exact Or.inl hRS
    · right
      rw [Polynomial.degree_eq_natDegree hRS,
        Polynomial.degree_eq_natDegree hR] at hdegreeDrop
      exact_mod_cast hdegreeDrop
  refine ⟨Q, ?_, ?_⟩
  · rw [koalaCyclicCompatibilitySix_sub6400,
      hcompat,
      koalaCyclicCompatibilitySix_eq_zero_of_norm_eq A B Q hnorm,
      sub_self]
  · simpa only [S] using hdrop

/-- Repeated exact leading-coefficient cancellation gives semilinear
division with a remainder below the common coefficient degree. -/
theorem exists_koalaPolynomialSemilinear_remainder6400
    (A B R : IRSProfile.Field[X])
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hdegree : A.natDegree = B.natDegree)
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B)
    (hcompat : koalaCyclicCompatibilitySix A B R = 0) :
    ∃ Q : IRSProfile.Field[X],
      koalaCyclicCompatibilitySix A B
          (R - koalaPolynomialSemilinear6400 A B Q) = 0 ∧
        ((R - koalaPolynomialSemilinear6400 A B Q) = 0 ∨
          (R - koalaPolynomialSemilinear6400 A B Q).natDegree <
            A.natDegree) := by
  by_cases hR : R = 0
  · refine ⟨0, ?_, Or.inl ?_⟩
    · simp only [hR, koalaPolynomialSemilinear6400_zero, sub_zero,
        koalaCyclicCompatibilitySix_zero6400]
    · simp only [hR, koalaPolynomialSemilinear6400_zero, sub_zero]
  by_cases hlow : R.natDegree < A.natDegree
  · refine ⟨0, ?_, Or.inr ?_⟩
    · simpa only [koalaPolynomialSemilinear6400_zero, sub_zero] using hcompat
    · simpa only [koalaPolynomialSemilinear6400_zero, sub_zero] using hlow
  have hle : A.natDegree ≤ R.natDegree := Nat.le_of_not_gt hlow
  obtain ⟨Q₀, hcompat₁, hstep₁⟩ :=
    exists_koalaSemilinear_leadingCorrection_degree_lt6400
      A B R hA hB hR hdegree hle hnorm hcompat
  let R₁ := R - koalaPolynomialSemilinear6400 A B Q₀
  have hcompat₁' : koalaCyclicCompatibilitySix A B R₁ = 0 := by
    simpa only [R₁, koalaPolynomialSemilinear6400] using hcompat₁
  have hstep₁' : R₁ = 0 ∨ R₁.natDegree < R.natDegree := by
    simpa only [R₁, koalaPolynomialSemilinear6400] using hstep₁
  rcases hstep₁' with hzero₁ | hdegree₁
  · refine ⟨Q₀, hcompat₁', Or.inl hzero₁⟩
  · obtain ⟨Q₁, hcompat₂, hremainder⟩ :=
      exists_koalaPolynomialSemilinear_remainder6400
        A B R₁ hA hB hdegree hnorm hcompat₁'
    refine ⟨Q₀ + Q₁, ?_, ?_⟩
    · rw [koalaPolynomialSemilinear6400_add]
      have hresidual :
          R - (koalaPolynomialSemilinear6400 A B Q₀ +
              koalaPolynomialSemilinear6400 A B Q₁) =
            R₁ - koalaPolynomialSemilinear6400 A B Q₁ := by
        dsimp only [R₁]
        ring
      rw [hresidual]
      exact hcompat₂
    · rw [koalaPolynomialSemilinear6400_add]
      have hresidual :
          R - (koalaPolynomialSemilinear6400 A B Q₀ +
              koalaPolynomialSemilinear6400 A B Q₁) =
            R₁ - koalaPolynomialSemilinear6400 A B Q₁ := by
        dsimp only [R₁]
        ring
      rw [hresidual]
      exact hremainder
termination_by R.natDegree
decreasing_by exact hdegree₁

end ProximityPrize.SubmissionLower.BCHKSSemilinearPolynomialDescent6400
