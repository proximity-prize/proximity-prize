import ProximityPrize.SubmissionLower.BCHKSFrobeniusPrimitiveCleanup6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusHilbert90Normalization6401
open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusPrimitiveCleanup6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
section ClearedGauge
variable {F : Type*} [Field F] [DecidableEq F]
noncomputable def frobeniusOne6401 (sigma : F →+* F) (P : F[X]) : F[X] :=
  P.map sigma
noncomputable def frobeniusTwo6401 (sigma : F →+* F) (P : F[X]) : F[X] :=
  (frobeniusOne6401 sigma P).map sigma
noncomputable def frobeniusThree6401 (sigma : F →+* F) (P : F[X]) : F[X] :=
  (frobeniusTwo6401 sigma P).map sigma
noncomputable def frobeniusFour6401 (sigma : F →+* F) (P : F[X]) : F[X] :=
  (frobeniusThree6401 sigma P).map sigma
noncomputable def frobeniusFive6401 (sigma : F →+* F) (P : F[X]) : F[X] :=
  (frobeniusFour6401 sigma P).map sigma
noncomputable def hilbert90Denominator6401
    (sigma : F →+* F) (B : F[X]) : F[X] :=
  B * frobeniusOne6401 sigma B * frobeniusTwo6401 sigma B *
    frobeniusThree6401 sigma B * frobeniusFour6401 sigma B
noncomputable def hilbert90Numerator6401
    (sigma : F →+* F) (A B : F[X]) (t : F) : F[X] :=
  hilbert90Denominator6401 sigma B * Polynomial.C t +
    (A * frobeniusOne6401 sigma B * frobeniusTwo6401 sigma B *
      frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma t) +
    (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma B *
      frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma (sigma t)) +
    (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
      frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma (sigma (sigma t))) +
    (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
      frobeniusThree6401 sigma A * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma (sigma (sigma (sigma t)))) +
    (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
      frobeniusThree6401 sigma A * frobeniusFour6401 sigma A) *
        Polynomial.C (sigma (sigma (sigma (sigma (sigma t)))))
theorem frobeniusOne_map6401 (sigma : F →+* F) (P : F[X]) :
    (frobeniusOne6401 sigma P).map sigma = frobeniusTwo6401 sigma P := rfl
theorem frobeniusTwo_map6401 (sigma : F →+* F) (P : F[X]) :
    (frobeniusTwo6401 sigma P).map sigma = frobeniusThree6401 sigma P := rfl
theorem frobeniusThree_map6401 (sigma : F →+* F) (P : F[X]) :
    (frobeniusThree6401 sigma P).map sigma = frobeniusFour6401 sigma P := rfl
theorem frobeniusFour_map6401 (sigma : F →+* F) (P : F[X]) :
    (frobeniusFour6401 sigma P).map sigma = frobeniusFive6401 sigma P := rfl
theorem frobeniusFive_map6401
    (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (P : F[X]) :
    (frobeniusFive6401 sigma P).map sigma = P := by
  ext n
  simp [frobeniusFive6401, frobeniusFour6401, frobeniusThree6401,
    frobeniusTwo6401, frobeniusOne6401, horder]
theorem frobeniusIterates_natDegree_le6401
    (sigma : F →+* F) (P : F[X]) (p : Nat) (hP : P.natDegree ≤ p) :
    (frobeniusOne6401 sigma P).natDegree ≤ p ∧
      (frobeniusTwo6401 sigma P).natDegree ≤ p ∧
      (frobeniusThree6401 sigma P).natDegree ≤ p ∧
      (frobeniusFour6401 sigma P).natDegree ≤ p ∧
      (frobeniusFive6401 sigma P).natDegree ≤ p := by
  have h1 : (frobeniusOne6401 sigma P).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans hP
  have h2 : (frobeniusTwo6401 sigma P).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans h1
  have h3 : (frobeniusThree6401 sigma P).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans h2
  have h4 : (frobeniusFour6401 sigma P).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans h3
  have h5 : (frobeniusFive6401 sigma P).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans h4
  exact ⟨h1, h2, h3, h4, h5⟩
private theorem fiveFactor_natDegree_le6401
    (P0 P1 P2 P3 P4 : F[X]) (p : Nat)
    (h0 : P0.natDegree ≤ p) (h1 : P1.natDegree ≤ p)
    (h2 : P2.natDegree ≤ p) (h3 : P3.natDegree ≤ p)
    (h4 : P4.natDegree ≤ p) :
    (P0 * P1 * P2 * P3 * P4).natDegree ≤ 5 * p := by
  have h01 := Polynomial.natDegree_mul_le (p := P0) (q := P1)
  have h012 := Polynomial.natDegree_mul_le (p := P0 * P1) (q := P2)
  have h0123 := Polynomial.natDegree_mul_le (p := P0 * P1 * P2) (q := P3)
  have h01234 := Polynomial.natDegree_mul_le
    (p := P0 * P1 * P2 * P3) (q := P4)
  omega
theorem hilbert90Denominator_natDegree_le6401
    (sigma : F →+* F) (B : F[X]) (p : Nat)
    (hB : B.natDegree ≤ p) :
    (hilbert90Denominator6401 sigma B).natDegree ≤ 5 * p := by
  have hi := frobeniusIterates_natDegree_le6401 sigma B p hB
  exact fiveFactor_natDegree_le6401 B
    (frobeniusOne6401 sigma B) (frobeniusTwo6401 sigma B)
    (frobeniusThree6401 sigma B) (frobeniusFour6401 sigma B)
    p hB hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1
theorem hilbert90Numerator_natDegree_le6401
    (sigma : F →+* F) (A B : F[X]) (t : F) (p : Nat)
    (hA : A.natDegree ≤ p) (hB : B.natDegree ≤ p) :
    (hilbert90Numerator6401 sigma A B t).natDegree ≤ 5 * p := by
  have hAi := frobeniusIterates_natDegree_le6401 sigma A p hA
  have hBi := frobeniusIterates_natDegree_le6401 sigma B p hB
  have h0 : (hilbert90Denominator6401 sigma B).natDegree ≤ 5 * p :=
    hilbert90Denominator_natDegree_le6401 sigma B p hB
  have h1 := fiveFactor_natDegree_le6401 A
    (frobeniusOne6401 sigma B) (frobeniusTwo6401 sigma B)
    (frobeniusThree6401 sigma B) (frobeniusFour6401 sigma B)
    p hA hBi.1 hBi.2.1 hBi.2.2.1 hBi.2.2.2.1
  have h2 := fiveFactor_natDegree_le6401 A
    (frobeniusOne6401 sigma A) (frobeniusTwo6401 sigma B)
    (frobeniusThree6401 sigma B) (frobeniusFour6401 sigma B)
    p hA hAi.1 hBi.2.1 hBi.2.2.1 hBi.2.2.2.1
  have h3 := fiveFactor_natDegree_le6401 A
    (frobeniusOne6401 sigma A) (frobeniusTwo6401 sigma A)
    (frobeniusThree6401 sigma B) (frobeniusFour6401 sigma B)
    p hA hAi.1 hAi.2.1 hBi.2.2.1 hBi.2.2.2.1
  have h4 := fiveFactor_natDegree_le6401 A
    (frobeniusOne6401 sigma A) (frobeniusTwo6401 sigma A)
    (frobeniusThree6401 sigma A) (frobeniusFour6401 sigma B)
    p hA hAi.1 hAi.2.1 hAi.2.2.1 hBi.2.2.2.1
  have h5 := fiveFactor_natDegree_le6401 A
    (frobeniusOne6401 sigma A) (frobeniusTwo6401 sigma A)
    (frobeniusThree6401 sigma A) (frobeniusFour6401 sigma A)
    p hA hAi.1 hAi.2.1 hAi.2.2.1 hAi.2.2.2.1
  have ht0 : (hilbert90Denominator6401 sigma B * Polynomial.C t).natDegree ≤
      5 * p := by
    exact Polynomial.natDegree_mul_le.trans (by
      have hc : (Polynomial.C t : F[X]).natDegree = 0 := by simp
      omega)
  have ht1 : ((A * frobeniusOne6401 sigma B * frobeniusTwo6401 sigma B *
      frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma t)).natDegree ≤ 5 * p := by
    exact Polynomial.natDegree_mul_le.trans (by
      have hc : (Polynomial.C (sigma t) : F[X]).natDegree = 0 := by simp
      omega)
  have ht2 : ((A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma B *
      frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma (sigma t))).natDegree ≤ 5 * p := by
    exact Polynomial.natDegree_mul_le.trans (by
      have hc : (Polynomial.C (sigma (sigma t)) : F[X]).natDegree = 0 := by simp
      omega)
  have ht3 : ((A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
      frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma (sigma (sigma t)))).natDegree ≤ 5 * p := by
    exact Polynomial.natDegree_mul_le.trans (by
      have hc : (Polynomial.C (sigma (sigma (sigma t))) : F[X]).natDegree = 0 := by simp
      omega)
  have ht4 : ((A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
      frobeniusThree6401 sigma A * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma (sigma (sigma (sigma t))))).natDegree ≤ 5 * p := by
    exact Polynomial.natDegree_mul_le.trans (by
      have hc : (Polynomial.C (sigma (sigma (sigma (sigma t)))) : F[X]).natDegree = 0 := by
        simp
      omega)
  have ht5 : ((A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
      frobeniusThree6401 sigma A * frobeniusFour6401 sigma A) *
        Polynomial.C (sigma (sigma (sigma (sigma (sigma t)))))).natDegree ≤
      5 * p := by
    exact Polynomial.natDegree_mul_le.trans (by
      have hc : (Polynomial.C
          (sigma (sigma (sigma (sigma (sigma t))))) : F[X]).natDegree = 0 := by
        simp
      omega)
  dsimp only [hilbert90Numerator6401]
  have h01 := Polynomial.natDegree_add_le
    (hilbert90Denominator6401 sigma B * Polynomial.C t)
    ((A * frobeniusOne6401 sigma B * frobeniusTwo6401 sigma B *
      frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma t))
  have h012 := Polynomial.natDegree_add_le
    (hilbert90Denominator6401 sigma B * Polynomial.C t +
      (A * frobeniusOne6401 sigma B * frobeniusTwo6401 sigma B *
        frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma t))
    ((A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma B *
      frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma (sigma t)))
  have h0123 := Polynomial.natDegree_add_le
    (hilbert90Denominator6401 sigma B * Polynomial.C t +
      (A * frobeniusOne6401 sigma B * frobeniusTwo6401 sigma B *
        frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma t) +
      (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma B *
        frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma (sigma t)))
    ((A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
      frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma (sigma (sigma t))))
  have h01234 := Polynomial.natDegree_add_le
    (hilbert90Denominator6401 sigma B * Polynomial.C t +
      (A * frobeniusOne6401 sigma B * frobeniusTwo6401 sigma B *
        frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma t) +
      (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma B *
        frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma (sigma t)) +
      (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
        frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma (sigma (sigma t))))
    ((A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
      frobeniusThree6401 sigma A * frobeniusFour6401 sigma B) *
        Polynomial.C (sigma (sigma (sigma (sigma t)))))
  have h012345 := Polynomial.natDegree_add_le
    (hilbert90Denominator6401 sigma B * Polynomial.C t +
      (A * frobeniusOne6401 sigma B * frobeniusTwo6401 sigma B *
        frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma t) +
      (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma B *
        frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma (sigma t)) +
      (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
        frobeniusThree6401 sigma B * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma (sigma (sigma t))) +
      (A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
        frobeniusThree6401 sigma A * frobeniusFour6401 sigma B) *
          Polynomial.C (sigma (sigma (sigma (sigma t)))))
    ((A * frobeniusOne6401 sigma A * frobeniusTwo6401 sigma A *
      frobeniusThree6401 sigma A * frobeniusFour6401 sigma A) *
        Polynomial.C (sigma (sigma (sigma (sigma (sigma t))))))
  omega
theorem hilbert90Numerator_shift6401
    (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (A B : F[X]) (t : F)
    (hnorm : polynomialFrobeniusNormSix sigma A =
      polynomialFrobeniusNormSix sigma B) :
    A * (hilbert90Numerator6401 sigma A B t).map sigma =
      frobeniusFive6401 sigma B * hilbert90Numerator6401 sigma A B t := by
  simp only [hilbert90Numerator6401, hilbert90Denominator6401,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    frobeniusOne_map6401, frobeniusTwo_map6401,
    frobeniusThree_map6401, frobeniusFour_map6401]
  have ht := horder t
  dsimp [polynomialFrobeniusNormSix, frobeniusFive6401,
    frobeniusFour6401, frobeniusThree6401, frobeniusTwo6401,
    frobeniusOne6401] at hnorm ⊢
  rw [ht]
  linear_combination Polynomial.C t * hnorm
theorem hilbert90Gauge_cross6401
    (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (A B : F[X]) (t : F)
    (hnorm : polynomialFrobeniusNormSix sigma A =
      polynomialFrobeniusNormSix sigma B) :
    A * (hilbert90Numerator6401 sigma A B t).map sigma *
        hilbert90Denominator6401 sigma B =
      B * hilbert90Numerator6401 sigma A B t *
        (hilbert90Denominator6401 sigma B).map sigma := by
  have hP := hilbert90Numerator_shift6401 sigma horder A B t hnorm
  simp only [hilbert90Denominator6401, Polynomial.map_mul,
    frobeniusOne_map6401, frobeniusTwo_map6401,
    frobeniusThree_map6401, frobeniusFour_map6401]
  rw [hP]
  simp only [frobeniusOne6401]
  ring
theorem eval_frobeniusOne_fixed6401
    (sigma : F →+* F) (P : F[X]) (x : F) (hx : sigma x = x) :
    Polynomial.eval x (frobeniusOne6401 sigma P) =
      sigma (Polynomial.eval x P) := by
  change Polynomial.eval x (P.map sigma) = _
  calc
    _ = Polynomial.eval (sigma x) (P.map sigma) := by rw [hx]
    _ = sigma (Polynomial.eval x P) :=
      Polynomial.eval_map_apply (p := P) sigma x
theorem eval_frobeniusTwo_fixed6401
    (sigma : F →+* F) (P : F[X]) (x : F) (hx : sigma x = x) :
    Polynomial.eval x (frobeniusTwo6401 sigma P) =
      sigma (sigma (Polynomial.eval x P)) := by
  change Polynomial.eval x ((frobeniusOne6401 sigma P).map sigma) = _
  calc
    _ = Polynomial.eval (sigma x)
        ((frobeniusOne6401 sigma P).map sigma) := by rw [hx]
    _ = sigma (Polynomial.eval x (frobeniusOne6401 sigma P)) :=
      Polynomial.eval_map_apply
        (p := frobeniusOne6401 sigma P) sigma x
    _ = _ := by rw [eval_frobeniusOne_fixed6401 sigma P x hx]
theorem eval_frobeniusThree_fixed6401
    (sigma : F →+* F) (P : F[X]) (x : F) (hx : sigma x = x) :
    Polynomial.eval x (frobeniusThree6401 sigma P) =
      sigma (sigma (sigma (Polynomial.eval x P))) := by
  change Polynomial.eval x ((frobeniusTwo6401 sigma P).map sigma) = _
  calc
    _ = Polynomial.eval (sigma x)
        ((frobeniusTwo6401 sigma P).map sigma) := by rw [hx]
    _ = sigma (Polynomial.eval x (frobeniusTwo6401 sigma P)) :=
      Polynomial.eval_map_apply
        (p := frobeniusTwo6401 sigma P) sigma x
    _ = _ := by rw [eval_frobeniusTwo_fixed6401 sigma P x hx]
theorem eval_frobeniusFour_fixed6401
    (sigma : F →+* F) (P : F[X]) (x : F) (hx : sigma x = x) :
    Polynomial.eval x (frobeniusFour6401 sigma P) =
      sigma (sigma (sigma (sigma (Polynomial.eval x P)))) := by
  change Polynomial.eval x ((frobeniusThree6401 sigma P).map sigma) = _
  calc
    _ = Polynomial.eval (sigma x)
        ((frobeniusThree6401 sigma P).map sigma) := by rw [hx]
    _ = sigma (Polynomial.eval x (frobeniusThree6401 sigma P)) :=
      Polynomial.eval_map_apply
        (p := frobeniusThree6401 sigma P) sigma x
    _ = _ := by rw [eval_frobeniusThree_fixed6401 sigma P x hx]
theorem eval_frobeniusFive_fixed6401
    (sigma : F →+* F) (P : F[X]) (x : F) (hx : sigma x = x) :
    Polynomial.eval x (frobeniusFive6401 sigma P) =
      sigma (sigma (sigma (sigma (sigma (Polynomial.eval x P))))) := by
  change Polynomial.eval x ((frobeniusFour6401 sigma P).map sigma) = _
  calc
    _ = Polynomial.eval (sigma x)
        ((frobeniusFour6401 sigma P).map sigma) := by rw [hx]
    _ = sigma (Polynomial.eval x (frobeniusFour6401 sigma P)) :=
      Polynomial.eval_map_apply
        (p := frobeniusFour6401 sigma P) sigma x
    _ = _ := by rw [eval_frobeniusFour_fixed6401 sigma P x hx]
theorem hilbert90Denominator_eval6401
    (sigma : F →+* F) (B : F[X]) (x : F) (hx : sigma x = x) :
    Polynomial.eval x (hilbert90Denominator6401 sigma B) =
      Polynomial.eval x B * sigma (Polynomial.eval x B) *
        sigma (sigma (Polynomial.eval x B)) *
        sigma (sigma (sigma (Polynomial.eval x B))) *
        sigma (sigma (sigma (sigma (Polynomial.eval x B)))) := by
  simp only [hilbert90Denominator6401, Polynomial.eval_mul]
  rw [eval_frobeniusOne_fixed6401 sigma B x hx,
    eval_frobeniusTwo_fixed6401 sigma B x hx,
    eval_frobeniusThree_fixed6401 sigma B x hx,
    eval_frobeniusFour_fixed6401 sigma B x hx]
theorem base_eval_eq_zero_of_hilbert90Denominator_eval_eq_zero6401
    (sigma : F →+* F)
    (B : F[X]) (x : F) (hx : sigma x = x)
    (hQ : Polynomial.eval x (hilbert90Denominator6401 sigma B) = 0) :
    Polynomial.eval x B = 0 := by
  rw [hilbert90Denominator_eval6401 sigma B x hx] at hQ
  by_contra hB
  have h1 : sigma (Polynomial.eval x B) ≠ 0 :=
    fun hz ↦ hB (sigma.injective (by simpa using hz))
  have h2 : sigma (sigma (Polynomial.eval x B)) ≠ 0 :=
    fun hz ↦ h1 (sigma.injective (by simpa using hz))
  have h3 : sigma (sigma (sigma (Polynomial.eval x B))) ≠ 0 :=
    fun hz ↦ h2 (sigma.injective (by simpa using hz))
  have h4 : sigma (sigma (sigma (sigma (Polynomial.eval x B)))) ≠ 0 :=
    fun hz ↦ h3 (sigma.injective (by simpa using hz))
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hB h1) h2) h3) h4 hQ)
theorem error_eq_zero_of_denominator_eval_eq_zero6401
    (sigma : F →+* F)
    (A B : F[X]) (hcoprime : IsCoprime A B)
    (x E : F) (hx : sigma x = x)
    (hrel : Polynomial.eval x A * sigma E = Polynomial.eval x B * E)
    (hQ : Polynomial.eval x (hilbert90Denominator6401 sigma B) = 0) :
    E = 0 := by
  have hB := base_eval_eq_zero_of_hilbert90Denominator_eval_eq_zero6401
    sigma B x hx hQ
  have hAorB := Polynomial.aeval_ne_zero_of_isCoprime hcoprime x
  have hA : Polynomial.eval x A ≠ 0 := by
    simpa [Polynomial.aeval_def, hB] using hAorB
  rw [hB, zero_mul] at hrel
  have hsE : sigma E = 0 := (mul_eq_zero.mp hrel).resolve_left hA
  exact sigma.injective (by simpa using hsE)
private theorem sixTerm_errorSeed_identity6401
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 e0 e1 e2 e3 e4 e5 : F)
    (h0 : a0 * e1 = b0 * e0)
    (h1 : a1 * e2 = b1 * e1)
    (h2 : a2 * e3 = b2 * e2)
    (h3 : a3 * e4 = b3 * e3)
    (h4 : a4 * e5 = b4 * e4) :
    b0 * b1 * b2 * b3 * b4 * e0 +
        a0 * b1 * b2 * b3 * b4 * e1 +
        a0 * a1 * b2 * b3 * b4 * e2 +
        a0 * a1 * a2 * b3 * b4 * e3 +
        a0 * a1 * a2 * a3 * b4 * e4 +
        a0 * a1 * a2 * a3 * a4 * e5 =
      (6 : F) * (b0 * b1 * b2 * b3 * b4 * e0) := by
  have ht1 : a0 * b1 * b2 * b3 * b4 * e1 =
      b0 * b1 * b2 * b3 * b4 * e0 := by
    calc
      _ = b1 * b2 * b3 * b4 * (a0 * e1) := by ring
      _ = b1 * b2 * b3 * b4 * (b0 * e0) := by rw [h0]
      _ = _ := by ring
  have ht2 : a0 * a1 * b2 * b3 * b4 * e2 =
      b0 * b1 * b2 * b3 * b4 * e0 := by
    calc
      _ = a0 * b2 * b3 * b4 * (a1 * e2) := by ring
      _ = a0 * b2 * b3 * b4 * (b1 * e1) := by rw [h1]
      _ = b1 * b2 * b3 * b4 * (a0 * e1) := by ring
      _ = b1 * b2 * b3 * b4 * (b0 * e0) := by rw [h0]
      _ = _ := by ring
  have ht3 : a0 * a1 * a2 * b3 * b4 * e3 =
      b0 * b1 * b2 * b3 * b4 * e0 := by
    calc
      _ = a0 * a1 * b3 * b4 * (a2 * e3) := by ring
      _ = a0 * a1 * b3 * b4 * (b2 * e2) := by rw [h2]
      _ = a0 * b2 * b3 * b4 * (a1 * e2) := by ring
      _ = a0 * b2 * b3 * b4 * (b1 * e1) := by rw [h1]
      _ = b1 * b2 * b3 * b4 * (a0 * e1) := by ring
      _ = b1 * b2 * b3 * b4 * (b0 * e0) := by rw [h0]
      _ = _ := by ring
  have ht4 : a0 * a1 * a2 * a3 * b4 * e4 =
      b0 * b1 * b2 * b3 * b4 * e0 := by
    calc
      _ = a0 * a1 * a2 * b4 * (a3 * e4) := by ring
      _ = a0 * a1 * a2 * b4 * (b3 * e3) := by rw [h3]
      _ = a0 * a1 * b3 * b4 * (a2 * e3) := by ring
      _ = a0 * a1 * b3 * b4 * (b2 * e2) := by rw [h2]
      _ = a0 * b2 * b3 * b4 * (a1 * e2) := by ring
      _ = a0 * b2 * b3 * b4 * (b1 * e1) := by rw [h1]
      _ = b1 * b2 * b3 * b4 * (a0 * e1) := by ring
      _ = b1 * b2 * b3 * b4 * (b0 * e0) := by rw [h0]
      _ = _ := by ring
  have ht5 : a0 * a1 * a2 * a3 * a4 * e5 =
      b0 * b1 * b2 * b3 * b4 * e0 := by
    calc
      _ = a0 * a1 * a2 * a3 * (a4 * e5) := by ring
      _ = a0 * a1 * a2 * a3 * (b4 * e4) := by rw [h4]
      _ = a0 * a1 * a2 * b4 * (a3 * e4) := by ring
      _ = a0 * a1 * a2 * b4 * (b3 * e3) := by rw [h3]
      _ = a0 * a1 * b3 * b4 * (a2 * e3) := by ring
      _ = a0 * a1 * b3 * b4 * (b2 * e2) := by rw [h2]
      _ = a0 * b2 * b3 * b4 * (a1 * e2) := by ring
      _ = a0 * b2 * b3 * b4 * (b1 * e1) := by rw [h1]
      _ = b1 * b2 * b3 * b4 * (a0 * e1) := by ring
      _ = b1 * b2 * b3 * b4 * (b0 * e0) := by rw [h0]
      _ = _ := by ring
  rw [ht1, ht2, ht3, ht4, ht5]
  ring
theorem hilbert90Numerator_eval_errorSeed6401
    (sigma : F →+* F) (A B : F[X]) (x E : F)
    (hx : sigma x = x)
    (hrel : Polynomial.eval x A * sigma E = Polynomial.eval x B * E) :
    Polynomial.eval x (hilbert90Numerator6401 sigma A B E) =
      (6 : F) *
        (Polynomial.eval x (hilbert90Denominator6401 sigma B) * E) := by
  have h1 := congrArg sigma hrel
  have h2 := congrArg sigma h1
  have h3 := congrArg sigma h2
  have h4 := congrArg sigma h3
  simp only [map_mul] at h1 h2 h3 h4
  simp only [hilbert90Numerator6401, hilbert90Denominator6401,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [eval_frobeniusOne_fixed6401 sigma A x hx,
    eval_frobeniusTwo_fixed6401 sigma A x hx,
    eval_frobeniusThree_fixed6401 sigma A x hx,
    eval_frobeniusFour_fixed6401 sigma A x hx,
    eval_frobeniusOne_fixed6401 sigma B x hx,
    eval_frobeniusTwo_fixed6401 sigma B x hx,
    eval_frobeniusThree_fixed6401 sigma B x hx,
    eval_frobeniusFour_fixed6401 sigma B x hx]
  exact sixTerm_errorSeed_identity6401
    (Polynomial.eval x A)
    (sigma (Polynomial.eval x A))
    (sigma (sigma (Polynomial.eval x A)))
    (sigma (sigma (sigma (Polynomial.eval x A))))
    (sigma (sigma (sigma (sigma (Polynomial.eval x A)))))
    (Polynomial.eval x B)
    (sigma (Polynomial.eval x B))
    (sigma (sigma (Polynomial.eval x B)))
    (sigma (sigma (sigma (Polynomial.eval x B))))
    (sigma (sigma (sigma (sigma (Polynomial.eval x B)))))
    E (sigma E) (sigma (sigma E)) (sigma (sigma (sigma E)))
    (sigma (sigma (sigma (sigma E))))
    (sigma (sigma (sigma (sigma (sigma E)))))
    hrel h1 h2 h3 h4
theorem hilbert90Numerator_errorSeed_ne_zero6401
    (sigma : F →+* F) (A B : F[X]) (hcoprime : IsCoprime A B)
    (x E : F) (hx : sigma x = x) (hE : E ≠ 0)
    (hsix : (6 : F) ≠ 0)
    (hrel : Polynomial.eval x A * sigma E = Polynomial.eval x B * E) :
    hilbert90Numerator6401 sigma A B E ≠ 0 := by
  have hQ : Polynomial.eval x (hilbert90Denominator6401 sigma B) ≠ 0 := by
    intro hQzero
    exact hE (error_eq_zero_of_denominator_eval_eq_zero6401 sigma A B
      hcoprime x E hx hrel hQzero)
  intro hP
  have heval := congrArg (Polynomial.eval x) hP
  rw [hilbert90Numerator_eval_errorSeed6401 sigma A B x E hx hrel,
    Polynomial.eval_zero] at heval
  exact (mul_ne_zero hsix (mul_ne_zero hQ hE)) heval
def hilbert90NormalizeValue6401 (E q p : F) : F := E * q / p
def hilbert90GaugeValue6401 (p q : F) : F := p / q
theorem hilbert90NormalizeValue_eq_div_gauge6401
    (E p q : F) (hq0 : q = 0 → E = 0) :
    hilbert90NormalizeValue6401 E q p =
      E / hilbert90GaugeValue6401 p q := by
  by_cases hq : q = 0
  · simp [hilbert90NormalizeValue6401, hilbert90GaugeValue6401,
      hq, hq0 hq]
  · simp only [hilbert90NormalizeValue6401, hilbert90GaugeValue6401,
      div_div_eq_mul_div]
theorem normalized_fixed_of_crossGauge6401
    (sigma : F →+* F)
    (a b E p q : F) (hp : p ≠ 0)
    (hq0 : q = 0 → E = 0)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hrel : a * sigma E = b * E)
    (hgauge : a * sigma p * q = b * p * sigma q) :
    sigma (hilbert90NormalizeValue6401 E q p) =
      hilbert90NormalizeValue6401 E q p := by
  classical
  by_cases hq : q = 0
  · have hE := hq0 hq
    simp [hilbert90NormalizeValue6401, hq, hE]
  by_cases hE : E = 0
  · simp [hilbert90NormalizeValue6401, hE]
  have hb : b ≠ 0 := by
    intro hb
    have ha : a ≠ 0 := hab.resolve_right (fun hbn ↦ hbn hb)
    rw [hb, zero_mul] at hrel
    have hsE : sigma E = 0 :=
      (mul_eq_zero.mp hrel).resolve_left ha
    exact hE (sigma.injective (by simpa using hsE))
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at hrel
    exact hE ((mul_eq_zero.mp hrel.symm).resolve_left hb)
  have hcross : sigma E * sigma q * p = E * q * sigma p := by
    apply mul_left_cancel₀ ha
    calc
      a * (sigma E * sigma q * p) = (a * sigma E) * sigma q * p := by ring
      _ = (b * E) * sigma q * p := by rw [hrel]
      _ = E * (b * p * sigma q) := by ring
      _ = E * (a * sigma p * q) := by rw [← hgauge]
      _ = a * (E * q * sigma p) := by ring
  simp only [hilbert90NormalizeValue6401, map_div₀, map_mul]
  have hsp : sigma p ≠ 0 :=
    fun hz ↦ hp (sigma.injective (by simpa using hz))
  exact (div_eq_div_iff hsp hp).2 hcross
theorem normalized_zero_iff6401
    (E p q : F) (hp : p ≠ 0) (hq0 : q = 0 → E = 0) :
    hilbert90NormalizeValue6401 E q p = 0 ↔ E = 0 := by
  classical
  by_cases hq : q = 0
  · simp [hilbert90NormalizeValue6401, hq, hq0 hq]
  · simp [hilbert90NormalizeValue6401, hp, hq]
noncomputable def hilbert90BadSet6401
    {I : Type*} [Fintype I] [DecidableEq I]
    (alpha : I → F) (P : F[X]) : Finset I := by
  classical
  exact Finset.univ.filter fun i ↦ Polynomial.eval (alpha i) P = 0
theorem hilbert90BadSet_card_le_natDegree6401
    {I : Type*} [Fintype I] [DecidableEq I]
    (alpha : I ↪ F) (P : F[X]) (hP : P ≠ 0) :
    (hilbert90BadSet6401 alpha P).card ≤ P.natDegree := by
  classical
  let roots : Finset F := (hilbert90BadSet6401 alpha P).map alpha
  have hsub : roots ⊆ P.roots.toFinset := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).2
      (by simpa [hilbert90BadSet6401] using hi))
  calc
    (hilbert90BadSet6401 alpha P).card = roots.card :=
      (Finset.card_map alpha).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
theorem hilbert90_owner_normalization6401
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (alpha : I ↪ F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (E : I → F) (A B : F[X]) (hcoprime : IsCoprime A B)
    (t : F) (p : Nat)
    (hAdegree : A.natDegree ≤ p) (hBdegree : B.natDegree ≤ p)
    (hnorm : polynomialFrobeniusNormSix sigma A =
      polynomialFrobeniusNormSix sigma B)
    (hseed : hilbert90Numerator6401 sigma A B t ≠ 0)
    (hrelation : TwoLaneFailureRelation sigma alpha E A B) :
    let P := hilbert90Numerator6401 sigma A B t
    let Q := hilbert90Denominator6401 sigma B
    let bad := hilbert90BadSet6401 alpha P
    P.natDegree ≤ 5 * p ∧ Q.natDegree ≤ 5 * p ∧
      bad.card ≤ 5 * p ∧
      ∀ i, i ∉ bad →
        sigma (hilbert90NormalizeValue6401 (E i)
          (Polynomial.eval (alpha i) Q) (Polynomial.eval (alpha i) P)) =
            hilbert90NormalizeValue6401 (E i)
              (Polynomial.eval (alpha i) Q) (Polynomial.eval (alpha i) P) ∧
        (hilbert90NormalizeValue6401 (E i)
          (Polynomial.eval (alpha i) Q) (Polynomial.eval (alpha i) P) = 0 ↔
            E i = 0) := by
  classical
  dsimp only
  have hPdegree := hilbert90Numerator_natDegree_le6401
    sigma A B t p hAdegree hBdegree
  have hQdegree := hilbert90Denominator_natDegree_le6401
    sigma B p hBdegree
  refine ⟨hPdegree, hQdegree,
    (hilbert90BadSet_card_le_natDegree6401 alpha _ hseed).trans hPdegree, ?_⟩
  intro i hi
  have hPi : Polynomial.eval (alpha i)
      (hilbert90Numerator6401 sigma A B t) ≠ 0 := by
    intro hz
    exact hi (by simpa [hilbert90BadSet6401] using hz)
  have hQi0 : Polynomial.eval (alpha i)
      (hilbert90Denominator6401 sigma B) = 0 → E i = 0 :=
    error_eq_zero_of_denominator_eval_eq_zero6401 sigma A B
      hcoprime (alpha i) (E i) (hfixed i) (hrelation i)
  have hgaugePoly := hilbert90Gauge_cross6401 sigma horder A B t hnorm
  have hgauge := congrArg (Polynomial.eval (alpha i)) hgaugePoly
  simp only [Polynomial.eval_mul] at hgauge
  have hab : Polynomial.eval (alpha i) A ≠ 0 ∨
      Polynomial.eval (alpha i) B ≠ 0 := by
    simpa [Polynomial.aeval_def] using
      (Polynomial.aeval_ne_zero_of_isCoprime hcoprime (alpha i))
  have hfixedNorm := normalized_fixed_of_crossGauge6401 sigma
    (Polynomial.eval (alpha i) A) (Polynomial.eval (alpha i) B) (E i)
    (Polynomial.eval (alpha i) (hilbert90Numerator6401 sigma A B t))
    (Polynomial.eval (alpha i) (hilbert90Denominator6401 sigma B))
    hPi hQi0 hab (hrelation i) (by
      have hmapP : Polynomial.eval (alpha i)
          ((hilbert90Numerator6401 sigma A B t).map sigma) =
            sigma (Polynomial.eval (alpha i)
              (hilbert90Numerator6401 sigma A B t)) := by
        exact eval_frobeniusOne_fixed6401 sigma _ _ (hfixed i)
      have hmapQ : Polynomial.eval (alpha i)
          ((hilbert90Denominator6401 sigma B).map sigma) =
            sigma (Polynomial.eval (alpha i)
              (hilbert90Denominator6401 sigma B)) := by
        exact eval_frobeniusOne_fixed6401 sigma _ _ (hfixed i)
      rw [hmapP, hmapQ] at hgauge
      exact hgauge)
  exact ⟨hfixedNorm,
    normalized_zero_iff6401 _ _ _ hPi hQi0⟩
theorem hilbert90_owner_normalization_of_nonzeroError6401
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsix : (6 : F) ≠ 0)
    (alpha : I ↪ F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (E : I → F) (A B : F[X]) (hcoprime : IsCoprime A B)
    (i0 : I) (hE0 : E i0 ≠ 0) (p : Nat)
    (hAdegree : A.natDegree ≤ p) (hBdegree : B.natDegree ≤ p)
    (hnorm : polynomialFrobeniusNormSix sigma A =
      polynomialFrobeniusNormSix sigma B)
    (hrelation : TwoLaneFailureRelation sigma alpha E A B) :
    let t := E i0
    let P := hilbert90Numerator6401 sigma A B t
    let Q := hilbert90Denominator6401 sigma B
    let bad := hilbert90BadSet6401 alpha P
    P.natDegree ≤ 5 * p ∧ Q.natDegree ≤ 5 * p ∧
      bad.card ≤ 5 * p ∧
      ∀ i, i ∉ bad →
        sigma (hilbert90NormalizeValue6401 (E i)
          (Polynomial.eval (alpha i) Q) (Polynomial.eval (alpha i) P)) =
            hilbert90NormalizeValue6401 (E i)
              (Polynomial.eval (alpha i) Q) (Polynomial.eval (alpha i) P) ∧
        (hilbert90NormalizeValue6401 (E i)
          (Polynomial.eval (alpha i) Q) (Polynomial.eval (alpha i) P) = 0 ↔
            E i = 0) := by
  dsimp only
  have hseed := hilbert90Numerator_errorSeed_ne_zero6401 sigma A B
    hcoprime (alpha i0) (E i0) (hfixed i0) hE0 hsix (hrelation i0)
  exact hilbert90_owner_normalization6401 sigma horder alpha hfixed E A B
    hcoprime (E i0) p hAdegree hBdegree hnorm hseed hrelation
theorem fixedPrimitivePair_family_normalization6401
    {I T : Type*} [Fintype I] [DecidableEq I]
    (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsix : (6 : F) ≠ 0)
    (alpha : I ↪ F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (E : T → I → F) (A B : F[X]) (hcoprime : IsCoprime A B)
    (z0 : T) (i0 : I) (hE0 : E z0 i0 ≠ 0) (p : Nat)
    (hAdegree : A.natDegree ≤ p) (hBdegree : B.natDegree ≤ p)
    (hnorm : polynomialFrobeniusNormSix sigma A =
      polynomialFrobeniusNormSix sigma B)
    (hrelation : ∀ z,
      TwoLaneFailureRelation sigma alpha (E z) A B) :
    let t := E z0 i0
    let P := hilbert90Numerator6401 sigma A B t
    let Q := hilbert90Denominator6401 sigma B
    let bad := hilbert90BadSet6401 alpha P
    P.natDegree ≤ 5 * p ∧ Q.natDegree ≤ 5 * p ∧
      bad.card ≤ 5 * p ∧
      ∀ z i, i ∉ bad →
        sigma (hilbert90NormalizeValue6401 (E z i)
          (Polynomial.eval (alpha i) Q) (Polynomial.eval (alpha i) P)) =
            hilbert90NormalizeValue6401 (E z i)
              (Polynomial.eval (alpha i) Q) (Polynomial.eval (alpha i) P) ∧
        (hilbert90NormalizeValue6401 (E z i)
          (Polynomial.eval (alpha i) Q) (Polynomial.eval (alpha i) P) = 0 ↔
            E z i = 0) := by
  dsimp only
  have hseed := hilbert90Numerator_errorSeed_ne_zero6401 sigma A B
    hcoprime (alpha i0) (E z0 i0) (hfixed i0) hE0 hsix
      (hrelation z0 i0)
  have hPdegree := hilbert90Numerator_natDegree_le6401
    sigma A B (E z0 i0) p hAdegree hBdegree
  have hQdegree := hilbert90Denominator_natDegree_le6401
    sigma B p hBdegree
  refine ⟨hPdegree, hQdegree,
    (hilbert90BadSet_card_le_natDegree6401 alpha _ hseed).trans hPdegree,
    ?_⟩
  intro z i hi
  have hz := hilbert90_owner_normalization6401 sigma horder alpha hfixed
    (E z) A B hcoprime (E z0 i0) p hAdegree hBdegree hnorm hseed
      (hrelation z)
  exact hz.2.2.2 i hi
end ClearedGauge
theorem hilbert90_bad_loss_at_primitive_cap6401 :
    5 * 22507 = 112535 ∧ 185354 - 5 * 22507 = 72819 := by
  norm_num
end BCHKSFrobeniusHilbert90Normalization6401
end ProximityPrize.SubmissionLower
