import ProximityPrize.SubmissionLower.Koala6831IntrinsicTail
import ProximityPrize.SubmissionLower.Koala6831IntrinsicGaussRoot

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2600000
set_option maxRecDepth 20000

variable {K E : Type} [Field K] [Field E]

def seedGraphEquation (coeff : K →+* E) (z₀ z₁ : E) : Carrier K →+* Polynomial (Polynomial E) :=
  MvPolynomial.eval₂Hom ((Polynomial.C.comp Polynomial.C).comp coeff)
    ![Polynomial.C Polynomial.X, Polynomial.X, Polynomial.C (Polynomial.C z₀),
      Polynomial.C (Polynomial.C z₁)]

private theorem seedGraphEquation_monomial (coeff : K →+* E) (z₀ z₁ : E)
    (d : Fin 4 →₀ ℕ) (a : K) :
    seedGraphEquation coeff z₀ z₁ (MvPolynomial.monomial d a) =
      Polynomial.monomial (d 1) (Polynomial.monomial (d 0) (coeff a * z₀ ^ d 2 * z₁ ^ d 3)) := by
  simp only [seedGraphEquation, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
  ring

theorem seedGraphEquation_coeff_coeff (coeff : K →+* E) (z₀ z₁ : E) (F : Carrier K) (i j : ℕ) :
    ((seedGraphEquation coeff z₀ z₁ F).coeff i).coeff j =
      ∑ d ∈ F.support, if d 0 = j ∧ d 1 = i then coeff (F.coeff d) * z₀ ^ d 2 * z₁ ^ d 3 else 0 := by
  conv_lhs => rw [MvPolynomial.as_sum F]
  simp only [map_sum, seedGraphEquation_monomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hx : d 0 = j <;> by_cases hy : d 1 = i <;>
    simp [Polynomial.coeff_monomial, hx, hy]

def seedCoefficientOnSurface {L : Type} [Field L] (c : K →+* L) (F : Carrier K)
    (i j : ℕ) : MvPolynomial (Fin 3) L :=
  ∑ d ∈ F.support, if d 0 = j ∧ d 1 = i then
    MvPolynomial.C (c (F.coeff d)) * MvPolynomial.X 1 ^ d 2 * MvPolynomial.X 2 ^ d 3 else 0

theorem seedCoefficientOnSurface_eval {L : Type} [Field L] (c : K →+* L) (e : L →+* E)
    (v : Fin 3 → E) (F : Carrier K) (i j : ℕ) :
    MvPolynomial.eval₂Hom e v (seedCoefficientOnSurface c F i j) =
      ((seedGraphEquation (e.comp c) (v 1) (v 2) F).coeff i).coeff j := by
  rw [seedGraphEquation_coeff_coeff]
  unfold seedCoefficientOnSurface
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

theorem seedGraphEquation_eval (coeff : K →+* E) (z₀ z₁ : E) (F : Carrier K)
    (P : Polynomial E) : (seedGraphEquation coeff z₀ z₁ F).eval P =
      MvPolynomial.eval₂Hom (Polynomial.C.comp coeff)
        ![Polynomial.X, P, Polynomial.C z₀, Polynomial.C z₁] F := by
  have h : (Polynomial.evalRingHom P).comp (seedGraphEquation coeff z₀ z₁) =
      MvPolynomial.eval₂Hom (Polynomial.C.comp coeff)
        ![Polynomial.X, P, Polynomial.C z₀, Polynomial.C z₁] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [seedGraphEquation]
    · intro i
      fin_cases i <;> simp [seedGraphEquation]
  exact DFunLike.congr_fun h F

private theorem seedGraphEquation_derivative (coeff : K →+* E) (z₀ z₁ : E) (F : Carrier K) :
    (seedGraphEquation coeff z₀ z₁ F).derivative =
      seedGraphEquation coeff z₀ z₁ (MvPolynomial.pderiv 1 F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [seedGraphEquation]
  | add P Q hP hQ => simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, Polynomial.derivative_mul, hP]
    fin_cases i <;> simp [seedGraphEquation, add_comm]

theorem seedGraphEquation_ne_zero_of_regular (coeff : K →+* E) (v : Fin 4 → E) (F : Carrier K)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0) :
    seedGraphEquation coeff (v 2) (v 3) F ≠ 0 := by
  intro hzero
  have hD := seedGraphEquation_derivative coeff (v 2) (v 3) F
  rw [hzero, Polynomial.derivative_zero] at hD
  have hEval := seedGraphEquation_eval coeff (v 2) (v 3) (implicitRegularity F)
    (Polynomial.C (v 1))
  have hD' : seedGraphEquation coeff (v 2) (v 3) (implicitRegularity F) = 0 := hD.symm
  rw [hD', Polynomial.eval_zero] at hEval
  have hhom : (Polynomial.evalRingHom (v 0)).comp
        (MvPolynomial.eval₂Hom (Polynomial.C.comp coeff)
          ![Polynomial.X, Polynomial.C (v 1), Polynomial.C (v 2), Polynomial.C (v 3)]) =
        MvPolynomial.eval₂Hom coeff v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      fin_cases i <;> simp
  have hz := congrArg (Polynomial.evalRingHom (v 0)) hEval.symm
  rw [map_zero, ← RingHom.comp_apply, hhom] at hz
  exact hS hz

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]

theorem seedGraphEquation_coefficient_value_le (v : Valuation E Γ₀) (coeff : K →+* E)
    (z₀ z₁ : E) (F : Carrier K) (t z : ℕ) (i j : ℕ)
    (hcoeff : ∀ a, v (coeff a) ≤ 1)
    (ht : ∀ d ∈ F.support, d 2 ≤ t) (hz : ∀ d ∈ F.support, d 3 ≤ z) :
    v (((seedGraphEquation coeff z₀ z₁ F).coeff i).coeff j) ≤
      (max (v z₀) 1) ^ t * (max (v z₁) 1) ^ z := by
  classical
  rw [seedGraphEquation_coeff_coeff]
  have hbound (d : Fin 4 →₀ ℕ) (hd : d ∈ F.support) :
      v (if d 0 = j ∧ d 1 = i then coeff (F.coeff d) * z₀ ^ d 2 * z₁ ^ d 3 else 0) ≤
      (max (v z₀) 1) ^ t * (max (v z₁) 1) ^ z := by
    split_ifs
    · rw [map_mul, map_mul, map_pow, map_pow]
      have h₀ : v z₀ ^ d 2 ≤ (max (v z₀) 1) ^ t :=
        (pow_le_pow_left₀ zero_le (le_max_left _ _) _).trans
          (pow_le_pow_right₀ (le_max_right _ _) (ht d hd))
      have h₁ : v z₁ ^ d 3 ≤ (max (v z₁) 1) ^ z :=
        (pow_le_pow_left₀ zero_le (le_max_left _ _) _).trans
          (pow_le_pow_right₀ (le_max_right _ _) (hz d hd))
      calc
        _ ≤ 1 * ((max (v z₀) 1) ^ t) * ((max (v z₁) 1) ^ z) := by
          exact mul_le_mul (mul_le_mul (hcoeff _) h₀ zero_le zero_le) h₁ zero_le zero_le
        _ = _ := by rw [one_mul]
    · rw [map_zero]
      exact zero_le
  have hsum (S : Finset (Fin 4 →₀ ℕ)) (hS : S ⊆ F.support) :
      v (∑ d ∈ S, if d 0 = j ∧ d 1 = i then coeff (F.coeff d) * z₀ ^ d 2 * z₁ ^ d 3 else 0) ≤
        (max (v z₀) 1) ^ t * (max (v z₁) 1) ^ z := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert d S hd ih =>
      rw [Finset.sum_insert hd]
      exact (v.map_add _ _).trans (max_le
        (hbound d (hS (Finset.mem_insert_self d S)))
        (ih (fun a ha => hS (Finset.mem_insert_of_mem ha))))
  exact hsum F.support (fun _ h => h)

open scoped WithZero in

theorem seedGraphEquation_agreement_pole_le
    (v : Valuation E (WithZero (Multiplicative ℤ))) (coeff : K →+* E)
    (z₀ z₁ : E) (F : Carrier K) (t z n : ℕ) (P : Polynomial E) (x u₀ u₁ : E)
    (hcoeff : ∀ a, v (coeff a) ≤ 1)
    (ht : ∀ d ∈ F.support, d 2 ≤ t) (hz : ∀ d ∈ F.support, d 3 ≤ z)
    (hx : v x ≤ 1) (hu₀ : v u₀ ≤ 1) (hu₁ : v u₁ ≤ 1)
    (hroot : (seedGraphEquation coeff z₀ z₁ F).eval P = 0) :
    let A := seedGraphEquation coeff z₀ z₁ F
    let a := A.leadingCoeff.coeff n
    RCN187.poleOrder v (a * (P.eval x - u₀ - u₁ * z₀)) ≤
      (t + 1 : ℤ) * RCN187.poleOrder v z₀ + (z : ℤ) * RCN187.poleOrder v z₁ := by
  let A := seedGraphEquation coeff z₀ z₁ F
  let a := A.leadingCoeff.coeff n
  let value := a * (P.eval x - u₀ - u₁ * z₀)
  have hsum : ∑ i ∈ Finset.range (A.natDegree + 1), A.coeff i * P ^ i = 0 := by
    rwa [← Polynomial.eval_eq_sum_range]
  have hb := normalized_value_le_of_root v A.coeff A.natDegree n t z P x u₀ u₁ z₀ z₁ hsum
    (fun i _ j => seedGraphEquation_coefficient_value_le v coeff z₀ z₁ F t z i j hcoeff ht hz)
    hx hu₀ hu₁
  change v value ≤ (max (v z₀) 1) ^ (t + 1) * (max (v z₁) 1) ^ z at hb
  let b₀ := max (v z₀) 1
  let b₁ := max (v z₁) 1
  have h₀ : 1 ≤ b₀ ^ (t + 1) := one_le_pow₀ (le_max_right _ _)
  have h₁ : 1 ≤ b₁ ^ z := one_le_pow₀ (le_max_right _ _)
  have hleft : max 1 (v value) ≠ 0 := ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
  have hright : 1 ≤ b₀ ^ (t + 1) * b₁ ^ z := one_le_mul_of_one_le_of_one_le h₀ h₁
  have hlog := (WithZero.log_le_log hleft (ne_of_gt (zero_lt_one.trans_le hright))).2
    (max_le hright hb)
  rw [WithZero.log_mul (ne_of_gt (zero_lt_one.trans_le h₀))
    (ne_of_gt (zero_lt_one.trans_le h₁)), WithZero.log_pow, WithZero.log_pow] at hlog
  simpa only [value, b₀, b₁, max_comm (v z₀) 1, max_comm (v z₁) 1, RCN187.log_max_one,
    RCN187.poleOrder, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hlog

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
