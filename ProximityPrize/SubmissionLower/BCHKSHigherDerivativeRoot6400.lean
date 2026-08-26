import ProximityPrize.SubmissionLower.BCHKSDerivativeRoot6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSHigherDerivativeRoot6400

open BCHKSSubstitutionVanish
open BCHKSDerivativeRoot6400

set_option maxHeartbeats 2000000

/-!
Generic iteration of the direct derivative root argument.

After `j` outer `Y` derivatives, local order is at least `m-j` and the
`(X+kY)` cap has fallen by `j*k`.  Therefore substitution still vanishes
whenever

`DX - j*k < (m-j) * agreement`,

equivalently when the initial root margin is strictly larger than
`j*(agreement-k)`.  This packages all higher-derivative scans behind one
compiled theorem.
-/

noncomputable def iterYDerivative
    {A : Type*} [CommSemiring A] :
    ℕ → Polynomial A → Polynomial A
  | 0, Q => Q
  | j + 1, Q => (iterYDerivative j Q).derivative

@[simp]
lemma iterYDerivative_zero
    {A : Type*} [CommSemiring A] (Q : Polynomial A) :
    iterYDerivative 0 Q = Q := rfl

@[simp]
lemma iterYDerivative_succ
    {A : Type*} [CommSemiring A] (j : ℕ) (Q : Polynomial A) :
    iterYDerivative (j + 1) Q = (iterYDerivative j Q).derivative := rfl

lemma iterYDerivative_eq_iterate
    {A : Type*} [CommSemiring A] (j : ℕ) (Q : Polynomial A) :
    iterYDerivative j Q = (Polynomial.derivative^[j]) Q := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iterYDerivative_succ, ih, Function.iterate_succ_apply']

/-- Iterated derivatives commute with the received-line shift. -/
theorem shift_iterYDerivative
    {A : Type*} [CommRing A]
    (j : ℕ) (Q : Polynomial (Polynomial A)) (x y : A) :
    Polynomial.Bivariate.shift (iterYDerivative j Q) x y =
      iterYDerivative j (Polynomial.Bivariate.shift Q x y) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iterYDerivative_succ, iterYDerivative_succ,
        shift_derivative, ih]

/-- Iterating the local derivative lemma loses exactly one available order
per step. -/
theorem iterYDerivative_shift_coeff_zero
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (omega : F) (yZ : Polynomial F) (m j : ℕ)
    (hj : j ≤ m)
    (hvan : ∀ s t h, s + t < m →
      shiftedScalarCoeff Q omega yZ t s h = 0) :
    ∀ s t h, s + t < m - j →
      shiftedScalarCoeff (iterYDerivative j Q) omega yZ t s h = 0 := by
  induction j with
  | zero => simpa using hvan
  | succ j ih =>
      have hjm : j ≤ m := by omega
      have hprev := ih hjm
      have hstep := derivative_shift_coeff_zero
        (iterYDerivative j Q) omega yZ (m - j) hprev
      intro s t h hst
      have hst' : s + t < (m - j) - 1 := by
        simpa [Nat.sub_sub] using hst
      simpa only [iterYDerivative_succ] using hstep s t h hst'

/-- Iterating the support lemma drops the strict weighted cap by `j*k`. -/
theorem iterYDerivative_weighted_X_cap
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (j k DX : ℕ) (hjk : j * k ≤ DX)
    (hcap : ∀ y x, ((Q.coeff y).coeff x) ≠ 0 →
      x + k * y < DX) :
    ∀ y x, (((iterYDerivative j Q).coeff y).coeff x) ≠ 0 →
      x + k * y < DX - j * k := by
  induction j with
  | zero => simpa using hcap
  | succ j ih =>
      have hjk' : j * k ≤ DX := by
        have : j * k ≤ (j + 1) * k := Nat.mul_le_mul_right k (by omega)
        exact this.trans (by simpa [Nat.add_mul] using hjk)
      have hprev := ih hjk'
      have hk : k ≤ DX - j * k := by
        have hsum : j * k + k ≤ DX := by
          simpa [Nat.add_mul] using hjk
        omega
      intro y x hcoeff
      have hstep := derivative_weighted_X_cap
        (iterYDerivative j Q) k (DX - j * k) hk hprev y x
        (by simpa only [iterYDerivative_succ] using hcoeff)
      simpa [Nat.sub_sub, Nat.add_mul] using hstep

/-- Generic higher-derivative GS root theorem. -/
theorem triEval_iterYDerivative_eq_zero
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (j m k DX : ℕ) (z : F)
    (P : Polynomial F) (omega : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F)
    (hj : j ≤ m) (hjk : j * k ≤ DX)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < m →
      shiftedScalarCoeff Q (omega i) (yZ i) t s h = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree ≤ k)
    (hcap : ∀ y x, ((Q.coeff y).coeff x) ≠ 0 →
      x + k * y < DX)
    (hmany : DX - j * k < (m - j) * A.card) :
    triEval (iterYDerivative j Q) z P = 0 := by
  apply triEval_eq_zero_of_many_shift_vanishing_of_weighted_X_cap
    (iterYDerivative j Q) z P omega A yZ (m - j) k (DX - j * k)
  · intro i hi s t h hst
    exact iterYDerivative_shift_coeff_zero Q (omega i) (yZ i)
      m j hj (hvan i hi) s t h hst
  · exact hmatch
  · exact hP
  · intro y x hcoeff
    exact le_of_lt (iterYDerivative_weighted_X_cap Q j k DX hjk hcap
      y x hcoeff)
  · exact hmany

/-- If all derivatives through order `j` vanish at a substituted root, then
the specialized polynomial has root multiplicity strictly larger than `j`.
The factorial non-zero-divisor hypothesis is the exact characteristic
condition; in the benchmark `j` is tiny compared with the field
characteristic. -/
theorem lt_rootMultiplicity_of_iterYDerivative_eval_zero
    {A : Type*} [CommRing A]
    (B : Polynomial A) (p : A) (j : ℕ)
    (hB : B ≠ 0)
    (hroot : ∀ r ≤ j, Polynomial.eval p (iterYDerivative r B) = 0)
    (hfactorial : (j.factorial : A) ∈ nonZeroDivisors A) :
    j < B.rootMultiplicity p := by
  apply Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
    hB
  · intro r hr
    rw [← iterYDerivative_eq_iterate]
    exact hroot r hr
  · exact hfactorial

end BCHKSHigherDerivativeRoot6400
end ProximityPrize.SubmissionLower
