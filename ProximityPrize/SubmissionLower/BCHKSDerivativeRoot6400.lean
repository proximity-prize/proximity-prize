import ProximityPrize.SubmissionLower.BCHKSDerivativeRetuneAudit6400
import ProximityPrize.SubmissionLower.BCHKSSubstitutionVanish

namespace ProximityPrize.SubmissionLower
namespace BCHKSDerivativeRoot6400

open BCHKSSubstitutionVanish
open BCHKSDerivativeLowering6400

set_option maxHeartbeats 2000000

/-!
The first `Y` derivative of the score-6400 interpolant still vanishes after
substitution by every close challenge polynomial.

Differentiation changes the two sides of the root count by different amounts:

* local interpolation order drops from `m` to `m-1`, costing `a=185364`
  roots;
* `(X+kY)` weight drops by `k=131071`;
* the initial interpolant already has the sharp-line margin `L=87382`.

Thus the derivative retains the positive gap

`L + k - a = 33089`.

Consequently both `Q_z(P_z)` and `(dQ/dY)_z(P_z)` vanish for every challenge.
If `Q` is squarefree in `Y`, this feeds directly into a nonzero resultant.
The only surviving obstruction is the global repeated-factor gcd
`gcd_Y(Q,dQ/dY)`.
-/

lemma shift_derivative
    {A : Type*} [CommRing A]
    (Q : Polynomial (Polynomial A)) (x y : A) :
    Polynomial.Bivariate.shift Q.derivative x y =
      (Polynomial.Bivariate.shift Q x y).derivative := by
  unfold Polynomial.Bivariate.shift
  rw [Polynomial.derivative_map, Polynomial.derivative_comp]
  simp

noncomputable def shiftedScalarCoeff
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (omega : F) (yZ : Polynomial F) (t s h : ℕ) : F :=
  (((Polynomial.Bivariate.shift Q (Polynomial.C omega) yZ).coeff t).coeff s).coeff h

/-- Total-order interpolation constraints descend by one under the outer
`Y` derivative, including all coefficients in the challenge variable. -/
theorem derivative_shift_coeff_zero
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (omega : F) (yZ : Polynomial F) (m : ℕ)
    (hvan : ∀ s t h, s + t < m →
      shiftedScalarCoeff Q omega yZ t s h = 0) :
    ∀ s t h, s + t < m - 1 →
      shiftedScalarCoeff Q.derivative omega yZ t s h = 0 := by
  have hlocal : BCHKSLocalValuation6400.LocalVanish
      (Polynomial.Bivariate.shift Q (Polynomial.C omega) yZ) m := by
    intro s t hst
    apply Polynomial.ext
    intro h
    exact hvan s t h hst
  have hder := localVanish_derivative hlocal
  intro s t h hst
  have hz := hder s t hst
  rw [← shift_derivative Q (Polynomial.C omega) yZ] at hz
  exact congrArg (fun P : Polynomial F => P.coeff h) hz

/-- A strict `(X+kY)` support cap drops by `k` under `Y` differentiation. -/
theorem derivative_weighted_X_cap
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (k DX : ℕ)
    (hkDX : k ≤ DX)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + k * j < DX) :
    ∀ j a, ((Q.derivative.coeff j).coeff a) ≠ 0 →
      a + k * j < DX - k := by
  intro j a hcoeff
  have horig : ((Q.coeff (j + 1)).coeff a) ≠ 0 := by
    intro hzero
    apply hcoeff
    rw [Polynomial.coeff_derivative]
    rw [show ((j : Polynomial (Polynomial F)) + 1) =
      Polynomial.C ((j : Polynomial F) + 1) by simp]
    rw [Polynomial.coeff_mul_C, hzero]
    simp
  have h := hcap (j + 1) a horig
  rw [Nat.mul_add] at h
  norm_num at h
  omega

def bchksDerivativeRootXCap6400 : ℕ := 37936377787
def bchksDerivativeRootGap6400 : ℕ := 33089

lemma bchksDerivativeRootXCap_eq6400 :
    bchksDerivativeRootXCap6400 =
      bchksDerivativeXSmallCap6400 - 131071 := by
  norm_num [bchksDerivativeRootXCap6400,
    bchksDerivativeXSmallCap6400]

lemma bchksDerivativeRootGap_eq6400 :
    (bchksDerivativeMultiplicity6400 - 1) * 185364 =
      bchksDerivativeRootXCap6400 + bchksDerivativeRootGap6400 := by
  norm_num [bchksDerivativeMultiplicity6400,
    bchksDerivativeRootXCap6400, bchksDerivativeRootGap6400]

lemma bchksDerivativeRootCount_strict6400 :
    bchksDerivativeRootXCap6400 <
      (bchksDerivativeMultiplicity6400 - 1) * 185364 := by
  norm_num [bchksDerivativeMultiplicity6400,
    bchksDerivativeRootXCap6400]

/-- Fully packaged direct derivative root theorem at the exact retuned
parameters.  This is independent of factorization and of any specialization
stability statement. -/
theorem triEval_derivative_eq_zero6400
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (omega : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F)
    (hvan : ∀ i ∈ A, ∀ s t h,
      s + t < bchksDerivativeMultiplicity6400 →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C (omega i))
        (yZ i)).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree ≤ 131071)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < bchksDerivativeXSmallCap6400)
    (hA : 185364 ≤ A.card) :
    triEval Q.derivative z P = 0 := by
  apply triEval_eq_zero_of_many_shift_vanishing_of_weighted_X_cap
    Q.derivative z P omega A yZ
    (bchksDerivativeMultiplicity6400 - 1) 131071
    bchksDerivativeRootXCap6400
  · intro i hi s t h hst
    exact derivative_shift_coeff_zero Q (omega i) (yZ i)
      bchksDerivativeMultiplicity6400 (hvan i hi) s t h hst
  · exact hmatch
  · exact hP
  · rw [bchksDerivativeRootXCap_eq6400]
    intro j a hcoeff
    exact le_of_lt (derivative_weighted_X_cap Q 131071
      bchksDerivativeXSmallCap6400 (by
        norm_num [bchksDerivativeXSmallCap6400]) hcap j a hcoeff)
  · have hstrict := bchksDerivativeRootCount_strict6400
    exact lt_of_lt_of_le hstrict
      (Nat.mul_le_mul_left (bchksDerivativeMultiplicity6400 - 1) hA)

end BCHKSDerivativeRoot6400
end ProximityPrize.SubmissionLower
