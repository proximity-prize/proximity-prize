import ProximityPrize.SubmissionLower.BCHKSLocalValuation6400
import ProximityPrize.SubmissionLower.BCHKSSharpScaledLine6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSDerivativeLowering6400

open BCHKSLocalValuation6400

/-!
Exact algebra behind the derivative-lowering experiment.

For a `Y`-degree-`d` factor `R` and a received line
`S = M Y - W`, the combination

`d M R - S * ∂R/∂Y`

cancels the top `Y` coefficient.  Locally, differentiation loses at most one
order and multiplication by the received line restores it.  These facts are
independent of the still-open global support-margin selection issue.
-/

/-- The global degree-lowering combination. -/
noncomputable def derivativeLowering
    {A : Type*} [CommRing A] (d : ℕ) (M : A)
    (S R : Polynomial A) : Polynomial A :=
  Polynomial.C ((d : A) * M) * R - S * R.derivative

/-- The leading `Y` coefficient cancels exactly. -/
theorem derivativeLowering_natDegree_le_pred
    {A : Type*} [CommRing A]
    (d : ℕ) (M : A) (S R : Polynomial A)
    (hd : 0 < d) (hR : R.natDegree ≤ d)
    (hS : S.natDegree ≤ 1) (hSone : S.coeff 1 = M) :
    (derivativeLowering d M S R).natDegree ≤ d - 1 := by
  have hder : R.derivative.natDegree ≤ d - 1 :=
    (Polynomial.natDegree_derivative_le R).trans
      (Nat.sub_le_sub_right hR 1)
  have hfirst : (Polynomial.C ((d : A) * M) * R).natDegree ≤ d :=
    (Polynomial.natDegree_C_mul_le _ R).trans hR
  have hsecond : (S * R.derivative).natDegree ≤ d := by
    calc
      (S * R.derivative).natDegree ≤ S.natDegree + R.derivative.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 + (d - 1) := Nat.add_le_add hS hder
      _ = d := by omega
  have hall : (derivativeLowering d M S R).natDegree ≤ d := by
    unfold derivativeLowering
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hfirst hsecond)
  have hcoeff : (derivativeLowering d M S R).coeff d = 0 := by
    unfold derivativeLowering
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    have hmul : (S * R.derivative).coeff d =
        S.coeff 1 * R.derivative.coeff (d - 1) := by
      have h := Polynomial.coeff_mul_add_eq_of_natDegree_le hS hder
      have hind : 1 + (d - 1) = d := by omega
      rw [hind] at h
      exact h
    rw [hmul, Polynomial.coeff_derivative]
    have hdidx : d - 1 + 1 = d := by omega
    rw [hdidx, hSone]
    have hcast : (d : A) = 1 + ((d - 1 : ℕ) : A) := by
      rw [← Nat.cast_one, ← Nat.cast_add,
        show 1 + (d - 1) = d by omega]
    rw [hcast]
    ring
  exact Polynomial.natDegree_le_pred hall hcoeff

/-- For an irreducible nonlinear factor below the characteristic, the
degree-lowering combination is genuinely nonzero.  If it vanished, primality
would force the factor to divide either the received line or its own strict
lower-degree derivative. -/
theorem derivativeLowering_ne_zero_of_irreducible
    {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid (Polynomial A)]
    (p : ℕ) [CharP A p]
    (M : A) (S R : Polynomial A)
    (hirr : Irreducible R) (hS0 : S ≠ 0) (hS : S.natDegree ≤ 1)
    (hdeg : 2 ≤ R.natDegree) (hlt : R.natDegree < p) :
    derivativeLowering R.natDegree M S R ≠ 0 := by
  have hpos : 0 < R.natDegree := by omega
  have hder0 : R.derivative ≠ 0 := by
    intro hzero
    have hc := congrArg
      (fun f : Polynomial A => f.coeff (R.natDegree - 1)) hzero
    rw [Polynomial.coeff_derivative] at hc
    have hs : R.natDegree - 1 + 1 = R.natDegree := by omega
    rw [hs, Polynomial.coeff_natDegree] at hc
    have hcastSucc : ((R.natDegree - 1 : ℕ) : A) + 1 =
        (R.natDegree : A) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun z : ℕ => (z : A)) hs
    rw [hcastSucc] at hc
    simp only [Polynomial.coeff_zero] at hc
    have hcast : (R.natDegree : A) ≠ 0 := by
      intro hz
      exact (Nat.not_dvd_of_pos_of_lt hpos hlt)
        ((CharP.cast_eq_zero_iff A p R.natDegree).mp hz)
    exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero)
      hcast) hc
  intro hzero
  have heq : Polynomial.C ((R.natDegree : A) * M) * R =
      S * R.derivative := by
    exact sub_eq_zero.mp (by simpa [derivativeLowering] using hzero)
  have hdvd : R ∣ S * R.derivative := by
    refine ⟨Polynomial.C ((R.natDegree : A) * M), ?_⟩
    simpa [mul_comm] using heq.symm
  rcases hirr.prime.dvd_mul.mp hdvd with hRS | hRd
  · have hle := Polynomial.natDegree_le_of_dvd hRS hS0
    omega
  · have hle := Polynomial.natDegree_le_of_dvd hRd hder0
    have hltder := Polynomial.natDegree_derivative_lt (by omega : R.natDegree ≠ 0)
    omega

/-- Local total-order vanishing is closed under subtraction. -/
theorem localVanish_sub
    {A : Type*} [CommRing A]
    {P Q : Polynomial (Polynomial A)} {m : ℕ}
    (hP : LocalVanish P m) (hQ : LocalVanish Q m) :
    LocalVanish (P - Q) m := by
  intro s t hst
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, hP s t hst, hQ s t hst]
  simp

/-- Differentiation in `Y` loses at most one unit of local total order. -/
theorem localVanish_derivative
    {A : Type*} [CommRing A]
    {R : Polynomial (Polynomial A)} {m : ℕ}
    (hR : LocalVanish R m) :
    LocalVanish R.derivative (m - 1) := by
  intro s t hst
  rw [Polynomial.coeff_derivative]
  have hlow : s + (t + 1) < m := by omega
  have hscalar : ((t : Polynomial A) + 1) =
      Polynomial.C ((t : A) + 1) := by simp
  rw [hscalar, Polynomial.coeff_mul_C,
    hR s (t + 1) hlow]
  simp

/-- Local orders add under multiplication, including the zero-factor cases. -/
theorem localVanish_mul
    {A : Type*} [CommSemiring A] [IsDomain A]
    {P Q : Polynomial (Polynomial A)} {m n : ℕ}
    (hP : LocalVanish P m) (hQ : LocalVanish Q n) :
    LocalVanish (P * Q) (m + n) := by
  by_cases hP0 : P = 0
  · subst P
    simp [LocalVanish]
  by_cases hQ0 : Q = 0
  · subst Q
    simp [LocalVanish]
  apply (localVanish_iff_le_localOrder (mul_ne_zero hP0 hQ0) (m + n)).mpr
  rw [localOrder_mul hP0 hQ0]
  exact Nat.add_le_add
    ((localVanish_iff_le_localOrder hP0 m).mp hP)
    ((localVanish_iff_le_localOrder hQ0 n).mp hQ)

/-- Purely local derivative replacement.  Multiplication by an arbitrary
`Y`-constant costs no guaranteed local order, while a first-order received
line exactly restores the order lost by the `Y` derivative. -/
theorem localVanish_derivativeLowering
    {A : Type*} [CommRing A] [IsDomain A]
    (d : ℕ) (M : Polynomial A)
    (S R : Polynomial (Polynomial A)) (m : ℕ)
    (hm : 0 < m) (hS : LocalVanish S 1) (hR : LocalVanish R m) :
    LocalVanish
      (Polynomial.C (Polynomial.C (d : A) * M) * R -
        S * R.derivative) m := by
  apply localVanish_sub
  · have hconst : LocalVanish
        (Polynomial.C (Polynomial.C (d : A) * M) :
          Polynomial (Polynomial A)) 0 := by
      intro s t hst
      omega
    simpa using localVanish_mul hconst hR
  · have hder := localVanish_derivative hR
    have hprod := localVanish_mul hS hder
    simpa [Nat.add_sub_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))]
      using hprod

/-- The score-6400 sharp line pays exactly `L=87382` beyond the `k` units
restored by differentiating once. -/
lemma derivativeLowering_weight_increment6400 :
    218453 - 131071 = 87382 := by norm_num

end BCHKSDerivativeLowering6400
end ProximityPrize.SubmissionLower
