import ProximityPrize.SubmissionLower.BCHKSFrobeniusExceptionalSlopes6400
import ProximityPrize.SubmissionLower.BCHKSResultantDegree

/-!
# The conjugate resultant obstruction

For a coprime direct pair `P,Q`, the remaining cofactor exception is that
`P+wQ` shares a factor with its coefficient-Frobenius conjugate.  Introduce
an independent challenge variable `Z` and the two bivariate polynomials

`P + Z Q`,  `sigma(P) + Z^p sigma(Q)`.

Their fixed-degree resultant specializes to the desired obstruction.  Its
challenge degree is at most `d*(p+1)`, where
`d=max(deg P,deg Q)`.  The load-bearing nonzeroness proof is developed below
from primitivity, variable swap, and the strict inequality `d<p`.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate

variable {F : Type} [Field F]

/-- `P + Z*Q`, represented as a polynomial in the root variable with
coefficients in the challenge polynomial ring. -/
noncomputable def affineBivariate (P Q : F[X]) : F[X][Y] :=
  P.map Polynomial.C +
    Polynomial.C Polynomial.X * Q.map Polynomial.C

/-- The same bivariate polynomial before swapping the challenge and root
variables. -/
noncomputable def affineCoefficientPolynomial (P Q : F[X]) : F[X][Y] :=
  Polynomial.C P + Polynomial.X * Polynomial.C Q

theorem swap_affineCoefficientPolynomial (P Q : F[X]) :
    Polynomial.Bivariate.swap (affineCoefficientPolynomial P Q) =
      affineBivariate P Q := by
  unfold affineCoefficientPolynomial affineBivariate
  rw [map_add, map_mul, Polynomial.Bivariate.swap_C,
    Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_C]

/-- Specializing the challenge coefficient recovers the ordinary affine
polynomial pencil. -/
theorem affineBivariate_specialize (P Q : F[X]) (w : F) :
    (affineBivariate P Q).map (Polynomial.evalRingHom w) =
      affinePolynomial P Q w := by
  have hcomp : (Polynomial.evalRingHom w).comp
      (Polynomial.C : F →+* F[X]) = RingHom.id F := by
    ext a
    simp
  simp [affineBivariate, affinePolynomial, Polynomial.map_map, hcomp]

/-- Extending the challenge coefficients to `F(Z)` gives the literal generic
affine pencil. -/
theorem affineBivariate_map_ratFunc (P Q : F[X]) :
    (affineBivariate P Q).map (algebraMap F[X] (RatFunc F)) =
      P.map (algebraMap F (RatFunc F)) +
        Polynomial.C (RatFunc.X : RatFunc F) *
          Q.map (algebraMap F (RatFunc F)) := by
  simp [affineBivariate, Polynomial.map_map]

theorem affineBivariate_natDegree_le (P Q : F[X]) :
    (affineBivariate P Q).natDegree ≤ max P.natDegree Q.natDegree := by
  have hPmap : (P.map Polynomial.C).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective P
  have hQmap : (Q.map Polynomial.C).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective Q
  calc
    (affineBivariate P Q).natDegree ≤
        max (P.map Polynomial.C).natDegree
          (Polynomial.C Polynomial.X * Q.map Polynomial.C).natDegree := by
      exact Polynomial.natDegree_add_le _ _
    _ ≤ max P.natDegree Q.natDegree := by
      apply max_le
      · exact hPmap.le.trans (le_max_left _ _)
      · exact (Polynomial.natDegree_C_mul_le Polynomial.X
          (Q.map Polynomial.C)).trans (by
            rw [hQmap]
            exact le_max_right _ _)

/-- Transcendental coefficient separation prevents any loss of root-variable
degree in the generic affine pencil. -/
theorem affineBivariate_natDegree_eq_max (P Q : F[X]) :
    (affineBivariate P Q).natDegree = max P.natDegree Q.natDegree := by
  let phi : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F)
  have hmapDegree :
      ((affineBivariate P Q).map phi).natDegree ≤
        (affineBivariate P Q).natDegree := Polynomial.natDegree_map_le
  have hgeneric := natDegree_le_generic_linear P Q
  rw [Polynomial.smul_eq_C_mul] at hgeneric
  have hmap : (affineBivariate P Q).map phi =
      P.map (algebraMap F (RatFunc F)) +
        Polynomial.C (RatFunc.X : RatFunc F) *
          Q.map (algebraMap F (RatFunc F)) :=
    affineBivariate_map_ratFunc P Q
  have hleft : P.natDegree ≤ (affineBivariate P Q).natDegree := by
    rw [hmap] at hmapDegree
    exact hgeneric.1.trans hmapDegree
  have hright : Q.natDegree ≤ (affineBivariate P Q).natDegree := by
    rw [hmap] at hmapDegree
    exact hgeneric.2.trans hmapDegree
  exact Nat.le_antisymm (affineBivariate_natDegree_le P Q)
    (max_le hleft hright)

/-- The coefficient-Frobenius affine pencil with parameter `Z^p`. -/
noncomputable def conjugateAffineBivariate
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) : F[X][Y] :=
  (P.map sigma.toRingHom).map Polynomial.C +
    Polynomial.C (Polynomial.X ^ p) *
      (Q.map sigma.toRingHom).map Polynomial.C

/-- Specialization at a point satisfying `sigma(w)=w^p` is exactly the
coefficient conjugate of `P+wQ`. -/
theorem conjugateAffineBivariate_specialize
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (w : F)
    (hpow : sigma w = w ^ p) :
    (conjugateAffineBivariate sigma p P Q).map
        (Polynomial.evalRingHom w) =
      (affinePolynomial P Q w).map sigma.toRingHom := by
  have hCEval : (Polynomial.evalRingHom w).comp
      (Polynomial.C : F →+* F[X]) = RingHom.id F := by
    ext a
    simp
  have hPmap : ((P.map sigma.toRingHom).map Polynomial.C).map
      (Polynomial.evalRingHom w) = P.map sigma.toRingHom := by
    rw [Polynomial.map_map, hCEval, Polynomial.map_id]
  have hQmap : ((Q.map sigma.toRingHom).map Polynomial.C).map
      (Polynomial.evalRingHom w) = Q.map sigma.toRingHom := by
    rw [Polynomial.map_map, hCEval, Polynomial.map_id]
  rw [affinePolynomial_map, hpow]
  change (conjugateAffineBivariate sigma p P Q).map
      (Polynomial.evalRingHom w) =
    affinePolynomial (P.map sigma.toRingHom) (Q.map sigma.toRingHom) (w ^ p)
  unfold conjugateAffineBivariate
  rw [Polynomial.map_add, Polynomial.map_mul, hPmap, hQmap]
  simp [affinePolynomial]

theorem conjugateAffineBivariate_natDegree_le
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) :
    (conjugateAffineBivariate sigma p P Q).natDegree ≤
      max P.natDegree Q.natDegree := by
  have hP : (P.map sigma.toRingHom).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective sigma.injective P
  have hQ : (Q.map sigma.toRingHom).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective sigma.injective Q
  have hPC : ((P.map sigma.toRingHom).map Polynomial.C).natDegree =
      P.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, hP]
  have hQC : ((Q.map sigma.toRingHom).map Polynomial.C).natDegree =
      Q.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, hQ]
  calc
    (conjugateAffineBivariate sigma p P Q).natDegree ≤
        max ((P.map sigma.toRingHom).map Polynomial.C).natDegree
          (Polynomial.C (Polynomial.X ^ p) *
            (Q.map sigma.toRingHom).map Polynomial.C).natDegree := by
      exact Polynomial.natDegree_add_le _ _
    _ ≤ max P.natDegree Q.natDegree := by
      apply max_le
      · rw [hPC]
        exact le_max_left _ _
      · exact (Polynomial.natDegree_C_mul_le (Polynomial.X ^ p)
          ((Q.map sigma.toRingHom).map Polynomial.C)).trans (by
            rw [hQC]
            exact le_max_right _ _)

/-- The univariate challenge obstruction obtained by eliminating the root
variable at the common degree `d`. -/
noncomputable def conjugateResultant
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) : F[X] :=
  let d := max P.natDegree Q.natDegree
  Polynomial.resultant (affineBivariate P Q)
    (conjugateAffineBivariate sigma p P Q) d d

/-- The ordinary affine bivariate polynomial is linear in the challenge
coefficient. -/
theorem affineBivariate_degreeX_le (P Q : F[X]) :
    Polynomial.Bivariate.degreeX (affineBivariate P Q) ≤ 1 := by
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  have hcoeff : (affineBivariate P Q).coeff i =
      Polynomial.C (P.coeff i) +
        Polynomial.X * Polynomial.C (Q.coeff i) := by
    simp [affineBivariate]
  rw [hcoeff]
  calc
    (Polynomial.C (P.coeff i) +
        Polynomial.X * Polynomial.C (Q.coeff i)).natDegree ≤
      max (Polynomial.C (P.coeff i)).natDegree
        (Polynomial.X * Polynomial.C (Q.coeff i)).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ 1 := by
      apply max_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)

/-- The conjugate pencil has challenge degree at most the Frobenius exponent
`p`. -/
theorem conjugateAffineBivariate_degreeX_le
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) :
    Polynomial.Bivariate.degreeX
      (conjugateAffineBivariate sigma p P Q) ≤ p := by
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  have hcoeff : (conjugateAffineBivariate sigma p P Q).coeff i =
      Polynomial.C (sigma (P.coeff i)) +
        Polynomial.X ^ p * Polynomial.C (sigma (Q.coeff i)) := by
    unfold conjugateAffineBivariate
    rw [Polynomial.coeff_add, Polynomial.coeff_map,
      Polynomial.coeff_C_mul, Polynomial.coeff_map]
    simp
  rw [hcoeff]
  calc
    (Polynomial.C (sigma (P.coeff i)) +
        Polynomial.X ^ p *
          Polynomial.C (sigma (Q.coeff i))).natDegree ≤
      max (Polynomial.C (sigma (P.coeff i))).natDegree
        (Polynomial.X ^ p *
          Polynomial.C (sigma (Q.coeff i))).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ p := by
      apply max_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)

/-- Sharp challenge-degree cap for the conjugate resultant. -/
theorem conjugateResultant_natDegree_le
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) :
    (conjugateResultant sigma p P Q).natDegree ≤
      max P.natDegree Q.natDegree * (p + 1) := by
  let d := max P.natDegree Q.natDegree
  have hres := bivariate_resultant_natDegree_le
    (affineBivariate P Q) (conjugateAffineBivariate sigma p P Q) d d
  have hfirst := affineBivariate_degreeX_le P Q
  have hsecond := conjugateAffineBivariate_degreeX_le sigma p P Q
  change (conjugateResultant sigma p P Q).natDegree ≤ d * (p + 1)
  calc
    (conjugateResultant sigma p P Q).natDegree ≤
        d * Polynomial.Bivariate.degreeX (affineBivariate P Q) +
          d * Polynomial.Bivariate.degreeX
            (conjugateAffineBivariate sigma p P Q) := by
      simpa only [conjugateResultant, d] using hres
    _ ≤ d * 1 + d * p :=
      Nat.add_le_add (Nat.mul_le_mul_left d hfirst)
        (Nat.mul_le_mul_left d hsecond)
    _ = d * (p + 1) := by ring

/-- Padding both input degrees preserves a zero resultant whenever the two
inputs are not coprime and the declared degree is positive. -/
theorem resultant_fixed_same_degree_eq_zero_of_not_isCoprime
    (A B : F[X]) (d : ℕ)
    (hAdegree : A.natDegree ≤ d) (hBdegree : B.natDegree ≤ d)
    (hd : 0 < d) (hbad : ¬IsCoprime A B) :
    Polynomial.resultant A B d d = 0 := by
  by_cases hnonzero : A ≠ 0 ∨ B ≠ 0
  · have hstandard : Polynomial.resultant A B = 0 :=
      (Polynomial.resultant_eq_zero_iff).2 ⟨hnonzero, hbad⟩
    by_cases hAd : A.natDegree = d
    · by_cases hBd : B.natDegree = d
      · simpa [hAd, hBd] using hstandard
      · have hB : B.natDegree + (d - B.natDegree) = d :=
          Nat.add_sub_of_le hBdegree
        calc
          Polynomial.resultant A B d d =
              Polynomial.resultant A B A.natDegree
                (B.natDegree + (d - B.natDegree)) := by rw [hAd, hB]
          _ = A.coeff A.natDegree ^ (d - B.natDegree) *
                Polynomial.resultant A B A.natDegree B.natDegree := by
            rw [Polynomial.resultant_add_right_deg]
            exact le_rfl
          _ = 0 := by simp [hstandard]
    · have hAlt : A.natDegree < d := lt_of_le_of_ne hAdegree hAd
      by_cases hBd : B.natDegree = d
      · have hA : A.natDegree + (d - A.natDegree) = d :=
          Nat.add_sub_of_le hAdegree
        calc
          Polynomial.resultant A B d d =
              Polynomial.resultant A B
                (A.natDegree + (d - A.natDegree)) B.natDegree := by
            rw [hA, hBd]
          _ = (-1) ^ (B.natDegree * (d - A.natDegree)) *
                B.coeff B.natDegree ^ (d - A.natDegree) *
                  Polynomial.resultant A B A.natDegree B.natDegree := by
            rw [Polynomial.resultant_add_left_deg]
            exact le_rfl
          _ = 0 := by simp [hstandard]
      · have hBlt : B.natDegree < d := lt_of_le_of_ne hBdegree hBd
        exact Polynomial.resultant_eq_zero_of_lt_lt
          A B d d hAlt hBlt
  · push Not at hnonzero
    rcases hnonzero with ⟨rfl, rfl⟩
    rcases d with _ | d <;> simp_all

/-- A non-coprime specialization is a root of the conjugate resultant. -/
theorem conjugateResultant_eval_eq_zero_of_not_isCoprime
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (w : F)
    (hdegree : 0 < max P.natDegree Q.natDegree)
    (hpow : sigma w = w ^ p)
    (hbad : ¬IsCoprime (affinePolynomial P Q w)
      ((affinePolynomial P Q w).map sigma.toRingHom)) :
    (conjugateResultant sigma p P Q).eval w = 0 := by
  let d := max P.natDegree Q.natDegree
  rw [show (conjugateResultant sigma p P Q).eval w =
      Polynomial.resultant
        ((affineBivariate P Q).map (Polynomial.evalRingHom w))
        ((conjugateAffineBivariate sigma p P Q).map
          (Polynomial.evalRingHom w)) d d by
    simp [conjugateResultant, d]]
  rw [affineBivariate_specialize,
    conjugateAffineBivariate_specialize sigma p P Q w hpow]
  apply resultant_fixed_same_degree_eq_zero_of_not_isCoprime
  · exact (affinePolynomial_natDegree_le P Q w).trans le_rfl
  · exact Polynomial.natDegree_map_le.trans
      ((affinePolynomial_natDegree_le P Q w).trans le_rfl)
  · exact hdegree
  · exact hbad

/-- The finite set of slopes where an affine member is not coprime to its
coefficient conjugate. -/
noncomputable def nonCoprimeConjugateSlopes
    (T : Finset F) (sigma : F ≃+* F) (P Q : F[X]) : Finset F := by
  classical
  exact T.filter (fun w ↦ ¬IsCoprime (affinePolynomial P Q w)
    ((affinePolynomial P Q w).map sigma.toRingHom))

/-- Once nonzeroness is supplied, ordinary root counting bounds every
conjugate-coprimality failure by `d*(p+1)`. -/
theorem card_nonCoprimeConjugateSlopes_le
    [DecidableEq F]
    (T : Finset F) (sigma : F ≃+* F) (p : ℕ) (P Q : F[X])
    (hdegree : 0 < max P.natDegree Q.natDegree)
    (hpow : ∀ w ∈ T, sigma w = w ^ p)
    (hresultant : conjugateResultant sigma p P Q ≠ 0) :
    (nonCoprimeConjugateSlopes T sigma P Q).card ≤
      max P.natDegree Q.natDegree * (p + 1) := by
  classical
  let Bad := nonCoprimeConjugateSlopes T sigma P Q
  let R := conjugateResultant sigma p P Q
  have hsubset : Bad ⊆ R.roots.toFinset := by
    intro w hw
    have hw' : w ∈ T ∧ ¬IsCoprime (affinePolynomial P Q w)
        ((affinePolynomial P Q w).map sigma.toRingHom) := by
      have hmem : w ∈ nonCoprimeConjugateSlopes T sigma P Q := by
        simpa only [Bad] using hw
      unfold nonCoprimeConjugateSlopes at hmem
      exact Finset.mem_filter.mp hmem
    have hroot : R.eval w = 0 := by
      exact conjugateResultant_eval_eq_zero_of_not_isCoprime
        sigma p P Q w hdegree (hpow w hw'.1) hw'.2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hresultant]
    exact hroot
  calc
    Bad.card ≤ R.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ R.roots.card := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := Polynomial.card_roots' R
    _ ≤ max P.natDegree Q.natDegree * (p + 1) :=
      conjugateResultant_natDegree_le sigma p P Q

end ProximityPrize.SubmissionLower
