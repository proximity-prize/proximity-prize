import ProximityPrize.SubmissionLower.BCHKSFrobeniusCofactor6400
import ProximityPrize.SubmissionLower.BCHKSFactorPigeon

/-!
# Exceptional slopes for a Frobenius amplitude atom

The first coprimality failure in the cofactor finish does not require a
resultant.  Every irreducible factor of the fixed amplitude multiplier can
divide at most one member of a coprime affine polynomial pencil.  Assigning
each bad slope one normalized factor therefore gives the sharp bound by the
degree of the amplitude multiplier.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F]

/-- A nonunit irreducible factor cannot divide two distinct members of an
affine pencil whose two coefficient polynomials are coprime. -/
theorem slope_eq_of_irreducible_dvd_two_affinePolynomials
    (P Q q : F[X]) (u v : F)
    (hPQ : IsCoprime P Q) (hq : Irreducible q)
    (hqu : q ∣ affinePolynomial P Q u)
    (hqv : q ∣ affinePolynomial P Q v) :
    u = v := by
  by_contra huv
  have hscalar : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hqScalarQ : q ∣ Polynomial.C (u - v) * Q := by
    have hsub := dvd_sub hqu hqv
    have heq : affinePolynomial P Q u - affinePolynomial P Q v =
        Polynomial.C (u - v) * Q := by
      simp only [affinePolynomial, Polynomial.C_sub]
      ring
    rw [heq] at hsub
    exact hsub
  have hqQ : q ∣ Q :=
    (Polynomial.isUnit_C.mpr hscalar.isUnit).dvd_mul_left.mp hqScalarQ
  have hqP : q ∣ P := by
    have hqScaledQ : q ∣ Polynomial.C u * Q :=
      dvd_mul_of_dvd_right hqQ _
    have hsub := dvd_sub hqu hqScaledQ
    simpa only [affinePolynomial, add_sub_cancel_right] using hsub
  exact hq.not_isUnit (hPQ.isUnit_of_dvd' hqP hqQ)

/-- Every failure of coprimality with a fixed nonzero polynomial owns a
normalized irreducible factor of that polynomial. -/
theorem exists_normalizedFactor_dvd_affinePolynomial_of_not_isCoprime
    [DecidableEq F]
    (P Q A : F[X]) (w : F) (hA : A ≠ 0)
    (hbad : ¬IsCoprime (affinePolynomial P Q w) A) :
    ∃ q ∈ (UniqueFactorizationMonoid.normalizedFactors A).toFinset,
      q ∣ affinePolynomial P Q w := by
  have hirr : ∃ r : F[X], Irreducible r ∧
      r ∣ affinePolynomial P Q w ∧ r ∣ A := by
    by_contra hnone
    apply hbad
    apply isCoprime_of_irreducible_dvd
    · intro hzero
      exact hA hzero.2
    · intro r hr hrdirect hrA
      exact hnone ⟨r, hr, hrdirect, hrA⟩
  obtain ⟨r, hr, hrdirect, hrA⟩ := hirr
  obtain ⟨q, hqfactor, hrq⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hA hr hrA
  refine ⟨q, Multiset.mem_toFinset.mpr hqfactor, ?_⟩
  exact hrq.dvd_iff_dvd_left.mp hrdirect

/-- The finite set of slopes where an affine polynomial pencil is not
coprime to a fixed polynomial. -/
noncomputable def nonCoprimeAffineSlopes
    (T : Finset F) (P Q A : F[X]) : Finset F := by
  classical
  exact T.filter (fun w ↦ ¬IsCoprime (affinePolynomial P Q w) A)

/-- At most `deg A` slopes in any finite set can make `P+wQ` non-coprime to
the fixed polynomial `A`. -/
theorem card_filter_not_isCoprime_affinePolynomial_le_natDegree
    [DecidableEq F]
    (T : Finset F) (P Q A : F[X])
    (hPQ : IsCoprime P Q) (hA : A ≠ 0) :
    (nonCoprimeAffineSlopes T P Q A).card ≤
      A.natDegree := by
  classical
  let Bad := nonCoprimeAffineSlopes T P Q A
  let Factors := (UniqueFactorizationMonoid.normalizedFactors A).toFinset
  have hfactor (w : {w // w ∈ Bad}) :
      ∃ q ∈ Factors, q ∣ affinePolynomial P Q w.1 := by
    have hwmem : w.1 ∈ nonCoprimeAffineSlopes T P Q A := by
      simpa only [Bad] using w.2
    unfold nonCoprimeAffineSlopes at hwmem
    have hwbad :
        ¬IsCoprime (affinePolynomial P Q w.1) A :=
      (Finset.mem_filter.mp hwmem).2
    exact exists_normalizedFactor_dvd_affinePolynomial_of_not_isCoprime
      P Q A w.1 hA hwbad
  let pick : {w // w ∈ Bad} → {q // q ∈ Factors} := fun w ↦
    ⟨Classical.choose (hfactor w),
      (Classical.choose_spec (hfactor w)).1⟩
  have hpickDvd (w : {w // w ∈ Bad}) :
      (pick w).1 ∣ affinePolynomial P Q w.1 :=
    (Classical.choose_spec (hfactor w)).2
  have hpickIrreducible (w : {w // w ∈ Bad}) :
      Irreducible (pick w).1 := by
    have hwFactor : (pick w).1 ∈
        UniqueFactorizationMonoid.normalizedFactors A := by
      exact Multiset.mem_toFinset.mp (pick w).2
    exact UniqueFactorizationMonoid.irreducible_of_normalized_factor
      (pick w).1 hwFactor
  have hpickInjective : Function.Injective pick := by
    intro u v huv
    apply Subtype.ext
    apply slope_eq_of_irreducible_dvd_two_affinePolynomials
      P Q (pick u).1 u.1 v.1 hPQ (hpickIrreducible u)
      (hpickDvd u)
    simpa only [huv] using hpickDvd v
  have hcard : Fintype.card {w // w ∈ Bad} ≤
      Fintype.card {q // q ∈ Factors} :=
    Fintype.card_le_of_injective pick hpickInjective
  have hfactorCard : Factors.card ≤ A.natDegree := by
    exact normalizedFactors_toFinset_card_le_natDegree_of_field A hA
  have hcard' : Bad.card ≤ Factors.card := by
    simpa only [Fintype.card_coe] using hcard
  simpa only [Bad] using hcard'.trans hfactorCard

variable {S : Finset F} {error₀ error₁ : F → F}
  {sigma : F ≃+* F} {z : F} {h : ℕ}

/-- Atom-level form of the sharp fixed-amplitude exceptional-slope bound. -/
theorem FrobeniusAmplitudeAtom.card_bad_amplitude_slopes_le
    [DecidableEq F]
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h)
    (T : Finset F) :
    (nonCoprimeAffineSlopes T atom.direct₀ atom.direct₁
      atom.amplitudeMultiplier).card ≤
      atom.amplitudeMultiplier.natDegree := by
  exact card_filter_not_isCoprime_affinePolynomial_le_natDegree
    T atom.direct₀ atom.direct₁ atom.amplitudeMultiplier
      atom.direct_coprime atom.amplitudeMultiplier_ne_zero

end ProximityPrize.SubmissionLower
