import ProximityPrize.SubmissionLower.BCHKSFrobeniusConjugateResultant6400
import ProximityPrize.SubmissionLower.BCHKSUniversalResultantSelection

/-!
# Nonvanishing of the conjugate-pencil resultant

The direct affine pencil is primitive and linear after swapping the root and
challenge variables.  If its conjugate resultant vanished, irreducibility
would make the direct pencil divide the conjugate pencil.  Evaluation at the
generic root `Z = -P/Q` then forces both `P^p | sigma(P)` and
`Q^p | sigma(Q)`, contradicting positive direct degree when `1 < p`.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate

variable {F : Type} [Field F]

theorem direct_pair_left_ne_zero_of_degree_pos
    (P Q : F[X]) (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree) : P ≠ 0 := by
  intro hP
  have hQunit : IsUnit Q := by
    rw [hP] at hcoprime
    exact isCoprime_zero_left.mp hcoprime
  have hQdegree : Q.natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hQunit
  simp [hP, hQdegree] at hdegree

theorem direct_pair_right_ne_zero_of_degree_pos
    (P Q : F[X]) (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree) : Q ≠ 0 := by
  intro hQ
  have hPunit : IsUnit P := by
    rw [hQ] at hcoprime
    exact isCoprime_zero_right.mp hcoprime
  have hPdegree : P.natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hPunit
  simp [hQ, hPdegree] at hdegree

/-- Before swapping variables, a coprime affine pencil is a primitive linear
polynomial and hence irreducible over `F[X]`. -/
theorem affineCoefficientPolynomial_irreducible
    (P Q : F[X]) (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree) :
    Irreducible (affineCoefficientPolynomial P Q) := by
  have hQ : Q ≠ 0 :=
    direct_pair_right_ne_zero_of_degree_pos P Q hcoprime hdegree
  have hirr : Irreducible
      (Polynomial.C Q * Polynomial.X + Polynomial.C P : F[X][Y]) :=
    Polynomial.irreducible_C_mul_X_add_C hQ hcoprime.symm.isRelPrime
  rw [show affineCoefficientPolynomial P Q =
      (Polynomial.C Q * Polynomial.X + Polynomial.C P : F[X][Y]) by
    unfold affineCoefficientPolynomial
    ring]
  exact hirr

/-- Swapping the challenge and root variables preserves irreducibility. -/
theorem affineBivariate_irreducible
    (P Q : F[X]) (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree) :
    Irreducible (affineBivariate P Q) := by
  rw [← swap_affineCoefficientPolynomial]
  exact (affineCoefficientPolynomial_irreducible P Q hcoprime hdegree).map
    Polynomial.Bivariate.swap

theorem conjugateAffineBivariate_coeff
    (sigma : F ≃+* F) (p i : ℕ) (P Q : F[X]) :
    (conjugateAffineBivariate sigma p P Q).coeff i =
      Polynomial.C (sigma (P.coeff i)) +
        Polynomial.X ^ p * Polynomial.C (sigma (Q.coeff i)) := by
  unfold conjugateAffineBivariate
  rw [Polynomial.coeff_add, Polynomial.coeff_map,
    Polynomial.coeff_C_mul, Polynomial.coeff_map]
  simp

theorem left_natDegree_le_conjugateAffineBivariate
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (hp : 0 < p)
    (hP : P ≠ 0) :
    P.natDegree ≤ (conjugateAffineBivariate sigma p P Q).natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  rw [conjugateAffineBivariate_coeff]
  intro hzero
  have hconstant := congrArg
    (fun A : F[X] ↦ A.coeff 0) hzero
  have hlead : P.coeff P.natDegree ≠ 0 := by
    simpa only [Polynomial.coeff_natDegree] using
      (Polynomial.leadingCoeff_ne_zero.mpr hP)
  have h0p : 0 ≠ p := (Nat.ne_of_gt hp).symm
  rw [show Polynomial.X ^ p * Polynomial.C (sigma (Q.coeff P.natDegree)) =
      Polynomial.C (sigma (Q.coeff P.natDegree)) * Polynomial.X ^ p by ring]
    at hconstant
  simp [h0p] at hconstant
  have hsigma : sigma (P.coeff P.natDegree) = sigma 0 := by
    simpa using hconstant
  exact hlead (sigma.injective hsigma)

theorem right_natDegree_le_conjugateAffineBivariate
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (hp : 0 < p)
    (hQ : Q ≠ 0) :
    Q.natDegree ≤ (conjugateAffineBivariate sigma p P Q).natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  rw [conjugateAffineBivariate_coeff]
  intro hzero
  have hpcoeff := congrArg
    (fun A : F[X] ↦ A.coeff p) hzero
  have hlead : Q.coeff Q.natDegree ≠ 0 := by
    simpa only [Polynomial.coeff_natDegree] using
      (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  have hp0 : p ≠ 0 := Nat.ne_of_gt hp
  rw [show Polynomial.X ^ p * Polynomial.C (sigma (Q.coeff Q.natDegree)) =
      Polynomial.C (sigma (Q.coeff Q.natDegree)) * Polynomial.X ^ p by ring]
    at hpcoeff
  simp [Polynomial.coeff_add, Polynomial.coeff_C, hp0] at hpcoeff
  have hsigma : sigma (Q.coeff Q.natDegree) = sigma 0 := by
    simpa using hpcoeff
  exact hlead (sigma.injective hsigma)

/-- Positive Frobenius exponent separates the constant and `Z^p`
coefficients, so the conjugate pencil also has the full direct degree. -/
theorem conjugateAffineBivariate_natDegree_eq_max
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (hp : 0 < p)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (conjugateAffineBivariate sigma p P Q).natDegree =
      max P.natDegree Q.natDegree := by
  apply Nat.le_antisymm
  · exact conjugateAffineBivariate_natDegree_le sigma p P Q
  · exact max_le
      (left_natDegree_le_conjugateAffineBivariate sigma p P Q hp hP)
      (right_natDegree_le_conjugateAffineBivariate sigma p P Q hp hQ)

/-- Vanishing of the fixed-degree obstruction would force divisibility by the
irreducible direct pencil. -/
theorem affineBivariate_dvd_conjugate_of_resultant_eq_zero
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (hp : 0 < p)
    (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree)
    (hzero : conjugateResultant sigma p P Q = 0) :
    affineBivariate P Q ∣ conjugateAffineBivariate sigma p P Q := by
  have hP : P ≠ 0 :=
    direct_pair_left_ne_zero_of_degree_pos P Q hcoprime hdegree
  have hQ : Q ≠ 0 :=
    direct_pair_right_ne_zero_of_degree_pos P Q hcoprime hdegree
  have haffine : (affineBivariate P Q).natDegree =
      max P.natDegree Q.natDegree := affineBivariate_natDegree_eq_max P Q
  have hconjugate : (conjugateAffineBivariate sigma p P Q).natDegree =
      max P.natDegree Q.natDegree :=
    conjugateAffineBivariate_natDegree_eq_max sigma p P Q hp hP hQ
  have hstandard : Polynomial.resultant (affineBivariate P Q)
      (conjugateAffineBivariate sigma p P Q) = 0 := by
    simpa only [conjugateResultant, haffine, hconjugate] using hzero
  have hcommuted : Polynomial.resultant
      (conjugateAffineBivariate sigma p P Q) (affineBivariate P Q) = 0 := by
    rw [Polynomial.resultant_comm, hstandard]
    simp
  exact irreducible_dvd_of_resultant_eq_zero_nonmonic
    (conjugateAffineBivariate sigma p P Q) (affineBivariate P Q)
    (affineBivariate_irreducible P Q hcoprime hdegree)
    (haffine.symm ▸ hdegree) hcommuted

/-- The conjugate pencil before swapping the challenge and root variables. -/
noncomputable def conjugateCoefficientPolynomial
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) : F[X][Y] :=
  Polynomial.C (P.map sigma.toRingHom) +
    Polynomial.X ^ p * Polynomial.C (Q.map sigma.toRingHom)

theorem swap_conjugateAffineBivariate
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) :
    Polynomial.Bivariate.swap
      (conjugateAffineBivariate sigma p P Q) =
        conjugateCoefficientPolynomial sigma p P Q := by
  have hpow : Polynomial.Bivariate.swap
      (Polynomial.C (Polynomial.X ^ p) : F[X][Y]) =
        (Polynomial.X ^ p : F[X][Y]) := by
    rw [Polynomial.Bivariate.swap_C, Polynomial.map_pow,
      Polynomial.map_X]
  unfold conjugateAffineBivariate conjugateCoefficientPolynomial
  rw [map_add, map_mul,
    Polynomial.Bivariate.swap_map_C,
    hpow,
    Polynomial.Bivariate.swap_map_C]

/-- The divisibility forced by a zero resultant remains literal after
swapping the two polynomial variables. -/
theorem affineCoefficientPolynomial_dvd_conjugate_of_resultant_eq_zero
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (hp : 0 < p)
    (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree)
    (hzero : conjugateResultant sigma p P Q = 0) :
    affineCoefficientPolynomial P Q ∣
      conjugateCoefficientPolynomial sigma p P Q := by
  have hdiv : affineBivariate P Q ∣
      conjugateAffineBivariate sigma p P Q :=
    affineBivariate_dvd_conjugate_of_resultant_eq_zero
      sigma p P Q hp hcoprime hdegree hzero
  have hswapAffine : Polynomial.Bivariate.swap (affineBivariate P Q) =
      affineCoefficientPolynomial P Q := by
    rw [← swap_affineCoefficientPolynomial,
      Polynomial.Bivariate.swap_swap_apply]
  obtain ⟨K, hK⟩ := hdiv
  refine ⟨Polynomial.Bivariate.swap K, ?_⟩
  calc
    conjugateCoefficientPolynomial sigma p P Q =
        Polynomial.Bivariate.swap
          (conjugateAffineBivariate sigma p P Q) :=
      (swap_conjugateAffineBivariate sigma p P Q).symm
    _ = Polynomial.Bivariate.swap (affineBivariate P Q * K) :=
      congrArg (fun A : F[X][Y] ↦ Polynomial.Bivariate.swap A) hK
    _ = Polynomial.Bivariate.swap (affineBivariate P Q) *
        Polynomial.Bivariate.swap K := map_mul _ _ _
    _ = affineCoefficientPolynomial P Q *
        Polynomial.Bivariate.swap K := by rw [hswapAffine]

/-- The root of `P+Z*Q` over the rational function field `F(X)`. -/
noncomputable def genericAffineRoot (P Q : F[X]) : RatFunc F :=
  -(algebraMap F[X] (RatFunc F) P) /
    algebraMap F[X] (RatFunc F) Q

theorem eval₂_affineCoefficientPolynomial_genericAffineRoot
    (P Q : F[X]) (hQ : Q ≠ 0) :
    Polynomial.eval₂ (algebraMap F[X] (RatFunc F))
      (genericAffineRoot P Q) (affineCoefficientPolynomial P Q) = 0 := by
  have hmapQ : algebraMap F[X] (RatFunc F) Q ≠ 0 :=
    by simpa using (IsFractionRing.injective F[X] (RatFunc F)).ne hQ
  simp [affineCoefficientPolynomial, genericAffineRoot]
  field_simp
  ring

theorem eval₂_conjugateCoefficientPolynomial
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (z : RatFunc F) :
    Polynomial.eval₂ (algebraMap F[X] (RatFunc F)) z
      (conjugateCoefficientPolynomial sigma p P Q) =
      algebraMap F[X] (RatFunc F) (P.map sigma.toRingHom) +
        z ^ p * algebraMap F[X] (RatFunc F) (Q.map sigma.toRingHom) := by
  simp [conjugateCoefficientPolynomial]
  ring

/-- A zero obstruction would make the conjugate pencil vanish at the generic
root of the direct pencil. -/
theorem generic_conjugate_relation_of_resultant_eq_zero
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (hp : 0 < p)
    (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree)
    (hzero : conjugateResultant sigma p P Q = 0) :
    algebraMap F[X] (RatFunc F) (P.map sigma.toRingHom) +
        genericAffineRoot P Q ^ p *
          algebraMap F[X] (RatFunc F) (Q.map sigma.toRingHom) = 0 := by
  have hQ : Q ≠ 0 :=
    direct_pair_right_ne_zero_of_degree_pos P Q hcoprime hdegree
  have hdiv :=
    affineCoefficientPolynomial_dvd_conjugate_of_resultant_eq_zero
      sigma p P Q hp hcoprime hdegree hzero
  obtain ⟨K, hK⟩ := hdiv
  have heval := congrArg
    (Polynomial.eval₂ (algebraMap F[X] (RatFunc F))
      (genericAffineRoot P Q)) hK
  rw [Polynomial.eval₂_mul,
    eval₂_affineCoefficientPolynomial_genericAffineRoot P Q hQ,
    zero_mul] at heval
  rw [eval₂_conjugateCoefficientPolynomial] at heval
  exact heval

/-- Clearing the generic denominator turns hypothetical resultant vanishing
into a polynomial identity back over `F`. -/
theorem cleared_conjugate_identity_of_resultant_eq_zero
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (hp : 0 < p)
    (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree)
    (hzero : conjugateResultant sigma p P Q = 0) :
    P.map sigma.toRingHom * Q ^ p +
        (-P) ^ p * Q.map sigma.toRingHom = 0 := by
  have hQ : Q ≠ 0 :=
    direct_pair_right_ne_zero_of_degree_pos P Q hcoprime hdegree
  have hmapQ : algebraMap F[X] (RatFunc F) Q ≠ 0 := by
    simpa using (IsFractionRing.injective F[X] (RatFunc F)).ne hQ
  have hrelation := generic_conjugate_relation_of_resultant_eq_zero
    sigma p P Q hp hcoprime hdegree hzero
  unfold genericAffineRoot at hrelation
  apply IsFractionRing.injective F[X] (RatFunc F)
  simp only [map_add, map_mul, map_pow, map_neg, map_zero]
  calc
    algebraMap F[X] (RatFunc F) (P.map sigma.toRingHom) *
          algebraMap F[X] (RatFunc F) Q ^ p +
        (-algebraMap F[X] (RatFunc F) P) ^ p *
          algebraMap F[X] (RatFunc F) (Q.map sigma.toRingHom) =
        (algebraMap F[X] (RatFunc F) (P.map sigma.toRingHom) +
          (-algebraMap F[X] (RatFunc F) P /
              algebraMap F[X] (RatFunc F) Q) ^ p *
            algebraMap F[X] (RatFunc F) (Q.map sigma.toRingHom)) *
          algebraMap F[X] (RatFunc F) Q ^ p := by
      rw [div_pow]
      field_simp [hmapQ]
    _ = 0 := by rw [hrelation, zero_mul]

/-- The cleared identity and direct coprimality force both `p`-th powers to
divide their coefficient conjugates. -/
theorem direct_powers_dvd_conjugates_of_resultant_eq_zero
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (hp : 0 < p)
    (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree)
    (hzero : conjugateResultant sigma p P Q = 0) :
    P ^ p ∣ P.map sigma.toRingHom ∧
      Q ^ p ∣ Q.map sigma.toRingHom := by
  have hidentity := cleared_conjugate_identity_of_resultant_eq_zero
    sigma p P Q hp hcoprime hdegree hzero
  have heq : P.map sigma.toRingHom * Q ^ p =
      -((-P) ^ p * Q.map sigma.toRingHom) :=
    eq_neg_of_add_eq_zero_left hidentity
  have hPproduct : P ^ p ∣ P.map sigma.toRingHom * Q ^ p := by
    rw [heq]
    exact ((pow_dvd_pow_of_dvd (dvd_neg.mpr dvd_rfl) p).mul_right
      (Q.map sigma.toRingHom)).neg_right
  have hPdvd : P ^ p ∣ P.map sigma.toRingHom :=
    hcoprime.pow.dvd_of_dvd_mul_right hPproduct
  have hQleft : Q ^ p ∣ P.map sigma.toRingHom * Q ^ p :=
    dvd_mul_left _ _
  have hQnegative : Q ^ p ∣
      -((-P) ^ p * Q.map sigma.toRingHom) := by
    rw [← heq]
    exact hQleft
  have hQproduct : Q ^ p ∣
      (-P) ^ p * Q.map sigma.toRingHom :=
    hQnegative.of_neg_right
  have hQcoprime : IsCoprime (Q ^ p) ((-P) ^ p) :=
    hcoprime.symm.neg_right.pow
  have hQdvd : Q ^ p ∣ Q.map sigma.toRingHom :=
    hQcoprime.dvd_of_dvd_mul_left hQproduct
  exact ⟨hPdvd, hQdvd⟩

theorem natDegree_eq_zero_of_pow_dvd_equiv_map
    (sigma : F ≃+* F) (p : ℕ) (P : F[X]) (hp : 1 < p)
    (hP : P ≠ 0) (hdvd : P ^ p ∣ P.map sigma.toRingHom) :
    P.natDegree = 0 := by
  have hmapP : P.map sigma.toRingHom ≠ 0 :=
    (Polynomial.map_eq_zero_iff sigma.injective).not.mpr hP
  have hdegree := Polynomial.natDegree_le_of_dvd hdvd hmapP
  rw [Polynomial.natDegree_pow,
    Polynomial.natDegree_map_eq_of_injective sigma.injective] at hdegree
  by_contra hnonzero
  have hpos : 0 < P.natDegree := Nat.pos_of_ne_zero hnonzero
  have hstrict : P.natDegree < p * P.natDegree :=
    lt_mul_of_one_lt_left hpos hp
  exact (Nat.not_lt_of_ge hdegree) hstrict

/-- The conjugate obstruction cannot vanish identically.  The production
hypothesis `d<p` is stronger than necessary: coprimality, positive direct
degree, and `1<p` already suffice. -/
theorem conjugateResultant_ne_zero
    (sigma : F ≃+* F) (p : ℕ) (P Q : F[X]) (hp : 1 < p)
    (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree) :
    conjugateResultant sigma p P Q ≠ 0 := by
  intro hzero
  have hP : P ≠ 0 :=
    direct_pair_left_ne_zero_of_degree_pos P Q hcoprime hdegree
  have hQ : Q ≠ 0 :=
    direct_pair_right_ne_zero_of_degree_pos P Q hcoprime hdegree
  have hdvd := direct_powers_dvd_conjugates_of_resultant_eq_zero
    sigma p P Q (Nat.zero_lt_of_lt hp) hcoprime hdegree hzero
  have hPdegree : P.natDegree = 0 :=
    natDegree_eq_zero_of_pow_dvd_equiv_map sigma p P hp hP hdvd.1
  have hQdegree : Q.natDegree = 0 :=
    natDegree_eq_zero_of_pow_dvd_equiv_map sigma p Q hp hQ hdvd.2
  simp [hPdegree, hQdegree] at hdegree

/-- Unconditional conjugate-exception count for a coprime positive-degree
affine pencil. -/
theorem card_nonCoprimeConjugateSlopes_le_of_coprime
    [DecidableEq F]
    (T : Finset F) (sigma : F ≃+* F) (p : ℕ) (P Q : F[X])
    (hp : 1 < p) (hcoprime : IsCoprime P Q)
    (hdegree : 0 < max P.natDegree Q.natDegree)
    (hpow : ∀ w ∈ T, sigma w = w ^ p) :
    (nonCoprimeConjugateSlopes T sigma P Q).card ≤
      max P.natDegree Q.natDegree * (p + 1) := by
  exact card_nonCoprimeConjugateSlopes_le T sigma p P Q hdegree hpow
    (conjugateResultant_ne_zero sigma p P Q hp hcoprime hdegree)

end ProximityPrize.SubmissionLower
