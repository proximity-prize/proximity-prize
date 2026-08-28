import ProximityPrize.SubmissionLower.BCHKSFrobeniusDegreeDescent6400

/-!
# Transcendental separation for the Frobenius pencil

The universal low-stack branch separates the challenge monomials `Z` and
`W = Z^p`.  This file records the algebraic no-cancellation fact used by the
common-denominator argument: a base-field divisor of a generic linear
combination over `F(W)` must divide both coefficients.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F]

/-- The constant and `W` coefficients of a linear rational function cannot
cancel because `RatFunc.X` is transcendental over the base field. -/
theorem ratFunc_linear_eq_zero_iff (a b : F) :
    algebraMap F (RatFunc F) a +
        RatFunc.X * algebraMap F (RatFunc F) b = 0 ↔
      a = 0 ∧ b = 0 := by
  constructor
  · intro hab
    have hmap : algebraMap F[X] (RatFunc F)
        (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0 := by
      calc
        algebraMap F[X] (RatFunc F)
            (Polynomial.C a + Polynomial.X * Polynomial.C b) =
            RatFunc.C a + RatFunc.C b * RatFunc.X := by simp
        _ = RatFunc.C a + RatFunc.X * RatFunc.C b := by
          rw [mul_comm (RatFunc.C b) RatFunc.X]
        _ = 0 := hab
    have hpoly : Polynomial.C a + Polynomial.X * Polynomial.C b = 0 := by
      apply RatFunc.algebraMap_injective F
      simpa using hmap
    constructor
    · have hcoeff := congrArg (fun P : F[X] ↦ P.coeff 0) hpoly
      simpa using hcoeff
    · have hcoeff := congrArg (fun P : F[X] ↦ P.coeff 1) hpoly
      simpa using hcoeff
  · rintro ⟨rfl, rfl⟩
    simp

/-- Coefficientwise version of `ratFunc_linear_eq_zero_iff` for polynomials
in a second variable. -/
theorem ratFunc_X_smul_map_eq_zero_iff (P Q : F[X]) :
    P.map (algebraMap F (RatFunc F)) +
        (RatFunc.X : RatFunc F) • Q.map (algebraMap F (RatFunc F)) = 0 ↔
      P = 0 ∧ Q = 0 := by
  constructor
  · intro h
    have hcoeff : ∀ n : ℕ, P.coeff n = 0 ∧ Q.coeff n = 0 := by
      intro n
      have hn := congrArg (fun R : (RatFunc F)[X] ↦ R.coeff n) h
      have hn' : algebraMap F (RatFunc F) (P.coeff n) +
          RatFunc.X * algebraMap F (RatFunc F) (Q.coeff n) = 0 := by
        simpa [smul_eq_mul] using hn
      exact (ratFunc_linear_eq_zero_iff (P.coeff n) (Q.coeff n)).mp hn'
    constructor
    · ext n
      simp [hcoeff n]
    · ext n
      simp [hcoeff n]
  · rintro ⟨rfl, rfl⟩
    simp

/-- A monic irreducible polynomial over `F` remains irreducible after the
purely transcendental coefficient extension `F → F(W)`.  The proof swaps
the two polynomial variables, where the polynomial becomes a prime constant,
and then applies Gauss's lemma when passing from `F[W]` to its fraction
field. -/
theorem irreducible_map_ratFunc_of_monic
    (q : F[X]) (hqmonic : q.Monic) (hqirr : Irreducible q) :
    Irreducible (q.map (algebraMap F (RatFunc F))) := by
  classical
  have hprimeConstant : Prime (Polynomial.C q : F[X][X]) :=
    Polynomial.prime_C_iff.mpr hqirr.prime
  have hprimeMapped : Prime (q.map Polynomial.C : F[X][X]) := by
    have hswap : Prime
        (Polynomial.Bivariate.swap (Polynomial.C q : F[X][X])) :=
      (MulEquiv.prime_iff Polynomial.Bivariate.swap.toRingEquiv).mpr
        hprimeConstant
    simpa only [Polynomial.Bivariate.swap_C] using hswap
  have hirrMapped : Irreducible (q.map Polynomial.C : F[X][X]) :=
    hprimeMapped.irreducible
  have hmonicMapped : (q.map Polynomial.C : F[X][X]).Monic :=
    hqmonic.map Polynomial.C
  have hfrac : Irreducible
      ((q.map Polynomial.C).map (algebraMap F[X] (RatFunc F))) :=
    hmonicMapped.irreducible_iff_irreducible_map_fraction_map.mp hirrMapped
  simpa only [Polynomial.map_map, RingHomCompTriple.comp_eq,
    RatFunc.algebraMap_comp_C, RatFunc.algebraMap_eq_C] using hfrac

/-- Let `d,a,b` have base-field coefficients and let `W` be transcendental.
For monic `d`, divisibility of `a+W*b` after extending coefficients to
`F(W)` is equivalent to divisibility of both coefficients over `F`.

This is the precise no-pole-cancellation lemma needed when proving that the
generic rational interpolant has the least common denominator of its two
specializations. -/
theorem monic_map_dvd_generic_linear_iff
    (d a b : F[X]) (hd : d.Monic) :
    d.map (algebraMap F (RatFunc F)) ∣
        a.map (algebraMap F (RatFunc F)) +
          (RatFunc.X : RatFunc F) • b.map (algebraMap F (RatFunc F)) ↔
      d ∣ a ∧ d ∣ b := by
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  constructor
  · intro hdiv
    have hmod :
        (a.map φ + RatFunc.X • b.map φ) %ₘ d.map φ = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (hd.map φ)).2 hdiv
    rw [Polynomial.add_modByMonic, Polynomial.smul_modByMonic,
      ← Polynomial.map_modByMonic φ hd,
      ← Polynomial.map_modByMonic φ hd] at hmod
    have hremainder : a %ₘ d = 0 ∧ b %ₘ d = 0 :=
      (ratFunc_X_smul_map_eq_zero_iff (a %ₘ d) (b %ₘ d)).mp hmod
    exact ⟨(Polynomial.modByMonic_eq_zero_iff_dvd hd).mp hremainder.1,
      (Polynomial.modByMonic_eq_zero_iff_dvd hd).mp hremainder.2⟩
  · rintro ⟨hda, hdb⟩
    have hda' : d.map φ ∣ a.map φ :=
      (Polynomial.map_dvd_map' φ).2 hda
    have hdb' : d.map φ ∣ b.map φ :=
      (Polynomial.map_dvd_map' φ).2 hdb
    apply dvd_add hda'
    rw [Polynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hdb' _

/-- A generic linear combination is coprime to a base polynomial when no
irreducible factor of the base polynomial divides both coefficients.  This
upgrades `monic_map_dvd_generic_linear_iff` from base divisors to arbitrary
factors over `F(W)`: factor `L` over `F`, use
`irreducible_map_ratFunc_of_monic` on every normalized factor, and compare
associated irreducible divisors. -/
theorem generic_linear_isCoprime_of_no_common_irreducible
    (L A B : F[X]) (hL : L ≠ 0)
    (havoid : ∀ q : F[X], q.Monic → Irreducible q → q ∣ L →
      ¬(q ∣ A ∧ q ∣ B)) :
    IsCoprime
      (L.map (algebraMap F (RatFunc F)))
      (A.map (algebraMap F (RatFunc F)) +
        (RatFunc.X : RatFunc F) • B.map (algebraMap F (RatFunc F))) := by
  classical
  letI : DecidableEq F := Classical.decEq F
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  let M := UniqueFactorizationMonoid.normalizedFactors L
  have hLmap : L.map φ ≠ 0 := Polynomial.map_ne_zero hL
  apply isCoprime_of_irreducible_dvd
  · exact fun hzero ↦ hLmap hzero.1
  · intro z hz hzdL hzdGeneric
    have hfactorization : Associated (M.prod.map φ) (L.map φ) :=
      (UniqueFactorizationMonoid.prod_normalizedFactors hL).map
        (Polynomial.mapRingHom φ)
    have hzdProd : z ∣ M.prod.map φ :=
      hfactorization.dvd_iff_dvd_right.mpr hzdL
    have hzdMappedProd :
        z ∣ (M.map (Polynomial.mapRingHom φ)).prod := by
      rw [← map_multiset_prod (Polynomial.mapRingHom φ) M]
      exact hzdProd
    have factor_of_dvd_mapped_prod :
        ∀ T : Multiset F[X],
          z ∣ (T.map (Polynomial.mapRingHom φ)).prod →
            ∃ q ∈ T, z ∣ q.map φ := by
      intro T
      induction T using Multiset.induction_on with
      | empty =>
          intro hzone
          simp only [Multiset.map_zero, Multiset.prod_zero] at hzone
          exact (hz.not_isUnit (isUnit_iff_dvd_one.mpr hzone)).elim
      | @cons q T ih =>
          intro hzprod
          simp only [Multiset.map_cons, Multiset.prod_cons] at hzprod
          rcases hz.prime.dvd_mul.mp hzprod with hzq | hzT
          · exact ⟨q, by simp, hzq⟩
          · obtain ⟨r, hrT, hzr⟩ := ih hzT
            exact ⟨r, by simp [hrT], hzr⟩
    obtain ⟨q, hqM, hzdq⟩ := factor_of_dvd_mapped_prod M hzdMappedProd
    obtain ⟨hqirr, hqmonic, hqL⟩ :=
      (Polynomial.mem_normalizedFactors_iff hL).mp hqM
    have hqmapIrr : Irreducible (q.map φ) :=
      irreducible_map_ratFunc_of_monic q hqmonic hqirr
    have hzassoc : Associated z (q.map φ) :=
      hz.associated_of_dvd hqmapIrr hzdq
    have hqDvdGeneric : q.map φ ∣
        A.map φ + (RatFunc.X : RatFunc F) • B.map φ :=
      hzassoc.dvd_iff_dvd_left.mp hzdGeneric
    have hqBoth : q ∣ A ∧ q ∣ B :=
      (monic_map_dvd_generic_linear_iff q A B hqmonic).mp
        hqDvdGeneric
    exact havoid q hqmonic hqirr hqL hqBoth

/-- Each base coefficient polynomial has degree at most the degree in `X` of
its transcendental linear combination. -/
theorem natDegree_le_generic_linear (A B : F[X]) :
    A.natDegree ≤
        (A.map (algebraMap F (RatFunc F)) +
          (RatFunc.X : RatFunc F) •
            B.map (algebraMap F (RatFunc F))).natDegree ∧
      B.natDegree ≤
        (A.map (algebraMap F (RatFunc F)) +
          (RatFunc.X : RatFunc F) •
            B.map (algebraMap F (RatFunc F))).natDegree := by
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  let P : (RatFunc F)[X] := A.map φ +
    (RatFunc.X : RatFunc F) • B.map φ
  have coefficient_ne_zero_of_left {n : ℕ} (hn : A.coeff n ≠ 0) :
      P.coeff n ≠ 0 := by
    intro hzero
    have hlinear : algebraMap F (RatFunc F) (A.coeff n) +
        RatFunc.X * algebraMap F (RatFunc F) (B.coeff n) = 0 := by
      simpa [P, φ, smul_eq_mul] using hzero
    exact hn ((ratFunc_linear_eq_zero_iff (A.coeff n) (B.coeff n)).mp
      hlinear).1
  have coefficient_ne_zero_of_right {n : ℕ} (hn : B.coeff n ≠ 0) :
      P.coeff n ≠ 0 := by
    intro hzero
    have hlinear : algebraMap F (RatFunc F) (A.coeff n) +
        RatFunc.X * algebraMap F (RatFunc F) (B.coeff n) = 0 := by
      simpa [P, φ, smul_eq_mul] using hzero
    exact hn ((ratFunc_linear_eq_zero_iff (A.coeff n) (B.coeff n)).mp
      hlinear).2
  constructor
  · by_cases hA : A = 0
    · simp [hA]
    · change A.natDegree ≤ P.natDegree
      apply Polynomial.le_natDegree_of_ne_zero
      apply coefficient_ne_zero_of_left
      simpa using Polynomial.leadingCoeff_ne_zero.mpr hA
  · by_cases hB : B = 0
    · simp [hB]
    · change B.natDegree ≤ P.natDegree
      apply Polynomial.le_natDegree_of_ne_zero
      apply coefficient_ne_zero_of_right
      simpa using Polynomial.leadingCoeff_ne_zero.mpr hB

/-- If a generic fraction with base denominator `L` is cross-multiplied
against any other representation, and no irreducible factor of `L` divides
both generic numerator coefficients, then `L` divides the other
denominator. -/
theorem generic_base_denominator_dvd
    (L A B : F[X]) (N D : (RatFunc F)[X])
    (hL : L ≠ 0)
    (havoid : ∀ q : F[X], q.Monic → Irreducible q → q ∣ L →
      ¬(q ∣ A ∧ q ∣ B))
    (hcross :
      N * L.map (algebraMap F (RatFunc F)) =
        (A.map (algebraMap F (RatFunc F)) +
          (RatFunc.X : RatFunc F) •
            B.map (algebraMap F (RatFunc F))) * D) :
    L.map (algebraMap F (RatFunc F)) ∣ D := by
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  let P : (RatFunc F)[X] := A.map φ +
    (RatFunc.X : RatFunc F) • B.map φ
  have hcoprime : IsCoprime (L.map φ) P :=
    generic_linear_isCoprime_of_no_common_irreducible L A B hL havoid
  have hdvdProduct : L.map φ ∣ P * D := by
    rw [← hcross]
    exact dvd_mul_left _ _
  exact hcoprime.dvd_of_dvd_mul_left hdvdProduct

/-- Degree form of `generic_base_denominator_dvd`.  A degree-`<h` generic
interpolant forces the common base denominator and both coefficients of its
generic numerator to have degree `<h`. -/
theorem generic_base_fraction_degree_transfer
    (L A B : F[X]) (N D : (RatFunc F)[X]) (h : ℕ)
    (hL : L ≠ 0) (hD : D ≠ 0)
    (hNdegree : N.natDegree < h) (hDdegree : D.natDegree < h)
    (havoid : ∀ q : F[X], q.Monic → Irreducible q → q ∣ L →
      ¬(q ∣ A ∧ q ∣ B))
    (hcross :
      N * L.map (algebraMap F (RatFunc F)) =
        (A.map (algebraMap F (RatFunc F)) +
          (RatFunc.X : RatFunc F) •
            B.map (algebraMap F (RatFunc F))) * D) :
    L.natDegree < h ∧ A.natDegree < h ∧ B.natDegree < h := by
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  let P : (RatFunc F)[X] := A.map φ +
    (RatFunc.X : RatFunc F) • B.map φ
  have hLmap : L.map φ ≠ 0 := Polynomial.map_ne_zero hL
  have hLdD : L.map φ ∣ D :=
    generic_base_denominator_dvd L A B N D hL havoid hcross
  have hLdegreeMap : (L.map φ).natDegree = L.natDegree :=
    Polynomial.natDegree_map_eq_of_injective φ.injective L
  have hLdegree : L.natDegree < h := by
    rw [← hLdegreeMap]
    exact (Polynomial.natDegree_le_of_dvd hLdD hD).trans_lt hDdegree
  obtain ⟨Q, hQ⟩ := hLdD
  have hQne : Q ≠ 0 := by
    intro hQzero
    apply hD
    simpa [hQzero] using hQ
  have hNP : N = P * Q := by
    apply mul_right_cancel₀ hLmap
    calc
      N * L.map φ = P * D := hcross
      _ = P * (L.map φ * Q) := by rw [hQ]
      _ = (P * Q) * L.map φ := by ring
  by_cases hPzero : P = 0
  · have hABzero : A = 0 ∧ B = 0 :=
      (ratFunc_X_smul_map_eq_zero_iff A B).mp hPzero
    rcases hABzero with ⟨rfl, rfl⟩
    have hh : 0 < h := by
      have : 0 ≤ D.natDegree := Nat.zero_le _
      omega
    exact ⟨hLdegree, by simpa using hh, by simpa using hh⟩
  · have hNne : N ≠ 0 := by
      rw [hNP]
      exact mul_ne_zero hPzero hQne
    have hPdegree : P.natDegree < h :=
      (Polynomial.natDegree_le_of_dvd ⟨Q, hNP⟩ hNne).trans_lt hNdegree
    have hcoeffDegrees := natDegree_le_generic_linear A B
    change A.natDegree ≤ P.natDegree ∧ B.natDegree ≤ P.natDegree at hcoeffDegrees
    exact ⟨hLdegree, hcoeffDegrees.1.trans_lt hPdegree,
      hcoeffDegrees.2.trans_lt hPdegree⟩

/-- Sharp form of `generic_base_fraction_degree_transfer`: the common base
denominator is no larger than the generic denominator, and the two base
numerators are no larger than the generic numerator.  This retains any
degree saved by cancelling the generic relation's gcd. -/
theorem generic_base_fraction_degree_transfer_le
    (L A B : F[X]) (N D : (RatFunc F)[X])
    (hL : L ≠ 0) (hD : D ≠ 0)
    (havoid : ∀ q : F[X], q.Monic → Irreducible q → q ∣ L →
      ¬(q ∣ A ∧ q ∣ B))
    (hcross :
      N * L.map (algebraMap F (RatFunc F)) =
        (A.map (algebraMap F (RatFunc F)) +
          (RatFunc.X : RatFunc F) •
            B.map (algebraMap F (RatFunc F))) * D) :
    L.natDegree ≤ D.natDegree ∧
      A.natDegree ≤ N.natDegree ∧ B.natDegree ≤ N.natDegree := by
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  let P : (RatFunc F)[X] := A.map φ +
    (RatFunc.X : RatFunc F) • B.map φ
  have hLmap : L.map φ ≠ 0 := Polynomial.map_ne_zero hL
  have hLdD : L.map φ ∣ D :=
    generic_base_denominator_dvd L A B N D hL havoid hcross
  have hLdegreeMap : (L.map φ).natDegree = L.natDegree :=
    Polynomial.natDegree_map_eq_of_injective φ.injective L
  have hLdegree : L.natDegree ≤ D.natDegree := by
    rw [← hLdegreeMap]
    exact Polynomial.natDegree_le_of_dvd hLdD hD
  obtain ⟨Q, hQ⟩ := hLdD
  have hQne : Q ≠ 0 := by
    intro hQzero
    apply hD
    simpa [hQzero] using hQ
  have hNP : N = P * Q := by
    apply mul_right_cancel₀ hLmap
    calc
      N * L.map φ = P * D := hcross
      _ = P * (L.map φ * Q) := by rw [hQ]
      _ = (P * Q) * L.map φ := by ring
  by_cases hPzero : P = 0
  · have hABzero : A = 0 ∧ B = 0 :=
      (ratFunc_X_smul_map_eq_zero_iff A B).mp hPzero
    rcases hABzero with ⟨rfl, rfl⟩
    exact ⟨hLdegree, Nat.zero_le _, Nat.zero_le _⟩
  · have hNne : N ≠ 0 := by
      rw [hNP]
      exact mul_ne_zero hPzero hQne
    have hPdegree : P.natDegree ≤ N.natDegree :=
      Polynomial.natDegree_le_of_dvd ⟨Q, hNP⟩ hNne
    have hcoeffDegrees := natDegree_le_generic_linear A B
    change A.natDegree ≤ P.natDegree ∧ B.natDegree ≤ P.natDegree at hcoeffDegrees
    exact ⟨hLdegree, hcoeffDegrees.1.trans hPdegree,
      hcoeffDegrees.2.trans hPdegree⟩

/-- A prime occurring in the quotient of an lcm by its right input must
occur in the left input.  This is the multiplicity comparison needed for
adjusted rational numerators, proved without introducing valuations. -/
theorem prime_dvd_lcm_div_right
    [DecidableEq F]
    (D₀ D₁ q : F[X]) (hD₁ : D₁ ≠ 0)
    (hdiv : q ∣ lcm D₀ D₁ / D₁) :
    q ∣ D₀ := by
  have hD₁L : D₁ ∣ lcm D₀ D₁ := dvd_lcm_right D₀ D₁
  have hcancel : D₁ * (lcm D₀ D₁ / D₁) = lcm D₀ D₁ :=
    EuclideanDomain.mul_div_cancel' hD₁ hD₁L
  obtain ⟨T, hT⟩ := hdiv
  have hqD₁L : q * D₁ ∣ lcm D₀ D₁ := by
    refine ⟨T, ?_⟩
    calc
      lcm D₀ D₁ = D₁ * (lcm D₀ D₁ / D₁) := hcancel.symm
      _ = D₁ * (q * T) := by rw [hT]
      _ = q * D₁ * T := by ring
  have hqD₁Product : q * D₁ ∣ D₀ * D₁ :=
    hqD₁L.trans (lcm_dvd_mul D₀ D₁)
  exact (mul_dvd_mul_iff_right hD₁).mp hqD₁Product

/-- Symmetric form of `prime_dvd_lcm_div_right`. -/
theorem prime_dvd_lcm_div_left
    [DecidableEq F]
    (D₀ D₁ q : F[X]) (hD₀ : D₀ ≠ 0)
    (hdiv : q ∣ lcm D₀ D₁ / D₀) :
    q ∣ D₁ := by
  rw [lcm_comm] at hdiv
  exact prime_dvd_lcm_div_right D₁ D₀ q hD₀ hdiv

/-- Reduced fractions retain no common irreducible factor after their
numerators are lifted to the least common denominator. -/
theorem lcm_adjusted_numerators_no_common_irreducible
    [DecidableEq F]
    (N₀ D₀ N₁ D₁ : F[X])
    (hD₀ : D₀ ≠ 0) (hD₁ : D₁ ≠ 0)
    (hcoprime₀ : IsCoprime N₀ D₀)
    (hcoprime₁ : IsCoprime N₁ D₁) :
    ∀ q : F[X], q.Monic → Irreducible q → q ∣ lcm D₀ D₁ →
      ¬(q ∣ N₀ * (lcm D₀ D₁ / D₀) ∧
        q ∣ N₁ * (lcm D₀ D₁ / D₁)) := by
  classical
  intro q hqmonic hqirr hqL hcommon
  let L := lcm D₀ D₁
  have hL : L ≠ 0 := by
    rw [Ne, lcm_eq_zero_iff]
    exact not_or_intro hD₀ hD₁
  have hqprime : Prime q := hqirr.prime
  have hq₀ := hqprime.dvd_mul.mp hcommon.1
  have hq₁ := hqprime.dvd_mul.mp hcommon.2
  have quotient₀_forces_right
      (hquot : q ∣ L / D₀) : q ∣ D₁ := by
    exact prime_dvd_lcm_div_left D₀ D₁ q hD₀ hquot
  have quotient₁_forces_left
      (hquot : q ∣ L / D₁) : q ∣ D₀ := by
    exact prime_dvd_lcm_div_right D₀ D₁ q hD₁ hquot
  rcases hq₀ with hqN₀ | hqQ₀
  · rcases hq₁ with hqN₁ | hqQ₁
    · rcases hqprime.dvd_lcm.mp hqL with hqD₀ | hqD₁
      · exact hqirr.not_isUnit
          (hcoprime₀.isUnit_of_dvd' hqN₀ hqD₀)
      · exact hqirr.not_isUnit
          (hcoprime₁.isUnit_of_dvd' hqN₁ hqD₁)
    · exact hqirr.not_isUnit
        (hcoprime₀.isUnit_of_dvd' hqN₀
          (quotient₁_forces_left hqQ₁))
  · rcases hq₁ with hqN₁ | hqQ₁
    · exact hqirr.not_isUnit
        (hcoprime₁.isUnit_of_dvd' hqN₁
          (quotient₀_forces_right hqQ₀))
    · have hqD₀L : q * D₀ ∣ L := by
        obtain ⟨T, hT⟩ := hqQ₀
        refine ⟨T, ?_⟩
        calc
          L = D₀ * (L / D₀) :=
            (EuclideanDomain.mul_div_cancel' hD₀
              (dvd_lcm_left D₀ D₁)).symm
          _ = D₀ * (q * T) := by rw [hT]
          _ = q * D₀ * T := by ring
      have hqD₁L : q * D₁ ∣ L := by
        obtain ⟨T, hT⟩ := hqQ₁
        refine ⟨T, ?_⟩
        calc
          L = D₁ * (L / D₁) :=
            (EuclideanDomain.mul_div_cancel' hD₁
              (dvd_lcm_right D₀ D₁)).symm
          _ = D₁ * (q * T) := by rw [hT]
          _ = q * D₁ * T := by ring
      have hqLself : q * L ∣ L := by
        have hlcm : lcm (q * D₀) (q * D₁) ∣ L :=
          lcm_dvd hqD₀L hqD₁L
        rw [lcm_mul_left, hqmonic.normalize_eq_self] at hlcm
        exact hlcm
      have hqOne : q ∣ (1 : F[X]) := by
        apply (mul_dvd_mul_iff_right hL).mp
        simpa using hqLself
      exact hqirr.not_isUnit (isUnit_iff_dvd_one.mpr hqOne)

/-- Convert the cross identity obtained directly from two denominators into
the least-common-denominator identity used by the degree-transfer theorem. -/
theorem lcm_cross_identity_of_product_cross_identity
    [DecidableEq F]
    (N₀ D₀ N₁ D₁ : F[X]) (N D : (RatFunc F)[X])
    (hD₀ : D₀ ≠ 0) (hD₁ : D₁ ≠ 0)
    (hcross :
      N * (D₀.map (algebraMap F (RatFunc F)) *
          D₁.map (algebraMap F (RatFunc F))) =
        D * (N₀.map (algebraMap F (RatFunc F)) *
            D₁.map (algebraMap F (RatFunc F)) +
          Polynomial.C (RatFunc.X : RatFunc F) *
            (N₁.map (algebraMap F (RatFunc F)) *
              D₀.map (algebraMap F (RatFunc F))))) :
    N * (lcm D₀ D₁).map (algebraMap F (RatFunc F)) =
      ((N₀ * (lcm D₀ D₁ / D₀)).map
          (algebraMap F (RatFunc F)) +
        (RatFunc.X : RatFunc F) •
          (N₁ * (lcm D₀ D₁ / D₁)).map
            (algebraMap F (RatFunc F))) * D := by
  let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
  let L : F[X] := lcm D₀ D₁
  let C : F[X] := (D₀ * D₁) / L
  let E₀ : F[X] := L / D₀
  let E₁ : F[X] := L / D₁
  have hL : L ≠ 0 := by
    dsimp only [L]
    rw [Ne, lcm_eq_zero_iff]
    exact not_or_intro hD₀ hD₁
  have hLC : L * C = D₀ * D₁ := by
    exact EuclideanDomain.mul_div_cancel' hL (lcm_dvd_mul D₀ D₁)
  have hC : C ≠ 0 := by
    intro hCzero
    have hproductZero : D₀ * D₁ = 0 := by
      rw [← hLC, hCzero, mul_zero]
    exact (mul_ne_zero hD₀ hD₁) hproductZero
  have hE₀C : E₀ * C = D₁ := by
    apply mul_left_cancel₀ hD₀
    calc
      D₀ * (E₀ * C) = (D₀ * E₀) * C := by ring
      _ = L * C := by
        rw [show D₀ * E₀ = L by
          exact EuclideanDomain.mul_div_cancel' hD₀
            (dvd_lcm_left D₀ D₁)]
      _ = D₀ * D₁ := hLC
  have hE₁C : E₁ * C = D₀ := by
    apply mul_left_cancel₀ hD₁
    calc
      D₁ * (E₁ * C) = (D₁ * E₁) * C := by ring
      _ = L * C := by
        rw [show D₁ * E₁ = L by
          exact EuclideanDomain.mul_div_cancel' hD₁
            (dvd_lcm_right D₀ D₁)]
      _ = D₁ * D₀ := by rw [hLC, mul_comm D₀ D₁]
  have hLCmap : L.map φ * C.map φ = D₀.map φ * D₁.map φ := by
    simpa only [Polynomial.map_mul] using
      congrArg (fun P : F[X] ↦ P.map φ) hLC
  have hE₀Cmap : E₀.map φ * C.map φ = D₁.map φ := by
    simpa only [Polynomial.map_mul] using
      congrArg (fun P : F[X] ↦ P.map φ) hE₀C
  have hE₁Cmap : E₁.map φ * C.map φ = D₀.map φ := by
    simpa only [Polynomial.map_mul] using
      congrArg (fun P : F[X] ↦ P.map φ) hE₁C
  have hCmap : C.map φ ≠ 0 := Polynomial.map_ne_zero hC
  apply mul_right_cancel₀ hCmap
  calc
    (N * L.map φ) * C.map φ =
        N * (D₀.map φ * D₁.map φ) := by
      rw [mul_assoc, hLCmap]
    _ = D * (N₀.map φ * D₁.map φ +
        Polynomial.C (RatFunc.X : RatFunc F) *
          (N₁.map φ * D₀.map φ)) := hcross
    _ = ((N₀ * E₀).map φ +
          (RatFunc.X : RatFunc F) • (N₁ * E₁).map φ) *
        D * C.map φ := by
      rw [Polynomial.smul_eq_C_mul]
      simp only [Polynomial.map_mul]
      calc
        D * (N₀.map φ * D₁.map φ +
            Polynomial.C (RatFunc.X : RatFunc F) *
              (N₁.map φ * D₀.map φ)) =
            D * (N₀.map φ * (E₀.map φ * C.map φ) +
              Polynomial.C (RatFunc.X : RatFunc F) *
                (N₁.map φ * (E₁.map φ * C.map φ))) := by
          rw [hE₀Cmap, hE₁Cmap]
        _ = (N₀.map φ * E₀.map φ +
              Polynomial.C (RatFunc.X : RatFunc F) *
                (N₁.map φ * E₁.map φ)) * D * C.map φ := by
          ring

/-- Complete least-common-denominator degree transfer.  Two reduced base
fractions are lifted to their lcm denominator.  If a generic degree-`<h`
fraction satisfies the resulting cross identity, then the lcm and both
adjusted base numerators all have degree `<h`. -/
theorem lcm_adjusted_fraction_degree_transfer
    [DecidableEq F]
    (N₀ D₀ N₁ D₁ : F[X]) (N D : (RatFunc F)[X]) (h : ℕ)
    (hD₀ : D₀ ≠ 0) (hD₁ : D₁ ≠ 0) (hD : D ≠ 0)
    (hcoprime₀ : IsCoprime N₀ D₀)
    (hcoprime₁ : IsCoprime N₁ D₁)
    (hNdegree : N.natDegree < h) (hDdegree : D.natDegree < h)
    (hcross :
      N * (lcm D₀ D₁).map (algebraMap F (RatFunc F)) =
        ((N₀ * (lcm D₀ D₁ / D₀)).map
            (algebraMap F (RatFunc F)) +
          (RatFunc.X : RatFunc F) •
            (N₁ * (lcm D₀ D₁ / D₁)).map
              (algebraMap F (RatFunc F))) * D) :
    (lcm D₀ D₁).natDegree < h ∧
      (N₀ * (lcm D₀ D₁ / D₀)).natDegree < h ∧
      (N₁ * (lcm D₀ D₁ / D₁)).natDegree < h := by
  have hL : lcm D₀ D₁ ≠ 0 := by
    rw [Ne, lcm_eq_zero_iff]
    exact not_or_intro hD₀ hD₁
  apply generic_base_fraction_degree_transfer
    (lcm D₀ D₁)
    (N₀ * (lcm D₀ D₁ / D₀))
    (N₁ * (lcm D₀ D₁ / D₁)) N D h
    hL hD hNdegree hDdegree
  · exact lcm_adjusted_numerators_no_common_irreducible
      N₀ D₀ N₁ D₁ hD₀ hD₁ hcoprime₀ hcoprime₁
  · exact hcross

/-- Product-denominator entry point to
`lcm_adjusted_fraction_degree_transfer`. -/
theorem lcm_adjusted_fraction_degree_transfer_of_product_cross_identity
    [DecidableEq F]
    (N₀ D₀ N₁ D₁ : F[X]) (N D : (RatFunc F)[X]) (h : ℕ)
    (hD₀ : D₀ ≠ 0) (hD₁ : D₁ ≠ 0) (hD : D ≠ 0)
    (hcoprime₀ : IsCoprime N₀ D₀)
    (hcoprime₁ : IsCoprime N₁ D₁)
    (hNdegree : N.natDegree < h) (hDdegree : D.natDegree < h)
    (hcross :
      N * (D₀.map (algebraMap F (RatFunc F)) *
          D₁.map (algebraMap F (RatFunc F))) =
        D * (N₀.map (algebraMap F (RatFunc F)) *
            D₁.map (algebraMap F (RatFunc F)) +
          Polynomial.C (RatFunc.X : RatFunc F) *
            (N₁.map (algebraMap F (RatFunc F)) *
              D₀.map (algebraMap F (RatFunc F))))) :
    (lcm D₀ D₁).natDegree < h ∧
      (N₀ * (lcm D₀ D₁ / D₀)).natDegree < h ∧
      (N₁ * (lcm D₀ D₁ / D₁)).natDegree < h := by
  apply lcm_adjusted_fraction_degree_transfer
    N₀ D₀ N₁ D₁ N D h hD₀ hD₁ hD
    hcoprime₀ hcoprime₁ hNdegree hDdegree
  exact lcm_cross_identity_of_product_cross_identity
    N₀ D₀ N₁ D₁ N D hD₀ hD₁ hcross

/-- Sharp lcm transfer retaining the actual generic numerator and denominator
degrees. -/
theorem lcm_adjusted_fraction_degree_transfer_le
    [DecidableEq F]
    (N₀ D₀ N₁ D₁ : F[X]) (N D : (RatFunc F)[X])
    (hD₀ : D₀ ≠ 0) (hD₁ : D₁ ≠ 0) (hD : D ≠ 0)
    (hcoprime₀ : IsCoprime N₀ D₀)
    (hcoprime₁ : IsCoprime N₁ D₁)
    (hcross :
      N * (lcm D₀ D₁).map (algebraMap F (RatFunc F)) =
        ((N₀ * (lcm D₀ D₁ / D₀)).map
            (algebraMap F (RatFunc F)) +
          (RatFunc.X : RatFunc F) •
            (N₁ * (lcm D₀ D₁ / D₁)).map
              (algebraMap F (RatFunc F))) * D) :
    (lcm D₀ D₁).natDegree ≤ D.natDegree ∧
      (N₀ * (lcm D₀ D₁ / D₀)).natDegree ≤ N.natDegree ∧
      (N₁ * (lcm D₀ D₁ / D₁)).natDegree ≤ N.natDegree := by
  have hL : lcm D₀ D₁ ≠ 0 := by
    rw [Ne, lcm_eq_zero_iff]
    exact not_or_intro hD₀ hD₁
  apply generic_base_fraction_degree_transfer_le
    (lcm D₀ D₁)
    (N₀ * (lcm D₀ D₁ / D₀))
    (N₁ * (lcm D₀ D₁ / D₁)) N D
    hL hD
  · exact lcm_adjusted_numerators_no_common_irreducible
      N₀ D₀ N₁ D₁ hD₀ hD₁ hcoprime₀ hcoprime₁
  · exact hcross

/-- Product-denominator entry point to the sharp lcm transfer. -/
theorem lcm_adjusted_fraction_degree_transfer_le_of_product_cross_identity
    [DecidableEq F]
    (N₀ D₀ N₁ D₁ : F[X]) (N D : (RatFunc F)[X])
    (hD₀ : D₀ ≠ 0) (hD₁ : D₁ ≠ 0) (hD : D ≠ 0)
    (hcoprime₀ : IsCoprime N₀ D₀)
    (hcoprime₁ : IsCoprime N₁ D₁)
    (hcross :
      N * (D₀.map (algebraMap F (RatFunc F)) *
          D₁.map (algebraMap F (RatFunc F))) =
        D * (N₀.map (algebraMap F (RatFunc F)) *
            D₁.map (algebraMap F (RatFunc F)) +
          Polynomial.C (RatFunc.X : RatFunc F) *
            (N₁.map (algebraMap F (RatFunc F)) *
              D₀.map (algebraMap F (RatFunc F))))) :
    (lcm D₀ D₁).natDegree ≤ D.natDegree ∧
      (N₀ * (lcm D₀ D₁ / D₀)).natDegree ≤ N.natDegree ∧
      (N₁ * (lcm D₀ D₁ / D₁)).natDegree ≤ N.natDegree := by
  apply lcm_adjusted_fraction_degree_transfer_le
    N₀ D₀ N₁ D₁ N D hD₀ hD₁ hD hcoprime₀ hcoprime₁
  exact lcm_cross_identity_of_product_cross_identity
    N₀ D₀ N₁ D₁ N D hD₀ hD₁ hcross

/-- Three bounded numerator/denominator factors can be cross-multiplied from
pointwise interpolation data once the source contains at least `3*h`
distinct points.  This is the root-counting part of the rational-scroll
argument, separated from its later gcd and denominator normalization. -/
theorem generic_interpolant_cross_identity
    {K : Type} [Field K]
    (N D N₀ D₀ N₁ D₁ : K[X]) (w : K) (S : Finset K) (h : ℕ)
    (hN : N.natDegree < h) (hD : D.natDegree < h)
    (hN₀ : N₀.natDegree < h) (hD₀ : D₀.natDegree < h)
    (hN₁ : N₁.natDegree < h) (hD₁ : D₁.natDegree < h)
    (hsize : 3 * h ≤ S.card)
    (heval : ∀ x ∈ S,
      N.eval x * D₀.eval x * D₁.eval x =
        D.eval x *
          (N₀.eval x * D₁.eval x + w * (N₁.eval x * D₀.eval x))) :
    N * D₀ * D₁ =
      D * (N₀ * D₁ + Polynomial.C w * (N₁ * D₀)) := by
  let P := N * D₀ * D₁ -
    D * (N₀ * D₁ + Polynomial.C w * (N₁ * D₀))
  have hlhs : (N * D₀ * D₁).natDegree < 3 * h := by
    calc
      (N * D₀ * D₁).natDegree ≤
          (N * D₀).natDegree + D₁.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (N.natDegree + D₀.natDegree) + D₁.natDegree := by
        exact Nat.add_le_add_right Polynomial.natDegree_mul_le _
      _ < 3 * h := by omega
  have hfirst : (N₀ * D₁).natDegree < 2 * h := by
    exact Polynomial.natDegree_mul_le.trans_lt (by omega)
  have hsecond : (Polynomial.C w * (N₁ * D₀)).natDegree < 2 * h := by
    calc
      (Polynomial.C w * (N₁ * D₀)).natDegree ≤
          (N₁ * D₀).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ N₁.natDegree + D₀.natDegree := Polynomial.natDegree_mul_le
      _ < 2 * h := by omega
  have hinner :
      (N₀ * D₁ + Polynomial.C w * (N₁ * D₀)).natDegree <
        2 * h :=
    (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hfirst hsecond)
  have hrhs :
      (D * (N₀ * D₁ + Polynomial.C w * (N₁ * D₀))).natDegree <
        3 * h := by
    exact Polynomial.natDegree_mul_le.trans_lt (by omega)
  have hPdegree : P.natDegree < S.card := by
    apply (Polynomial.natDegree_sub_le _ _).trans_lt
    exact (max_lt hlhs hrhs).trans_le hsize
  have hProot : ∀ x ∈ S, P.eval x = 0 := by
    intro x hx
    simp only [P, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_C]
    exact sub_eq_zero.mpr (heval x hx)
  have hPzero : P = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      P S hProot hPdegree
  exact sub_eq_zero.mp hPzero

/-- Defect-aware form of `generic_interpolant_cross_identity`.

Reducing each of the three kernel fractions may discard the source points at
which its removed gcd vanishes.  The parameters `g`, `g₀`, and `g₁` pay
for those discarded points.  The same parameters lower the three reduced
degree budgets, so the strict global surplus `3*h < |S|` still forces the
cross identity on the remaining valid set `T`. -/
theorem generic_interpolant_cross_identity_with_defects
    {K : Type} [Field K]
    (N D N₀ D₀ N₁ D₁ : K[X]) (w : K)
    (S T : Finset K) (h g g₀ g₁ : ℕ)
    (hN : N.natDegree + g < h) (hD : D.natDegree + g < h)
    (hN₀ : N₀.natDegree + g₀ < h) (hD₀ : D₀.natDegree + g₀ < h)
    (hN₁ : N₁.natDegree + g₁ < h) (hD₁ : D₁.natDegree + g₁ < h)
    (hstrict : 3 * h < S.card)
    (hcoverage : S.card ≤ T.card + (g + g₀ + g₁))
    (heval : ∀ x ∈ T,
      N.eval x * D₀.eval x * D₁.eval x =
        D.eval x *
          (N₀.eval x * D₁.eval x + w * (N₁.eval x * D₀.eval x))) :
    N * D₀ * D₁ =
      D * (N₀ * D₁ + Polynomial.C w * (N₁ * D₀)) := by
  let G := g + g₀ + g₁
  let P := N * D₀ * D₁ -
    D * (N₀ * D₁ + Polynomial.C w * (N₁ * D₀))
  have hlhs : (N * D₀ * D₁).natDegree + G < 3 * h := by
    have hdegree : (N * D₀ * D₁).natDegree ≤
        (N.natDegree + D₀.natDegree) + D₁.natDegree := by
      exact Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add_right Polynomial.natDegree_mul_le _)
    dsimp only [G]
    omega
  have hfirst : (N₀ * D₁).natDegree + (g₀ + g₁) < 2 * h := by
    have hdegree : (N₀ * D₁).natDegree ≤
        N₀.natDegree + D₁.natDegree := Polynomial.natDegree_mul_le
    omega
  have hsecond :
      (Polynomial.C w * (N₁ * D₀)).natDegree + (g₀ + g₁) <
        2 * h := by
    have hdegree : (Polynomial.C w * (N₁ * D₀)).natDegree ≤
        N₁.natDegree + D₀.natDegree := by
      exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_mul_le
    omega
  have hinner :
      (N₀ * D₁ + Polynomial.C w * (N₁ * D₀)).natDegree +
          (g₀ + g₁) < 2 * h := by
    have hdegree := Polynomial.natDegree_add_le
      (N₀ * D₁) (Polynomial.C w * (N₁ * D₀))
    omega
  have hrhs :
      (D * (N₀ * D₁ + Polynomial.C w * (N₁ * D₀))).natDegree + G <
        3 * h := by
    have hdegree :
        (D * (N₀ * D₁ + Polynomial.C w * (N₁ * D₀))).natDegree ≤
          D.natDegree +
            (N₀ * D₁ + Polynomial.C w * (N₁ * D₀)).natDegree :=
      Polynomial.natDegree_mul_le
    dsimp only [G]
    omega
  have hPbudget : P.natDegree + G < 3 * h := by
    dsimp only [P]
    have hdegree := Polynomial.natDegree_sub_le
      (N * D₀ * D₁)
      (D * (N₀ * D₁ + Polynomial.C w * (N₁ * D₀)))
    omega
  have hPdegree : P.natDegree < T.card := by
    dsimp only [G] at hPbudget
    omega
  have hProot : ∀ x ∈ T, P.eval x = 0 := by
    intro x hx
    simp only [P, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_C]
    exact sub_eq_zero.mpr (heval x hx)
  have hPzero : P = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      P T hProot hPdegree
  exact sub_eq_zero.mp hPzero

end ProximityPrize.SubmissionLower
