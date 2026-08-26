import ProximityPrize.SubmissionLower.BCHKSLocalValuation6400
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap

namespace ProximityPrize.SubmissionLower
namespace BCHKSWeightedSecant6400

open Polynomial
open BCHKSLocalValuation6400

set_option maxHeartbeats 2000000

/-! A local jet survives substitution by a branch tangent to the received
line.  This is the algebraic core of the weighted-secant argument. -/

theorem eval_shift_eq_comp_eval
    {A : Type*} [CommRing A]
    (R : Polynomial (Polynomial A)) (x y : A) (P : Polynomial A) :
    Polynomial.eval
        (P.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y)
        (Polynomial.Bivariate.shift R x y) =
      (Polynomial.eval P R).comp (Polynomial.X + Polynomial.C x) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      rw [show Polynomial.Bivariate.shift (R + S) x y =
        Polynomial.Bivariate.shift R x y +
          Polynomial.Bivariate.shift S x y by
            simp [Polynomial.Bivariate.shift]]
      simp [hR, hS]
  | monomial n a =>
      simp [Polynomial.Bivariate.shift, Polynomial.map_monomial,
        Polynomial.eval_monomial, Polynomial.eval_comp]

theorem X_pow_dvd_eval_of_localVanish_of_X_dvd
    {A : Type*} [CommSemiring A]
    (R : Polynomial (Polynomial A)) (P : Polynomial A) (nu : ℕ)
    (hR : LocalVanish R nu) (hP : Polynomial.X ∣ P) :
    Polynomial.X ^ nu ∣ Polynomial.eval P R := by
  rw [Polynomial.eval_eq_sum]
  apply Finset.dvd_sum
  intro t ht
  have hPt : Polynomial.X ^ t ∣ P ^ t :=
    pow_dvd_pow_of_dvd hP t
  by_cases htnu : t < nu
  · have hcoeff : Polynomial.X ^ (nu - t) ∣ R.coeff t := by
      rw [Polynomial.X_pow_dvd_iff]
      intro s hs
      exact hR s t (by omega)
    have hprod := mul_dvd_mul hcoeff hPt
    have hsum : nu - t + t = nu := Nat.sub_add_cancel (Nat.le_of_lt htnu)
    simpa [← pow_add, hsum] using hprod
  · have hle : nu ≤ t := Nat.le_of_not_gt htnu
    have hpow : Polynomial.X ^ nu ∣ Polynomial.X ^ t :=
      pow_dvd_pow (Polynomial.X : Polynomial A) hle
    exact dvd_mul_of_dvd_right (hpow.trans hPt) (R.coeff t)

/-- Substituting an `X`-degree-`k` polynomial for `Y` costs exactly `k` per
outer degree. -/
theorem eval_natDegree_le_of_coeff_weight_cap
    {A : Type*} [CommSemiring A]
    (R : Polynomial (Polynomial A)) (P : Polynomial A) (k w : ℕ)
    (hP : P.natDegree ≤ k)
    (hcap : ∀ j, R.coeff j ≠ 0 →
      (R.coeff j).natDegree + k * j ≤ w) :
    (Polynomial.eval P R).natDegree ≤ w := by
  rw [Polynomial.eval_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hj0 : R.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  calc
    (R.coeff j * P ^ j).natDegree ≤
        (R.coeff j).natDegree + (P ^ j).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (R.coeff j).natDegree + j * k := by
      exact Nat.add_le_add_left
        (Polynomial.natDegree_pow_le_of_le j hP) _
    _ = (R.coeff j).natDegree + k * j := by rw [Nat.mul_comm j k]
    _ ≤ w := hcap j hj0

/-! ## The coefficientwise affine secant -/

/-- Affine interpolation in `Z` between two `X`-polynomials. -/
noncomputable def affineSecant
    {F : Type*} [Field F] (z0 z1 : F)
    (P0 P1 : Polynomial F) : Polynomial (Polynomial F) :=
  P0.map Polynomial.C +
    Polynomial.C ((Polynomial.X - Polynomial.C z0) *
      Polynomial.C (z1 - z0)⁻¹) * (P1 - P0).map Polynomial.C

@[simp]
theorem map_map_C_eval
    {F : Type*} [Field F] (z : F) (P : Polynomial F) :
    (P.map Polynomial.C).map (Polynomial.evalRingHom z) = P := by
  ext n
  simp [Polynomial.coeff_map]

theorem affineSecant_specialize_left
    {F : Type*} [Field F] (z0 z1 : F) (P0 P1 : Polynomial F) :
    (affineSecant z0 z1 P0 P1).map (Polynomial.evalRingHom z0) = P0 := by
  simp [affineSecant, map_map_C_eval]

theorem affineSecant_specialize_right
    {F : Type*} [Field F] (z0 z1 : F) (P0 P1 : Polynomial F)
    (hne : z0 ≠ z1) :
    (affineSecant z0 z1 P0 P1).map (Polynomial.evalRingHom z1) = P1 := by
  have hsub : z1 - z0 ≠ 0 := sub_ne_zero.mpr hne.symm
  simp [affineSecant, map_map_C_eval, hsub]
  rw [← Polynomial.C_sub, ← Polynomial.C_mul]
  simp [hsub]

theorem affineSecant_natDegree_le
    {F : Type*} [Field F] (z0 z1 : F) (P0 P1 : Polynomial F)
    (k : ℕ) (hP0 : P0.natDegree ≤ k) (hP1 : P1.natDegree ≤ k) :
    (affineSecant z0 z1 P0 P1).natDegree ≤ k := by
  unfold affineSecant
  have hmap0 : (P0.map Polynomial.C).natDegree ≤ k :=
    Polynomial.natDegree_map_le.trans hP0
  have hmap10 : ((P1 - P0).map Polynomial.C).natDegree ≤ k :=
    Polynomial.natDegree_map_le.trans
      ((Polynomial.natDegree_sub_le P1 P0).trans (max_le hP1 hP0))
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le hmap0 ((Polynomial.natDegree_C_mul_le _ _).trans hmap10))

/-- Two common challenge agreements make the secant equal the received
affine line on that coordinate for every `Z`. -/
theorem eval_affineSecant_eq_affine_of_endpoint_agreement
    {F : Type*} [Field F] [DecidableEq F]
    (z0 z1 x : F) (P0 P1 u : Polynomial F)
    (hne : z0 ≠ z1) (hu : u.natDegree ≤ 1)
    (h0 : Polynomial.eval x P0 = Polynomial.eval z0 u)
    (h1 : Polynomial.eval x P1 = Polynomial.eval z1 u) :
    Polynomial.eval (Polynomial.C x) (affineSecant z0 z1 P0 P1) = u := by
  let A : Polynomial F :=
    Polynomial.eval (Polynomial.C x) (affineSecant z0 z1 P0 P1)
  have hAdeg : A.natDegree ≤ 1 := by
    dsimp [A]
    rw [affineSecant]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_map]
    have hlin : ((Polynomial.X - Polynomial.C z0) *
        Polynomial.C (z1 - z0)⁻¹).natDegree ≤ 1 := by
      exact (Polynomial.natDegree_mul_le.trans (by simp))
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (by simp) ((Polynomial.natDegree_mul_le).trans
        (by simpa using hlin)))
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
    A u ({z0, z1} : Finset F)
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · subst z
      rw [← h0]
      change Polynomial.eval z0 A = Polynomial.eval x P0
      dsimp [A]
      rw [← eval_map_eval_eq_eval_eval_C]
      rw [affineSecant_specialize_left]
    · subst z
      rw [← h1]
      change Polynomial.eval z1 A = Polynomial.eval x P1
      dsimp [A]
      rw [← eval_map_eval_eq_eval_eval_C]
      rw [affineSecant_specialize_right z0 z1 P0 P1 hne]
  · have hcard : ({z0, z1} : Finset F).card = 2 := by
      simp [hne]
    rw [hcard]
    omega

/-- After undoing the translation, a branch agreeing with the received
value at `x` turns local total order `nu` into ordinary `X`-multiplicity
`nu` after substitution. -/
theorem X_sub_C_pow_dvd_eval_of_shift_localVanish
    {A : Type*} [CommRing A]
    (R : Polynomial (Polynomial A)) (x y : A)
    (P : Polynomial A) (nu : ℕ)
    (hR : LocalVanish (Polynomial.Bivariate.shift R x y) nu)
    (hP : Polynomial.eval x P = y) :
    (Polynomial.X - Polynomial.C x) ^ nu ∣ Polynomial.eval P R := by
  rw [Polynomial.X_sub_C_pow_dvd_iff]
  rw [← eval_shift_eq_comp_eval R x y P]
  apply X_pow_dvd_eval_of_localVanish_of_X_dvd
    (Polynomial.Bivariate.shift R x y)
      (P.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y) nu hR
  rw [Polynomial.X_dvd_iff]
  simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, hP]

/-- Pairwise distinct constant `X` fibers may be added with their full local
multiplicities.  This is the weighted root-counting step used by the secant
argument. -/
theorem eq_zero_of_weighted_constant_roots
    {F ι : Type*} [Field F] [DecidableEq ι]
    (T : Polynomial (Polynomial F)) (S : Finset ι)
    (x : ι → F) (nu : ι → ℕ)
    (hinj : Set.InjOn x S)
    (hroots : ∀ i ∈ S,
      (Polynomial.X - Polynomial.C (Polynomial.C (x i))) ^ nu i ∣ T)
    (hdegree : T.natDegree < ∑ i ∈ S, nu i) :
    T = 0 := by
  classical
  by_contra hT
  let f : ι → Polynomial (Polynomial F) := fun i ↦
    (Polynomial.X - Polynomial.C (Polynomial.C (x i))) ^ nu i
  have hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (f i) (f j) := by
    intro i hi j hj hij
    have hx : x i ≠ x j := fun h => hij (hinj hi hj h)
    have hunit : IsUnit
        ((Polynomial.C (x i) : Polynomial F) - Polynomial.C (x j)) := by
      rw [← Polynomial.C_sub]
      exact Polynomial.isUnit_C.mpr (sub_ne_zero.mpr hx).isUnit
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit).pow
  have hprod : ∏ i ∈ S, f i ∣ T := by
    exact Finset.prod_dvd_of_coprime hcop (fun i hi ↦ hroots i hi)
  have hprodDegree : (∏ i ∈ S, f i).natDegree = ∑ i ∈ S, nu i := by
    rw [Polynomial.natDegree_prod_of_monic]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [f]
    · intro i hi
      exact (Polynomial.monic_X_sub_C _).pow _
  have hle := Polynomial.natDegree_le_of_dvd hprod hT
  rw [hprodDegree] at hle
  omega

/-- Weighted secant root count.  If one polynomial branch agrees with the
received affine line on a set of identity fibers, the full local orders on
those fibers count as distinct `X` roots after substitution. -/
theorem eval_eq_zero_of_weighted_secant
    {F ι : Type*} [Field F] [DecidableEq ι]
    (R : Polynomial (Polynomial (Polynomial F)))
    (Psec : Polynomial (Polynomial F))
    (S : Finset ι) (omega : ι → F)
    (u : ι → Polynomial F) (nu : ι → ℕ) (w : ℕ)
    (homega : Set.InjOn omega S)
    (hlocal : ∀ i ∈ S,
      LocalVanish (Polynomial.Bivariate.shift R
        (Polynomial.C (omega i)) (u i)) (nu i))
    (hsecant : ∀ i ∈ S,
      Polynomial.eval (Polynomial.C (omega i)) Psec = u i)
    (hdegree : (Polynomial.eval Psec R).natDegree ≤ w)
    (hmass : w < ∑ i ∈ S, nu i) :
    Polynomial.eval Psec R = 0 := by
  apply eq_zero_of_weighted_constant_roots
    (Polynomial.eval Psec R) S omega nu homega
  · intro i hi
    exact X_sub_C_pow_dvd_eval_of_shift_localVanish
      R (Polynomial.C (omega i)) (u i) Psec (nu i)
        (hlocal i hi) (hsecant i hi)
  · omega

/-- A genuine irreducible nonlinear polynomial cannot admit a polynomial
root over its coefficient ring. -/
theorem not_irreducible_of_eval_eq_zero_of_two_le_natDegree
    {A : Type*} [CommRing A] [IsDomain A]
    (R : Polynomial A) (P : A)
    (hdeg : 2 ≤ R.natDegree) (heval : Polynomial.eval P R = 0) :
    ¬ Irreducible R := by
  intro hirr
  have hdiv : Polynomial.X - Polynomial.C P ∣ R := by
    rw [Polynomial.dvd_iff_isRoot]
    exact heval
  obtain ⟨E, hRE⟩ := hdiv
  have hLnonunit : ¬ IsUnit (Polynomial.X - Polynomial.C P) :=
    Polynomial.not_isUnit_X_sub_C P
  rcases hirr.isUnit_or_isUnit hRE with hLunit | hEunit
  · exact hLnonunit hLunit
  · have hL0 : Polynomial.X - Polynomial.C P ≠ 0 :=
      (Polynomial.monic_X_sub_C P).ne_zero
    have hE0 : E ≠ 0 := hEunit.ne_zero
    have hRdegree : R.natDegree = 1 := by
      rw [hRE, Polynomial.natDegree_mul hL0 hE0,
        Polynomial.natDegree_X_sub_C,
        Polynomial.natDegree_eq_zero_of_isUnit hEunit]
    omega

/-- Complete algebraic contradiction supplied by a weighted secant. -/
theorem not_irreducible_of_weighted_secant
    {F ι : Type*} [Field F] [DecidableEq ι]
    (R : Polynomial (Polynomial (Polynomial F)))
    (Psec : Polynomial (Polynomial F))
    (S : Finset ι) (omega : ι → F)
    (u : ι → Polynomial F) (nu : ι → ℕ) (w : ℕ)
    (hRdeg : 2 ≤ R.natDegree)
    (homega : Set.InjOn omega S)
    (hlocal : ∀ i ∈ S,
      LocalVanish (Polynomial.Bivariate.shift R
        (Polynomial.C (omega i)) (u i)) (nu i))
    (hsecant : ∀ i ∈ S,
      Polynomial.eval (Polynomial.C (omega i)) Psec = u i)
    (hdegree : (Polynomial.eval Psec R).natDegree ≤ w)
    (hmass : w < ∑ i ∈ S, nu i) :
    ¬ Irreducible R := by
  apply not_irreducible_of_eval_eq_zero_of_two_le_natDegree R Psec hRdeg
  exact eval_eq_zero_of_weighted_secant R Psec S omega u nu w
    homega hlocal hsecant hdegree hmass

/-- End-to-end two-challenge secant theorem.  Two degree-`k` owner roots
which share identity fibers of total local mass greater than the factor
weight force a global linear factor, contradicting nonlinear
irreducibility. -/
theorem not_irreducible_of_two_owner_weighted_intersection
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (R : Polynomial (Polynomial (Polynomial F)))
    (z0 z1 : F) (P0 P1 : Polynomial F)
    (S : Finset ι) (omega : ι ↪ F)
    (u : ι → Polynomial F) (nu : ι → ℕ)
    (k w : ℕ)
    (hz : z0 ≠ z1)
    (hP0 : P0.natDegree ≤ k) (hP1 : P1.natDegree ≤ k)
    (hu : ∀ i ∈ S, (u i).natDegree ≤ 1)
    (hlocal : ∀ i ∈ S,
      LocalVanish (Polynomial.Bivariate.shift R
        (Polynomial.C (omega i)) (u i)) (nu i))
    (hmatch0 : ∀ i ∈ S,
      Polynomial.eval (omega i) P0 = Polynomial.eval z0 (u i))
    (hmatch1 : ∀ i ∈ S,
      Polynomial.eval (omega i) P1 = Polynomial.eval z1 (u i))
    (hcap : ∀ j, R.coeff j ≠ 0 →
      (R.coeff j).natDegree + k * j ≤ w)
    (hRdeg : 2 ≤ R.natDegree)
    (hmass : w < ∑ i ∈ S, nu i) :
    ¬ Irreducible R := by
  let Psec := affineSecant z0 z1 P0 P1
  apply not_irreducible_of_weighted_secant
    R Psec S omega u nu w hRdeg omega.injective.injOn
  · exact hlocal
  · intro i hi
    exact eval_affineSecant_eq_affine_of_endpoint_agreement
      z0 z1 (omega i) P0 P1 (u i) hz (hu i hi)
        (hmatch0 i hi) (hmatch1 i hi)
  · apply eval_natDegree_le_of_coeff_weight_cap R Psec k w
    · exact affineSecant_natDegree_le z0 z1 P0 P1 k hP0 hP1
    · exact hcap
  · exact hmass

/-! ## Valid three-challenge / divided-difference refinement -/

/-- Codeword slope from a pivot challenge. -/
noncomputable def dividedDifference
    {F : Type*} [Field F] (z0 z : F)
    (P0 P : Polynomial F) : Polynomial F :=
  Polynomial.C (z - z0)⁻¹ * (P - P0)

theorem dividedDifference_natDegree_le
    {F : Type*} [Field F] (z0 z : F)
    (P0 P : Polynomial F) (k : ℕ)
    (hP0 : P0.natDegree ≤ k) (hP : P.natDegree ≤ k) :
    (dividedDifference z0 z P0 P).natDegree ≤ k := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_sub_le P P0).trans (max_le hP hP0))

/-- Every secant slope of a degree-one received line is its linear
coefficient. -/
theorem affine_divided_slope_eq_coeff_one
    {F : Type*} [Field F]
    (u : Polynomial F) (z0 z : F)
    (hu : u.natDegree ≤ 1) (hz : z0 ≠ z) :
    (z - z0)⁻¹ * (Polynomial.eval z u - Polynomial.eval z0 u) =
      u.coeff 1 := by
  have hsub : z - z0 ≠ 0 := sub_ne_zero.mpr hz.symm
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hu]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X, Polynomial.coeff_C, if_pos]
  field_simp
  simp
  ring

/-- At a coordinate shared by a pivot and another challenge, the divided
difference codeword evaluates to the received slope. -/
theorem eval_dividedDifference_eq_received_slope
    {F : Type*} [Field F]
    (z0 z x : F) (P0 P u : Polynomial F)
    (hz : z0 ≠ z) (hu : u.natDegree ≤ 1)
    (h0 : Polynomial.eval x P0 = Polynomial.eval z0 u)
    (h : Polynomial.eval x P = Polynomial.eval z u) :
    Polynomial.eval x (dividedDifference z0 z P0 P) = u.coeff 1 := by
  simp only [dividedDifference, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub]
  rw [h0, h]
  exact affine_divided_slope_eq_coeff_one u z0 z hu hz

/-- This is the correct use of the ordinary Reed--Solomon common-root cap:
relative to a fixed pivot, two distinct divided-difference codewords cannot
share more than `k` received-slope coordinates.  Equivalently, more than
`k` triple agreements force the three challenges onto one affine codeword
line. -/
theorem dividedDifferences_eq_of_many_triple_agreements
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (z0 z1 z2 : F) (P0 P1 P2 : Polynomial F)
    (S : Finset ι) (omega : ι ↪ F) (u : ι → Polynomial F)
    (k : ℕ)
    (hz1 : z0 ≠ z1) (hz2 : z0 ≠ z2)
    (hP0 : P0.natDegree ≤ k)
    (hP1 : P1.natDegree ≤ k) (hP2 : P2.natDegree ≤ k)
    (hu : ∀ i ∈ S, (u i).natDegree ≤ 1)
    (hmatch0 : ∀ i ∈ S,
      Polynomial.eval (omega i) P0 = Polynomial.eval z0 (u i))
    (hmatch1 : ∀ i ∈ S,
      Polynomial.eval (omega i) P1 = Polynomial.eval z1 (u i))
    (hmatch2 : ∀ i ∈ S,
      Polynomial.eval (omega i) P2 = Polynomial.eval z2 (u i))
    (hmany : k < S.card) :
    dividedDifference z0 z1 P0 P1 =
      dividedDifference z0 z2 P0 P2 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (dividedDifference z0 z1 P0 P1)
    (dividedDifference z0 z2 P0 P2)
    (f := fun i : S ↦ omega i.1)
  · exact omega.injective.comp Subtype.val_injective
  · intro i
    rw [eval_dividedDifference_eq_received_slope
        z0 z1 (omega i.1) P0 P1 (u i.1) hz1 (hu i.1 i.2)
          (hmatch0 i.1 i.2) (hmatch1 i.1 i.2),
      eval_dividedDifference_eq_received_slope
        z0 z2 (omega i.1) P0 P2 (u i.1) hz2 (hu i.1 i.2)
          (hmatch0 i.1 i.2) (hmatch2 i.1 i.2)]
  · have hD1 := dividedDifference_natDegree_le
      z0 z1 P0 P1 k hP0 hP1
    have hD2 := dividedDifference_natDegree_le
      z0 z2 P0 P2 k hP0 hP2
    simpa using (show
      max (dividedDifference z0 z1 P0 P1).natDegree
          (dividedDifference z0 z2 P0 P2).natDegree < S.card by omega)

/-- Equality of pivot slopes is exactly affine alignment of the two
non-pivot codewords. -/
theorem eq_affine_of_dividedDifference_eq
    {F : Type*} [Field F]
    (z0 z : F) (P0 P D : Polynomial F)
    (hz : z0 ≠ z)
    (hD : dividedDifference z0 z P0 P = D) :
    P = (P0 - Polynomial.C z0 * D) + Polynomial.C z * D := by
  have hsub : z - z0 ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold dividedDifference at hD
  have hrecover : P - P0 = Polynomial.C (z - z0) * D := by
    calc
      P - P0 = Polynomial.C (z - z0) *
          (Polynomial.C (z - z0)⁻¹ * (P - P0)) := by
        rw [← mul_assoc, ← Polynomial.C_mul]
        simp [hsub]
      _ = Polynomial.C (z - z0) * D := by rw [hD]
  calc
    P = P0 + (P - P0) := by ring
    _ = P0 + Polynomial.C (z - z0) * D := by rw [hrecover]
    _ = (P0 - Polynomial.C z0 * D) + Polynomial.C z * D := by
      rw [Polynomial.C_sub]
      ring

end BCHKSWeightedSecant6400
end ProximityPrize.SubmissionLower
