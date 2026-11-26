import ProximityPrize.SubmissionBinaryLower.Binary6402SmallAlgPart2
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.B6401KerD2
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.Binary6402IntSmallCerts
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT1
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT2
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT3
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

/-!
# Tables 1, 2, 3, and 3-2B: Contiguous Certificate Coverage, Char-2 Resultant & UFD Algebra

Provides:
1. `decide`-verified contiguous coverage theorems (`exists_t1Cert`, `exists_t2Cert`, `exists_t3Cert`)
   over `B6402CertsT1`, `B6402CertsT2`, and `B6402CertsT3` (`O(n)` synchronized cover check for T3!).
2. Multiplicativity of `wdegBi` (`wdegBi_mul`) and exact 2D multiplicity `biMult` (`biMult_mul`,
   `biMult_even_of_in_F_X2_Y2`).
3. Resultant shift/cancellation identity (`resultant_add_mul_right_deg`) and char-2 `ker(D)`
   resultant divisibility theorems:
   - `kerD1_resY_ord` (Table 1 `v_ker` + `v_pln`),
   - `kerD2_resY_f0_g_ord` (Table 3 general `v_ker` + `v_pln` and 2B `q, g_1`),
   - `kerD2_resY_f0_g_2A_ord` (Table 3 Subcase 2A `g = q(X) * g_e(X^2, Y^2)`).
4. Char-2 `ker(D)` UFD decomposition for `deg_R = 2` (`kerD2_gcd_decomp` and `kerD2_2A_2B_dichotomy`).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402SmallAlg

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial  B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6402IntFarkas B6402IntSmallCerts
open B6402CertsT1 B6402CertsT2 B6402CertsT3
open scoped BigOperators
local notation (priority := high) "X" => Polynomial.X
section KerD2UFD
variable {F : Type*} [Field F] [CharP F 2]

lemma deriv_eq_zero_iff_even_coeffs {A : Type*} [CommRing A] [CharP A 2] (p : Polynomial A) :
    p.derivative = 0 ↔ ∀ j, j % 2 = 1 → p.coeff j = 0 := by
  constructor
  · intro h j hj
    have h0 := congrArg (fun q : Polynomial A => q.coeff (j - 1)) h
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, ← Nat.cast_succ, Nat.succ_eq_add_one,
      show j - 1 + 1 = j by omega] at h0
    have hodd : ((j : ℕ) : A) = 1 := by
      have : j = 2 * (j / 2) + 1 := by omega
      rw [this, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        CharTwo.two_eq_zero, zero_mul, zero_add]
    rwa [hodd, mul_one] at h0
  · intro h; ext n
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, ← Nat.cast_succ]
    by_cases hn : (n + 1) % 2 = 1
    · rw [h (n + 1) hn, zero_mul]
    · have hev : ((n + 1 : ℕ) : A) = 0 := by
        have : n + 1 = 2 * ((n + 1) / 2) := by omega
        rw [this, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul]
      rw [hev, mul_zero]

lemma natDegree_even_of_deriv_eq_zero {A : Type*} [CommRing A] [CharP A 2] {p : Polynomial A}
    (hp : p.derivative = 0) : p.natDegree % 2 = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  · by_contra hne
    have hodd : p.natDegree % 2 = 1 := by omega
    have hz := (deriv_eq_zero_iff_even_coeffs p).mp hp p.natDegree hodd
    exact Polynomial.leadingCoeff_ne_zero.mpr h0 hz

lemma dXBi_eq_zero_iff_even_X (g : BiPoly F) :
    B6401ContactKerD.dXBi g = 0 ↔ ∀ j i, i % 2 = 1 → (g.coeff j).coeff i = 0 := by
  constructor
  · intro h j i hi
    have hj : (g.coeff j).derivative = 0 := by
      have := congrArg (fun p : BiPoly F => p.coeff j) h
      rwa [B6401ContactKerD.coeff_dXBi, Polynomial.coeff_zero] at this
    exact (deriv_eq_zero_iff_even_coeffs (g.coeff j)).mp hj i hi
  · intro h; rw [Polynomial.ext_iff]; intro j
    rw [B6401ContactKerD.coeff_dXBi, Polynomial.coeff_zero]
    exact (deriv_eq_zero_iff_even_coeffs (g.coeff j)).mpr (h j)

lemma dXBi_sq (g : BiPoly F) : B6401ContactKerD.dXBi (g ^ 2) = 0 := by
  rw [sq, B6401ContactKerD.dXBi_mul, mul_comm g (B6401ContactKerD.dXBi g), CharTwo.add_self_eq_zero]

lemma dXBi_pow_two_mul (g : BiPoly F) (k : ℕ) : B6401ContactKerD.dXBi (g ^ (2 * k)) = 0 := by
  rw [mul_comm, pow_mul]; exact dXBi_sq (g ^ k)

lemma dXBi_C (p : Polynomial F) : B6401ContactKerD.dXBi (C p) = C p.derivative := by
  rw [Polynomial.ext_iff]; intro j
  rw [B6401ContactKerD.coeff_dXBi, Polynomial.coeff_C, Polynomial.coeff_C]
  split_ifs <;> simp

lemma natDegree_contact_dXBi_le (g : BiPoly F) : (B6401ContactKerD.dXBi g).natDegree ≤ g.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
  rw [B6401ContactKerD.coeff_dXBi, Polynomial.coeff_eq_zero_of_natDegree_lt hj, Polynomial.derivative_zero]

lemma deriv_pow_two_mul {A : Type*} [CommRing A] [CharP A 2] (p : Polynomial A) (k : ℕ) :
    (p ^ (2 * k)).derivative = 0 := by
  rw [mul_comm, pow_mul, sq, Polynomial.derivative_mul, mul_comm (p ^ k) _, CharTwo.add_self_eq_zero]

lemma natDegree_le_or_even_of_deriv_eq_dXBi (f g : BiPoly F) (h : f.derivative = B6401ContactKerD.dXBi g) :
    f.natDegree ≤ g.natDegree + 1 ∨ f.natDegree % 2 = 0 := by
  by_cases hev : f.natDegree % 2 = 0
  · exact Or.inr hev
  · left
    have hf0 : f ≠ 0 := by intro h0; simp [h0] at hev
    have hodd : f.natDegree % 2 = 1 := by omega
    have hpos : 1 ≤ f.natDegree := by omega
    have hcoeff : (f.derivative).coeff (f.natDegree - 1) ≠ 0 := by
      rw [Polynomial.coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one,
        show f.natDegree - 1 + 1 = f.natDegree by omega]
      have hc1 : ((f.natDegree : ℕ) : Polynomial F) = 1 := by
        have : f.natDegree = 2 * (f.natDegree / 2) + 1 := by omega
        rw [this, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
          CharTwo.two_eq_zero, zero_mul, zero_add]
      rw [hc1, mul_one]
      exact Polynomial.leadingCoeff_ne_zero.mpr hf0
    have hle1 : f.natDegree - 1 ≤ (f.derivative).natDegree := Polynomial.le_natDegree_of_ne_zero hcoeff
    have hle2 : (f.derivative).natDegree ≤ g.natDegree := by rw [h]; exact natDegree_contact_dXBi_le g
    omega

/-- **Char-2 `ker(D)` PDE & Parity Facts (`deg_R = 1`):** -/
theorem kerD1_pde_facts {Fpoly : ContactPoly F} (hker : contactDeriv Fpoly = 0) (hdeg : Fpoly.natDegree ≤ 1) :
    (Fpoly.coeff 1).derivative = 0 ∧
    (Fpoly.coeff 1).natDegree % 2 = 0 ∧
    (Fpoly.coeff 0).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 1) ∧
    ((Fpoly.coeff 0).natDegree ≤ (Fpoly.coeff 1).natDegree + 1 ∨ (Fpoly.coeff 0).natDegree % 2 = 0) := by
  have hc2 := congrArg (fun Q : ContactPoly F => Q.coeff 2) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Fpoly.natDegree < 2)] at hc2
  have hd0 : B6401ContactKerD.dXBi (0 : BiPoly F) = 0 := by
    rw [Polynomial.ext_iff]; intro j; simp [B6401ContactKerD.coeff_dXBi]
  rw [hd0, zero_add] at hc2
  simp only [show (2 : ℕ) ≠ 0 by omega, ↓reduceIte, show 2 - 1 = 1 by rfl] at hc2
  have hc1 := congrArg (fun Q : ContactPoly F => Q.coeff 1) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero] at hc1
  simp only [one_ne_zero, ↓reduceIte, Nat.sub_self] at hc1
  have hf0d : (Fpoly.coeff 0).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 1) := by
    have h := congrArg (· + B6401ContactKerD.dXBi (Fpoly.coeff 1)) hc1
    rw [zero_add, add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h
    exact h
  exact ⟨hc2, natDegree_even_of_deriv_eq_zero hc2, hf0d,
    natDegree_le_or_even_of_deriv_eq_dXBi _ _ hf0d⟩

/-- **Char-2 `ker(D)` PDE & Parity Facts (`deg_R = 2`):** -/
theorem kerD2_pde_facts {Fpoly : ContactPoly F} (hker : contactDeriv Fpoly = 0) (hdeg : Fpoly.natDegree ≤ 2) :
    (Fpoly.coeff 2).derivative = 0 ∧
    (Fpoly.coeff 2).natDegree % 2 = 0 ∧
    (Fpoly.coeff 1).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 2) ∧
    ((Fpoly.coeff 1).natDegree ≤ (Fpoly.coeff 2).natDegree + 1 ∨ (Fpoly.coeff 1).natDegree % 2 = 0) ∧
    (Fpoly.coeff 0).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 1) ∧
    ((Fpoly.coeff 0).natDegree ≤ (Fpoly.coeff 1).natDegree + 1 ∨ (Fpoly.coeff 0).natDegree % 2 = 0) := by
  have hd0 : B6401ContactKerD.dXBi (0 : BiPoly F) = 0 := by
    rw [Polynomial.ext_iff]; intro j; simp [B6401ContactKerD.coeff_dXBi]
  have hc3 := congrArg (fun Q : ContactPoly F => Q.coeff 3) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Fpoly.natDegree < 3), hd0, zero_add] at hc3
  simp only [show (3 : ℕ) ≠ 0 by omega, ↓reduceIte, show 3 - 1 = 2 by rfl] at hc3
  have hc2 := congrArg (fun Q : ContactPoly F => Q.coeff 2) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero] at hc2
  simp only [show (2 : ℕ) ≠ 0 by omega, ↓reduceIte, show 2 - 1 = 1 by rfl] at hc2
  have hf1d : (Fpoly.coeff 1).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 2) := by
    have h := congrArg (· + B6401ContactKerD.dXBi (Fpoly.coeff 2)) hc2
    rw [zero_add, add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h
    exact h
  have hc1 := congrArg (fun Q : ContactPoly F => Q.coeff 1) hker
  rw [coeff_contactDeriv, Polynomial.coeff_zero] at hc1
  simp only [one_ne_zero, ↓reduceIte, Nat.sub_self] at hc1
  have hf0d : (Fpoly.coeff 0).derivative = B6401ContactKerD.dXBi (Fpoly.coeff 1) := by
    have h := congrArg (· + B6401ContactKerD.dXBi (Fpoly.coeff 1)) hc1
    rw [zero_add, add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h
    exact h
  exact ⟨hc3, natDegree_even_of_deriv_eq_zero hc3, hf1d,
    natDegree_le_or_even_of_deriv_eq_dXBi _ _ hf1d, hf0d,
    natDegree_le_or_even_of_deriv_eq_dXBi _ _ hf0d⟩

lemma natDegree_pos_of_irred {K : Type*} [Field K] {p : K[X]} (hp : Irreducible p) :
    0 < p.natDegree :=
  Nat.pos_of_ne_zero fun h0 => hp.not_isUnit
    (Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hp.ne_zero, h0]; rfl))

open scoped Classical in
lemma isPrimitive_pow_bi {p : BiPoly F} (hp : p.IsPrimitive) :
    ∀ n : ℕ, (p ^ n).IsPrimitive
  | 0 => by rw [pow_zero]; exact Polynomial.isPrimitive_one
  | n + 1 => by rw [pow_succ]; exact (isPrimitive_pow_bi hp n).mul hp

/-- Over ANY char-2 field `K`, if `g.derivative ≠ 0`, then `g` has an irreducible factor `p`
with `p.derivative ≠ 0` appearing to an ODD exact multiplicity `2k + 1`! -/
lemma exists_odd_irred_of_deriv_ne_zero {K : Type*} [Field K] [CharP K 2] :
    ∀ n : ℕ, ∀ g : K[X], g.natDegree ≤ n → g.derivative ≠ 0 →
      ∃ (p r : K[X]) (k : ℕ), Irreducible p ∧ p.derivative ≠ 0 ∧ g = p ^ (2 * k + 1) * r ∧ ¬ p ∣ r := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro g hgn hgd
    have hg0 : g ≠ 0 := by intro h0; subst h0; simp at hgd
    have hgpos : 0 < g.natDegree := by
      by_contra h0
      have hC := Polynomial.eq_C_of_natDegree_eq_zero (p := g) (by omega)
      rw [hC, Polynomial.derivative_C] at hgd; exact hgd rfl
    have hgn_nu : ¬ IsUnit g := fun hu => by
      have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
    obtain ⟨p, hp_irr, hp_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hgn_nu hg0
    have hp_prime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irr
    have hp_pos : 0 < p.natDegree := natDegree_pos_of_irred hp_irr
    -- Extract maximal power m ≥ 1 of p dividing g!
    have hex_max : ∃ m : ℕ, 1 ≤ m ∧ p ^ m ∣ g ∧ ¬ p ^ (m + 1) ∣ g := by
      have hfin : ∃ m : ℕ, ¬ p ^ (m + 1) ∣ g := by
        refine ⟨g.natDegree, fun hd => ?_⟩
        have hle := Polynomial.natDegree_le_of_dvd hd hg0
        rw [Polynomial.natDegree_pow] at hle; nlinarith
      let m0 := Nat.find hfin
      have hm0_not : ¬ p ^ (m0 + 1) ∣ g := Nat.find_spec hfin
      have hm0_pos : 1 ≤ m0 := by
        by_contra h0
        have hm0z : m0 = 0 := by omega
        rw [hm0z, zero_add, pow_one] at hm0_not; exact hm0_not hp_dvd
      have hm0_dvd : p ^ m0 ∣ g := by
        have hlt := Nat.find_min hfin (show m0 - 1 < m0 by omega)
        push Not at hlt; rwa [show m0 - 1 + 1 = m0 by omega] at hlt
      exact ⟨m0, hm0_pos, hm0_dvd, hm0_not⟩
    obtain ⟨m, hm1, ⟨r, hr_eq⟩, hnot_succ⟩ := hex_max
    have hndvd_r : ¬ p ∣ r := by
      intro ⟨s, hs⟩; apply hnot_succ; refine ⟨s, ?_⟩
      rw [hr_eq, hs, pow_succ]; ring
    have hr0 : r ≠ 0 := by intro h0; subst h0; rw [mul_zero] at hr_eq; exact hg0 hr_eq
    have hr_lt : r.natDegree < g.natDegree := by
      rw [hr_eq, Polynomial.natDegree_mul (pow_ne_zero m hp_irr.ne_zero) hr0, Polynomial.natDegree_pow]
      nlinarith
    by_cases hpd_odd : p.derivative ≠ 0 ∧ m % 2 = 1
    · exact ⟨p, r, m / 2, hp_irr, hpd_odd.1, by rwa [show 2 * (m / 2) + 1 = m by omega], hndvd_r⟩
    · have hpm_d : (p ^ m).derivative = 0 := by
        by_cases hpd0 : p.derivative = 0
        · rw [Polynomial.derivative_pow, hpd0, mul_zero]
        · have hm_ev : m % 2 ≠ 1 := fun h => hpd_odd ⟨hpd0, h⟩
          have hev : m = 2 * (m / 2) := by omega
          rw [hev]; exact deriv_pow_two_mul p (m / 2)
      have hrd : r.derivative ≠ 0 := by
        intro h0; apply hgd
        rw [hr_eq, Polynomial.derivative_mul, hpm_d, h0, zero_mul, mul_zero, add_zero]
      obtain ⟨p', r', k', hp'_irr, hp'_d, hr'_eq, hp'_ndvd⟩ := ih r.natDegree (by omega) r le_rfl hrd
      have hp'_prime : Prime p' := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp'_irr
      have hndvd_pm : ¬ p' ∣ p ^ m := by
        intro hdiv
        have hp'_dvd_p : p' ∣ p := hp'_prime.dvd_of_dvd_pow hdiv
        have hassoc : Associated p' p := hp'_irr.associated_of_dvd hp_irr hp'_dvd_p
        have hp_dvd_r : p ∣ r := (hassoc.symm.dvd).trans (by rw [hr'_eq]; exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _)
        exact hndvd_r hp_dvd_r
      have hndvd_prod : ¬ p' ∣ p ^ m * r' := fun h =>
        (hp'_prime.dvd_or_dvd h).elim hndvd_pm hp'_ndvd
      exact ⟨p', p ^ m * r', k', hp'_irr, hp'_d, by rw [hr_eq, hr'_eq]; ring, hndvd_prod⟩

/-- Pull any nonzero `pK : (RatFunc F)[X]` back to a primitive polynomial `p : BiPoly F`
whose image in `(RatFunc F)[X]` is associated to `pK`! -/
lemma exists_prim_associated_ratFunc (pK : Polynomial (RatFunc F)) (hpK : pK ≠ 0) :
    ∃ p : BiPoly F, p.IsPrimitive ∧ p ≠ 0 ∧ p.natDegree = pK.natDegree ∧
      Associated (p.map (algebraMap (Polynomial F) (RatFunc F))) pK := by
  classical
  let ι : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial F) (RatFunc F)
  -- Clear denominators of all coefficients j ≤ pK.natDegree!
  have hclear : ∀ j : ℕ, ∃ (n d : Polynomial F), d ≠ 0 ∧ pK.coeff j * ι d = ι n := by
    intro j
    obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial F)) (pK.coeff j)
    exact ⟨n, d, nonZeroDivisors.ne_zero d.2, hd⟩
  choose num den hden_ne hden_eq using hclear
  let D : Polynomial F := ∏ j ∈ Finset.range (pK.natDegree + 1), den j
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hden_ne j
  let q : BiPoly F := ∑ j ∈ Finset.range (pK.natDegree + 1),
    Polynomial.monomial j (num j * ∏ l ∈ (Finset.range (pK.natDegree + 1)).erase j, den l)
  have hq_map : q.map ι = C (ι D) * pK := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
    by_cases hj : j < pK.natDegree + 1
    · have hj_mem : j ∈ Finset.range (pK.natDegree + 1) := Finset.mem_range.mpr hj
      dsimp only [q]
      rw [finset_sum_coeff, Finset.sum_eq_single j]
      · rw [Polynomial.coeff_monomial_same, map_mul, map_prod]
        have hD_split : D = den j * ∏ l ∈ (Finset.range (pK.natDegree + 1)).erase j, den l :=
          (Finset.mul_prod_erase _ _ hj_mem).symm
        rw [hD_split, map_mul, map_prod, ← hden_eq j]; ring
      · intro l _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro hnot; exact absurd hj_mem hnot
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : pK.natDegree < j), mul_zero]
      dsimp only [q]; rw [finset_sum_coeff]
      have h0 : (∑ x ∈ Finset.range (pK.natDegree + 1),
          (Polynomial.monomial x (num x * ∏ l ∈ (Finset.range (pK.natDegree + 1)).erase x, den l)).coeff j) = 0 := by
        apply Finset.sum_eq_zero; intro x hx
        have := Finset.mem_range.mp hx
        simp [Polynomial.coeff_monomial, show x ≠ j by omega]
      rw [h0, map_zero]
  have hq_ne : q ≠ 0 := by
    intro h0; rw [h0, Polynomial.map_zero] at hq_map
    have hDι : ι D ≠ 0 := fun h => hD_ne (hι (by rwa [map_zero]))
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hDι) hpK) hq_map.symm
  let p : BiPoly F := q.primPart
  have hp_prim : p.IsPrimitive := q.isPrimitive_primPart
  have hp_ne : p ≠ 0 := q.primPart_ne_zero
  have hcont_ne : q.content ≠ 0 := (Polynomial.content_eq_zero_iff).not.mpr hq_ne
  have hcont_ι : ι q.content ≠ 0 := fun h => hcont_ne (hι (by rwa [map_zero]))
  have hD_ι : ι D ≠ 0 := fun h => hD_ne (hι (by rwa [map_zero]))
  have hp_map : p.map ι = C ((ι q.content)⁻¹ * ι D) * pK := by
    have hq_fac := congrArg (Polynomial.map ι) q.eq_C_content_mul_primPart
    rw [Polynomial.map_mul, Polynomial.map_C, hq_map] at hq_fac
    have hm := congrArg (C (ι q.content)⁻¹ * ·) hq_fac
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcont_ι, map_one, one_mul] at hm
    rw [← hm, map_mul, mul_assoc]
  have hu : IsUnit (C ((ι q.content)⁻¹ * ι D) : Polynomial (RatFunc F)) :=
    Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (mul_ne_zero (inv_ne_zero hcont_ι) hD_ι))
  obtain ⟨u, hu_eq⟩ := hu
  refine ⟨p, hp_prim, hp_ne, ?_, ⟨u⁻¹, ?_⟩⟩
  · have h1 := congrArg Polynomial.natDegree hp_map
    rw [Polynomial.natDegree_map_eq_of_injective hι,
      Polynomial.natDegree_C_mul (mul_ne_zero (inv_ne_zero hcont_ι) hD_ι)] at h1
    exact h1
  · rw [hp_map, ← hu_eq, mul_comm (↑u : Polynomial (RatFunc F)) pK, mul_assoc, Units.mul_inv, mul_one]

/-- Exact even multiplicity of any primitive irreducible `p : BiPoly F` (`p.derivative ≠ 0`) in
a nonzero `f : BiPoly F` with `f.derivative = 0`! -/
lemma even_max_pow_of_deriv_eq_zero {p f : BiPoly F}
    (hp_prim : p.IsPrimitive) (hp_irrK : Irreducible (p.map (algebraMap (Polynomial F) (RatFunc F))))
    (hp_d : p.derivative ≠ 0) (hf0 : f ≠ 0) (hf_d : f.derivative = 0)
    (m : ℕ) (r : BiPoly F) (heq : f = p ^ m * r) (hndvd : ¬ p ∣ r) :
    m % 2 = 0 := by
  classical
  let ι : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial F) (RatFunc F)
  by_contra hodd
  have hm1 : 1 ≤ m := by omega
  have hodd' : ((m : ℕ) : Polynomial F) = 1 := by
    have : m = 2 * (m / 2) + 1 := by omega
    rw [this, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      CharTwo.two_eq_zero, zero_mul, zero_add]
  have hd := congrArg Polynomial.derivative heq
  rw [hf_d, Polynomial.derivative_mul, Polynomial.derivative_pow] at hd
  have hm_cast : ((m : ℕ) : BiPoly F) = 1 := by rw [← map_natCast C, hodd', map_one]
  simp only [Polynomial.C_eq_natCast, hm_cast, one_mul] at hd
  have hp_dvd_prod : p ∣ p.derivative * r := by
    have hp_ne : p ^ (m - 1) ≠ 0 := pow_ne_zero _ hp_prim.ne_zero
    have hsplit : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hm1]
    rw [hsplit] at hd
    have hfact : p ^ (m - 1) * (p.derivative * r + p * r.derivative) = 0 := by
      linear_combination -hd
    have hzero : p.derivative * r + p * r.derivative = 0 := (mul_eq_zero.mp hfact).resolve_left hp_ne
    refine ⟨r.derivative, ?_⟩
    have := congrArg (· + p * r.derivative) hzero
    rw [zero_add, add_assoc, CharTwo.add_self_eq_zero, add_zero] at this
    exact this
  -- Lift divisibility to (RatFunc F)[X] where p.map ι is prime!
  have hp_dvdK : p.map ι ∣ (p.derivative).map ι * r.map ι := by
    rcases hp_dvd_prod with ⟨q, hq⟩
    exact ⟨q.map ι, by rw [← Polynomial.map_mul, hq, Polynomial.map_mul]⟩
  have hp_primeK : Prime (p.map ι) := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irrK
  rcases hp_primeK.dvd_or_dvd hp_dvdK with hdvd_d | hdvd_r
  · have hd_ne : (p.derivative).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hp_d
    have hle := Polynomial.natDegree_le_of_dvd hdvd_d hd_ne
    rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι] at hle
    have hlt := Polynomial.natDegree_derivative_lt (p := p) (fun h0 =>
      hp_d (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]))
    omega
  · exact hndvd (hp_prim.dvd_of_fraction_map_dvd_fraction_map hdvd_r)

/-- **Master Char-2 `ker(D)` `deg_R = 2` Primitive GCD Decomposition (`kerD2_gcd_decomp`):**
For ANY `Fpoly ∈ ker(D)` of `deg_R = 2` (`f1 ≠ 0, f2 ≠ 0`) over ANY `[Field F] [CharP F 2]`:
extracts `qX : F[X]`, `gPrim, h1, h2 : BiPoly F` with:
- `g = C qX * gPrim`, `f1 = g * h1`, `f2 = g * h2`,
- `gPrim.IsPrimitive`, `IsRelPrime (h1.map ι) (h2.map ι)`,
- `gPrim.derivative = 0`, `g.derivative = 0`, `h2.derivative = 0`, `g.natDegree % 2 = 0`,
- `gPrim ∣ dXBi gPrim * h2`! -/
theorem kerD2_gcd_decomp {Fpoly : ContactPoly F}
    (hker : contactDeriv Fpoly = 0) (hdeg : Fpoly.natDegree ≤ 2)
    (hf1_ne : Fpoly.coeff 1 ≠ 0) (hf2_ne : Fpoly.coeff 2 ≠ 0) :
    let f1 := Fpoly.coeff 1
    let f2 := Fpoly.coeff 2
    let ι : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
    ∃ (qX : Polynomial F) (gPrim h1 h2 : BiPoly F),
      qX ≠ 0 ∧ gPrim.IsPrimitive ∧ gPrim ≠ 0 ∧ h1 ≠ 0 ∧ h2 ≠ 0 ∧
      f1 = C qX * gPrim * h1 ∧
      f2 = C qX * gPrim * h2 ∧
      IsRelPrime (h1.map ι) (h2.map ι) ∧
      gPrim.derivative = 0 ∧
      (C qX * gPrim).derivative = 0 ∧
      h2.derivative = 0 ∧
      (C qX * gPrim).natDegree = gPrim.natDegree ∧
      gPrim.natDegree % 2 = 0 ∧
      gPrim ∣ B6401ContactKerD.dXBi gPrim * h2 := by
  intro f1 f2 ι
  classical
  change f1 ≠ 0 at hf1_ne
  change f2 ≠ 0 at hf2_ne
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial F) (RatFunc F)
  have ⟨hf2_d, _, hf1_d, _, _, _⟩ := kerD2_pde_facts hker hdeg
  set f1K : Polynomial (RatFunc F) := f1.map ι
  set f2K : Polynomial (RatFunc F) := f2.map ι
  have hf1K_ne : f1K ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf1_ne
  have hf2K_ne : f2K ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf2_ne
  let gK : Polynomial (RatFunc F) := EuclideanDomain.gcd f1K f2K
  have hgK_ne : gK ≠ 0 := fun h0 => hf2K_ne (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
  obtain ⟨gPrim, hgP_prim, hgP_ne, hgP_deg, hgP_assoc⟩ := exists_prim_associated_ratFunc gK hgK_ne
  have hgP_dvd1 : gPrim ∣ f1 :=
    hgP_prim.dvd_of_fraction_map_dvd_fraction_map (hgP_assoc.dvd.trans (EuclideanDomain.gcd_dvd_left f1K f2K))
  have hgP_dvd2 : gPrim ∣ f2 :=
    hgP_prim.dvd_of_fraction_map_dvd_fraction_map (hgP_assoc.dvd.trans (EuclideanDomain.gcd_dvd_right f1K f2K))
  rcases hgP_dvd1 with ⟨h1_raw, hh1_raw⟩
  rcases hgP_dvd2 with ⟨h2_raw, hh2_raw⟩
  have hh1r_ne : h1_raw ≠ 0 := fun h0 => hf1_ne (by rw [hh1_raw, h0, mul_zero])
  have hh2r_ne : h2_raw ≠ 0 := fun h0 => hf2_ne (by rw [hh2_raw, h0, mul_zero])
  -- Factor out common X-content qX = gcd(h1_raw.content, h2_raw.content)!
  let qX : Polynomial F := EuclideanDomain.gcd h1_raw.content h2_raw.content
  have hqX_ne : qX ≠ 0 := fun h0 =>
    (Polynomial.content_eq_zero_iff.not.mpr hh2r_ne) (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
  have hqX_dvd1 : C qX ∣ h1_raw :=
    (_root_.map_dvd C (EuclideanDomain.gcd_dvd_left _ _)).trans h1_raw.C_content_dvd
  have hqX_dvd2 : C qX ∣ h2_raw :=
    (_root_.map_dvd C (EuclideanDomain.gcd_dvd_right _ _)).trans h2_raw.C_content_dvd
  rcases hqX_dvd1 with ⟨h1, hh1⟩
  rcases hqX_dvd2 with ⟨h2, hh2⟩
  have hf1_fac : f1 = C qX * gPrim * h1 := by rw [hh1_raw, hh1]; ring
  have hf2_fac : f2 = C qX * gPrim * h2 := by rw [hh2_raw, hh2]; ring
  have hh1_ne : h1 ≠ 0 := fun h0 => hf1_ne (by rw [hf1_fac, h0, mul_zero])
  have hh2_ne : h2 ≠ 0 := fun h0 => hf2_ne (by rw [hf2_fac, h0, mul_zero])
  -- Prove IsRelPrime (h1.map ι) (h2.map ι) in (RatFunc F)[X]!
  have hrel : IsRelPrime (h1.map ι) (h2.map ι) := by
    intro d hd1 hd2
    have hqι : ι qX ≠ 0 := fun h => hqX_ne (hι (by rwa [map_zero]))
    have hqU : IsUnit (C (ι qX) : Polynomial (RatFunc F)) := Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hqι)
    have h1_eq : f1K = C (ι qX) * gPrim.map ι * h1.map ι := by
      dsimp [f1K]; rw [hf1_fac, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C]
    have h2_eq : f2K = C (ι qX) * gPrim.map ι * h2.map ι := by
      dsimp [f2K]; rw [hf2_fac, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C]
    have hd_mul : gPrim.map ι * d ∣ gK := by
      apply EuclideanDomain.dvd_gcd
      · rw [h1_eq]; rcases hd1 with ⟨a, ha⟩; exact ⟨C (ι qX) * a, by rw [ha]; ring⟩
      · rw [h2_eq]; rcases hd2 with ⟨b, hb⟩; exact ⟨C (ι qX) * b, by rw [hb]; ring⟩
    have hd_self : gPrim.map ι * d ∣ gPrim.map ι := hd_mul.trans hgP_assoc.symm.dvd
    rcases hd_self with ⟨w, hw⟩
    have hne : gPrim.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hgP_ne
    have hdw : d * w = 1 := mul_left_cancel₀ hne (by
      calc gPrim.map ι * (d * w) = gPrim.map ι * d * w := by ring
        _ = gPrim.map ι := hw.symm
        _ = gPrim.map ι * 1 := (mul_one _).symm)
    exact isUnit_iff_exists_inv.mpr ⟨w, hdw⟩
  -- Prove gPrim.derivative = 0 using exists_odd_irred_of_deriv_ne_zero + ker(D) PDE!
  have hgP_d : gPrim.derivative = 0 := by
    by_contra hgd
    have hgPK_d : (gPrim.map ι).derivative ≠ 0 := by
      rw [Polynomial.derivative_map]; exact (Polynomial.map_ne_zero_iff hι).mpr hgd
    obtain ⟨pK, rK, k, hpK_irr, hpK_d, hgK_fac, hpK_ndvd_r⟩ :=
      exists_odd_irred_of_deriv_ne_zero (gPrim.map ι).natDegree (gPrim.map ι) le_rfl hgPK_d
    obtain ⟨p, hp_prim, hp_ne, hp_deg, hp_assoc⟩ := exists_prim_associated_ratFunc pK hpK_irr.ne_zero
    have hp_irrK : Irreducible (p.map ι) := hp_assoc.irreducible_iff.mpr hpK_irr
    have hp_d : p.derivative ≠ 0 := by
      intro h0; apply hpK_d
      obtain ⟨u, hu⟩ := hp_assoc
      have hu_c : (u : Polynomial (RatFunc F)).derivative = 0 := by
        have hdu := Polynomial.natDegree_eq_zero_of_isUnit u.isUnit
        rw [Polynomial.eq_C_of_natDegree_eq_zero hdu, Polynomial.derivative_C]
      rw [← hu, Polynomial.derivative_mul, Polynomial.derivative_map, h0, Polynomial.map_zero, hu_c]
      simp
    -- Extract exact max power of p dividing f2 (must be EVEN = 2 * k2)!
    have hex_max : ∀ (q : BiPoly F), q ≠ 0 → ∃ m r, q = p ^ m * r ∧ ¬ p ∣ r := by
      intro q hq0
      have hp_pos : 0 < p.natDegree := by rw [hp_deg]; exact natDegree_pos_of_irred hpK_irr
      have hfin : ∃ m : ℕ, ¬ p ^ (m + 1) ∣ q := by
        refine ⟨q.natDegree, fun hd => ?_⟩
        have hle := Polynomial.natDegree_le_of_dvd hd hq0
        rw [Polynomial.natDegree_pow] at hle; nlinarith
      let m := Nat.find hfin
      have hnot : ¬ p ^ (m + 1) ∣ q := Nat.find_spec hfin
      have hdvd : p ^ m ∣ q := by
        by_cases hm0 : m = 0
        · rw [hm0, pow_zero]; exact one_dvd _
        · have hlt := Nat.find_min hfin (show m - 1 < m by omega)
          push Not at hlt; rwa [show m - 1 + 1 = m by omega] at hlt
      rcases hdvd with ⟨r, hr⟩
      refine ⟨m, r, hr, fun ⟨s, hs⟩ => hnot ⟨s, ?_⟩⟩
      rw [hr, hs, pow_succ]; ring
    obtain ⟨e2, q2, hf2_p, hp_ndvd_q2⟩ := hex_max f2 hf2_ne
    have he2_ev : e2 % 2 = 0 := even_max_pow_of_deriv_eq_zero hp_prim hp_irrK hp_d hf2_ne hf2_d e2 q2 hf2_p hp_ndvd_q2
    obtain ⟨e1, q1, hf1_p, hp_ndvd_q1⟩ := hex_max f1 hf1_ne
    -- Show min(e1, e2) = 2*k + 1!
    have hp_dvd_gP : p ^ (2 * k + 1) ∣ gPrim := by
      refine (isPrimitive_pow_bi hp_prim (2 * k + 1)).dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) ?_
      rw [Polynomial.map_pow, hgK_fac]
      exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hp_assoc.dvd _) _
    have hp_ndvd_gP : ¬ p ^ (2 * k + 2) ∣ gPrim := by
      intro hd
      have hdK : pK ^ (2 * k + 2) ∣ pK ^ (2 * k + 1) * rK := by
        rw [← hgK_fac]
        exact (pow_dvd_pow_of_dvd hp_assoc.symm.dvd _).trans (by
          rcases hd with ⟨s, hs⟩; exact ⟨s.map ι, by rw [hs, Polynomial.map_mul, Polynomial.map_pow]⟩)
      have hpK_dvd_r : pK ∣ rK := by
        rcases hdK with ⟨s, hs⟩
        have h1 : pK ^ (2 * k + 1) * rK = pK ^ (2 * k + 1) * (pK * s) := by
          rw [hs, pow_succ]; ring
        exact ⟨s, mul_left_cancel₀ (pow_ne_zero _ hpK_irr.ne_zero) h1⟩
      exact hpK_ndvd_r hpK_dvd_r
    have hmin_ge : 2 * k + 1 ≤ e1 ∧ 2 * k + 1 ≤ e2 := by
      have hle_of : ∀ (q r : BiPoly F) (e : ℕ), q = p ^ e * r → ¬ p ∣ r → p ^ (2 * k + 1) ∣ q → 2 * k + 1 ≤ e := by
        intro q r e hqr hnd hd
        by_contra hlt
        have hle : e + 1 ≤ 2 * k + 1 := by omega
        have hd1 : p ^ (e + 1) ∣ p ^ e * r := (pow_dvd_pow p hle).trans (hqr ▸ hd)
        rcases hd1 with ⟨s, hs⟩
        have h1 : p ^ e * r = p ^ e * (p * s) := by rw [hs, pow_succ]; ring
        exact hnd ⟨s, mul_left_cancel₀ (pow_ne_zero _ hp_ne) h1⟩
      exact ⟨hle_of f1 q1 e1 hf1_p hp_ndvd_q1 (hp_dvd_gP.trans (by rw [hf1_fac]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)),
             hle_of f2 q2 e2 hf2_p hp_ndvd_q2 (hp_dvd_gP.trans (by rw [hf2_fac]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _))⟩
    -- Since gPrim is associated to gcd(f1, f2) in K[Y], we cannot have BOTH 2*k+2 ≤ e1 and 2*k+2 ≤ e2!
    have he1_eq : e1 = 2 * k + 1 := by
      by_contra hne
      have h1 : 2 * k + 2 ≤ e1 := by omega
      have h2 : 2 * k + 2 ≤ e2 := by omega
      apply hp_ndvd_gP
      refine (isPrimitive_pow_bi hp_prim (2 * k + 2)).dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) ?_
      rw [Polynomial.map_pow]
      refine (EuclideanDomain.dvd_gcd ?_ ?_).trans hgP_assoc.symm.dvd
      · exact (pow_dvd_pow _ h1).trans (by
          dsimp [f1K]; rw [hf1_p, Polynomial.map_mul, Polynomial.map_pow]; exact dvd_mul_right _ _)
      · exact (pow_dvd_pow _ h2).trans (by
          dsimp [f2K]; rw [hf2_p, Polynomial.map_mul, Polynomial.map_pow]; exact dvd_mul_right _ _)
    -- Now e2 = 2 * (e2/2) ≥ 2*k + 2, so p^(2*k+2) ∣ dXBi f2 = f1.derivative, contradicting e1 = 2*k+1!
    have he2_ge : 2 * k + 1 ≤ e2 := hmin_ge.2
    have hpdvd_dXf2 : p ^ e2 ∣ B6401ContactKerD.dXBi f2 := by
      rw [hf2_p, B6401ContactKerD.dXBi_mul, show e2 = 2 * (e2 / 2) by omega, dXBi_pow_two_mul, zero_mul, zero_add]
      exact dvd_mul_right _ _
    have hpdvd_f1d : p ^ (2 * k + 1) ∣ f1.derivative :=
      (pow_dvd_pow p he2_ge).trans (hf1_d.symm ▸ hpdvd_dXf2)
    have hf1d_eq : f1.derivative = p ^ (2 * k) * p.derivative * q1 + p ^ (2 * k + 1) * q1.derivative := by
      rw [hf1_p, he1_eq, Polynomial.derivative_mul, Polynomial.derivative_pow]
      have hodd' : ((2 * k + 1 : ℕ) : Polynomial F) = 1 := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, CharTwo.two_eq_zero, zero_mul, zero_add]
      have hm_cast : ((2 * k + 1 : ℕ) : BiPoly F) = 1 := by rw [← map_natCast C, hodd', map_one]
      simp only [Polynomial.C_eq_natCast, hm_cast, one_mul, show 2 * k + 1 - 1 = 2 * k by omega]
    have hpdvd_term : p ^ (2 * k + 1) ∣ p ^ (2 * k) * p.derivative * q1 := by
      rcases hpdvd_f1d with ⟨s, hs⟩
      refine ⟨s + q1.derivative, ?_⟩
      have h := congrArg (· + p ^ (2 * k + 1) * q1.derivative) (hs.symm.trans hf1d_eq)
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h
      linear_combination -h
    have hp_dvd_pq1 : p ∣ p.derivative * q1 := by
      rcases hpdvd_term with ⟨s, hs⟩
      have h1 : p ^ (2 * k) * (p.derivative * q1) = p ^ (2 * k) * (p * s) := by
        rw [pow_succ] at hs; linear_combination hs
      exact ⟨s, mul_left_cancel₀ (pow_ne_zero _ hp_ne) h1⟩
    have hp_dvdK : p.map ι ∣ (p.derivative).map ι * q1.map ι := by
      rcases hp_dvd_pq1 with ⟨s, hs⟩; exact ⟨s.map ι, by rw [← Polynomial.map_mul, hs, Polynomial.map_mul]⟩
    rcases (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irrK).dvd_or_dvd hp_dvdK with hdvd_d | hdvd_q
    · have hle := Polynomial.natDegree_le_of_dvd hdvd_d ((Polynomial.map_ne_zero_iff hι).mpr hp_d)
      rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι] at hle
      have hlt := Polynomial.natDegree_derivative_lt (p := p) (fun h0 =>
        hp_d (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]))
      omega
    · exact hp_ndvd_q1 (hp_prim.dvd_of_fraction_map_dvd_fraction_map hdvd_q)
  have hg_d : (C qX * gPrim).derivative = 0 := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_C, hgP_d, zero_mul, mul_zero, add_zero]
  have hh2_d : h2.derivative = 0 := by
    have hd := congrArg Polynomial.derivative hf2_fac
    rw [hf2_d, Polynomial.derivative_mul, hg_d, zero_mul, zero_add] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (mul_ne_zero (Polynomial.C_ne_zero.mpr hqX_ne) hgP_ne)
  -- Finally prove gPrim ∣ dXBi gPrim * h2 from f1.derivative = dXBi f2!
  have hdvd_dX : gPrim ∣ B6401ContactKerD.dXBi gPrim * h2 := by
    have heq : (C qX * gPrim) * h1.derivative =
        (C qX.derivative * gPrim + C qX * B6401ContactKerD.dXBi gPrim) * h2 +
          (C qX * gPrim) * B6401ContactKerD.dXBi h2 := by
      have hL : f1.derivative = (C qX * gPrim) * h1.derivative := by
        rw [hf1_fac, Polynomial.derivative_mul, hg_d, zero_mul, zero_add]
      have hR : B6401ContactKerD.dXBi f2 =
          (C qX.derivative * gPrim + C qX * B6401ContactKerD.dXBi gPrim) * h2 +
            (C qX * gPrim) * B6401ContactKerD.dXBi h2 := by
        rw [hf2_fac, B6401ContactKerD.dXBi_mul, B6401ContactKerD.dXBi_mul, dXBi_C]
      rw [← hL, ← hR, hf1_d]
    have hdvd_C : gPrim ∣ C qX * (B6401ContactKerD.dXBi gPrim * h2) := by
      refine ⟨C qX * h1.derivative + C qX * B6401ContactKerD.dXBi h2 + C qX.derivative * h2, ?_⟩
      have h0 : C qX * (B6401ContactKerD.dXBi gPrim * h2) +
          gPrim * (C qX * h1.derivative + C qX * B6401ContactKerD.dXBi h2 + C qX.derivative * h2) = 0 := by
        have hadd := congrArg (· + (C qX * gPrim) * h1.derivative) heq
        rw [CharTwo.add_self_eq_zero] at hadd
        have h2z : ∀ a : BiPoly F, a + a = 0 := CharTwo.add_self_eq_zero
        linear_combination -hadd
      have hfin := congrArg (· + gPrim * (C qX * h1.derivative + C qX * B6401ContactKerD.dXBi h2 + C qX.derivative * h2)) h0
      rw [zero_add, add_assoc, CharTwo.add_self_eq_zero, add_zero] at hfin
      exact hfin
    refine hgP_prim.dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) ?_
    rcases hdvd_C with ⟨w, hw⟩
    have hqι : ι qX ≠ 0 := fun h => hqX_ne (hι (h.trans (map_zero ι).symm))
    refine ⟨C (ι qX)⁻¹ * w.map ι, ?_⟩
    have hm := congrArg (Polynomial.map ι) hw
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C] at hm
    have hm' := congrArg (C (ι qX)⁻¹ * ·) hm
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hqι, map_one, one_mul] at hm'
    change (B6401ContactKerD.dXBi gPrim * h2).map ι = gPrim.map ι * (C (ι qX)⁻¹ * w.map ι)
    rw [Polynomial.map_mul, hm', Polynomial.map_mul]; ring
  exact ⟨qX, gPrim, h1, h2, hqX_ne, hgP_prim, hgP_ne, hh1_ne, hh2_ne,
    hf1_fac, hf2_fac, hrel, hgP_d, hg_d, hh2_d, Polynomial.natDegree_C_mul hqX_ne,
    natDegree_even_of_deriv_eq_zero hgP_d, hdvd_dX⟩

end KerD2UFD
end B6402SmallAlg
end ProximityPrize.SubmissionBinaryLower
