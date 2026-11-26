import ProximityPrize.SubmissionBinaryLower.Binary6402SmallAlgPart3
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

/-- Helper: if `gPrim ∣ dXBi gPrim` in `BiPoly F` (`gPrim ≠ 0`), then `dXBi gPrim = 0`! -/
lemma dXBi_eq_zero_of_dvd_dXBi {gPrim : BiPoly F} (hg : gPrim ≠ 0)
    (hdvd : gPrim ∣ B6401ContactKerD.dXBi gPrim) : B6401ContactKerD.dXBi gPrim = 0 := by
  classical
  rcases hdvd with ⟨c, hc⟩
  by_cases hc0 : c = 0
  · rw [hc, hc0, mul_zero]
  · exfalso
    have hc_deg : c.natDegree = 0 := by
      have h1 := natDegree_contact_dXBi_le gPrim
      rw [hc, Polynomial.natDegree_mul hg hc0] at h1; omega
    have hcC : c = C (c.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hc_deg
    have hc0_ne : c.coeff 0 ≠ 0 := fun h => hc0 (by rw [hcC, h, map_zero])
    -- Pick j0 ∈ gPrim.support maximizing (gPrim.coeff j).natDegree!
    have hsupp : gPrim.support.Nonempty := Polynomial.support_nonempty.mpr hg
    obtain ⟨j0, hj0_mem, hj0_max⟩ := Finset.exists_max_image gPrim.support (fun j => (gPrim.coeff j).natDegree) hsupp
    have hj0_ne : gPrim.coeff j0 ≠ 0 := Polynomial.mem_support_iff.mp hj0_mem
    have hcoeff := congrArg (fun p : BiPoly F => p.coeff j0) hc
    rw [B6401ContactKerD.coeff_dXBi, hcC, Polynomial.coeff_mul_C] at hcoeff
    have hderiv_ne : (gPrim.coeff j0).derivative ≠ 0 := by
      rw [hcoeff]; exact mul_ne_zero hj0_ne hc0_ne
    have hlt := Polynomial.natDegree_derivative_lt (p := gPrim.coeff j0) (fun h0 =>
      hderiv_ne (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]))
    rw [hcoeff, Polynomial.natDegree_mul hj0_ne hc0_ne] at hlt
    omega

/-- **Table 3 Subcase `2A` / `2B` Dichotomy (`kerD2_2A_2B_dichotomy`):**
1. For `h2.natDegree = 0` (`(8, 8, 10, 11)`): ALWAYS Subcase `2A` (`gPrim ∈ F[X^2, Y^2]`)!
2. For `gPrim.natDegree = 6, h2.natDegree = 2` (`(8, 6, 10, 11)`):
   EITHER Subcase `2A` (`gPrim ∈ F[X^2, Y^2]`)
   OR Subcase `2B` (`∃ uX q g1`, `h2 = C uX * q`, `gPrim = q * g1`, `q, g1 ∈ F[X, Y^2]`,
   `q.natDegree = 2`, `g1.natDegree = 4`, `IsRelPrime (h1.map ι) (q.map ι)`)! -/
theorem kerD2_2A_2B_dichotomy {gPrim h1 h2 : BiPoly F}
    (hgP_prim : gPrim.IsPrimitive) (hgP_ne : gPrim ≠ 0) (hh1_ne : h1 ≠ 0) (hh2_ne : h2 ≠ 0)
    (hgP_d : gPrim.derivative = 0) (hh2_d : h2.derivative = 0)
    (hrel : IsRelPrime (h1.map (algebraMap (Polynomial F) (RatFunc F)))
                       (h2.map (algebraMap (Polynomial F) (RatFunc F))))
    (hdvd_dX : gPrim ∣ B6401ContactKerD.dXBi gPrim * h2) :
    (h2.natDegree = 0 → ∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) ∧
    (gPrim.natDegree = 6 → h2.natDegree = 2 →
      (∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) ∨
      ∃ (uX : Polynomial F) (q g1 : BiPoly F),
        uX ≠ 0 ∧ q.IsPrimitive ∧ q ≠ 0 ∧ g1 ≠ 0 ∧
        q.natDegree = 2 ∧ g1.natDegree = 4 ∧
        q.derivative = 0 ∧ g1.derivative = 0 ∧
        h2 = C uX * q ∧ gPrim = q * g1 ∧
        IsRelPrime (h1.map (algebraMap (Polynomial F) (RatFunc F)))
                   (q.map (algebraMap (Polynomial F) (RatFunc F)))) := by
  classical
  let ι : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial F) (RatFunc F)
  have h2A_of_dX0 : B6401ContactKerD.dXBi gPrim = 0 →
      ∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    intro hdX0 j i hnz
    constructor
    · by_contra hne
      exact hnz ((dXBi_eq_zero_iff_even_X gPrim).mp hdX0 j i (by omega))
    · by_contra hne
      have hj0 := (deriv_eq_zero_iff_even_coeffs gPrim).mp hgP_d j (by omega)
      rw [hj0, Polynomial.coeff_zero] at hnz; exact hnz rfl
  constructor
  · intro hh2_0
    have hh2C : h2 = C (h2.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hh2_0
    have hc0_ne : h2.coeff 0 ≠ 0 := fun h => hh2_ne (by rw [hh2C, h, map_zero])
    have hdvd_self : gPrim ∣ B6401ContactKerD.dXBi gPrim := by
      refine hgP_prim.dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) ?_
      rcases hdvd_dX with ⟨w, hw⟩
      have hcι : ι (h2.coeff 0) ≠ 0 := fun h => hc0_ne (hι (h.trans (map_zero ι).symm))
      refine ⟨C (ι (h2.coeff 0))⁻¹ * w.map ι, ?_⟩
      have hm := congrArg (Polynomial.map ι) hw
      rw [Polynomial.map_mul, Polynomial.map_mul, hh2C, Polynomial.map_C] at hm
      have hm' := congrArg (· * C (ι (h2.coeff 0))⁻¹) hm
      simp only [mul_assoc, ← map_mul, mul_inv_cancel₀ hcι, map_one, mul_one] at hm'
      change (B6401ContactKerD.dXBi gPrim).map ι = gPrim.map ι * (C (ι (h2.coeff 0))⁻¹ * w.map ι)
      rw [hm']; ring
    exact h2A_of_dX0 (dXBi_eq_zero_of_dvd_dXBi hgP_ne hdvd_self)
  · intro hdg6 hh2_2
    let qK : Polynomial (RatFunc F) := EuclideanDomain.gcd (gPrim.map ι) (h2.map ι)
    have hqK_ne : qK ≠ 0 := fun h0 => ((Polynomial.map_ne_zero_iff hι).mpr hgP_ne) (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
    obtain ⟨q, hq_prim, hq_ne, hq_deg, hq_assoc⟩ := exists_prim_associated_ratFunc qK hqK_ne
    have hq_dvd_gP : q ∣ gPrim :=
      hq_prim.dvd_of_fraction_map_dvd_fraction_map (hq_assoc.dvd.trans (EuclideanDomain.gcd_dvd_left _ _))
    have hq_dvd_h2 : q ∣ h2 :=
      hq_prim.dvd_of_fraction_map_dvd_fraction_map (hq_assoc.dvd.trans (EuclideanDomain.gcd_dvd_right _ _))
    -- Prove q.derivative = 0 (since both gPrim.derivative = 0 and h2.derivative = 0, every irreducible
    -- with p.derivative ≠ 0 has even multiplicity in BOTH gPrim and h2, hence in q = gcd!)
    have hq_d : q.derivative = 0 := by
      by_contra hqd
      have hqK_d : (q.map ι).derivative ≠ 0 := by
        rw [Polynomial.derivative_map]; exact (Polynomial.map_ne_zero_iff hι).mpr hqd
      obtain ⟨pK, rK, k, hpK_irr, hpK_d, hqK_fac, hpK_ndvd_r⟩ :=
        exists_odd_irred_of_deriv_ne_zero (q.map ι).natDegree (q.map ι) le_rfl hqK_d
      obtain ⟨p, hp_prim, hp_ne, hp_deg, hp_assoc⟩ := exists_prim_associated_ratFunc pK hpK_irr.ne_zero
      have hp_irrK : Irreducible (p.map ι) := hp_assoc.irreducible_iff.mpr hpK_irr
      have hp_d : p.derivative ≠ 0 := by
        intro h0; apply hpK_d
        obtain ⟨u, hu⟩ := hp_assoc
        have hu_c : (u : Polynomial (RatFunc F)).derivative = 0 := by
          rw [Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit u.isUnit), Polynomial.derivative_C]
        rw [← hu, Polynomial.derivative_mul, Polynomial.derivative_map, h0, Polynomial.map_zero, hu_c]; simp
      have hex_max : ∀ (f : BiPoly F), f ≠ 0 → ∃ m r, f = p ^ m * r ∧ ¬ p ∣ r := by
        intro f hf0
        have hp_pos : 0 < p.natDegree := by rw [hp_deg]; exact natDegree_pos_of_irred hpK_irr
        have hfin : ∃ m : ℕ, ¬ p ^ (m + 1) ∣ f := ⟨f.natDegree, fun hd => by
          have hle := Polynomial.natDegree_le_of_dvd hd hf0; rw [Polynomial.natDegree_pow] at hle; nlinarith⟩
        let m := Nat.find hfin
        have hnot : ¬ p ^ (m + 1) ∣ f := Nat.find_spec hfin
        have hdvd : p ^ m ∣ f := by
          by_cases hm0 : m = 0
          · rw [hm0, pow_zero]; exact one_dvd _
          · have hlt := Nat.find_min hfin (show m - 1 < m by omega)
            push Not at hlt; rwa [show m - 1 + 1 = m by omega] at hlt
        rcases hdvd with ⟨r, hr⟩
        exact ⟨m, r, hr, fun ⟨s, hs⟩ => hnot ⟨s, by rw [hr, hs, pow_succ]; ring⟩⟩
      obtain ⟨e1, r1, hgP_p, hp_ndvd1⟩ := hex_max gPrim hgP_ne
      obtain ⟨e2, r2, hh2_p, hp_ndvd2⟩ := hex_max h2 hh2_ne
      have he1_ev := even_max_pow_of_deriv_eq_zero hp_prim hp_irrK hp_d hgP_ne hgP_d e1 r1 hgP_p hp_ndvd1
      have he2_ev := even_max_pow_of_deriv_eq_zero hp_prim hp_irrK hp_d hh2_ne hh2_d e2 r2 hh2_p hp_ndvd2
      have hp_dvd_q : p ^ (2 * k + 1) ∣ q :=
        (isPrimitive_pow_bi hp_prim (2 * k + 1)).dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F) (by
          rw [Polynomial.map_pow, hqK_fac]; exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hp_assoc.dvd _) _)
      have hge1 : 2 * k + 1 ≤ e1 := by
        by_contra hlt
        have hd1 : p ^ (e1 + 1) ∣ p ^ e1 * r1 := (pow_dvd_pow p (by omega)).trans (hgP_p ▸ hp_dvd_q.trans hq_dvd_gP)
        rcases hd1 with ⟨s, hs⟩
        exact hp_ndvd1 ⟨s, mul_left_cancel₀ (pow_ne_zero _ hp_ne) (by rw [hs, pow_succ]; ring)⟩
      have hge2 : 2 * k + 1 ≤ e2 := by
        by_contra hlt
        have hd2 : p ^ (e2 + 1) ∣ p ^ e2 * r2 := (pow_dvd_pow p (by omega)).trans (hh2_p ▸ hp_dvd_q.trans hq_dvd_h2)
        rcases hd2 with ⟨s, hs⟩
        exact hp_ndvd2 ⟨s, mul_left_cancel₀ (pow_ne_zero _ hp_ne) (by rw [hs, pow_succ]; ring)⟩
      have hge1' : 2 * k + 2 ≤ e1 := by omega
      have hge2' : 2 * k + 2 ≤ e2 := by omega
      have hdK : pK ^ (2 * k + 2) ∣ pK ^ (2 * k + 1) * rK := by
        rw [← hqK_fac]
        refine (pow_dvd_pow_of_dvd hp_assoc.symm.dvd _).trans ((EuclideanDomain.dvd_gcd ?_ ?_).trans hq_assoc.symm.dvd)
        · exact (pow_dvd_pow _ hge1').trans (by rw [hgP_p, Polynomial.map_mul, Polynomial.map_pow]; exact dvd_mul_right _ _)
        · exact (pow_dvd_pow _ hge2').trans (by rw [hh2_p, Polynomial.map_mul, Polynomial.map_pow]; exact dvd_mul_right _ _)
      rcases hdK with ⟨s, hs⟩
      exact hpK_ndvd_r ⟨s, mul_left_cancel₀ (pow_ne_zero _ hpK_irr.ne_zero) (by rw [hs, pow_succ]; ring)⟩
    have hq_ev : q.natDegree % 2 = 0 := natDegree_even_of_deriv_eq_zero hq_d
    have hq_le2 : q.natDegree ≤ 2 := (Polynomial.natDegree_le_of_dvd hq_dvd_h2 hh2_ne).trans (le_of_eq hh2_2)
    rcases (show q.natDegree = 0 ∨ q.natDegree = 2 by omega) with hq0 | hq2
    · -- Subcase 2A: gcd_K(gPrim, h2) is a unit => IsRelPrime (gPrim.map ι) (h2.map ι) => gPrim ∣ dXBi gPrim => dXBi gPrim = 0!
      left
      have hqU : IsUnit qK := Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hqK_ne, ← hq_deg, hq0]; rfl)
      have hcop : IsCoprime (gPrim.map ι) (h2.map ι) := by
        obtain ⟨u, hu⟩ := hqU
        refine ⟨EuclideanDomain.gcdA (gPrim.map ι) (h2.map ι) * ↑u⁻¹,
                EuclideanDomain.gcdB (gPrim.map ι) (h2.map ι) * ↑u⁻¹, ?_⟩
        have hbez := EuclideanDomain.gcd_eq_gcd_ab (gPrim.map ι) (h2.map ι)
        change qK = _ at hbez; rw [← hu] at hbez
        calc EuclideanDomain.gcdA (gPrim.map ι) (h2.map ι) * ↑u⁻¹ * gPrim.map ι +
              EuclideanDomain.gcdB (gPrim.map ι) (h2.map ι) * ↑u⁻¹ * h2.map ι
            = (gPrim.map ι * EuclideanDomain.gcdA (gPrim.map ι) (h2.map ι) +
                h2.map ι * EuclideanDomain.gcdB (gPrim.map ι) (h2.map ι)) * ↑u⁻¹ := by ring
          _ = ↑u * ↑u⁻¹ := by rw [← hbez]
          _ = 1 := Units.mul_inv u
      have hdvdK : gPrim.map ι ∣ (B6401ContactKerD.dXBi gPrim).map ι := by
        refine hcop.dvd_of_dvd_mul_right ?_
        rcases hdvd_dX with ⟨w, hw⟩
        exact ⟨w.map ι, by rw [← Polynomial.map_mul, hw, Polynomial.map_mul]⟩
      exact h2A_of_dX0 (dXBi_eq_zero_of_dvd_dXBi hgP_ne (hgP_prim.dvd_of_fraction_map_dvd_fraction_map hdvdK))
    · -- Subcase 2B: deg_Y q = 2 => h2 = C uX * q, gPrim = q * g1!
      right
      rcases hq_dvd_gP with ⟨g1, hg1_eq⟩
      rcases hq_dvd_h2 with ⟨uPoly, hu_eq⟩
      have hg1_ne : g1 ≠ 0 := fun h0 => hgP_ne (by rw [hg1_eq, h0, mul_zero])
      have hu_ne : uPoly ≠ 0 := fun h0 => hh2_ne (by rw [hu_eq, h0, mul_zero])
      have hg1_deg : g1.natDegree = 4 := by
        have h := congrArg Polynomial.natDegree hg1_eq
        rw [hdg6, Polynomial.natDegree_mul hq_ne hg1_ne, hq2] at h; omega
      have hu_deg : uPoly.natDegree = 0 := by
        have h := congrArg Polynomial.natDegree hu_eq
        rw [hh2_2, Polynomial.natDegree_mul hq_ne hu_ne, hq2] at h; omega
      have huC : uPoly = C (uPoly.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hu_deg
      have huX_ne : uPoly.coeff 0 ≠ 0 := fun h => hu_ne (by rw [huC, h, map_zero])
      have hg1_d : g1.derivative = 0 := by
        have hd := congrArg Polynomial.derivative hg1_eq
        rw [hgP_d, Polynomial.derivative_mul, hq_d, zero_mul, zero_add] at hd
        exact (mul_eq_zero.mp hd.symm).resolve_left hq_ne
      have hrel_q : IsRelPrime (h1.map ι) (q.map ι) := by
        intro d hd1 hdq
        exact hrel hd1 (hdq.trans (by rw [hu_eq, Polynomial.map_mul]; exact dvd_mul_right _ _))
      exact ⟨uPoly.coeff 0, q, g1, huX_ne, hq_prim, hq_ne, hg1_ne, hq2, hg1_deg, hq_d, hg1_d,
        by conv_lhs => rw [hu_eq, huC, mul_comm], hg1_eq, hrel_q⟩

end KerD2UFD


end B6402SmallAlg
end ProximityPrize.SubmissionBinaryLower
