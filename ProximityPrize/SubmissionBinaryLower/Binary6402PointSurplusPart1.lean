import ProximityPrize.SubmissionBinaryLower.Binary6402PointSurplusPart0
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.B6401KerD2
import ProximityPrize.SubmissionBinaryLower.Binary6402FarkasVerifier
import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid12
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.Binary6402IntSmallCerts
import ProximityPrize.SubmissionBinaryLower.B6401T4Rows
import ProximityPrize.SubmissionBinaryLower.B6401T4Grid
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT1
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT2
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT3
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4a
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4b1
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4b2
import ProximityPrize.SubmissionBinaryLower.Binary6402SmallAlg
import ProximityPrize.SubmissionBinaryLower.B6401ResLineOrd
import ProximityPrize.SubmissionBinaryLower.Binary6402QuotBridge
import ProximityPrize.SubmissionBinaryLower.B6401ListAndMCA
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

/-!
# Exact Local Orders, Global Resultant Non-Vanishing, & Single-Point Surplus (`B6402PointSurplus`)

Provides the foundation for `B6401FactorBound`:
1. Fast `decide` side-bounds on certificate tables (`certsT1_linear_caps`, `*_ms_bound`).
2. Left-inverse local hom `invLocalHom`, unconditional `localShift_ne_zero`, and exact `(t, w)`-order `exactTwOrd`.
3. Monotonicity of `resOrdWeighted2Fast`, `resOrdExact`, `t3Vrf0Ord`, `t3_2BVrf0Sub`.
4. Global resultant non-vanishing over `Fld[Z][X]` (`resY_f0_f1_ne_zero_of_irred_deg1`,
   `exists_t_resY_ne_zero_of_irred_deg2`) and `evalZ` root counting.
5. Single-point surplus theorems `t1_surplus_of_point` (Table 1) and `t23_surplus_of_point`
   (Tables 2, 3, 2A, and 2B).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402PointSurplus

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial  B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6402FarkasVerifier B6402HybridP64 B6402IntFarkas
open B6402IntSmallCerts B6401T4Rows B6401T4Grid
open B6402CertsT1 B6402CertsT2 B6402CertsT3 B6401CertsT4a B6401CertsT4b1 B6401CertsT4b2
open B6402SmallAlg B6401ResLineOrd B6402QuotBridge B6401ListAndMCA
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

lemma evalZ_resultant_biPoly (f g : BiPoly (Polynomial Fld)) (df dg : ℕ) (z : Fld) :
    (Polynomial.resultant f g df dg).map (Polynomial.evalRingHom z) =
      Polynomial.resultant (evalZBiPoly f z) (evalZBiPoly g z) df dg := by
  have h := Polynomial.resultant_map_map f g df dg (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  simpa only [evalZBiPoly, Polynomial.coe_mapRingHom] using h.symm

lemma exists_prim_associated_ratFunc_gen {K : Type*} [Field K]
    (pK : Polynomial (RatFunc K)) (hpK : pK ≠ 0) :
    ∃ p : BiPoly K, p.IsPrimitive ∧ p ≠ 0 ∧ p.natDegree = pK.natDegree ∧
      Associated (p.map (algebraMap (Polynomial K) (RatFunc K))) pK := by
  classical
  let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial K) (RatFunc K)
  have hclear : ∀ j : ℕ, ∃ (n d : Polynomial K), d ≠ 0 ∧ pK.coeff j * ι d = ι n := by
    intro j
    obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial K)) (pK.coeff j)
    exact ⟨n, d, nonZeroDivisors.ne_zero d.2, hd⟩
  choose num den hden_ne hden_eq using hclear
  let D : Polynomial K := ∏ j ∈ Finset.range (pK.natDegree + 1), den j
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hden_ne j
  let q : BiPoly K := ∑ j ∈ Finset.range (pK.natDegree + 1),
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
  let p : BiPoly K := q.primPart
  have hp_prim : p.IsPrimitive := q.isPrimitive_primPart
  have hp_ne : p ≠ 0 := q.primPart_ne_zero
  have hc_ne : q.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hq_ne
  have hq_eq : q = C q.content * p := q.eq_C_content_mul_primPart
  have hp_map : p.map ι = C (ι D * (ι q.content)⁻¹) * pK := by
    have hcι : ι q.content ≠ 0 := fun h => hc_ne (hι (by rwa [map_zero]))
    have hm := congrArg (Polynomial.map ι) hq_eq
    rw [hq_map, Polynomial.map_mul, Polynomial.map_C] at hm
    have hm' := congrArg (C (ι q.content)⁻¹ * ·) hm
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcι, map_one, one_mul] at hm'
    rw [← hm', mul_comm (ι D)]
  have hu : IsUnit (C (ι D * (ι q.content)⁻¹) : Polynomial (RatFunc K)) := by
    have hDι : ι D ≠ 0 := fun h => hD_ne (hι (by rwa [map_zero]))
    have hcι : ι q.content ≠ 0 := fun h => hc_ne (hι (by rwa [map_zero]))
    exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (mul_ne_zero hDι (inv_ne_zero hcι)))
  obtain ⟨u, hu_eq⟩ := hu
  have hassoc : Associated (p.map ι) pK :=
    ⟨u⁻¹, by rw [hp_map, ← hu_eq, mul_comm (↑u : Polynomial (RatFunc K)) pK, mul_assoc, Units.mul_inv, mul_one]⟩
  have hdeg : p.natDegree = pK.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective hι, hp_map]
    exact Polynomial.natDegree_C_mul (by
      have hDι : ι D ≠ 0 := fun h => hD_ne (hι (by rwa [map_zero]))
      have hcι : ι q.content ≠ 0 := fun h => hc_ne (hι (by rwa [map_zero]))
      exact mul_ne_zero hDι (inv_ne_zero hcι))
  exact ⟨p, hp_prim, hp_ne, hdeg, hassoc⟩

/-- If `F : ContactPoly K` is irreducible with `F.natDegree ≥ 1`, its `R`-coefficients have no
common non-unit divisor in `(RatFunc K)[Y]`! -/
theorem no_common_irred_factor_of_irred {K : Type*} [Field K] {F : ContactPoly K}
    (hirr : Irreducible F) (hdeg : 1 ≤ F.natDegree) :
    let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
    ∀ p : Polynomial (RatFunc K), (∀ k, p ∣ (F.coeff k).map ι) → IsUnit p := by
  classical
  intro ι p hp
  by_contra hnu
  have hp_ne : p ≠ 0 := by
    intro h0; subst h0
    have hF0 : F = 0 := by
      rw [Polynomial.ext_iff]; intro k
      have hk := zero_dvd_iff.mp (hp k)
      exact (Polynomial.map_eq_zero_iff (IsFractionRing.injective (Polynomial K) (RatFunc K))).mp hk
    exact hirr.ne_zero hF0
  obtain ⟨q, hq_prim, hq_ne, hq_deg, hq_assoc⟩ := exists_prim_associated_ratFunc_gen p hp_ne
  have hq_pos : 0 < q.natDegree := by
    rw [hq_deg]
    by_contra h0
    have hd0 : p.natDegree = 0 := by omega
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hc0 : p.coeff 0 ≠ 0 := fun h => hp_ne (by rw [hC, h, map_zero])
    exact hnu (by rw [hC]; exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hc0))
  have hq_dvd : ∀ k, q ∣ F.coeff k := fun k =>
    hq_prim.dvd_of_fraction_map_dvd_fraction_map (hq_assoc.dvd.trans (hp k))
  choose c hc using hq_dvd
  let G : ContactPoly K := ∑ k ∈ Finset.range (F.natDegree + 1), Polynomial.monomial k (c k)
  have hF_eq : F = Polynomial.C q * G := by
    rw [Polynomial.ext_iff]; intro k
    rw [Polynomial.coeff_C_mul]
    dsimp only [G]; rw [finset_sum_coeff]
    by_cases hk : k < F.natDegree + 1
    · rw [Finset.sum_eq_single k]
      · simp [hc k]
      · intro l _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    · rw [Finset.sum_eq_zero, mul_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      intro l hl; have := Finset.mem_range.mp hl; simp [Polynomial.coeff_monomial, show l ≠ k by omega]
  rcases hirr.isUnit_or_isUnit hF_eq with huq | huG
  · have hqU : IsUnit q := by
      rcases huq with ⟨u, hu⟩
      have h1 := congrArg (fun r : ContactPoly K => r.coeff 0) u.mul_inv
      rw [hu, Polynomial.coeff_C_mul, Polynomial.coeff_one_zero] at h1
      exact isUnit_iff_exists_inv.mpr ⟨(↑u⁻¹ : ContactPoly K).coeff 0, h1⟩
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hqU
    omega
  · have hG0 := Polynomial.natDegree_eq_zero_of_isUnit huG
    have hF0 : F.natDegree = 0 := by
      rw [hF_eq, Polynomial.natDegree_C_mul hq_ne, hG0]
    omega

theorem resY_f0_f1_ne_zero_of_irred_deg1_aux {K : Type*} [Field K]
    (F : ContactPoly K) (hirr : Irreducible F) (hdeg : F.natDegree = 1)
    (hd1 : 1 ≤ (F.coeff 1).natDegree) :
    F.coeff 0 ≠ 0 ∧ F.coeff 1 ≠ 0 ∧
    Polynomial.resultant (F.coeff 0) (F.coeff 1) (F.coeff 0).natDegree (F.coeff 1).natDegree ≠ 0 := by
  classical
  let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial K) (RatFunc K)
  have hFne : F ≠ 0 := hirr.ne_zero
  have hf1_ne : F.coeff 1 ≠ 0 := by
    rw [← hdeg, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hFne
  have hnoc := no_common_irred_factor_of_irred hirr (by omega)
  have hcop : IsCoprime ((F.coeff 0).map ι) ((F.coeff 1).map ι) := by
    refine EuclideanDomain.isCoprime_of_dvd ?_ ?_
    · rintro ⟨_, h1⟩; exact ((Polynomial.map_ne_zero_iff hι).mpr hf1_ne) h1
    · intro p hp _ hp0 hp1
      apply hp
      apply hnoc p
      intro k
      rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
      · exact hp0
      · exact hp1
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.map_zero]; exact dvd_zero p
  have hf0_ne : F.coeff 0 ≠ 0 := by
    intro h0
    have h1 : IsUnit ((F.coeff 1).map ι) := by
      rcases hcop with ⟨a, b, hab⟩
      rw [h0, Polynomial.map_zero, mul_zero, zero_add] at hab
      exact isUnit_iff_exists_inv.mpr ⟨b, by rw [mul_comm]; exact hab⟩
    have hd0 := Polynomial.natDegree_eq_zero_of_isUnit h1
    rw [Polynomial.natDegree_map_eq_of_injective hι] at hd0
    omega
  refine ⟨hf0_ne, hf1_ne, ?_⟩
  intro hres0
  have hresL : Polynomial.resultant ((F.coeff 0).map ι) ((F.coeff 1).map ι)
      ((F.coeff 0).map ι).natDegree ((F.coeff 1).map ι).natDegree = 0 := by
    rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
      Polynomial.resultant_map_map, hres0, map_zero]
  exact Polynomial.resultant_ne_zero _ _ hcop hresL

/-- For irreducible `F ∈ ContactPoly (Polynomial Fld)` of `deg_R = 1` with `1 ≤ (F.coeff 1).natDegree`:
`f0 ≠ 0`, `f1 ≠ 0`, AND `Res_Y(f0, f1; d0, d1) ≠ 0` in `Fld[Z][X]`! -/
theorem resY_f0_f1_ne_zero_of_irred_deg1 (Fpoly : ContactPoly (Polynomial Fld))
    (hirr : Irreducible (liftCRat Fpoly)) (hdeg : Fpoly.natDegree = 1)
    (hd1 : 1 ≤ (Fpoly.coeff 1).natDegree) :
    let f0 := Fpoly.coeff 0
    let f1 := Fpoly.coeff 1
    f0 ≠ 0 ∧ f1 ≠ 0 ∧
    Polynomial.resultant f0 f1 f0.natDegree f1.natDegree ≠ 0 := by
  intro f0 f1
  let alg : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have halg : Function.Injective alg := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  have hmap_alg : Function.Injective (Polynomial.mapRingHom alg) := Polynomial.map_injective alg halg
  have hlift_bi : Function.Injective (liftBiRat (F := Fld)) :=
    Polynomial.map_injective _ hmap_alg
  have hdeg_rat : (liftCRat Fpoly).natDegree = 1 := by
    rw [liftCRat, Polynomial.coe_mapRingHom, Polynomial.natDegree_map_eq_of_injective hlift_bi, hdeg]
  have hcoeff : ∀ k, (liftCRat Fpoly).coeff k = (Fpoly.coeff k).map (Polynomial.mapRingHom alg) := fun k => by
    simp only [liftCRat, liftBiRat, Polynomial.coe_mapRingHom, Polynomial.coeff_map]; rfl
  have hd1_rat : 1 ≤ ((liftCRat Fpoly).coeff 1).natDegree := by
    rw [hcoeff 1, Polynomial.natDegree_map_eq_of_injective hmap_alg]; exact hd1
  have ⟨hf0_rat, hf1_rat, hres_rat⟩ := resY_f0_f1_ne_zero_of_irred_deg1_aux (liftCRat Fpoly) hirr hdeg_rat hd1_rat
  refine ⟨fun h0 => hf0_rat (by rw [hcoeff 0, show Fpoly.coeff 0 = 0 from h0, Polynomial.map_zero]),
    fun h1 => hf1_rat (by rw [hcoeff 1, show Fpoly.coeff 1 = 0 from h1, Polynomial.map_zero]),
    fun hres0 => hres_rat ?_⟩
  rw [hcoeff 0, hcoeff 1, Polynomial.natDegree_map_eq_of_injective hmap_alg,
    Polynomial.natDegree_map_eq_of_injective hmap_alg, Polynomial.resultant_map_map, hres0, map_zero]

theorem exists_t_resY_ne_zero_of_irred_deg2_aux {K : Type*} [Field K]
    (cEmb0 : Fld →+* K) (hcEmb0 : Function.Injective cEmb0)
    (F : ContactPoly K) (hirr : Irreducible F) (hdeg : F.natDegree = 2)
    (hf1_ne : F.coeff 1 ≠ 0) (hf2_ne : F.coeff 2 ≠ 0)
    (hd0_le : (F.coeff 0).natDegree ≤ 25) :
    F.coeff 0 ≠ 0 ∧ ∃ t : Fld,
      let ht := F.coeff 1 + Polynomial.C (Polynomial.C (cEmb0 t)) * F.coeff 2
      ht ≠ 0 ∧ Polynomial.resultant (F.coeff 0) ht (F.coeff 0).natDegree ht.natDegree ≠ 0 := by
  classical
  let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial K) (RatFunc K)
  have hf0_ne : F.coeff 0 ≠ 0 := by
    intro h0
    have hFfac : F = Polynomial.X * (Polynomial.C (F.coeff 1) + Polynomial.C (F.coeff 2) * Polynomial.X) := by
      rw [Polynomial.ext_iff]; intro k
      cases k with
      | zero => simp [h0]
      | succ k' =>
          cases k' with
          | zero => simp
          | succ k'' =>
              cases k'' with
              | zero => simp
              | succ k''' =>
                  rw [Polynomial.coeff_X_mul, Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega),
                    zero_add, Polynomial.coeff_mul_X, Polynomial.coeff_C, if_neg (by omega),
                    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    rcases hirr.isUnit_or_isUnit hFfac with hX | hQ
    · have := Polynomial.natDegree_eq_zero_of_isUnit hX; simp at this
    · have hQdeg : (Polynomial.C (F.coeff 1) + Polynomial.C (F.coeff 2) * Polynomial.X).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hQ
      have h1 := congrArg (fun p : ContactPoly K => p.coeff 1)
        (Polynomial.eq_C_of_natDegree_eq_zero hQdeg)
      simp only [Polynomial.coeff_add, Polynomial.coeff_C, one_ne_zero, ↓reduceIte, zero_add,
        Polynomial.coeff_mul_X] at h1
      exact hf2_ne h1
  have hnoc := no_common_irred_factor_of_irred hirr (by omega)
  let f0L : Polynomial (RatFunc K) := (F.coeff 0).map ι
  let f1L : Polynomial (RatFunc K) := (F.coeff 1).map ι
  let f2L : Polynomial (RatFunc K) := (F.coeff 2).map ι
  have hf0L_ne : f0L ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf0_ne
  have hf1L_ne : f1L ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf1_ne
  have hf2L_ne : f2L ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf2_ne
  let cEmb : Fld →+* RatFunc K := ι.comp (Polynomial.C.comp cEmb0)
  have hcEmb_inj : Function.Injective cEmb :=
    hι.comp (Polynomial.C_injective.comp hcEmb0)
  let ts : Fin 27 → Fld := fun i => BinaryIRSProfile.domain ⟨i.val, lt_trans i.isLt (by norm_num)⟩
  have hts_inj : Function.Injective ts := fun i j hij => by
    have := BinaryIRSProfile.domain.injective hij
    exact Fin.ext (by simpa using congrArg Fin.val this)
  let facs : Finset (Polynomial (RatFunc K)) := (UniqueFactorizationMonoid.normalizedFactors f0L).toFinset
  have hbad_le1 : ∀ p ∈ facs, (Finset.univ.filter fun j : Fin 27 => p ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L).card ≤ 1 := by
    intro p hp
    have hp_mem : p ∈ UniqueFactorizationMonoid.normalizedFactors f0L := Multiset.mem_toFinset.mp hp
    have hp_irr : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp_mem
    have hp_dvd0 : p ∣ f0L := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp_mem
    refine Finset.card_le_one.mpr fun j1 hj1 j2 hj2 => ?_
    by_contra hne
    have hne_t : ts j1 ≠ ts j2 := fun h => hne (hts_inj h)
    have hd1 : p ∣ f1L + Polynomial.C (cEmb (ts j1)) * f2L := (Finset.mem_filter.mp hj1).2
    have hd2 : p ∣ f1L + Polynomial.C (cEmb (ts j2)) * f2L := (Finset.mem_filter.mp hj2).2
    have hsub : p ∣ Polynomial.C (cEmb (ts j1 - ts j2)) * f2L := by
      have h := dvd_sub hd1 hd2
      have heq : (f1L + Polynomial.C (cEmb (ts j1)) * f2L) - (f1L + Polynomial.C (cEmb (ts j2)) * f2L) =
          Polynomial.C (cEmb (ts j1 - ts j2)) * f2L := by
        rw [map_sub, map_sub]; ring
      rwa [heq] at h
    have hc_ne : cEmb (ts j1 - ts j2) ≠ 0 := fun h0 => sub_ne_zero.mpr hne_t (hcEmb_inj (h0.trans (map_zero cEmb).symm))
    have hp_dvd2 : p ∣ f2L := by
      rcases hsub with ⟨w, hw⟩
      refine ⟨Polynomial.C (cEmb (ts j1 - ts j2))⁻¹ * w, ?_⟩
      have h1 := congrArg (Polynomial.C (cEmb (ts j1 - ts j2))⁻¹ * ·) hw
      simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc_ne, map_one, one_mul] at h1
      rw [h1]; ring
    have hp_dvd1 : p ∣ f1L := by
      have h := dvd_sub hd1 (dvd_mul_of_dvd_right hp_dvd2 (Polynomial.C (cEmb (ts j1))))
      simpa using h
    apply hp_irr.not_isUnit
    apply hnoc p
    intro k
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk3
    · exact hp_dvd0
    · exact hp_dvd1
    · exact hp_dvd2
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.map_zero]; exact dvd_zero p
  have hbad_zero : (Finset.univ.filter fun j : Fin 27 => f1L + Polynomial.C (cEmb (ts j)) * f2L = 0).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun j1 hj1 j2 hj2 => ?_
    by_contra hne
    have hne_t : ts j1 ≠ ts j2 := fun h => hne (hts_inj h)
    have h1 := (Finset.mem_filter.mp hj1).2
    have h2 := (Finset.mem_filter.mp hj2).2
    have hdiff : Polynomial.C (cEmb (ts j1 - ts j2)) * f2L = 0 := by
      have := congrArg₂ (· - ·) h1 h2
      rw [sub_self] at this
      have heq : (f1L + Polynomial.C (cEmb (ts j1)) * f2L) - (f1L + Polynomial.C (cEmb (ts j2)) * f2L) =
          Polynomial.C (cEmb (ts j1 - ts j2)) * f2L := by rw [map_sub, map_sub]; ring
      rwa [heq] at this
    have hc_ne : cEmb (ts j1 - ts j2) ≠ 0 := fun h0 => sub_ne_zero.mpr hne_t (hcEmb_inj (h0.trans (map_zero cEmb).symm))
    exact hf2L_ne ((mul_eq_zero.mp hdiff).resolve_left (Polynomial.C_ne_zero.mpr hc_ne))
  have hfacs_card : facs.card ≤ 25 := by
    have h1 : facs.card ≤ (UniqueFactorizationMonoid.normalizedFactors f0L).card := Multiset.toFinset_card_le _
    have h2 : (UniqueFactorizationMonoid.normalizedFactors f0L).card ≤ f0L.natDegree := by
      have hprod := UniqueFactorizationMonoid.prod_normalizedFactors hf0L_ne
      obtain ⟨u, hu⟩ := hprod
      have hdeg_eq : ((UniqueFactorizationMonoid.normalizedFactors f0L).prod).natDegree = f0L.natDegree := by
        have hu0 : (u : Polynomial (RatFunc K)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit u.isUnit
        have hpne : (UniqueFactorizationMonoid.normalizedFactors f0L).prod ≠ 0 := fun h0 =>
          hf0L_ne (by rw [← hu, h0, zero_mul])
        conv_rhs => rw [← hu]
        rw [Polynomial.natDegree_mul hpne u.ne_zero, hu0, add_zero]
      have hsum : ∀ (m : Multiset (Polynomial (RatFunc K))),
          (∀ p ∈ m, Irreducible p) → m.card ≤ m.prod.natDegree := by
        intro m
        induction m using Multiset.induction_on with
        | empty => intro _; simp
        | cons a s ih =>
            intro h
            have ha_irr : Irreducible a := h a (Multiset.mem_cons_self a s)
            have hs_irr : ∀ p ∈ s, Irreducible p := fun p hp => h p (Multiset.mem_cons_of_mem hp)
            have ha_pos : 1 ≤ a.natDegree :=
              Nat.pos_of_ne_zero fun h0 => ha_irr.not_isUnit
                (Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree ha_irr.ne_zero, h0]; rfl))
            have hs_ne : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => (hs_irr 0 h0).ne_zero rfl
            rw [Multiset.card_cons, Multiset.prod_cons, Polynomial.natDegree_mul ha_irr.ne_zero hs_ne]
            have := ih hs_irr; omega
      exact (hsum _ fun p hp => UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp).trans (le_of_eq hdeg_eq)
    have h3 : f0L.natDegree = (F.coeff 0).natDegree := Polynomial.natDegree_map_eq_of_injective hι (F.coeff 0)
    omega
  let allBad : Finset (Fin 27) :=
    (Finset.univ.filter fun j : Fin 27 => f1L + Polynomial.C (cEmb (ts j)) * f2L = 0) ∪
    facs.biUnion (fun p => Finset.univ.filter fun j : Fin 27 => p ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L)
  have hallBad_lt : allBad.card < (Finset.univ : Finset (Fin 27)).card := by
    have h1 : allBad.card ≤ 1 + facs.card := by
      calc allBad.card
          ≤ (Finset.univ.filter fun j : Fin 27 => f1L + Polynomial.C (cEmb (ts j)) * f2L = 0).card +
            (facs.biUnion (fun p => Finset.univ.filter fun j : Fin 27 => p ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L)).card :=
            Finset.card_union_le _ _
        _ ≤ 1 + ∑ p ∈ facs, (Finset.univ.filter fun j : Fin 27 => p ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L).card :=
            Nat.add_le_add hbad_zero Finset.card_biUnion_le
        _ ≤ 1 + ∑ _p ∈ facs, 1 := Nat.add_le_add_left (Finset.sum_le_sum hbad_le1) 1
        _ = 1 + facs.card := by simp
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hex_j : ∃ j : Fin 27, j ∉ allBad := by
    by_contra hall; push Not at hall
    have hle := Finset.card_le_card (show (Finset.univ : Finset (Fin 27)) ⊆ allBad from fun j _ => hall j)
    omega
  obtain ⟨j, hj⟩ := hex_j
  refine ⟨hf0_ne, ts j, ?_⟩
  set ht_poly : BiPoly K := F.coeff 1 + Polynomial.C (Polynomial.C (cEmb0 (ts j))) * F.coeff 2
  have hht_map : ht_poly.map ι = f1L + Polynomial.C (cEmb (ts j)) * f2L := by
    simp [ht_poly, f1L, f2L, cEmb, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  have hhtL_ne : ht_poly.map ι ≠ 0 := by
    rw [hht_map]; intro h0; apply hj
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)
  have hht_ne : ht_poly ≠ 0 := fun h0 => hhtL_ne (by rw [h0, Polynomial.map_zero])
  have hcop : IsCoprime f0L (ht_poly.map ι) := by
    refine EuclideanDomain.isCoprime_of_dvd (fun h => hf0L_ne h.1) ?_
    intro p hp hp_ne hp0 hp1
    obtain ⟨p', hp'_irr, hp'_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hp hp_ne
    obtain ⟨q, hq_mem, hq_assoc⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf0L_ne hp'_irr (hp'_dvd.trans hp0)
    have hq_facs : q ∈ facs := Multiset.mem_toFinset.mpr hq_mem
    have hq_dvd1 : q ∣ f1L + Polynomial.C (cEmb (ts j)) * f2L := by
      rw [← hht_map]; exact hq_assoc.symm.dvd.trans (hp'_dvd.trans hp1)
    apply hj
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq_facs, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_dvd1⟩⟩)
  refine ⟨hht_ne, ?_⟩
  intro hres0
  have hresL : Polynomial.resultant f0L (ht_poly.map ι) f0L.natDegree (ht_poly.map ι).natDegree = 0 := by
    dsimp only [f0L]
    rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
      Polynomial.resultant_map_map, hres0, map_zero]
  exact Polynomial.resultant_ne_zero _ _ hcop hresL

/-- For irreducible `F ∈ ContactPoly (Polynomial Fld)` of `deg_R = 2` (`f1 ≠ 0, f2 ≠ 0, d0 ≤ 25`):
there exists `t ∈ Fld` such that `Res_Y(f0, f1 + t * f2; d0, dh) ≠ 0` in `Fld[Z][X]`! -/
theorem exists_t_resY_ne_zero_of_irred_deg2 (Fpoly : ContactPoly (Polynomial Fld))
    (hirr : Irreducible (liftCRat Fpoly)) (hdeg : Fpoly.natDegree = 2)
    (hf1_ne : Fpoly.coeff 1 ≠ 0) (hf2_ne : Fpoly.coeff 2 ≠ 0)
    (hd0_le : (Fpoly.coeff 0).natDegree ≤ 25) :
    let f0 := Fpoly.coeff 0
    let f1 := Fpoly.coeff 1
    let f2 := Fpoly.coeff 2
    f0 ≠ 0 ∧ ∃ t : Fld,
      let ht := f1 + Polynomial.C (Polynomial.C (Polynomial.C t)) * f2
      ht ≠ 0 ∧ Polynomial.resultant f0 ht f0.natDegree ht.natDegree ≠ 0 := by
  intro f0 f1 f2
  let alg : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have halg : Function.Injective alg := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  have hmap_alg : Function.Injective (Polynomial.mapRingHom alg) := Polynomial.map_injective alg halg
  have hlift_bi : Function.Injective (liftBiRat (F := Fld)) :=
    Polynomial.map_injective _ hmap_alg
  have hdeg_rat : (liftCRat Fpoly).natDegree = 2 := by
    rw [liftCRat, Polynomial.coe_mapRingHom, Polynomial.natDegree_map_eq_of_injective hlift_bi, hdeg]
  have hcoeff : ∀ k, (liftCRat Fpoly).coeff k = (Fpoly.coeff k).map (Polynomial.mapRingHom alg) := fun k => by
    simp only [liftCRat, liftBiRat, Polynomial.coe_mapRingHom, Polynomial.coeff_map]; rfl
  let cEmb0 : Fld →+* RatFunc Fld := alg.comp Polynomial.C
  have hcEmb0 : Function.Injective cEmb0 := halg.comp Polynomial.C_injective
  have hf1_rat : (liftCRat Fpoly).coeff 1 ≠ 0 := by
    rw [hcoeff 1]; exact (Polynomial.map_ne_zero_iff hmap_alg).mpr hf1_ne
  have hf2_rat : (liftCRat Fpoly).coeff 2 ≠ 0 := by
    rw [hcoeff 2]; exact (Polynomial.map_ne_zero_iff hmap_alg).mpr hf2_ne
  have hd0_rat : ((liftCRat Fpoly).coeff 0).natDegree ≤ 25 := by
    rw [hcoeff 0, Polynomial.natDegree_map_eq_of_injective hmap_alg]; exact hd0_le
  obtain ⟨hf0_rat, t, hht_rat, hres_rat⟩ :=
    exists_t_resY_ne_zero_of_irred_deg2_aux cEmb0 hcEmb0 (liftCRat Fpoly) hirr hdeg_rat hf1_rat hf2_rat hd0_rat
  refine ⟨fun h0 => hf0_rat (by rw [hcoeff 0, show Fpoly.coeff 0 = 0 from h0, Polynomial.map_zero]), t, ?_⟩
  set ht : BiPoly (Polynomial Fld) := f1 + Polynomial.C (Polynomial.C (Polynomial.C t)) * f2
  have hht_map : ht.map (Polynomial.mapRingHom alg) =
      (liftCRat Fpoly).coeff 1 + Polynomial.C (Polynomial.C (cEmb0 t)) * (liftCRat Fpoly).coeff 2 := by
    rw [hcoeff 1, hcoeff 2]
    simp only [ht, f1, f2, cEmb0, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.coe_mapRingHom, RingHom.comp_apply]
  refine ⟨fun h0 => hht_rat (by rw [← hht_map, h0, Polynomial.map_zero]), fun hres0 => hres_rat ?_⟩
  rw [hcoeff 0, ← hht_map, Polynomial.natDegree_map_eq_of_injective hmap_alg,
    Polynomial.natDegree_map_eq_of_injective hmap_alg, Polynomial.resultant_map_map, hres0, map_zero]

/-! ### Part 3: Single-Point Surplus Theorems (`t1_surplus_of_point` & `t23_surplus_of_point`) -/

lemma X_sub_C_pow_dvd_resultant_of_biMultGE {F : Type*} [Field F]
    (x0 y0 : F) (f g : BiPoly F) (df mf dg mg : ℕ)
    (hf : biMultGE x0 y0 f mf) (hg : biMultGE x0 y0 g mg)
    (hdf : f.natDegree ≤ df) (hdg : g.natDegree ≤ dg) :
    (X - C x0) ^ resOrdExact df mf dg mg ∣ Polynomial.resultant f g df dg := by
  have h := pow_dvd_resultant_of_biMultGE x0 y0 f g df mf dg mg hf hg hdf hdg
  rw [resultant_shiftBi x0 y0 f g df dg hdf hdg] at h
  exact X_sub_C_pow_dvd_of_comp_shift x0 _ _ h

lemma eval_resultant_eq_zero_of_common_root {F : Type*} [Field F]
    (f g : BiPoly F) (df dg : ℕ) (hf : f.natDegree ≤ df) (hg : g.natDegree ≤ dg)
    (P : Polynomial F) (hPf : f.eval P = 0) (hPg : g.eval P = 0) (hpos : 0 < df + dg) :
    Polynomial.resultant f g df dg = 0 := by
  let ψ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hψ : Function.Injective ψ := IsFractionRing.injective (Polynomial F) (RatFunc F)
  apply hψ; rw [map_zero, ← Polynomial.resultant_map_map]
  have hroot_f : (f.map ψ).IsRoot (ψ P) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map_apply, hPf, map_zero]
  have hroot_g : (g.map ψ).IsRoot (ψ P) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map_apply, hPg, map_zero]
  have hdf : (f.map ψ).natDegree ≤ df := Polynomial.natDegree_map_le.trans hf
  have hdg : (g.map ψ).natDegree ≤ dg := Polynomial.natDegree_map_le.trans hg
  by_cases hfn : f.map ψ = 0
  · rw [hfn, Polynomial.resultant_zero_left]
    by_cases hdg0 : dg = 0
    · subst hdg0
      have hgn : g.map ψ = 0 := by
        have hgd0 : (g.map ψ).natDegree = 0 := Nat.eq_zero_of_le_zero hdg
        have hC := Polynomial.eq_C_of_natDegree_eq_zero hgd0
        rw [hC, Polynomial.IsRoot.def, Polynomial.eval_C] at hroot_g
        rw [hC, hroot_g, map_zero]
      rw [hgn, Polynomial.coeff_zero, zero_pow (by omega : df ≠ 0), mul_zero]
    · rw [zero_pow hdg0, zero_mul]
  · by_cases hgn : g.map ψ = 0
    · rw [hgn, Polynomial.resultant_zero_right]
      by_cases hdf0 : df = 0
      · subst hdf0
        have hfn' : f.map ψ = 0 := by
          have hfd0 : (f.map ψ).natDegree = 0 := Nat.eq_zero_of_le_zero hdf
          have hC := Polynomial.eq_C_of_natDegree_eq_zero hfd0
          rw [hC, Polynomial.IsRoot.def, Polynomial.eval_C] at hroot_f
          rw [hC, hroot_f, map_zero]
        exact absurd hfn' hfn
      · rw [zero_pow hdf0, zero_mul]
    · rcases Polynomial.dvd_iff_isRoot.mpr hroot_f with ⟨f', hf'⟩
      have hf'_ne : f' ≠ 0 := fun h0 => hfn (by rw [hf', h0, mul_zero])
      have hdf_eq : (f.map ψ).natDegree = 1 + f'.natDegree := by
        rw [hf', Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hf'_ne, Polynomial.natDegree_X_sub_C]
      have hres_nat : Polynomial.resultant (f.map ψ) (g.map ψ) (f.map ψ).natDegree (g.map ψ).natDegree = 0 := by
        rw [hdf_eq, hf']
        have h1 := Polynomial.resultant_mul_left (Polynomial.X - Polynomial.C (ψ P)) f' (g.map ψ)
          (g.map ψ).natDegree le_rfl
        rw [Polynomial.natDegree_X_sub_C] at h1
        rw [h1]
        have hlin := Polynomial.resultant_X_sub_C_left (g.map ψ) (g.map ψ).natDegree (ψ P) le_rfl
        rw [hlin, Polynomial.IsRoot.def.mp hroot_g, zero_mul]
      rw [show df = (f.map ψ).natDegree + (df - (f.map ψ).natDegree) by omega,
        Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl,
        show dg = (g.map ψ).natDegree + (dg - (g.map ψ).natDegree) by omega,
        Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, hres_nat]
      ring

lemma resYKerD1Fn_le_ord (d0 d1 k : ℕ) (hd0 : d0 ≤ max d0 (d1 + 1)) :
    resYKerD1Fn d1 (max d0 (d1 + 1)) k ≤ resYKerD1Ord d0 d1 k := by
  unfold resYKerD1Fn
  by_cases hle : d0 ≤ d1 + 1
  · have hmax : max d0 (d1 + 1) = d1 + 1 := Nat.max_eq_right hle
    rw [hmax]; simp only [beq_self_eq_true, ↓reduceIte]
    unfold resYKerD1MinLe
    exact foldl_map_min_le_mem (fun d => resYKerD1Ord d d1 k) (List.range (d1 + 2))
      (resYKerD1Ord 0 d1 k) d0 (List.mem_range.mpr (by omega))
  · have hmax : max d0 (d1 + 1) = d0 := Nat.max_eq_left (by omega)
    rw [hmax]
    have hne : (d0 == d1 + 1) = false := beq_false_of_ne (by omega)
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact le_rfl

/-- **Table 1 Single-Point Surplus Theorem (`t1_surplus_of_point`):**
For ANY `F ∈ K_{W_F}(1)` over `Fld` outside Table 4 (`¬ (d1 = 4 ∧ d0 ≤ 5 ∧ W_F/wY < 28/5)`),
any point `(y, P, Az)` with `evalContact F P = 0`, `|Az| ≥ A`, `twOrdGE (localShift i) (k i)`,
produces a verified `c ∈ certsT1` giving strict quotient-interpolation surplus on `k`! -/
theorem t1_surplus_of_point {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Fld)
    (y : Idx → Fld) (k : Idx → ℕ)
    (hvan : ∀ i : Idx, twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (y i) e.1) (k i))
    (P : Polynomial Fld) (hPdeg : P.natDegree ≤ wY)
    (Az : Finset Idx) (hAz : A ≤ Az.card)
    (hagree : ∀ i ∈ Az, P.eval (BinaryIRSProfile.domain i) = y i)
    (hFvan : evalContact (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) P = 0)
    (hf1_ne : (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2)
    (hRes_ne : 2 ≤ ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree →
      Polynomial.resultant
        ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 0)
        ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1)
        ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).natDegree
        ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree ≠ 0)
    (hnotT4 : ¬ (((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree = 4 ∧
      ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).natDegree ≤ 5 ∧
      (W_F : ℚ) / (wY : ℚ) < 28 / 5)) :
    ∃ c ∈ certsT1, checkT1Entry c = true ∧ 0 < c.m ∧ c.m ≤ 3000 ∧ c.s ≤ 300 ∧
      (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) ∧
      (W_F : ℚ) / (wY : ℚ) ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ) ∧
      (c.δNum : ℚ) / (c.δDen : ℚ) <
        vquotLbQ 1 c.m c.s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 c.m c.s (k i)) / (N : ℚ) ∧
      checkCapWitness 1 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap1 = true ∧
      c.cap1.c1Bkt ≤ linearSlopeCap ∧ c.cap1.c0Bkt ≤ linearConstantCap ∧
      ((W_F : ℚ) / (wY : ℚ) < 13 →
        checkCapWitness 1 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 2 c.cap2 = true ∧
        c.cap2.c1Bkt * 1811 + c.cap2.c0Bkt ≤ linearPowerCap) := by
  set Fpoly : ContactPoly Fld := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
  set f0 : BiPoly Fld := Fpoly.coeff 0
  set f1 : BiPoly Fld := Fpoly.coeff 1
  set d0 : ℕ := f0.natDegree
  set d1 : ℕ := f1.natDegree
  set d0Eff : ℕ := max d0 (d1 + 1)
  have hwYpos : 0 < wY := by norm_num [wY]
  have hwYQ : (0 : ℚ) < (wY : ℚ) := by exact_mod_cast hwYpos
  have hFmem : contactDeriv Fpoly = 0 ∧ Fpoly.natDegree ≤ 1 ∧ wdeg wY Fpoly ≤ W_F :=
    (mem_kerD_iff_exists_unique_coords (by norm_num [wY]) Fpoly).mpr ⟨f_coord, rfl, fun c' hc' => by
      funext ⟨⟨k', r', b', a'⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W_F 1 hwYpos k' r' b' a').mp he).1
      rcases (show r' = 0 ∨ r' = 1 by omega) with rfl | rfl
      · have h := congrArg (fun Q : ContactPoly Fld => ((Q.coeff k').coeff (2 * b')).coeff (2 * a')) hc'
        dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
        simpa [he] using h.symm
      · have h := congrArg (fun Q : ContactPoly Fld => ((Q.coeff k').coeff (2 * b' + 1)).coeff (2 * a')) hc'
        dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
        have h1 : (2 * b' + 1) % 2 = 1 := by omega
        have h2 : (2 * a') % 2 = 0 := by omega
        have h3 : (2 * b' + 1) / 2 = b' := by omega
        have h4 : (2 * a') / 2 = a' := by omega
        simpa [h1, h2, h3, h4, he] using h.symm⟩
  have ⟨_, hd1_ev, _, hd0_par⟩ := kerD1_pde_facts hFmem.1 hFmem.2.1
  have hWf1 : wdegBi wY f1 + (wY - 1) ≤ W_F := by
    simpa only [one_mul] using wdegBi_coeff_le_of_wdeg hFmem.2.2 1 hf1_ne
  have hWf0 : wdegBi wY f0 ≤ W_F := by simpa using wdegBi_le_of_wdeg_coeff hFmem.2.2 0
  have hd1_wY : d1 * wY ≤ wdegBi wY f1 := by
    have hlc := Polynomial.leadingCoeff_ne_zero.mpr hf1_ne
    have hle := (wdegBi_le_iff wY (wdegBi wY f1) f1).mp le_rfl d1 _ (Polynomial.leadingCoeff_ne_zero.mpr hlc)
    omega
  have hWF_le_nat : 2 * W_F ≤ 51 * wY := by
    have : 2 * (W_F : ℚ) ≤ 51 * (wY : ℚ) := by
      have := (div_le_div_iff₀ hwYQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi; linarith
    exact_mod_cast this
  have hWf1' : wdegBi wY f1 + 1048574 ≤ W_F := hWf1
  have hd1_wY' : d1 * 1048575 ≤ wdegBi wY f1 := hd1_wY
  have hWF_le' : 2 * W_F ≤ 51 * 1048575 := hWF_le_nat
  have hd1_le24 : d1 ≤ 24 := by omega
  have hd0_eff_spec : d0Eff = d1 + 1 ∨ (d1 + 1 < d0Eff ∧ d0Eff ≤ 24 ∧ d0Eff % 2 = 0) := by
    by_cases hle : d0 ≤ d1 + 1
    · exact Or.inl (Nat.max_eq_right hle)
    · right
      have heq : d0Eff = d0 := Nat.max_eq_left (by omega)
      have hev : d0 % 2 = 0 := hd0_par.resolve_left hle
      have hf0_ne : f0 ≠ 0 := by intro h0; simp [d0, h0] at hle
      have hd0_wY : d0 * 1048575 ≤ W_F := by
        have hlc := Polynomial.leadingCoeff_ne_zero.mpr hf0_ne
        have hle' := (wdegBi_le_iff wY W_F f0).mp hWf0 d0 _ (Polynomial.leadingCoeff_ne_zero.mpr hlc)
        exact (Nat.le_add_left (d0 * wY) _).trans hle'
      refine ⟨by omega, by omega, by omega⟩
  have hlo_t1 : ((t1StartPair d1 d0Eff).1 : ℚ) / ((t1StartPair d1 d0Eff).2 : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) := by
    unfold t1StartPair
    by_cases h45 : d1 = 4 ∧ d0Eff = 5
    · have hb : (d1 == 4 && d0Eff == 5) = true := by simp [h45.1, h45.2]
      rw [if_pos hb]
      by_contra hlt; push Not at hlt
      exact hnotT4 ⟨h45.1, by omega, hlt⟩
    · have hb : (d1 == 4 && d0Eff == 5) = false := by
        rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
        by_cases h1 : d1 = 4
        · exact Or.inr fun h2 => h45 ⟨h1, h2⟩
        · exact Or.inl h1
      rw [if_neg (by simp [hb])]
      by_cases heq : d0Eff = d1 + 1
      · simp only [heq, beq_self_eq_true, ↓reduceIte]
        apply div_le_div_of_nonneg_right _ hwYQ.le
        have h1 : (d1 + 1) * wY - 1 ≤ W_F := by change (d1 + 1) * 1048575 - 1 ≤ W_F; omega
        exact_mod_cast h1
      · have hne : (d0Eff == d1 + 1) = false := beq_false_of_ne heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte, Nat.cast_one, div_one]
        have hd0_gt : d1 + 1 < d0 := by omega
        have hf0_ne : f0 ≠ 0 := by intro h0; simp [d0, h0] at hd0_gt
        have hd0_wY : d0 * wY ≤ W_F := by
          have hlc := Polynomial.leadingCoeff_ne_zero.mpr hf0_ne
          have hle' := (wdegBi_le_iff wY W_F f0).mp hWf0 d0 _ (Polynomial.leadingCoeff_ne_zero.mpr hlc)
          omega
        rw [le_div_iff₀ hwYQ]
        have : d0Eff = d0 := Nat.max_eq_left (by omega)
        rw [this]; exact_mod_cast hd0_wY
  obtain ⟨c, hc_mem, hcd1, hcd0, hc_entry, hc_lo, hc_hi⟩ :=
    exists_t1Cert d1 d0Eff hd1_le24 hd1_ev hd0_eff_spec ((W_F : ℚ) / (wY : ℚ)) hlo_t1 hWF_hi
  have hchk : checkT1Cert c = true := (Bool.and_eq_true _ _).mp hc_entry |>.1
  -- Prove f1.eval P ≠ 0!
  have hf1_P_ne : f1.eval P ≠ 0 := by
    intro h0
    by_cases hd1_0 : d1 = 0
    · have hC := Polynomial.eq_C_of_natDegree_eq_zero hd1_0
      rw [hC, Polynomial.eval_C] at h0
      exact hf1_ne (by rw [hC, h0, map_zero])
    · have hd1_2 : 2 ≤ d1 := by change d1 % 2 = 0 at hd1_ev; omega
      have hf0_P : f0.eval P = 0 := by
        have hFexp : Fpoly = Polynomial.C f0 + Polynomial.C f1 * Polynomial.X := by
          rw [Polynomial.ext_iff]; intro r; cases r with
          | zero => simp [f0]
          | succ r' => cases r' with
            | zero => simp [f1]
            | succ r'' =>
                rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Fpoly.natDegree < r''.succ.succ)]
                simp [Polynomial.coeff_C, Polynomial.coeff_mul_X]
        have hev := hFvan
        change evalContact Fpoly P = 0 at hev
        rw [hFexp] at hev; unfold evalContact at hev
        simpa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, h0] using hev
      exact hRes_ne hd1_2 (eval_resultant_eq_zero_of_common_root f0 f1 d0 d1 le_rfl le_rfl P hf0_P h0 (by omega))
  -- Prove the 3 sum bounds for checkT1Cert_sound!
  have hbm1 : ∀ i : Idx, biMultGE (BinaryIRSProfile.domain i) (y i) f1 (2 * k i - 1) :=
    fun i => (kerD1_local_ords hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)).2
  have hf1_sum : (∑ i ∈ Az, ((2 * k i - 1 : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 1) * (wY : ℚ) + 1 := by
    have hnat : ∑ i ∈ Az, (2 * k i - 1) ≤ W_F - (wY - 1) :=
      sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - (wY - 1)) f1 P (fun i => 2 * k i - 1)
        hPdeg (by omega) hf1_P_ne (fun i hi => by rw [hagree i hi]; exact hbm1 i)
    have hQ : ((∑ i ∈ Az, (2 * k i - 1) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) : ℕ) : ℚ) := by exact_mod_cast hnat
    rw [Nat.cast_sum] at hQ
    have h1 : wY - 1 ≤ W_F := by omega
    have h2 : 1 ≤ wY := by norm_num [wY]
    rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_one] at hQ
    have heq : ((W_F : ℚ) / (wY : ℚ) - 1) * (wY : ℚ) + 1 = (W_F : ℚ) - ((wY : ℚ) - 1) := by
      field_simp [hwYQ.ne']; ring
    linarith
  have hlc1_sum : (∑ i : Idx, ((2 * k i - 1 - c.d1 : ℕ) : ℚ)) ≤
      ((W_F : ℚ) / (wY : ℚ) - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1 := by
    rw [hcd1]
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
        (X - C (BinaryIRSProfile.domain i)) ^ (2 * k i - 1 - d1) ∣ f1.leadingCoeff := fun i _ =>
      pow_dvd_leadingCoeff_of_biMultGE (BinaryIRSProfile.domain i) (y i) f1 d1 (2 * k i - 1) rfl (hbm1 i)
    have hdeg_lc : f1.leadingCoeff.natDegree ≤ W_F - (wY - 1) - d1 * wY := by
      have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hf1_ne)
      have hle := (wdegBi_le_iff wY (W_F - (wY - 1)) f1).mp (by omega) d1 _ hnz
      omega
    have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ f1.leadingCoeff
      (Polynomial.leadingCoeff_ne_zero.mpr hf1_ne) _ hdvd).trans hdeg_lc
    have hQ : ((∑ i : Idx, (2 * k i - 1 - d1) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) - d1 * wY : ℕ) : ℚ) := by
      exact_mod_cast hnat
    rw [Nat.cast_sum] at hQ
    have h1 : wY - 1 + d1 * wY ≤ W_F := by omega
    have h2 : 1 ≤ wY := by norm_num [wY]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub h2, Nat.cast_mul, Nat.cast_one] at hQ
    have heq : ((W_F : ℚ) / (wY : ℚ) - 1 - (d1 : ℚ)) * (wY : ℚ) + 1 =
        (W_F : ℚ) - ((wY : ℚ) - 1) - (d1 : ℚ) * (wY : ℚ) := by
      field_simp [hwYQ.ne']; ring
    linarith
  have hres_sum : 2 ≤ c.d1 →
      (∑ i : Idx, (resYKerD1Fn c.d1 c.d0Eff (k i) : ℚ)) ≤
        ((c.d1 : ℚ) * ((W_F : ℚ) / (wY : ℚ)) +
          ((max c.d0Eff (c.d1 + 1) : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1 - (c.d1 : ℚ))) * (wY : ℚ) +
          ((max c.d0Eff (c.d1 + 1) : ℕ) : ℚ) := by
    rw [hcd1, hcd0]; intro hd1_2
    have hdp_eq : max d0Eff (d1 + 1) = d0Eff := Nat.max_eq_left (by omega)
    rw [hdp_eq]
    set R : Polynomial Fld := f1.leadingCoeff ^ (d0Eff - d0) * Polynomial.resultant f0 f1 d0 d1
    have hRne : R ≠ 0 := mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hf1_ne)) (hRes_ne hd1_2)
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
        (X - C (BinaryIRSProfile.domain i)) ^ resYKerD1Fn d1 d0Eff (k i) ∣ R := fun i _ =>
      (pow_dvd_pow _ (resYKerD1Fn_le_ord d0 d1 (k i) (le_max_left _ _))).trans
        (kerD1_resY_ord hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i) hd1_2)
    have hdeg_lc : f1.leadingCoeff.natDegree ≤ W_F - (wY - 1) - d1 * wY := by
      have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hf1_ne)
      have hle := (wdegBi_le_iff wY (W_F - (wY - 1)) f1).mp (by omega) d1 _ hnz; omega
    have hdeg_res : (Polynomial.resultant f0 f1 d0 d1).natDegree ≤
        d1 * W_F + d0 * (W_F - (wY - 1)) - d0 * d1 * wY :=
      natDegree_resultant_le_wdegBi wY W_F (W_F - (wY - 1)) d0 d1 f0 f1 hWf0 (by omega) le_rfl le_rfl
    have hdeg_R : R.natDegree ≤ d1 * W_F + d0Eff * (W_F - (wY - 1) - d1 * wY) := by
      have h1 : R.natDegree ≤ (d0Eff - d0) * f1.leadingCoeff.natDegree + (Polynomial.resultant f0 f1 d0 d1).natDegree :=
        Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_pow_le _)
      have h2 : (d0Eff - d0) * f1.leadingCoeff.natDegree ≤ (d0Eff - d0) * (W_F - (wY - 1) - d1 * wY) :=
        Nat.mul_le_mul_left _ hdeg_lc
      have hd0_le_eff : d0 ≤ d0Eff := le_max_left _ _
      have hmul_le : d0 * d1 * wY ≤ d0 * (W_F - (wY - 1)) := by
        rw [mul_assoc]; exact Nat.mul_le_mul_left d0 (by omega)
      have hsub_eq : d0 * (W_F - (wY - 1)) - d0 * d1 * wY = d0 * (W_F - (wY - 1) - d1 * wY) := by
        rw [mul_assoc d0 d1 wY, ← Nat.mul_sub]
      have hsum_eq : (d0Eff - d0) * (W_F - (wY - 1) - d1 * wY) + d0 * (W_F - (wY - 1) - d1 * wY) =
          d0Eff * (W_F - (wY - 1) - d1 * wY) := by
        rw [← add_mul, Nat.sub_add_cancel hd0_le_eff]
      omega
    have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ R hRne _ hdvd).trans hdeg_R
    have hQ : ((∑ i : Idx, resYKerD1Fn d1 d0Eff (k i) : ℕ) : ℚ) ≤
        ((d1 * W_F + d0Eff * (W_F - (wY - 1) - d1 * wY) : ℕ) : ℚ) := by exact_mod_cast hnat
    rw [Nat.cast_sum] at hQ
    have h1 : wY - 1 + d1 * wY ≤ W_F := by omega
    have h2 : 1 ≤ wY := by norm_num [wY]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
      Nat.cast_sub h2, Nat.cast_mul, Nat.cast_one] at hQ
    have heq : ((d1 : ℚ) * ((W_F : ℚ) / (wY : ℚ)) + (d0Eff : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1 - (d1 : ℚ))) * (wY : ℚ) +
        (d0Eff : ℚ) = (d1 : ℚ) * (W_F : ℚ) + (d0Eff : ℚ) * ((W_F : ℚ) - ((wY : ℚ) - 1) - (d1 : ℚ) * (wY : ℚ)) := by
      field_simp [hwYQ.ne']; ring
    linarith
  have ⟨hm0, hsurp_fn⟩ := checkT1Cert_sound c hchk ((W_F : ℚ) / (wY : ℚ)) hc_lo hc_hi Az hAz k hf1_sum hlc1_sum hres_sum
  have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
  have ⟨hsurp, hcap1, hcap2_fn⟩ := hsurp_fn hmpos
  have hlin := List.all_eq_true.mp certsT1_linear_caps c hc_mem
  have hmne : (c.m == 0) = false := beq_false_of_ne hm0
  simp only [hmne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at hlin
  refine ⟨c, hc_mem, hc_entry, hmpos, hlin.1.1, hlin.1.2, hc_lo, hc_hi, hsurp, hcap1,
    hlin.2.1.1, hlin.2.1.2, fun hlt13 => ?_⟩
  have hcLoD : 0 < c.cLoDen := by
    by_contra h0; unfold checkT1Cert at hchk
    simp [show c.cLoDen = 0 by omega] at hchk
  have hcLo_lt13 : c.cLoNum < 13 * c.cLoDen := by
    have h1 : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) < 13 := lt_of_le_of_lt hc_lo hlt13
    have hcLoDQ : (0 : ℚ) < (c.cLoDen : ℚ) := by exact_mod_cast hcLoD
    have h2 : (c.cLoNum : ℚ) < 13 * (c.cLoDen : ℚ) := (div_lt_iff₀ hcLoDQ).mp h1
    exact_mod_cast h2
  have hcap2_ok : c.hasCap2 = true ∧ c.cap2.c1Bkt * 1811 + c.cap2.c0Bkt ≤ T1_CAP_BOUND := by
    unfold checkT1Entry at hc_entry
    simp only [hmne, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at hc_entry
    rcases hc_entry.2.2 with hnot | hok
    · exact absurd hcLo_lt13 (decide_eq_false_iff_not.mp hnot)
    · exact hok
  refine ⟨hcap2_fn hcap2_ok.1, ?_⟩
  rcases hlin.2.2 with hf | hle
  · rw [hcap2_ok.1] at hf; cases hf
  · exact hle

end B6402PointSurplus
end ProximityPrize.SubmissionBinaryLower
