import ProximityPrize.SubmissionBinaryLower.Binary6402PointSurplusPart1
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

/-- Helper: in char 2, `f0 = expand 2 A0 + Y * f0.derivative` where `A0.coeff j = f0.coeff (2 * j)`. -/
lemma char2_biPoly_eq_expand2_add_X_deriv {F : Type*} [Field F] [CharP F 2] (f0 : BiPoly F) :
    let A0 : BiPoly F := ∑ j ∈ Finset.range (f0.natDegree / 2 + 1), Polynomial.monomial j (f0.coeff (2 * j))
    (∀ j, A0.coeff j = f0.coeff (2 * j)) ∧
    f0 = Polynomial.expand (Polynomial F) 2 A0 + Polynomial.X * f0.derivative := by
  intro A0
  have hA0_c : ∀ j, A0.coeff j = f0.coeff (2 * j) := by
    intro j; dsimp [A0]; rw [finset_sum_coeff]
    by_cases hj : j < f0.natDegree / 2 + 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd (Finset.mem_range.mpr hj) h
    · rw [Finset.sum_eq_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      intro l hl; have := Finset.mem_range.mp hl; simp [Polynomial.coeff_monomial, show l ≠ j by omega]
  refine ⟨hA0_c, ?_⟩
  rw [Polynomial.ext_iff]; intro n
  rw [Polynomial.coeff_add, Polynomial.coeff_expand (by norm_num : 0 < 2)]
  cases n with
  | zero => simp [hA0_c 0]
  | succ m =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, ← Nat.cast_succ]
      by_cases hev : 2 ∣ m + 1
      · rw [if_pos hev, hA0_c, show 2 * ((m + 1) / 2) = m + 1 by omega]
        have hm0 : ((m + 1 : ℕ) : Polynomial F) = 0 := by
          obtain ⟨q, hq⟩ := hev; rw [hq, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul]
        rw [hm0, mul_zero, add_zero]
      · rw [if_neg hev, zero_add]
        have hm1 : ((m + 1 : ℕ) : Polynomial F) = 1 := by
          have : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
          rw [this, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
            CharTwo.two_eq_zero, zero_mul, zero_add]
        rw [hm1, mul_one]

lemma biMultGE_mono {F : Type*} [Field F] {x0 y0 : F} {f : BiPoly F} {m1 m2 : ℕ}
    (hle : m1 ≤ m2) (h : biMultGE x0 y0 f m2) : biMultGE x0 y0 f m1 :=
  fun i j hij => h i j (lt_of_lt_of_le hij hle)

/-- **Tables 2, 3, 2A, and 2B Unified Single-Point Surplus Theorem (`t23_surplus_of_point`):** -/
theorem t23_surplus_of_point {W_F : ℕ} (f_coord : KerDIdx wY W_F 2 → Fld)
    (y : Idx → Fld) (k : Idx → ℕ)
    (hvan : ∀ i : Idx, twOrdGE (∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (y i) e.1) (k i))
    (P : Polynomial Fld) (hPdeg : P.natDegree ≤ wY)
    (Az : Finset Idx) (hAz : A ≤ Az.card)
    (hagree : ∀ i ∈ Az, P.eval (BinaryIRSProfile.domain i) = y i)
    (hf1_ne : (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0)
    (hf2_ne : (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2 ≠ 0)
    (hf1_P_ne : ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).eval P ≠ 0)
    (hf2_P_ne : ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2).eval P ≠ 0)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2)
    (hcop_all : ∀ p : Polynomial (RatFunc Fld),
      p ∣ ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
      p ∣ ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
      p ∣ ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
      IsUnit p) :
    ∃ (m s cHiNum cHiDen δNum δDen : ℕ) (w : CapWitness),
      0 < m ∧ m ≤ 3000 ∧ 2 ≤ s ∧ s ≤ 300 ∧ 0 < cHiDen ∧ 0 < δNum ∧ 0 < δDen ∧
      (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ) ∧
      (δNum : ℚ) / (δDen : ℚ) <
        vquotLbQ 2 m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 2 m s (k i)) / (N : ℚ) ∧
      checkCapWitness 2 m s cHiNum cHiDen δNum δDen 1 1 1 w = true ∧
      w.c1Bkt * 1811 + w.c0Bkt ≤ T3_CAP_BOUND := by
  set Fpoly : ContactPoly Fld := ∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1
  set f0 : BiPoly Fld := Fpoly.coeff 0
  set f1 : BiPoly Fld := Fpoly.coeff 1
  set f2 : BiPoly Fld := Fpoly.coeff 2
  set d0 : ℕ := f0.natDegree
  set d1 : ℕ := f1.natDegree
  set d2 : ℕ := f2.natDegree
  let ι : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  have hwYpos : 0 < wY := by norm_num [wY]
  have hwYQ : (0 : ℚ) < (wY : ℚ) := by exact_mod_cast hwYpos
  have hFmem : contactDeriv Fpoly = 0 ∧ Fpoly.natDegree ≤ 2 ∧ wdeg wY Fpoly ≤ W_F :=
    (mem_kerD_iff_exists_unique_coords (by norm_num [wY]) Fpoly).mpr ⟨f_coord, rfl, fun c' hc' => by
      funext ⟨⟨k', r', b', a'⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W_F 2 hwYpos k' r' b' a').mp he).1
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
  have ⟨_, hd2_ev, _, hd1_par, hf0_d, hd0_par⟩ := kerD2_pde_facts hFmem.1 hFmem.2.1
  have hWf0 : wdegBi wY f0 ≤ W_F := by simpa using wdegBi_le_of_wdeg_coeff hFmem.2.2 0
  have hWf1 : wdegBi wY f1 + (wY - 1) ≤ W_F := by
    simpa only [one_mul] using wdegBi_coeff_le_of_wdeg hFmem.2.2 1 hf1_ne
  have hWf2 : wdegBi wY f2 + 2 * (wY - 1) ≤ W_F := wdegBi_coeff_le_of_wdeg hFmem.2.2 2 hf2_ne
  have hWF_le_nat : 2 * W_F ≤ 51 * wY := by
    have : 2 * (W_F : ℚ) ≤ 51 * (wY : ℚ) := by
      have := (div_le_div_iff₀ hwYQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi; linarith
    exact_mod_cast this
  have hd_wdeg : ∀ h : BiPoly Fld, h ≠ 0 → h.natDegree * wY ≤ wdegBi wY h := fun h hne => by
    have hlc := Polynomial.leadingCoeff_ne_zero.mpr hne
    have hle := (wdegBi_le_iff wY (wdegBi wY h) h).mp le_rfl h.natDegree _ (Polynomial.leadingCoeff_ne_zero.mpr hlc)
    omega
  have hd1_wY : d1 * wY ≤ wdegBi wY f1 := hd_wdeg f1 hf1_ne
  have hd2_wY : d2 * wY ≤ wdegBi wY f2 := hd_wdeg f2 hf2_ne
  have hWf1' : wdegBi wY f1 + 1048574 ≤ W_F := hWf1
  have hWf2' : wdegBi wY f2 + 2 * 1048574 ≤ W_F := hWf2
  have hd1_wY' : d1 * 1048575 ≤ wdegBi wY f1 := hd1_wY
  have hd2_wY' : d2 * 1048575 ≤ wdegBi wY f2 := hd2_wY
  have hWF_le' : 2 * W_F ≤ 51 * 1048575 := hWF_le_nat
  change d2 % 2 = 0 at hd2_ev
  have hd2_le22 : d2 ≤ 22 := by omega
  have hd1_le24 : d1 ≤ 24 := by omega
  have hords_all : ∀ i : Idx,
      biMultGE (BinaryIRSProfile.domain i) (y i) f1 (2 * k i - 1) ∧
      biMultGE (BinaryIRSProfile.domain i) (y i) f2 (2 * k i - 2) := fun i => by
    have h := kerD2_local_ords hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)
    exact ⟨h.2.1, h.2.2.1⟩
  obtain ⟨qX, gPrim, h1, h2, hqX_ne, hgP_prim, hgP_ne, hh1_ne, hh2_ne,
    hf1_fac, hf2_fac, hrel_h, hgP_d, hg_d, hh2_d, hdg_eq, hdg_ev, hdvd_dX⟩ :=
    kerD2_gcd_decomp hFmem.1 hFmem.2.1 hf1_ne hf2_ne
  set g : BiPoly Fld := C qX * gPrim
  change f1 = g * h1 at hf1_fac
  change f2 = g * h2 at hf2_fac
  change f0.derivative = B6401ContactKerD.dXBi f1 at hf0_d
  set dg : ℕ := gPrim.natDegree
  have hg_ne : g ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hqX_ne) hgP_ne
  have hdg_g : g.natDegree = dg := hdg_eq
  have hd1_eq : d1 = dg + h1.natDegree := by
    dsimp [d1]; rw [hf1_fac, Polynomial.natDegree_mul hg_ne hh1_ne, hdg_g]
  have hd2_eq : d2 = dg + h2.natDegree := by
    dsimp [d2]; rw [hf2_fac, Polynomial.natDegree_mul hg_ne hh2_ne, hdg_g]
  -- Helper: sum of lc orders for any nonzero h : BiPoly Fld
  have hsum_lc : ∀ (h : BiPoly Fld) (hne : h ≠ 0) (W_h : ℕ) (hWh : wdegBi wY h ≤ W_h) (r : Idx → ℕ),
      (∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) h (r i)) →
      ∑ i : Idx, (r i - h.natDegree) ≤ W_h - h.natDegree * wY := by
    intro h hne W_h hWh r hr
    have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
        (X - C (BinaryIRSProfile.domain i)) ^ (r i - h.natDegree) ∣ h.leadingCoeff := fun i _ =>
      pow_dvd_leadingCoeff_of_biMultGE (BinaryIRSProfile.domain i) (y i) h h.natDegree (r i) rfl (hr i)
    have hdeg_lc : h.leadingCoeff.natDegree ≤ W_h - h.natDegree * wY := by
      have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hne)
      have hle := (wdegBi_le_iff wY W_h h).mp hWh h.natDegree _ hnz; omega
    exact (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ h.leadingCoeff
      (Polynomial.leadingCoeff_ne_zero.mpr hne) _ hdvd).trans hdeg_lc
  by_cases hdg0 : dg = 0
  · -- TABLE 2 (`dg = 0`, so `f1` and `f2` are coprime in `(RatFunc Fld)[Y]`)!
    have hlo_t2 : ((max (d2 + 2) (d1 + 1) * wY - 2 : ℕ) : ℚ) / (wY : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) := by
      apply div_le_div_of_nonneg_right _ hwYQ.le
      have h1 : (d2 + 2) * wY - 2 ≤ W_F := by change (d2 + 2) * 1048575 - 2 ≤ W_F; omega
      have h2 : (d1 + 1) * wY - 2 ≤ W_F := by change (d1 + 1) * 1048575 - 2 ≤ W_F; omega
      have h3 : max (d2 + 2) (d1 + 1) * wY - 2 ≤ W_F := by
        rcases le_total (d2 + 2) (d1 + 1) with hle | hle
        · rw [Nat.max_eq_right hle]; exact h2
        · rw [Nat.max_eq_left hle]; exact h1
      exact_mod_cast h3
    obtain ⟨c, hc_mem, hcd1, hcd2, hc_entry, hc_lo, hc_hi⟩ :=
      exists_t2Cert d1 d2 hd2_le22 hd2_ev hd1_le24 hd1_par ((W_F : ℚ) / (wY : ℚ)) hlo_t2 hWF_hi
    have hchk : checkT2Cert c = true := (Bool.and_eq_true _ _).mp hc_entry |>.1
    have hf1_sum : (∑ i ∈ Az, ((2 * k i - 1 : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 1) * (wY : ℚ) + 1 := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - (wY - 1)) f1 P
        (fun i => 2 * k i - 1) hPdeg (by omega) hf1_P_ne (fun i hi => by rw [hagree i hi]; exact (hords_all i).1)
      have hQ : ((∑ i ∈ Az, (2 * k i - 1) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one] at hQ
      have heq : ((W_F : ℚ) / (wY : ℚ) - 1) * (wY : ℚ) + 1 = (W_F : ℚ) - ((wY : ℚ) - 1) := by
        field_simp [hwYQ.ne']; ring
      linarith
    have hf2_sum : (∑ i ∈ Az, ((2 * k i - 2 : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 2) * (wY : ℚ) + 2 := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - 2 * (wY - 1)) f2 P
        (fun i => 2 * k i - 2) hPdeg (by omega) hf2_P_ne (fun i hi => by rw [hagree i hi]; exact (hords_all i).2)
      have hQ : ((∑ i ∈ Az, (2 * k i - 2) : ℕ) : ℚ) ≤ ((W_F - 2 * (wY - 1) : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_ofNat, Nat.cast_one] at hQ
      have heq : ((W_F : ℚ) / (wY : ℚ) - 2) * (wY : ℚ) + 2 = (W_F : ℚ) - 2 * ((wY : ℚ) - 1) := by
        field_simp [hwYQ.ne']; ring
      linarith
    have hlc1_sum : (∑ i : Idx, ((2 * k i - 1 - c.d1 : ℕ) : ℚ)) ≤
        ((W_F : ℚ) / (wY : ℚ) - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1 := by
      rw [hcd1]
      have hnat := hsum_lc f1 hf1_ne (W_F - (wY - 1)) (by omega) (fun i => 2 * k i - 1) (fun i => (hords_all i).1)
      have hQ : ((∑ i : Idx, (2 * k i - 1 - d1) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) - d1 * wY : ℕ) : ℚ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        Nat.cast_mul, Nat.cast_one] at hQ
      have heq : ((W_F : ℚ) / (wY : ℚ) - 1 - (d1 : ℚ)) * (wY : ℚ) + 1 =
          (W_F : ℚ) - ((wY : ℚ) - 1) - (d1 : ℚ) * (wY : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith
    have hlc2_sum : (∑ i : Idx, ((2 * k i - 2 - c.d2 : ℕ) : ℚ)) ≤
        ((W_F : ℚ) / (wY : ℚ) - 2 - (c.d2 : ℚ)) * (wY : ℚ) + 2 := by
      rw [hcd2]
      have hnat := hsum_lc f2 hf2_ne (W_F - 2 * (wY - 1)) (by omega) (fun i => 2 * k i - 2) (fun i => (hords_all i).2)
      have hQ : ((∑ i : Idx, (2 * k i - 2 - d2) : ℕ) : ℚ) ≤ ((W_F - 2 * (wY - 1) - d2 * wY : ℕ) : ℚ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_mul,
        Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hQ
      have heq : ((W_F : ℚ) / (wY : ℚ) - 2 - (d2 : ℚ)) * (wY : ℚ) + 2 =
          (W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (d2 : ℚ) * (wY : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith
    have hres_sum : 1 ≤ c.d1 ∧ 2 ≤ c.d2 →
        (∑ i : Idx, (resOrdExact c.d1 (2 * k i - 1) c.d2 (2 * k i - 2) : ℚ)) ≤
          ((c.d2 : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1) + (c.d1 : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 2) -
            (c.d1 : ℚ) * (c.d2 : ℚ)) * (wY : ℚ) + ((c.d2 : ℚ) + 2 * (c.d1 : ℚ)) := by
      rw [hcd1, hcd2]; intro _
      have hgU : IsUnit (g.map ι) := by
        have hgd0 : (g.map ι).natDegree = 0 := by
          rw [Polynomial.natDegree_map_eq_of_injective hι, hdg_g, hdg0]
        have hC := Polynomial.eq_C_of_natDegree_eq_zero hgd0
        have hc0 : (g.map ι).coeff 0 ≠ 0 := fun h0 =>
          ((Polynomial.map_ne_zero_iff hι).mpr hg_ne) (by rw [hC, h0, map_zero])
        rw [hC]; exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hc0)
      have hrel_f : IsRelPrime (f1.map ι) (f2.map ι) := by
        intro p hp1 hp2
        have h1 : p ∣ h1.map ι := by
          rw [hf1_fac, Polynomial.map_mul] at hp1
          rcases hgU with ⟨u, hu⟩; rw [← hu] at hp1
          rcases hp1 with ⟨w, hw⟩
          exact ⟨(↑u⁻¹ : Polynomial (RatFunc Fld)) * w, by
            have := congrArg ((↑u⁻¹ : Polynomial (RatFunc Fld)) * ·) hw
            simp only [← mul_assoc, Units.inv_mul, one_mul] at this
            rw [this]; ring⟩
        have h2 : p ∣ h2.map ι := by
          rw [hf2_fac, Polynomial.map_mul] at hp2
          rcases hgU with ⟨u, hu⟩; rw [← hu] at hp2
          rcases hp2 with ⟨w, hw⟩
          exact ⟨(↑u⁻¹ : Polynomial (RatFunc Fld)) * w, by
            have := congrArg ((↑u⁻¹ : Polynomial (RatFunc Fld)) * ·) hw
            simp only [← mul_assoc, Units.inv_mul, one_mul] at this
            rw [this]; ring⟩
        exact hrel_h h1 h2
      have hRne : Polynomial.resultant f1 f2 d1 d2 ≠ 0 :=
        resultant_ne_zero_of_coprime_ratFunc f1 f2 hf1_ne hf2_ne hrel_f
      have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
          (X - C (BinaryIRSProfile.domain i)) ^ resOrdExact d1 (2 * k i - 1) d2 (2 * k i - 2) ∣
            Polynomial.resultant f1 f2 d1 d2 := fun i _ =>
        X_sub_C_pow_dvd_resultant_of_biMultGE (BinaryIRSProfile.domain i) (y i) f1 f2 d1 (2 * k i - 1) d2 (2 * k i - 2)
          (hords_all i).1 (hords_all i).2 le_rfl le_rfl
      have hdeg_R := natDegree_resultant_le_wdegBi wY (W_F - (wY - 1)) (W_F - 2 * (wY - 1)) d1 d2 f1 f2
        (by omega) (by omega) le_rfl le_rfl
      have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ _ hRne _ hdvd).trans hdeg_R
      have hQ : ((∑ i : Idx, resOrdExact d1 (2 * k i - 1) d2 (2 * k i - 2) : ℕ) : ℚ) ≤
          ((d2 * (W_F - (wY - 1)) + d1 * (W_F - 2 * (wY - 1)) - d1 * d2 * wY : ℕ) : ℚ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sum] at hQ
      have hsub_ge : d1 * d2 * wY ≤ d2 * (W_F - (wY - 1)) + d1 * (W_F - 2 * (wY - 1)) :=
        calc d1 * d2 * wY = d2 * (d1 * wY) := by ring
          _ ≤ d2 * (W_F - (wY - 1)) := Nat.mul_le_mul_left d2 (by omega)
          _ ≤ _ := Nat.le_add_right _ _
      rw [Nat.cast_sub hsub_ge, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub (by omega : wY - 1 ≤ W_F), Nat.cast_sub (by omega : 2 * (wY - 1) ≤ W_F), Nat.cast_mul,
        Nat.cast_sub (by omega : 1 ≤ wY), Nat.cast_one, show ((2 : ℕ) : ℚ) = 2 by norm_num] at hQ
      have heq : ((d2 : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1) + (d1 : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 2) -
          (d1 : ℚ) * (d2 : ℚ)) * (wY : ℚ) + ((d2 : ℚ) + 2 * (d1 : ℚ)) =
          (d2 : ℚ) * ((W_F : ℚ) - ((wY : ℚ) - 1)) + (d1 : ℚ) * ((W_F : ℚ) - 2 * ((wY : ℚ) - 1)) -
            (d1 : ℚ) * (d2 : ℚ) * (wY : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith [hQ, heq]
    have ⟨hm0, hsurp_fn⟩ := checkT2Cert_sound c hchk ((W_F : ℚ) / (wY : ℚ)) hc_lo hc_hi Az hAz k
      hf1_sum hf2_sum hlc1_sum hlc2_sum hres_sum
    have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
    have ⟨hsurp, hcap⟩ := hsurp_fn hmpos
    have hms := List.all_eq_true.mp certsT2_ms_bound c hc_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
    have hpars : 2 ≤ c.s ∧ 0 < c.cHiDen ∧ 0 < c.δNum ∧ 0 < c.δDen := by
      unfold checkT2Cert at hchk
      have hmne : (c.m != 0) = true := bne_iff_ne.mpr hm0
      by_contra hbad
      push Not at hbad
      have hfail : (c.cLoDen == 0 || c.cHiDen == 0) = true ∨
          (c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0)) = true := by
        rcases lt_or_ge c.s 2 with hs | hs
        · exact Or.inr (by simp [hmne, hs])
        · rcases Nat.eq_zero_or_pos c.cHiDen with hd | hd
          · exact Or.inl (by simp [hd])
          · rcases Nat.eq_zero_or_pos c.δNum with hdn | hdn
            · exact Or.inr (by simp [hmne, hdn])
            · rcases Nat.eq_zero_or_pos c.δDen with hdd | hdd
              · exact Or.inr (by simp [hmne, hdd])
              · exfalso; have := hbad hs hd hdn; omega
      rcases hfail with hf | hf
      · simp [hf] at hchk
      · split_ifs at hchk <;> simp_all
    have hcap_bd : c.cap.c1Bkt * 1811 + c.cap.c0Bkt ≤ T3_CAP_BOUND := by
      unfold checkT2Entry at hc_entry
      have hmne : (c.m == 0) = false := beq_false_of_ne hm0
      simp only [hmne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc_entry
      have h1 : T2_CAP_BOUND ≤ T3_CAP_BOUND := by norm_num [T2_CAP_BOUND, T3_CAP_BOUND]
      omega
    exact ⟨c.m, c.s, c.cHiNum, c.cHiDen, c.δNum, c.δDen, c.cap, hmpos, hms.1, hpars.1, hms.2,
      hpars.2.1, hpars.2.2.1, hpars.2.2.2, hc_hi, hsurp, hcap, hcap_bd⟩
  · -- TABLE 3 (`2 ≤ dg`)!
    have hdg_lo : 2 ≤ dg := by omega
    have hf0_ne : f0 ≠ 0 := by
      intro h0
      have hg_nu : ¬ IsUnit (g.map ι) := by
        intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu
        rw [Polynomial.natDegree_map_eq_of_injective hι, hdg_g] at this; omega
      exact hg_nu (hcop_all (g.map ι) (by rw [h0, Polynomial.map_zero]; exact dvd_zero _)
        ⟨h1.map ι, by rw [hf1_fac, Polynomial.map_mul]⟩
        ⟨h2.map ι, by rw [hf2_fac, Polynomial.map_mul]⟩)
    set dStar : ℕ := max d0 (max (d2 + 2) (d1 + 1))
    have hdStar_spec : dStar = max (d2 + 2) (d1 + 1) ∨
        (max (d2 + 2) (d1 + 1) < dStar ∧ dStar ≤ 24 ∧ dStar % 2 = 0) := by
      by_cases hle : d0 ≤ max (d2 + 2) (d1 + 1)
      · exact Or.inl (Nat.max_eq_right hle)
      · right
        have heq : dStar = d0 := Nat.max_eq_left (by omega)
        change d0 ≤ d1 + 1 ∨ d0 % 2 = 0 at hd0_par
        have hd0_ev : d0 % 2 = 0 := hd0_par.resolve_left (by omega)
        have hd0_wY : d0 * 1048575 ≤ W_F := (hd_wdeg f0 hf0_ne).trans hWf0
        exact ⟨by omega, by omega, by omega⟩
    have hlo_t3 : ((dStar * wY - 2 : ℕ) : ℚ) / (wY : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) := by
      apply div_le_div_of_nonneg_right _ hwYQ.le
      have h1 : (d2 + 2) * wY - 2 ≤ W_F := by change (d2 + 2) * 1048575 - 2 ≤ W_F; omega
      have h2 : (d1 + 1) * wY - 2 ≤ W_F := by change (d1 + 1) * 1048575 - 2 ≤ W_F; omega
      have h0 : d0 * wY - 2 ≤ W_F := by
        have h := (hd_wdeg f0 hf0_ne).trans hWf0; change d0 * wY ≤ W_F at h; omega
      have h3 : dStar * wY - 2 ≤ W_F := by
        rcases le_total d0 (max (d2 + 2) (d1 + 1)) with hle | hle
        · rw [show dStar = max (d2 + 2) (d1 + 1) from Nat.max_eq_right hle]
          rcases le_total (d2 + 2) (d1 + 1) with h' | h'
          · rw [Nat.max_eq_right h']; exact h2
          · rw [Nat.max_eq_left h']; exact h1
        · rw [show dStar = d0 from Nat.max_eq_left hle]; exact h0
      exact_mod_cast h3
    -- Shared T3 weight & order facts!
    set W_g : ℕ := wdegBi wY g
    set cgVal : ℚ := (W_g : ℚ) / (wY : ℚ)
    have hg_P_ne : g.eval P ≠ 0 := by
      intro h0; apply hf1_P_ne; rw [hf1_fac, Polynomial.eval_mul, h0, zero_mul]
    have hh1_P_ne : h1.eval P ≠ 0 := by
      intro h0; apply hf1_P_ne; rw [hf1_fac, Polynomial.eval_mul, h0, mul_zero]
    have hh2_P_ne : h2.eval P ≠ 0 := by
      intro h0; apply hf2_P_ne; rw [hf2_fac, Polynomial.eval_mul, h0, mul_zero]
    have hWf1_eq : wdegBi wY f1 = W_g + wdegBi wY h1 := by
      rw [hf1_fac]; exact wdegBiDom_mul wY hg_ne hh1_ne
    have hWf2_eq : wdegBi wY f2 = W_g + wdegBi wY h2 := by
      rw [hf2_fac]; exact wdegBiDom_mul wY hg_ne hh2_ne
    have hWg_lo : dg * wY ≤ W_g := by rw [← hdg_g]; exact hd_wdeg g hg_ne
    have hWh1_lo : (d1 - dg) * wY ≤ wdegBi wY h1 := by
      rw [show d1 - dg = h1.natDegree by omega]; exact hd_wdeg h1 hh1_ne
    have hWh2_lo : (d2 - dg) * wY ≤ wdegBi wY h2 := by
      rw [show d2 - dg = h2.natDegree by omega]; exact hd_wdeg h2 hh2_ne
    have hWh1_lo' : (d1 - dg) * 1048575 ≤ wdegBi wY h1 := hWh1_lo
    have hWh2_lo' : (d2 - dg) * 1048575 ≤ wdegBi wY h2 := hWh2_lo
    have hcg_lo : (dg : ℚ) ≤ cgVal := by
      dsimp [cgVal]; rw [le_div_iff₀ hwYQ]; exact_mod_cast hWg_lo
    have hcg_hi : cgVal ≤ max (dg : ℚ) ((W_F : ℚ) / (wY : ℚ) -
        ((max (2 + (d2 - dg)) (1 + (d1 - dg)) : ℕ) : ℚ) + 2 / (wY : ℚ)) := by
      refine le_max_of_le_right ?_
      have h1 : W_g + (2 + (d2 - dg)) * wY ≤ W_F + 2 := by
        change W_g + (2 + (d2 - dg)) * 1048575 ≤ W_F + 2; omega
      have h2 : W_g + (1 + (d1 - dg)) * wY ≤ W_F + 2 := by
        change W_g + (1 + (d1 - dg)) * 1048575 ≤ W_F + 2; omega
      have h3 : W_g + max (2 + (d2 - dg)) (1 + (d1 - dg)) * wY ≤ W_F + 2 := by
        rcases le_total (2 + (d2 - dg)) (1 + (d1 - dg)) with hle | hle
        · rw [Nat.max_eq_right hle]; exact h2
        · rw [Nat.max_eq_left hle]; exact h1
      have hQ : (W_g : ℚ) + ((max (2 + (d2 - dg)) (1 + (d1 - dg)) : ℕ) : ℚ) * (wY : ℚ) ≤ (W_F : ℚ) + 2 := by
        exact_mod_cast h3
      dsimp [cgVal]
      have heq : (W_F : ℚ) / (wY : ℚ) - ((max (2 + (d2 - dg)) (1 + (d1 - dg)) : ℕ) : ℚ) + 2 / (wY : ℚ) =
          ((W_F : ℚ) + 2 - ((max (2 + (d2 - dg)) (1 + (d1 - dg)) : ℕ) : ℚ) * (wY : ℚ)) / (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      rw [heq]; exact div_le_div_of_nonneg_right (by linarith) hwYQ.le
    set rr : Idx → ℕ := fun i => min (2 * k i) (biMult (BinaryIRSProfile.domain i) (y i) g)
    have hrr_le : ∀ i, rr i ≤ 2 * k i := fun i => Nat.min_le_left _ _
    have hbm_g : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) g (rr i) := fun i =>
      biMultGE_mono (Nat.min_le_right _ _) (biMultGE_biMult _ _ g)
    have hbm_h1 : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) h1 (2 * k i - 1 - rr i) := fun i => by
      have hmul := biMult_mul (BinaryIRSProfile.domain i) (y i) hg_ne hh1_ne
      rw [← hf1_fac] at hmul
      have hge := le_biMult_of_biMultGE (BinaryIRSProfile.domain i) (y i) hf1_ne (hords_all i).1
      exact biMultGE_mono (by dsimp [rr]; omega) (biMultGE_biMult _ _ h1)
    have hbm_h2 : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) h2 (2 * k i - 2 - rr i) := fun i => by
      have hmul := biMult_mul (BinaryIRSProfile.domain i) (y i) hg_ne hh2_ne
      rw [← hf2_fac] at hmul
      have hge := le_biMult_of_biMultGE (BinaryIRSProfile.domain i) (y i) hf2_ne (hords_all i).2
      exact biMultGE_mono (by dsimp [rr]; omega) (biMultGE_biMult _ _ h2)
    have hg_sum : (∑ i ∈ Az, (rr i : ℚ)) ≤ cgVal * (wY : ℚ) := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY W_g g P rr hPdeg le_rfl hg_P_ne
        (fun i hi => by rw [hagree i hi]; exact hbm_g i)
      have hQ : ((∑ i ∈ Az, rr i : ℕ) : ℚ) ≤ (W_g : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum] at hQ; dsimp [cgVal]; rw [div_mul_cancel₀ _ hwYQ.ne']; exact hQ
    have hh1_sum : (∑ i ∈ Az, ((2 * k i - 1 - rr i : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 1 - cgVal) * (wY : ℚ) + 1 := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - (wY - 1) - W_g) h1 P
        (fun i => 2 * k i - 1 - rr i) hPdeg (by omega) hh1_P_ne
        (fun i hi => by rw [hagree i hi]; exact hbm_h1 i)
      have hQ : ((∑ i ∈ Az, (2 * k i - 1 - rr i) : ℕ) : ℚ) ≤ ((W_F - (wY - 1) - W_g : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one] at hQ
      dsimp [cgVal]
      have heq : ((W_F : ℚ) / (wY : ℚ) - 1 - (W_g : ℚ) / (wY : ℚ)) * (wY : ℚ) + 1 =
          (W_F : ℚ) - ((wY : ℚ) - 1) - (W_g : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith
    have hh2_sum : (∑ i ∈ Az, ((2 * k i - 2 - rr i : ℕ) : ℚ)) ≤ ((W_F : ℚ) / (wY : ℚ) - 2 - cgVal) * (wY : ℚ) + 2 := by
      have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY (W_F - 2 * (wY - 1) - W_g) h2 P
        (fun i => 2 * k i - 2 - rr i) hPdeg (by omega) hh2_P_ne
        (fun i hi => by rw [hagree i hi]; exact hbm_h2 i)
      have hQ : ((∑ i ∈ Az, (2 * k i - 2 - rr i) : ℕ) : ℚ) ≤ ((W_F - 2 * (wY - 1) - W_g : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_mul,
        Nat.cast_sub (by omega), Nat.cast_ofNat, Nat.cast_one] at hQ
      dsimp [cgVal]
      have heq : ((W_F : ℚ) / (wY : ℚ) - 2 - (W_g : ℚ) / (wY : ℚ)) * (wY : ℚ) + 2 =
          (W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (W_g : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith
    have hlcg_sum : (∑ i : Idx, ((rr i - dg : ℕ) : ℚ)) ≤ (cgVal - (dg : ℚ)) * (wY : ℚ) := by
      have hnat := hsum_lc g hg_ne W_g le_rfl rr hbm_g
      rw [hdg_g] at hnat
      have hQ : ((∑ i : Idx, (rr i - dg) : ℕ) : ℚ) ≤ ((W_g - dg * wY : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub hWg_lo, Nat.cast_mul] at hQ
      dsimp [cgVal]; have heq : ((W_g : ℚ) / (wY : ℚ) - (dg : ℚ)) * (wY : ℚ) = (W_g : ℚ) - (dg : ℚ) * (wY : ℚ) := by
        field_simp [hwYQ.ne']
      linarith
    have hlch1_sum : (∑ i : Idx, ((2 * k i - 1 - rr i - (d1 - dg) : ℕ) : ℚ)) ≤
        ((W_F : ℚ) / (wY : ℚ) - 1 - cgVal - ((d1 - dg : ℕ) : ℚ)) * (wY : ℚ) + 1 := by
      have hnat := hsum_lc h1 hh1_ne (W_F - (wY - 1) - W_g) (by omega) (fun i => 2 * k i - 1 - rr i) hbm_h1
      rw [show h1.natDegree = d1 - dg by omega] at hnat
      have hQ : ((∑ i : Idx, (2 * k i - 1 - rr i - (d1 - dg)) : ℕ) : ℚ) ≤
          ((W_F - (wY - 1) - W_g - (d1 - dg) * wY : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_one] at hQ
      dsimp [cgVal]
      have heq : ((W_F : ℚ) / (wY : ℚ) - 1 - (W_g : ℚ) / (wY : ℚ) - ((d1 - dg : ℕ) : ℚ)) * (wY : ℚ) + 1 =
          (W_F : ℚ) - ((wY : ℚ) - 1) - (W_g : ℚ) - ((d1 - dg : ℕ) : ℚ) * (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      linarith
    have hlch2_sum : (∑ i : Idx, ((2 * k i - 2 - rr i - (d2 - dg) : ℕ) : ℚ)) ≤
        ((W_F : ℚ) / (wY : ℚ) - 2 - cgVal - ((d2 - dg : ℕ) : ℚ)) * (wY : ℚ) + 2 := by
      have hnat := hsum_lc h2 hh2_ne (W_F - 2 * (wY - 1) - W_g) (by omega) (fun i => 2 * k i - 2 - rr i) hbm_h2
      rw [show h2.natDegree = d2 - dg by omega] at hnat
      have hQ : ((∑ i : Idx, (2 * k i - 2 - rr i - (d2 - dg)) : ℕ) : ℚ) ≤
          ((W_F - 2 * (wY - 1) - W_g - (d2 - dg) * wY : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hQ
      dsimp [cgVal]
      have heq : ((W_F : ℚ) / (wY : ℚ) - 2 - (W_g : ℚ) / (wY : ℚ) - ((d2 - dg : ℕ) : ℚ)) * (wY : ℚ) + 2 =
          (W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (W_g : ℚ) - ((d2 - dg : ℕ) : ℚ) * (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      linarith
    have hrh_sum : 1 ≤ d1 - dg ∧ 2 ≤ d2 - dg →
        (∑ i : Idx, (resOrdExact (d1 - dg) (2 * k i - 1 - rr i) (d2 - dg) (2 * k i - 2 - rr i) : ℚ)) ≤
          (((d2 - dg : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1 - cgVal) +
            ((d1 - dg : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 2 - cgVal) -
            ((d1 - dg : ℕ) : ℚ) * ((d2 - dg : ℕ) : ℚ)) * (wY : ℚ) +
            (((d2 - dg : ℕ) : ℚ) + 2 * ((d1 - dg : ℕ) : ℚ)) := by
      intro _
      have hRne : Polynomial.resultant h1 h2 (d1 - dg) (d2 - dg) ≠ 0 := by
        rw [show d1 - dg = h1.natDegree by omega, show d2 - dg = h2.natDegree by omega]
        exact resultant_ne_zero_of_coprime_ratFunc h1 h2 hh1_ne hh2_ne hrel_h
      have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
          (X - C (BinaryIRSProfile.domain i)) ^
            resOrdExact (d1 - dg) (2 * k i - 1 - rr i) (d2 - dg) (2 * k i - 2 - rr i) ∣
            Polynomial.resultant h1 h2 (d1 - dg) (d2 - dg) := fun i _ =>
        X_sub_C_pow_dvd_resultant_of_biMultGE (BinaryIRSProfile.domain i) (y i) h1 h2
          (d1 - dg) (2 * k i - 1 - rr i) (d2 - dg) (2 * k i - 2 - rr i)
          (hbm_h1 i) (hbm_h2 i) (by omega) (by omega)
      have hdeg_R := natDegree_resultant_le_wdegBi wY (W_F - (wY - 1) - W_g) (W_F - 2 * (wY - 1) - W_g)
        (d1 - dg) (d2 - dg) h1 h2 (by omega) (by omega) (by omega) (by omega)
      have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ _ hRne _ hdvd).trans hdeg_R
      have hQ : ((∑ i : Idx, resOrdExact (d1 - dg) (2 * k i - 1 - rr i) (d2 - dg) (2 * k i - 2 - rr i) : ℕ) : ℚ) ≤
          (((d2 - dg) * (W_F - (wY - 1) - W_g) + (d1 - dg) * (W_F - 2 * (wY - 1) - W_g) -
            (d1 - dg) * (d2 - dg) * wY : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_sum] at hQ
      have hsub_ge : (d1 - dg) * (d2 - dg) * wY ≤
          (d2 - dg) * (W_F - (wY - 1) - W_g) + (d1 - dg) * (W_F - 2 * (wY - 1) - W_g) :=
        calc (d1 - dg) * (d2 - dg) * wY = (d2 - dg) * ((d1 - dg) * wY) := by ring
          _ ≤ (d2 - dg) * (W_F - (wY - 1) - W_g) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ _ := Nat.le_add_right _ _
      rw [Nat.cast_sub hsub_ge, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub (by omega : W_g ≤ W_F - (wY - 1)), Nat.cast_sub (by omega : wY - 1 ≤ W_F),
        Nat.cast_sub (by omega : W_g ≤ W_F - 2 * (wY - 1)), Nat.cast_sub (by omega : 2 * (wY - 1) ≤ W_F),
        Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ wY), Nat.cast_one, show ((2 : ℕ) : ℚ) = 2 by norm_num] at hQ
      dsimp [cgVal]
      have heq : (((d2 - dg : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 1 - (W_g : ℚ) / (wY : ℚ)) +
          ((d1 - dg : ℕ) : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 2 - (W_g : ℚ) / (wY : ℚ)) -
          ((d1 - dg : ℕ) : ℚ) * ((d2 - dg : ℕ) : ℚ)) * (wY : ℚ) +
          (((d2 - dg : ℕ) : ℚ) + 2 * ((d1 - dg : ℕ) : ℚ)) =
          ((d2 - dg : ℕ) : ℚ) * ((W_F : ℚ) - ((wY : ℚ) - 1) - (W_g : ℚ)) +
          ((d1 - dg : ℕ) : ℚ) * ((W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (W_g : ℚ)) -
          ((d1 - dg : ℕ) : ℚ) * ((d2 - dg : ℕ) : ℚ) * (wY : ℚ) := by field_simp [hwYQ.ne']; ring
      linarith [hQ, heq]
    -- Shared helper for mode ∈ {0, 1} hrf0 bound!
    have hrf0_std : ∀ (mode : ℕ), mode = 0 ∨ mode = 1 →
        (∑ i : Idx, (t3Vrf0Ord mode dg dStar (k i) (rr i) : ℚ)) ≤
          ((dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - (dStar : ℚ)) + (dStar : ℚ) * cgVal) * (wY : ℚ) := by
      intro mode hmode
      have hrel_f0g : IsRelPrime (f0.map ι) (g.map ι) := fun p hp0 hpg =>
        hcop_all p hp0 (hpg.trans ⟨h1.map ι, by rw [hf1_fac, Polynomial.map_mul]⟩)
          (hpg.trans ⟨h2.map ι, by rw [hf2_fac, Polynomial.map_mul]⟩)
      set R : Polynomial Fld := g.leadingCoeff ^ (dStar - d0) * Polynomial.resultant f0 g d0 dg
      have hRne : R ≠ 0 := mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hg_ne))
        (by rw [← hdg_g]; exact resultant_ne_zero_of_coprime_ratFunc f0 g hf0_ne hg_ne hrel_f0g)
      have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
          (X - C (BinaryIRSProfile.domain i)) ^ t3Vrf0Ord mode dg dStar (k i) (rr i) ∣ R := by
        intro i _
        have hmono := t3Vrf0Ord_mono_std mode dg dStar (k i) (by omega)
          (Nat.min_le_right (2 * k i) (biMult (BinaryIRSProfile.domain i) (y i) g))
        refine (pow_dvd_pow _ hmono).trans ?_
        have hg_ev : ∀ j, j % 2 = 1 → g.coeff j = 0 := (deriv_eq_zero_iff_even_coeffs g).mp hg_d
        have ⟨hvk, hvp⟩ := kerD2_resY_f0_g_ord hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)
          g hg_ne hg_ev (by change g ∣ f1; rw [hf1_fac]; exact dvd_mul_right _ _)
          (by change g ∣ f2; rw [hf2_fac]; exact dvd_mul_right _ _)
          dStar le_rfl
        rw [hdg_g] at hvk hvp
        by_cases hk0 : k i = 0
        · simp [t3Vrf0Ord, hk0]
        · have hk0b : (k i == 0) = false := beq_false_of_ne hk0
          rcases hmode with rfl | rfl
          · unfold t3Vrf0Ord; simp only [hk0b, Bool.false_eq_true, ↓reduceIte,
              show (0 == 3) = false by decide, show (0 == 1 || 0 == 2) = false by decide, resOrdWeighted2Fast_eq]
            exact hvk
          · unfold t3Vrf0Ord; simp only [hk0b, Bool.false_eq_true, ↓reduceIte,
              show (1 == 3) = false by decide, show (1 == 1 || 1 == 2) = true by decide, resOrdWeighted2Fast_eq]
            rcases le_total (resOrdWeighted dStar (4 * k i + 4) (dg / 2) (biMult (BinaryIRSProfile.domain i) (y i) g) 2 - 2 * dg)
                (((List.range (dStar + 1)).map (fun d0' =>
                  resOrdExact d0' (2 * k i - 2) dg (biMult (BinaryIRSProfile.domain i) (y i) g) +
                    (dStar - d0') * (biMult (BinaryIRSProfile.domain i) (y i) g - dg))).foldl Nat.min
                      (resOrdExact 0 (2 * k i - 2) dg (biMult (BinaryIRSProfile.domain i) (y i) g) +
                        dStar * (biMult (BinaryIRSProfile.domain i) (y i) g - dg))) with hle | hle
            · rw [Nat.max_eq_right hle]
              refine (pow_dvd_pow _ (foldl_map_min_le_mem _ (List.range (dStar + 1)) _ d0
                (List.mem_range.mpr (by omega)))).trans hvp
            · rw [Nat.max_eq_left hle]; exact hvk
      have hdeg_lc : g.leadingCoeff.natDegree ≤ W_g - dg * wY := by
        have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg_ne)
        have hle := (wdegBi_le_iff wY W_g g).mp le_rfl dg _ (by rwa [← hdg_g]); omega
      have hdeg_res := natDegree_resultant_le_wdegBi wY W_F W_g d0 dg f0 g hWf0 le_rfl le_rfl (le_of_eq hdg_g)
      have hdeg_R : R.natDegree + dg * dStar * wY ≤ dg * W_F + dStar * W_g := by
        have h1 : R.natDegree ≤ (dStar - d0) * g.leadingCoeff.natDegree + (Polynomial.resultant f0 g d0 dg).natDegree :=
          Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_pow_le _)
        have h2 : (dStar - d0) * g.leadingCoeff.natDegree ≤ (dStar - d0) * (W_g - dg * wY) :=
          Nat.mul_le_mul_left _ hdeg_lc
        have hd0_le : d0 ≤ dStar := le_max_left _ _
        have hmul_le : d0 * dg * wY ≤ d0 * W_g := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left d0 hWg_lo
        have hsub1 : (dStar - d0) * (W_g - dg * wY) + (dStar - d0) * (dg * wY) = (dStar - d0) * W_g := by
          rw [← mul_add, Nat.sub_add_cancel hWg_lo]
        have hsum_d : (dStar - d0) * W_g + d0 * W_g = dStar * W_g := by
          rw [← add_mul, Nat.sub_add_cancel hd0_le]
        have hsum_w : (dStar - d0) * (dg * wY) + d0 * dg * wY = dg * dStar * wY := by
          rw [mul_assoc d0, ← add_mul, Nat.sub_add_cancel hd0_le]; ring
        omega
      have hnat := sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ R hRne _ hdvd
      have hQ : ((∑ i : Idx, t3Vrf0Ord mode dg dStar (k i) (rr i) : ℕ) : ℚ) + (dg : ℚ) * (dStar : ℚ) * (wY : ℚ) ≤
          (dg : ℚ) * (W_F : ℚ) + (dStar : ℚ) * (W_g : ℚ) := by
        have htot : (∑ i : Idx, t3Vrf0Ord mode dg dStar (k i) (rr i)) + dg * dStar * wY ≤ dg * W_F + dStar * W_g := by omega
        have htotQ : (((∑ i : Idx, t3Vrf0Ord mode dg dStar (k i) (rr i)) + dg * dStar * wY : ℕ) : ℚ) ≤
            ((dg * W_F + dStar * W_g : ℕ) : ℚ) := by exact_mod_cast htot
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul] at htotQ
        exact htotQ
      rw [Nat.cast_sum] at hQ
      dsimp [cgVal]
      have heq : ((dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - (dStar : ℚ)) + (dStar : ℚ) * ((W_g : ℚ) / (wY : ℚ))) * (wY : ℚ) =
          (dg : ℚ) * (W_F : ℚ) + (dStar : ℚ) * (W_g : ℚ) - (dg : ℚ) * (dStar : ℚ) * (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      linarith
    -- Shared helper for mode = 3 (Subcase 2A, dStar = 11, dStarEff = 10)!
    have hrf0_2A : (∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) →
        dStar = 11 →
        (∑ i : Idx, (t3Vrf0Ord 3 dg 10 (k i) (rr i) : ℚ)) ≤
          ((dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - (10 : ℚ)) + (10 : ℚ) * cgVal) * (wY : ℚ) := by
      intro hgP_X2Y2 hdStar11
      set A0 : BiPoly Fld := ∑ j ∈ Finset.range (f0.natDegree / 2 + 1), Polynomial.monomial j (f0.coeff (2 * j))
      have ⟨hA0_c, hf0_sp⟩ := char2_biPoly_eq_expand2_add_X_deriv f0
      set A0exp : BiPoly Fld := Polynomial.expand (Polynomial Fld) 2 A0
      have hA0_deg : 2 * A0.natDegree ≤ 10 := by
        have hle : A0.natDegree ≤ f0.natDegree / 2 := by
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
          rw [hA0_c]; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have hd0_le11 : d0 ≤ 11 := by have : d0 ≤ dStar := le_max_left _ _; omega
        omega
      have hdA_eq : A0exp.natDegree = 2 * A0.natDegree := by
        dsimp [A0exp]; rw [Polynomial.natDegree_expand, mul_comm]
      have hWA0 : wdegBi wY A0exp ≤ W_F := by
        rw [wdegBi_le_iff]; intro j i hnz
        dsimp [A0exp] at hnz
        rw [Polynomial.coeff_expand (by norm_num : 0 < 2)] at hnz
        split_ifs at hnz with hj
        · rw [hA0_c, show 2 * (j / 2) = j by omega] at hnz
          exact (wdegBi_le_iff wY W_F f0).mp hWf0 j i hnz
        · simp at hnz
      have hgP_dvd_dX : gPrim ∣ f0.derivative := by
        rw [hf0_d, hf1_fac]; dsimp only [g]
        rw [mul_assoc, B6401ContactKerD.dXBi_mul]
        have hdX_gP : B6401ContactKerD.dXBi gPrim = 0 :=
          (dXBi_eq_zero_iff_even_X gPrim).mpr fun j i hi => by
            by_contra hnz; have := hgP_X2Y2 j i hnz; omega
        rw [B6401ContactKerD.dXBi_mul, hdX_gP, zero_mul, zero_add]
        exact dvd_add ⟨B6401ContactKerD.dXBi (C qX) * h1, by ring⟩ ⟨C qX * B6401ContactKerD.dXBi h1, by ring⟩
      have hrel_A0g : IsRelPrime (A0exp.map ι) (g.map ι) := by
        intro p hpA hpg
        have hqU : IsUnit (C (ι qX) : Polynomial (RatFunc Fld)) :=
          Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (fun h => hqX_ne (hι (h.trans (map_zero ι).symm))))
        have hpgP : p ∣ gPrim.map ι := by
          dsimp [g] at hpg; rw [Polynomial.map_mul, Polynomial.map_C] at hpg
          rcases hqU with ⟨u, hu⟩; rw [← hu] at hpg
          rcases hpg with ⟨w, hw⟩
          exact ⟨(↑u⁻¹ : Polynomial (RatFunc Fld)) * w, by
            have := congrArg ((↑u⁻¹ : Polynomial (RatFunc Fld)) * ·) hw
            simp only [← mul_assoc, Units.inv_mul, one_mul] at this
            rw [this]; ring⟩
        have hp_f0 : p ∣ f0.map ι := by
          rw [hf0_sp, Polynomial.map_add, Polynomial.map_mul]
          refine dvd_add hpA (dvd_mul_of_dvd_right (hpgP.trans ?_) _)
          rcases hgP_dvd_dX with ⟨w, hw⟩; exact ⟨w.map ι, by rw [hw, Polynomial.map_mul]⟩
        exact hcop_all p hp_f0
          (hpg.trans ⟨h1.map ι, by rw [hf1_fac, Polynomial.map_mul]⟩)
          (hpg.trans ⟨h2.map ι, by rw [hf2_fac, Polynomial.map_mul]⟩)
      have hA0_ne : A0exp ≠ 0 := by
        intro h0
        have hg_nu : ¬ IsUnit (g.map ι) := by
          intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu
          rw [Polynomial.natDegree_map_eq_of_injective hι, hdg_g] at this; omega
        exact hg_nu (hrel_A0g (by rw [h0, Polynomial.map_zero]; exact dvd_zero _) dvd_rfl)
      set R : Polynomial Fld := g.leadingCoeff ^ (10 - A0exp.natDegree) * Polynomial.resultant A0exp g A0exp.natDegree dg
      have hRne : R ≠ 0 := mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hg_ne))
        (by rw [← hdg_g]; exact resultant_ne_zero_of_coprime_ratFunc A0exp g hA0_ne hg_ne hrel_A0g)
      have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
          (X - C (BinaryIRSProfile.domain i)) ^ t3Vrf0Ord 3 dg 10 (k i) (rr i) ∣ R := by
        intro i _
        refine (pow_dvd_pow _ (t3Vrf0Ord_mode3_le_min_two_mul dg 10 (k i) _)).trans ?_
        have hord := kerD2_resY_f0_g_2A_ord hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)
          qX gPrim A0 hqX_ne hgP_ne hgP_X2Y2 hA0_c
          (by change gPrim ∣ f1; rw [hf1_fac]; dsimp only [g]; exact ⟨C qX * h1, by ring⟩)
          (by change gPrim ∣ f2; rw [hf2_fac]; dsimp only [g]; exact ⟨C qX * h2, by ring⟩)
          10 (by decide) hA0_deg
          (by change d1 ≤ 10; have : d1 + 1 ≤ dStar := le_trans (le_max_right _ _) (le_max_right _ _); omega)
          (by change d2 + 2 ≤ 10; have : d2 + 2 ≤ dStar := le_trans (le_max_left _ _) (le_max_right _ _); omega)
        simpa only [g, dg, A0exp, hdg_g] using hord
      have hdeg_lc : g.leadingCoeff.natDegree ≤ W_g - dg * wY := by
        have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg_ne)
        have hle := (wdegBi_le_iff wY W_g g).mp le_rfl dg _ (by rwa [← hdg_g]); omega
      have hdeg_res := natDegree_resultant_le_wdegBi wY W_F W_g A0exp.natDegree dg A0exp g hWA0 le_rfl le_rfl (le_of_eq hdg_g)
      have hdeg_R : R.natDegree + dg * 10 * wY ≤ dg * W_F + 10 * W_g := by
        have h1 : R.natDegree ≤ (10 - A0exp.natDegree) * g.leadingCoeff.natDegree +
            (Polynomial.resultant A0exp g A0exp.natDegree dg).natDegree :=
          Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_pow_le _)
        have h2 : (10 - A0exp.natDegree) * g.leadingCoeff.natDegree ≤ (10 - A0exp.natDegree) * (W_g - dg * wY) :=
          Nat.mul_le_mul_left _ hdeg_lc
        have hdA_le : A0exp.natDegree ≤ 10 := by omega
        have hmul_le : A0exp.natDegree * dg * wY ≤ A0exp.natDegree * W_g := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left A0exp.natDegree hWg_lo
        have hsub1 : (10 - A0exp.natDegree) * (W_g - dg * wY) + (10 - A0exp.natDegree) * (dg * wY) =
            (10 - A0exp.natDegree) * W_g := by rw [← mul_add, Nat.sub_add_cancel hWg_lo]
        have hsum_d : (10 - A0exp.natDegree) * W_g + A0exp.natDegree * W_g = 10 * W_g := by
          rw [← add_mul, Nat.sub_add_cancel hdA_le]
        have hsum_w : (10 - A0exp.natDegree) * (dg * wY) + A0exp.natDegree * dg * wY = dg * 10 * wY := by
          rw [mul_assoc A0exp.natDegree, ← add_mul, Nat.sub_add_cancel hdA_le]; ring
        omega
      have hnat := sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ R hRne _ hdvd
      have htot : (∑ i : Idx, t3Vrf0Ord 3 dg 10 (k i) (rr i)) + dg * 10 * wY ≤ dg * W_F + 10 * W_g := by omega
      have hQ : ((∑ i : Idx, t3Vrf0Ord 3 dg 10 (k i) (rr i) : ℕ) : ℚ) + (dg : ℚ) * 10 * (wY : ℚ) ≤
          (dg : ℚ) * (W_F : ℚ) + 10 * (W_g : ℚ) := by
        have htotQ : (((∑ i : Idx, t3Vrf0Ord 3 dg 10 (k i) (rr i)) + dg * 10 * wY : ℕ) : ℚ) ≤
            ((dg * W_F + 10 * W_g : ℕ) : ℚ) := by exact_mod_cast htot
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat] at htotQ
        exact htotQ
      rw [Nat.cast_sum] at hQ
      dsimp [cgVal]
      have heq : ((dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 10) + 10 * ((W_g : ℚ) / (wY : ℚ))) * (wY : ℚ) =
          (dg : ℚ) * (W_F : ℚ) + 10 * (W_g : ℚ) - (dg : ℚ) * 10 * (wY : ℚ) := by
        field_simp [hwYQ.ne']; ring
      linarith
    -- Shared helper to conclude from any T3Cert `c ∈ certsT3All` with `checkT3Entry c = true`!
    have hfinish_t3 : ∀ c ∈ certsT3All, c.d2 = d2 → c.dg = dg → c.d1 = d1 → checkT3Entry c = true →
        (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) →
        (W_F : ℚ) / (wY : ℚ) ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ) →
        c.mode ≠ 2 →
        (c.hasDStar = true →
          let dStarEff : ℕ := if c.mode == 3 then c.dStar - 1 else c.dStar
          (∑ i : Idx, (t3Vrf0Ord c.mode c.dg dStarEff (k i) (rr i) : ℚ)) ≤
            ((c.dg : ℚ) * ((W_F : ℚ) / (wY : ℚ) - (dStarEff : ℚ)) + (dStarEff : ℚ) * cgVal) * (wY : ℚ)) →
        ∃ (m s cHiNum cHiDen δNum δDen : ℕ) (w : CapWitness),
          0 < m ∧ m ≤ 3000 ∧ 2 ≤ s ∧ s ≤ 300 ∧ 0 < cHiDen ∧ 0 < δNum ∧ 0 < δDen ∧
          (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ) ∧
          (δNum : ℚ) / (δDen : ℚ) <
            vquotLbQ 2 m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 2 m s (k i)) / (N : ℚ) ∧
          checkCapWitness 2 m s cHiNum cHiDen δNum δDen 1 1 1 w = true ∧
          w.c1Bkt * 1811 + w.c0Bkt ≤ T3_CAP_BOUND := by
      intro c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi hmode2 hrf0
      have hchk : checkT3Cert c = true := (Bool.and_eq_true _ _).mp hc_entry |>.1
      have ⟨hm0, hsurp_fn⟩ := checkT3Cert_sound c hchk ((W_F : ℚ) / (wY : ℚ)) cgVal hc_lo hc_hi
        (by rw [hcdg]; exact hcg_lo) (by rw [hcd2, hcd1, hcdg]; exact hcg_hi)
        Az hAz k rr hrr_le hg_sum hh1_sum hh2_sum
        (by rw [hcdg]; exact hlcg_sum) (by rw [hcd1, hcdg]; exact hlch1_sum)
        (by rw [hcd2, hcdg]; exact hlch2_sum) (by rw [hcd1, hcd2, hcdg]; exact hrh_sum)
        hrf0 (fun h2 => absurd h2 hmode2)
      have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
      have ⟨hsurp, hcap⟩ := hsurp_fn hmpos
      have ⟨hmle, hsle⟩ := certsT3All_ms_bound c hc_mem
      have hpars : 2 ≤ c.s ∧ 0 < c.cHiDen ∧ 0 < c.δNum ∧ 0 < c.δDen := by
        unfold checkT3Cert at hchk
        have hmne : (c.m != 0) = true := bne_iff_ne.mpr hm0
        by_contra hbad; push Not at hbad
        have hfail : (c.cLoDen == 0 || c.cHiDen == 0 || c.dg == 0 || c.dg > c.d1 || c.dg > c.d2) = true ∨
            (c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0)) = true := by
          rcases lt_or_ge c.s 2 with hs | hs
          · exact Or.inr (by simp [hmne, hs])
          · rcases Nat.eq_zero_or_pos c.cHiDen with hd | hd
            · exact Or.inl (by simp [hd])
            · rcases Nat.eq_zero_or_pos c.δNum with hdn | hdn
              · exact Or.inr (by simp [hmne, hdn])
              · rcases Nat.eq_zero_or_pos c.δDen with hdd | hdd
                · exact Or.inr (by simp [hmne, hdd])
                · exfalso; have := hbad hs hd hdn; omega
        rcases hfail with hf | hf
        · simp [hf] at hchk
        · split_ifs at hchk <;> simp_all
      have hcap_bd : c.cap.c1Bkt * 1811 + c.cap.c0Bkt ≤ T3_CAP_BOUND := by
        unfold checkT3Entry at hc_entry
        have hmne : (c.m == 0) = false := beq_false_of_ne hm0
        simp only [hmne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc_entry
        exact hc_entry.2
      exact ⟨c.m, c.s, c.cHiNum, c.cHiDen, c.δNum, c.δDen, c.cap, hmpos, hmle, hpars.1, hsle,
        hpars.2.1, hpars.2.2.1, hpars.2.2.2, hc_hi, hsurp, hcap, hcap_bd⟩
    -- Dispatch via `exists_t3Cert`!
    rcases exists_t3Cert d2 dg d1 dStar (by omega) hd2_le22 hd2_ev hdg_lo (by omega) hdg_ev
        (by omega) hd1_le24 hd1_par hdStar_spec ((W_F : ℚ) / (wY : ℚ)) hlo_t3 hWF_hi with
      ⟨c, hc_mem, hcd2, hcdg, hcd1, hc_entry, hmode_cases, hc_lo, hc_hi⟩ |
      ⟨hd2_8, hdg_6, hd1_10, hdStar_11, ⟨cA, hcA_mem, hA2, hAg, hA1, hcA_entry, hA_hd, hA_ds, hA_m, hA_lo, hA_hi⟩, h2B_cov⟩
    · rcases hmode_cases with ⟨hno, hm0⟩ | ⟨hhas, hcds, hm_cases⟩
      · exact hfinish_t3 c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi (by omega) (fun h => by rw [hno] at h; cases h)
      · rcases hm_cases with hm0 | hm1 | ⟨hd2_8, hdg_8, hd1_10, hds_11, hm3⟩
        · refine hfinish_t3 c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi (by omega) (fun _ => ?_)
          dsimp only; rw [hm0, hcds, hcdg]; simp only [show (0 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hrf0_std 0 (Or.inl rfl)
        · refine hfinish_t3 c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi (by omega) (fun _ => ?_)
          dsimp only; rw [hm1, hcds, hcdg]; simp only [show (1 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hrf0_std 1 (Or.inr rfl)
        · have hh2_0 : h2.natDegree = 0 := by omega
          have hgP_X2Y2 := (kerD2_2A_2B_dichotomy hgP_prim hgP_ne hh1_ne hh2_ne hgP_d hh2_d hrel_h hdvd_dX).1 hh2_0
          refine hfinish_t3 c hc_mem hcd2 hcdg hcd1 hc_entry hc_lo hc_hi (by omega) (fun _ => ?_)
          dsimp only; rw [hm3, hcds, hcdg, hds_11]
          simp only [beq_self_eq_true, ↓reduceIte]
          exact hrf0_2A hgP_X2Y2 hds_11
    · -- Special case `(d2, dg, d1, dStar) = (8, 6, 10, 11)`: 2A / 2B dichotomy!
      have hgP6 : gPrim.natDegree = 6 := hdg_6
      have hh2_2 : h2.natDegree = 2 := by omega
      rcases (kerD2_2A_2B_dichotomy hgP_prim hgP_ne hh1_ne hh2_ne hgP_d hh2_d hrel_h hdvd_dX).2 hgP6 hh2_2 with
        hgP_X2Y2 | ⟨uX, q, g1, huX_ne, hq_prim, hq_ne, hg1_ne, hq_deg, hg1_deg, hq_d, hg1_d, hh2_eq, hgP_eq, hrel_q⟩
      · -- Subcase 2A!
        refine hfinish_t3 cA hcA_mem (by omega) (by omega) (by omega) hcA_entry hA_lo hA_hi (by omega) (fun _ => ?_)
        dsimp only
        rcases hA_m with hm3 | hm0
        · rw [hm3, hA_ds, hAg, ← hdg_6]
          simp only [beq_self_eq_true, ↓reduceIte]
          exact hrf0_2A hgP_X2Y2 hdStar_11
        · rw [hm0, hA_ds, hAg, ← hdg_6, ← hdStar_11]
          simp only [show (0 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hrf0_std 0 (Or.inl rfl)
      · -- Subcase 2B!
        rcases h2B_cov with ⟨b, hb_mem, hb_entry, hb_lo, hb_hi⟩ |
            ⟨cS, hcS_mem, hS2, hSg, hS1, hcS_entry, hS_hd, hS_ds, hS_m, hS_lo, hS_hi⟩
        · -- Apply `checkT3_2BCert_sound b`!
          have hchk_b : checkT3_2BCert b = true := (Bool.and_eq_true _ _).mp hb_entry |>.1
          set g1' : BiPoly Fld := C qX * g1
          have hg1'_ne : g1' ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hqX_ne) hg1_ne
          have hg_fac : g = q * g1' := by dsimp [g, g1']; rw [hgP_eq]; ring
          have hg1'_deg : g1'.natDegree = 4 := by dsimp [g1']; rw [Polynomial.natDegree_C_mul hqX_ne, hg1_deg]
          have hg1'_d : g1'.derivative = 0 := by
            dsimp [g1']; rw [Polynomial.derivative_mul, Polynomial.derivative_C, hg1_d, zero_mul, mul_zero, add_zero]
          set W_q : ℕ := wdegBi wY q
          set W_g1' : ℕ := wdegBi wY g1'
          set cqVal : ℚ := (W_q : ℚ) / (wY : ℚ)
          have hWg_split : W_g = W_q + W_g1' := by
            dsimp only [W_g, W_q, W_g1']; rw [hg_fac]; exact wdegBiDom_mul wY hq_ne hg1'_ne
          have hWq_lo : 2 * wY ≤ W_q := by rw [← hq_deg]; exact hd_wdeg q hq_ne
          have hWg1'_lo : 4 * wY ≤ W_g1' := by rw [← hg1'_deg]; exact hd_wdeg g1' hg1'_ne
          have hWq_lo' : 2 * 1048575 ≤ W_q := hWq_lo
          have hcq_lo : (2 : ℚ) ≤ cqVal := by dsimp [cqVal]; rw [le_div_iff₀ hwYQ]; exact_mod_cast hWq_lo
          have hcg_lo_2B : cqVal + 4 ≤ cgVal := by
            dsimp [cqVal, cgVal]
            have h1 : W_q + 4 * wY ≤ W_g := by omega
            have hQ : (W_q : ℚ) + 4 * (wY : ℚ) ≤ (W_g : ℚ) := by exact_mod_cast h1
            have heq : (W_q : ℚ) / (wY : ℚ) + 4 = ((W_q : ℚ) + 4 * (wY : ℚ)) / (wY : ℚ) := by field_simp [hwYQ.ne']
            rw [heq]; exact div_le_div_of_nonneg_right hQ hwYQ.le
          have hcg_hi1 : cgVal ≤ (W_F : ℚ) / (wY : ℚ) - 5 + 2 / (wY : ℚ) := by
            have h1 : W_g + 5 * wY ≤ W_F + 2 := by
              have hwh1 : 4 * 1048575 ≤ wdegBi wY h1 := by
                have : d1 - dg = 4 := by omega
                simpa [this] using hWh1_lo'
              change W_g + 5 * 1048575 ≤ W_F + 2; omega
            have hQ : (W_g : ℚ) + 5 * (wY : ℚ) ≤ (W_F : ℚ) + 2 := by exact_mod_cast h1
            dsimp [cgVal]
            have heq : (W_F : ℚ) / (wY : ℚ) - 5 + 2 / (wY : ℚ) = ((W_F : ℚ) + 2 - 5 * (wY : ℚ)) / (wY : ℚ) := by
              field_simp [hwYQ.ne']; ring
            rw [heq]; exact div_le_div_of_nonneg_right (by linarith) hwYQ.le
          set rq : Idx → ℕ := fun i => min (rr i) (biMult (BinaryIRSProfile.domain i) (y i) q)
          have hrq_le : ∀ i, rq i ≤ rr i := fun i => Nat.min_le_left _ _
          have hbm_q : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) q (rq i) := fun i =>
            biMultGE_mono (Nat.min_le_right _ _) (biMultGE_biMult _ _ q)
          have hbm_g1' : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) g1' (rr i - rq i) := fun i => by
            have hmul := biMult_mul (BinaryIRSProfile.domain i) (y i) hq_ne hg1'_ne
            rw [← hg_fac] at hmul
            have hle : rr i - rq i ≤ biMult (BinaryIRSProfile.domain i) (y i) g1' := by
              dsimp [rq, rr]; omega
            exact biMultGE_mono hle (biMultGE_biMult _ _ g1')
          have hbm_uX : ∀ i, biMultGE (BinaryIRSProfile.domain i) (y i) (C uX) (2 * k i - 2 - rr i - rq i) := fun i => by
            have hmul1 := biMult_mul (BinaryIRSProfile.domain i) (y i) hg_ne hh2_ne
            rw [← hf2_fac] at hmul1
            have hmul2 := biMult_mul (BinaryIRSProfile.domain i) (y i) (Polynomial.C_ne_zero.mpr huX_ne) hq_ne
            rw [← hh2_eq] at hmul2
            have hmul3 := biMult_mul (BinaryIRSProfile.domain i) (y i) hq_ne hg1'_ne
            rw [← hg_fac] at hmul3
            have hge := le_biMult_of_biMultGE (BinaryIRSProfile.domain i) (y i) hf2_ne (hords_all i).2
            have hle : 2 * k i - 2 - rr i - rq i ≤ biMult (BinaryIRSProfile.domain i) (y i) (C uX) := by
              dsimp [rq, rr]; omega
            exact biMultGE_mono hle (biMultGE_biMult _ _ (C uX))
          have hq_P_ne : q.eval P ≠ 0 := by
            intro h0; apply hg_P_ne; rw [hg_fac, Polynomial.eval_mul, h0, zero_mul]
          have hg1'_P_ne : g1'.eval P ≠ 0 := by
            intro h0; apply hg_P_ne; rw [hg_fac, Polynomial.eval_mul, h0, mul_zero]
          have hq_sum : (∑ i ∈ Az, (rq i : ℚ)) ≤ cqVal * (wY : ℚ) := by
            have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY W_q q P rq hPdeg le_rfl hq_P_ne
              (fun i hi => by rw [hagree i hi]; exact hbm_q i)
            have hQ : ((∑ i ∈ Az, rq i : ℕ) : ℚ) ≤ (W_q : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum] at hQ; dsimp [cqVal]; rw [div_mul_cancel₀ _ hwYQ.ne']; exact hQ
          have hg1'_sum : (∑ i ∈ Az, ((rr i - rq i : ℕ) : ℚ)) ≤ (cgVal - cqVal) * (wY : ℚ) := by
            have hnat := sum_biMultGE_eval_le BinaryIRSProfile.domain Az wY W_g1' g1' P (fun i => rr i - rq i)
              hPdeg le_rfl hg1'_P_ne (fun i hi => by rw [hagree i hi]; exact hbm_g1' i)
            have hQ : ((∑ i ∈ Az, (rr i - rq i) : ℕ) : ℚ) ≤ (W_g1' : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum] at hQ; dsimp [cgVal, cqVal]
            have heq : ((W_g : ℚ) / (wY : ℚ) - (W_q : ℚ) / (wY : ℚ)) * (wY : ℚ) = (W_g1' : ℚ) := by
              rw [hWg_split, Nat.cast_add]; field_simp [hwYQ.ne']; ring
            linarith
          have hu_sum : (∑ i : Idx, ((2 * k i - 2 - rr i - rq i : ℕ) : ℚ)) ≤
              ((W_F : ℚ) / (wY : ℚ) - 2 - cgVal - cqVal) * (wY : ℚ) + 2 := by
            have hWh2_eq : wdegBi wY h2 = uX.natDegree + W_q := by
              rw [hh2_eq]
              have h1 := wdegBiDom_mul wY (Polynomial.C_ne_zero.mpr huX_ne) hq_ne
              rwa [wdegBiDom_C] at h1
            have hnat := hsum_lc (C uX) (Polynomial.C_ne_zero.mpr huX_ne) uX.natDegree
              (by rw [show wdegBi wY (C uX) = uX.natDegree from wdegBiDom_C wY uX])
              (fun i => 2 * k i - 2 - rr i - rq i) hbm_uX
            simp only [Polynomial.natDegree_C, Nat.sub_zero, zero_mul] at hnat
            have hle_uX : uX.natDegree ≤ W_F - 2 * (wY - 1) - W_g - W_q := by omega
            have hQ : ((∑ i : Idx, (2 * k i - 2 - rr i - rq i) : ℕ) : ℚ) ≤
                ((W_F - 2 * (wY - 1) - W_g - W_q : ℕ) : ℚ) := by exact_mod_cast (hnat.trans hle_uX)
            rw [Nat.cast_sum, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
              Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_ofNat, Nat.cast_one] at hQ
            dsimp [cgVal, cqVal]
            have heq : ((W_F : ℚ) / (wY : ℚ) - 2 - (W_g : ℚ) / (wY : ℚ) - (W_q : ℚ) / (wY : ℚ)) * (wY : ℚ) + 2 =
                (W_F : ℚ) - 2 * ((wY : ℚ) - 1) - (W_g : ℚ) - (W_q : ℚ) := by field_simp [hwYQ.ne']; ring
            linarith
          have hlcq_sum : (∑ i : Idx, ((rq i - 2 : ℕ) : ℚ)) ≤ (cqVal - 2) * (wY : ℚ) := by
            have hnat := hsum_lc q hq_ne W_q le_rfl rq hbm_q
            rw [hq_deg] at hnat
            have hQ : ((∑ i : Idx, (rq i - 2) : ℕ) : ℚ) ≤ ((W_q - 2 * wY : ℕ) : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum, Nat.cast_sub hWq_lo, Nat.cast_mul, Nat.cast_ofNat] at hQ
            dsimp [cqVal]; have heq : ((W_q : ℚ) / (wY : ℚ) - 2) * (wY : ℚ) = (W_q : ℚ) - 2 * (wY : ℚ) := by
              field_simp [hwYQ.ne']
            linarith
          have hlcg1_sum : (∑ i : Idx, ((rr i - rq i - 4 : ℕ) : ℚ)) ≤ (cgVal - cqVal - 4) * (wY : ℚ) := by
            have hnat := hsum_lc g1' hg1'_ne W_g1' le_rfl (fun i => rr i - rq i) hbm_g1'
            rw [hg1'_deg] at hnat
            have hQ : ((∑ i : Idx, (rr i - rq i - 4) : ℕ) : ℚ) ≤ ((W_g1' - 4 * wY : ℕ) : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum, Nat.cast_sub hWg1'_lo, Nat.cast_mul, Nat.cast_ofNat] at hQ
            dsimp [cgVal, cqVal]
            have heq : ((W_g : ℚ) / (wY : ℚ) - (W_q : ℚ) / (wY : ℚ) - 4) * (wY : ℚ) = (W_g1' : ℚ) - 4 * (wY : ℚ) := by
              rw [hWg_split, Nat.cast_add]; field_simp [hwYQ.ne']; ring
            linarith
          have hlch1_2B : (∑ i : Idx, ((2 * k i - 1 - rr i - 4 : ℕ) : ℚ)) ≤
              ((W_F : ℚ) / (wY : ℚ) - 5 - cgVal) * (wY : ℚ) + 1 := by
            have h1 := hlch1_sum; rw [show d1 - dg = 4 by omega] at h1
            have : (W_F : ℚ) / (wY : ℚ) - 1 - cgVal - ((4 : ℕ) : ℚ) = (W_F : ℚ) / (wY : ℚ) - 5 - cgVal := by
              push_cast; ring
            rwa [this] at h1
          have hrq_res : (∑ i : Idx, (resOrdExact 4 (2 * k i - 1 - rr i) 2 (rq i) : ℚ)) ≤
              (2 * ((W_F : ℚ) / (wY : ℚ) - 1 - cgVal) + 4 * cqVal - 8) * (wY : ℚ) + 2 := by
            have hh1_4 : h1.natDegree = 4 := by omega
            have hRne : Polynomial.resultant h1 q 4 2 ≠ 0 := by
              rw [← hh1_4, ← hq_deg]; exact resultant_ne_zero_of_coprime_ratFunc h1 q hh1_ne hq_ne hrel_q
            have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
                (X - C (BinaryIRSProfile.domain i)) ^ resOrdExact 4 (2 * k i - 1 - rr i) 2 (rq i) ∣
                  Polynomial.resultant h1 q 4 2 := fun i _ =>
              X_sub_C_pow_dvd_resultant_of_biMultGE (BinaryIRSProfile.domain i) (y i) h1 q
                4 (2 * k i - 1 - rr i) 2 (rq i) (hbm_h1 i) (hbm_q i) (by omega) (by omega)
            have hdeg_R := natDegree_resultant_le_wdegBi wY (W_F - (wY - 1) - W_g) W_q 4 2 h1 q
              (by omega) le_rfl (by omega) (by omega)
            have hnat := (sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ _ hRne _ hdvd).trans hdeg_R
            have hsub_ge : 4 * 2 * wY ≤ 2 * (W_F - (wY - 1) - W_g) + 4 * W_q := by
              have h1 : 4 * wY ≤ W_F - (wY - 1) - W_g := by
                have := hWh1_lo; rw [show d1 - dg = 4 by omega] at this; omega
              have h2 : 2 * (4 * wY) ≤ 2 * (W_F - (wY - 1) - W_g) := Nat.mul_le_mul_left 2 h1
              omega
            have hQ : ((∑ i : Idx, resOrdExact 4 (2 * k i - 1 - rr i) 2 (rq i) : ℕ) : ℚ) ≤
                ((2 * (W_F - (wY - 1) - W_g) + 4 * W_q - 4 * 2 * wY : ℕ) : ℚ) := by exact_mod_cast hnat
            rw [Nat.cast_sum, Nat.cast_sub hsub_ge, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
              Nat.cast_sub (by omega : W_g ≤ W_F - (wY - 1)), Nat.cast_sub (by omega : wY - 1 ≤ W_F),
              Nat.cast_sub (by omega : 1 ≤ wY), Nat.cast_mul, Nat.cast_one,
              show ((4 * 2 : ℕ) : ℚ) = 4 * 2 by norm_num,
              show ((2 : ℕ) : ℚ) = 2 by norm_num, show ((4 : ℕ) : ℚ) = 4 by norm_num] at hQ
            dsimp [cgVal, cqVal]
            have heq : (2 * ((W_F : ℚ) / (wY : ℚ) - 1 - (W_g : ℚ) / (wY : ℚ)) + 4 * ((W_q : ℚ) / (wY : ℚ)) - 8) * (wY : ℚ) + 2 =
                2 * ((W_F : ℚ) - ((wY : ℚ) - 1) - (W_g : ℚ)) + 4 * (W_q : ℚ) - 4 * 2 * (wY : ℚ) := by
              field_simp [hwYQ.ne']; ring
            linarith [hQ, heq]
          -- Shared helper for Res_Y(f0, sub) with sub ∈ {q, g1'}!
          have hrf0_sub : ∀ (sub : BiPoly Fld) (dSub W_sub : ℕ) (rSub : Idx → ℕ),
              sub ≠ 0 → sub.natDegree = dSub → sub.derivative = 0 → sub ∣ g → wdegBi wY sub = W_sub →
              (∀ i, rSub i ≤ biMult (BinaryIRSProfile.domain i) (y i) sub) →
              (∑ i : Idx, (t3_2BVrf0Sub dSub (k i) (rSub i) : ℚ)) ≤
                ((dSub : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 11) + 11 * ((W_sub : ℚ) / (wY : ℚ))) * (wY : ℚ) := by
            intro sub dSub W_sub rSub hsub_ne hsub_deg hsub_d hsub_dvd hWsub hrSub
            have hrel_s : IsRelPrime (f0.map ι) (sub.map ι) := fun p hp0 hps => by
              have hpg : p ∣ g.map ι := hps.trans (by rcases hsub_dvd with ⟨w, hw⟩; exact ⟨w.map ι, by rw [hw, Polynomial.map_mul]⟩)
              exact hcop_all p hp0 (hpg.trans ⟨h1.map ι, by rw [hf1_fac, Polynomial.map_mul]⟩)
                (hpg.trans ⟨h2.map ι, by rw [hf2_fac, Polynomial.map_mul]⟩)
            set R : Polynomial Fld := sub.leadingCoeff ^ (11 - d0) * Polynomial.resultant f0 sub d0 dSub
            have hRne : R ≠ 0 := mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hsub_ne))
              (by rw [← hsub_deg]; exact resultant_ne_zero_of_coprime_ratFunc f0 sub hf0_ne hsub_ne hrel_s)
            have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
                (X - C (BinaryIRSProfile.domain i)) ^ t3_2BVrf0Sub dSub (k i) (rSub i) ∣ R := by
              intro i _
              refine (pow_dvd_pow _ (t3_2BVrf0Sub_mono dSub (k i) (hrSub i))).trans ?_
              have hsub_ev : ∀ j, j % 2 = 1 → sub.coeff j = 0 := (deriv_eq_zero_iff_even_coeffs sub).mp hsub_d
              have ⟨hvk, hvp⟩ := kerD2_resY_f0_g_ord hwYpos (BinaryIRSProfile.domain i) (y i) f_coord (hvan i)
                sub hsub_ne hsub_ev
                (hsub_dvd.trans (by change g ∣ f1; rw [hf1_fac]; exact dvd_mul_right _ _))
                (hsub_dvd.trans (by change g ∣ f2; rw [hf2_fac]; exact dvd_mul_right _ _))
                11 (by change max d0 (max (d2 + 2) (d1 + 1)) ≤ 11; omega)
              rw [hsub_deg] at hvk hvp
              by_cases hk0 : k i = 0
              · simp [t3_2BVrf0Sub, hk0]
              · have hk0b : (k i == 0) = false := beq_false_of_ne hk0
                unfold t3_2BVrf0Sub; simp only [hk0b, Bool.false_eq_true, ↓reduceIte, resOrdWeighted2Fast_eq]
                rcases le_total (resOrdWeighted 11 (4 * k i + 4) (dSub / 2) (biMult (BinaryIRSProfile.domain i) (y i) sub) 2 - 2 * dSub)
                    (((List.range 12).map (fun d0' =>
                      resOrdExact d0' (2 * k i - 2) dSub (biMult (BinaryIRSProfile.domain i) (y i) sub) +
                        (11 - d0') * (biMult (BinaryIRSProfile.domain i) (y i) sub - dSub))).foldl Nat.min
                          (resOrdExact 0 (2 * k i - 2) dSub (biMult (BinaryIRSProfile.domain i) (y i) sub) +
                            11 * (biMult (BinaryIRSProfile.domain i) (y i) sub - dSub))) with hle | hle
                · rw [Nat.max_eq_right hle]
                  refine (pow_dvd_pow _ (foldl_map_min_le_mem _ (List.range 12) _ d0
                    (List.mem_range.mpr (by have : d0 ≤ dStar := le_max_left _ _; omega)))).trans hvp
                · rw [Nat.max_eq_left hle]; exact hvk
            have hWsub_lo : dSub * wY ≤ W_sub := by rw [← hWsub, ← hsub_deg]; exact hd_wdeg sub hsub_ne
            have hdeg_lc : sub.leadingCoeff.natDegree ≤ W_sub - dSub * wY := by
              have hnz := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hsub_ne)
              have hle := (wdegBi_le_iff wY W_sub sub).mp (le_of_eq hWsub) dSub _ (by rwa [← hsub_deg]); omega
            have hdeg_res := natDegree_resultant_le_wdegBi wY W_F W_sub d0 dSub f0 sub hWf0 (le_of_eq hWsub) le_rfl (le_of_eq hsub_deg)
            have hdeg_R : R.natDegree + dSub * 11 * wY ≤ dSub * W_F + 11 * W_sub := by
              have h1 : R.natDegree ≤ (11 - d0) * sub.leadingCoeff.natDegree + (Polynomial.resultant f0 sub d0 dSub).natDegree :=
                Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_pow_le _)
              have h2 : (11 - d0) * sub.leadingCoeff.natDegree ≤ (11 - d0) * (W_sub - dSub * wY) :=
                Nat.mul_le_mul_left _ hdeg_lc
              have hd0_le : d0 ≤ 11 := by have : d0 ≤ dStar := le_max_left _ _; omega
              have hmul_le : d0 * dSub * wY ≤ d0 * W_sub := by
                rw [mul_assoc]; exact Nat.mul_le_mul_left d0 hWsub_lo
              have hsub1 : (11 - d0) * (W_sub - dSub * wY) + (11 - d0) * (dSub * wY) = (11 - d0) * W_sub := by
                rw [← mul_add, Nat.sub_add_cancel hWsub_lo]
              have hsum_d : (11 - d0) * W_sub + d0 * W_sub = 11 * W_sub := by
                rw [← add_mul, Nat.sub_add_cancel hd0_le]
              have hsum_w : (11 - d0) * (dSub * wY) + d0 * dSub * wY = dSub * 11 * wY := by
                rw [mul_assoc d0, ← add_mul, Nat.sub_add_cancel hd0_le]; ring
              omega
            have hnat := sum_ord_univariate_le BinaryIRSProfile.domain Finset.univ R hRne _ hdvd
            have htot : (∑ i : Idx, t3_2BVrf0Sub dSub (k i) (rSub i)) + dSub * 11 * wY ≤ dSub * W_F + 11 * W_sub := by omega
            have hQ : ((∑ i : Idx, t3_2BVrf0Sub dSub (k i) (rSub i) : ℕ) : ℚ) + (dSub : ℚ) * 11 * (wY : ℚ) ≤
                (dSub : ℚ) * (W_F : ℚ) + 11 * (W_sub : ℚ) := by
              have htotQ : (((∑ i : Idx, t3_2BVrf0Sub dSub (k i) (rSub i)) + dSub * 11 * wY : ℕ) : ℚ) ≤
                  ((dSub * W_F + 11 * W_sub : ℕ) : ℚ) := by exact_mod_cast htot
              rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
                show ((11 : ℕ) : ℚ) = 11 by norm_num] at htotQ
              exact htotQ
            rw [Nat.cast_sum] at hQ
            have heq : ((dSub : ℚ) * ((W_F : ℚ) / (wY : ℚ) - 11) + 11 * ((W_sub : ℚ) / (wY : ℚ))) * (wY : ℚ) =
                (dSub : ℚ) * (W_F : ℚ) + 11 * (W_sub : ℚ) - (dSub : ℚ) * 11 * (wY : ℚ) := by
              field_simp [hwYQ.ne']; ring
            linarith [hQ, heq]
          have hrf0q := hrf0_sub q 2 W_q rq hq_ne hq_deg hq_d (by rw [hg_fac]; exact dvd_mul_right _ _) rfl
            (fun i => Nat.min_le_right _ _)
          have hrf0g1 : (∑ i : Idx, (t3_2BVrf0Sub 4 (k i) (rr i - rq i) : ℚ)) ≤
              (4 * ((W_F : ℚ) / (wY : ℚ) - 11) + 11 * (cgVal - cqVal)) * (wY : ℚ) := by
            have h1 := hrf0_sub g1' 4 W_g1' (fun i => rr i - rq i) hg1'_ne hg1'_deg hg1'_d
              (by rw [hg_fac]; exact dvd_mul_left _ _) rfl (fun i => by
                have hmul := biMult_mul (BinaryIRSProfile.domain i) (y i) hq_ne hg1'_ne
                rw [← hg_fac] at hmul; dsimp [rq, rr]; omega)
            have heq : cgVal - cqVal = (W_g1' : ℚ) / (wY : ℚ) := by
              dsimp [cgVal, cqVal]; rw [hWg_split, Nat.cast_add, add_div]; ring
            rwa [heq]
          have ⟨hm0, hsurp_fn⟩ := checkT3_2BCert_sound b hchk_b ((W_F : ℚ) / (wY : ℚ)) cgVal cqVal
            hb_lo hb_hi hcq_lo hcg_lo_2B hcg_hi1 Az hAz k rr rq hrr_le hrq_le
            hq_sum hg1'_sum hh1_sum hu_sum hlcq_sum hlcg1_sum hlch1_2B hrq_res
            (by simpa [cqVal] using hrf0q) hrf0g1
          have hmpos : 0 < b.m := Nat.pos_of_ne_zero hm0
          have ⟨hsurp, hcap⟩ := hsurp_fn hmpos
          have hms := List.all_eq_true.mp certsT3_2B_ms_bound b hb_mem
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
          have hpars : 2 ≤ b.s ∧ 0 < b.cHiDen ∧ 0 < b.δNum ∧ 0 < b.δDen := by
            unfold checkT3_2BCert at hchk_b
            have hmne : (b.m != 0) = true := bne_iff_ne.mpr hm0
            by_contra hbad; push Not at hbad
            have hfail : (b.cLoDen == 0 || b.cHiDen == 0) = true ∨
                (b.m != 0 && (b.s < 2 || b.vx == 0 || b.δNum == 0 || b.δDen == 0)) = true := by
              rcases lt_or_ge b.s 2 with hs | hs
              · exact Or.inr (by simp [hmne, hs])
              · rcases Nat.eq_zero_or_pos b.cHiDen with hd | hd
                · exact Or.inl (by simp [hd])
                · rcases Nat.eq_zero_or_pos b.δNum with hdn | hdn
                  · exact Or.inr (by simp [hmne, hdn])
                  · rcases Nat.eq_zero_or_pos b.δDen with hdd | hdd
                    · exact Or.inr (by simp [hmne, hdd])
                    · exfalso; have := hbad hs hd hdn; omega
            rcases hfail with hf | hf
            · simp [hf] at hchk_b
            · split_ifs at hchk_b <;> simp_all
          have hcap_bd : b.cap.c1Bkt * 1811 + b.cap.c0Bkt ≤ T3_CAP_BOUND := by
            unfold checkT3_2BEntry at hb_entry
            have hmne : (b.m == 0) = false := beq_false_of_ne hm0
            simp only [hmne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hb_entry
            exact hb_entry.2
          exact ⟨b.m, b.s, b.cHiNum, b.cHiDen, b.δNum, b.δDen, b.cap, hmpos, hms.1, hpars.1, hms.2,
            hpars.2.1, hpars.2.2.1, hpars.2.2.2, hb_hi, hsurp, hcap, hcap_bd⟩
        · -- Standard `mode = 0` certificate `cS`!
          refine hfinish_t3 cS hcS_mem (by omega) (by omega) (by omega) hcS_entry hS_lo hS_hi (by omega) (fun _ => ?_)
          dsimp only; rw [hS_m, hS_ds, hSg, ← hdg_6, ← hdStar_11]
          simp only [show (0 == 3) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hrf0_std 0 (Or.inl rfl)


end B6402PointSurplus
end ProximityPrize.SubmissionBinaryLower
