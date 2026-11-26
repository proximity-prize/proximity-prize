import ProximityPrize.SubmissionBinaryLower.Binary6402SmallAlgPart1
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
section KerDResultants

/-- **Table 3 General Local Resultant Divisibility (`kerD2_resY_f0_g_ord`):**
For `Fpoly ∈ K_{W_F}(2)` with `twOrdGE (localShift F) k`, ANY `g ∈ F[X, Y^2]` (`g = expand 2 gHalf`)
dividing BOTH `Fpoly.coeff 1` and `Fpoly.coeff 2`, with `dg = g.natDegree` even, `r = biMult x0 y0 g`,
and `dStar ≥ max (Fpoly.coeff 0).natDegree (max ((Fpoly.coeff 2).natDegree + 2) ((Fpoly.coeff 1).natDegree + 1))`:
BOTH `v_ker = resOrdWeighted dStar (4*k + 4) (dg / 2) r 2 - 2 * dg` AND
`v_pln = resOrdExact d0 (2*k - 2) dg r + (dStar - d0) * (r - dg)` divide
`g.leadingCoeff ^ (dStar - d0) * Polynomial.resultant (Fpoly.coeff 0) g d0 dg`! -/
theorem kerD2_resY_f0_g_ord {F : Type*} [Field F] [CharP F 2] {wY W_F k : ℕ} (hwY : 0 < wY)
    (x0 y0 : F) (f_coord : KerDIdx wY W_F 2 → F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) k)
    (g : BiPoly F) (hg_ne : g ≠ 0) (hg_ev : ∀ j, j % 2 = 1 → g.coeff j = 0)
    (hdvd1 : g ∣ (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1)
    (hdvd2 : g ∣ (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2)
    (dStar : ℕ)
    (hdStar : max ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).natDegree
        (max (((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2).natDegree + 2)
          (((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree + 1)) ≤ dStar) :
    let Fpoly : ContactPoly F := ∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1
    let d0 := (Fpoly.coeff 0).natDegree
    let dg := g.natDegree
    let r := biMult x0 y0 g
    (X - C x0) ^ (resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 - 2 * dg) ∣
      g.leadingCoeff ^ (dStar - d0) * Polynomial.resultant (Fpoly.coeff 0) g d0 dg ∧
    (X - C x0) ^ (resOrdExact d0 (2 * k - 2) dg r + (dStar - d0) * (r - dg)) ∣
      g.leadingCoeff ^ (dStar - d0) * Polynomial.resultant (Fpoly.coeff 0) g d0 dg := by
  intro Fpoly d0 dg r
  have hd0_le : d0 ≤ dStar := le_trans (le_max_left _ _) hdStar
  have hd1_le : (Fpoly.coeff 1).natDegree + 1 ≤ dStar :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hdStar
  have hd2_le : (Fpoly.coeff 2).natDegree + 2 ≤ dStar :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hdStar
  obtain ⟨hbm0, _, _, Pe, Po, hdecomp, hPe_d, hPo_d, _, _, hP_ord⟩ := kerD2_local_ords hwY x0 y0 f_coord hvan
  have hbmg : biMultGE x0 y0 g r := biMultGE_biMult x0 y0 g
  constructor
  · -- Branch 1: v_ker!
    obtain ⟨g0, hg0_eq, _, _⟩ := exists_expand2_of_even_Y g hg_ev
    have hsh_exp : shiftBi x0 y0 g =
        Polynomial.expand (Polynomial F) 2
          ((g0.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)) := by
      rw [hg0_eq, shiftBi_expand2]
    set g1 : BiPoly F := (g0.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)
    have hshg_deg : (shiftBi x0 y0 g).natDegree = dg := by
      unfold shiftBi
      have hinj : Function.Injective (Polynomial.compRingHom (C x0 + X) : Polynomial F →+* Polynomial F) := by
        intro p q hpq; have := congrArg (fun r => r.comp (X - C x0)) hpq
        simpa [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.comp_X] using this
      have h1 : (g.map (Polynomial.compRingHom (C x0 + X))).natDegree = dg :=
        Polynomial.natDegree_map_eq_of_injective hinj _
      have hcomp : ∀ (p : BiPoly F) (c : Polynomial F), (p.comp (C c + X)).natDegree = p.natDegree := by
        intro p c; apply le_antisymm
        · refine Polynomial.natDegree_comp_le.trans ?_
          have h2 : (C c + X : BiPoly F).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith only [h2]
        · have hb : ((p.comp (C c + X)).comp (C (-c) + X)).natDegree = p.natDegree := by
            rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
              show C c + (C (-c) + X) = X by rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add],
              Polynomial.comp_X]
          rw [← hb]; refine Polynomial.natDegree_comp_le.trans ?_
          have h2 : (C (-c) + X : BiPoly F).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith only [h2]
      rw [hcomp, h1]
    have hdg_ev : dg % 2 = 0 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hsh_exp, hshg_deg] at h2; omega
    have hg1_deg : g1.natDegree = dg / 2 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hsh_exp, hshg_deg] at h2; omega
    have hg1_ord : weightedOrdGE 2 r g1 := by
      intro j
      have hc : (shiftBi x0 y0 g).coeff (2 * j) = g1.coeff j := by
        rw [hsh_exp, Polynomial.coeff_expand (by norm_num : 0 < 2), if_pos ⟨j, rfl⟩,
          Nat.mul_div_cancel_left j (by norm_num)]
      rw [← hc]
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one x0 y0 g r).mp hbmg (2 * j)
    have hPe2 : 2 * Pe.natDegree ≤ dStar := by omega
    have hPo2 : 2 * Po.natDegree + 1 ≤ dStar := by omega
    have hres_eq1 : Polynomial.resultant
        (shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) +
         shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X) +
         shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2)
        (shiftBi x0 y0 g) dStar dg =
        Polynomial.resultant (Pe ^ 2 + X * Po ^ 2) g1 dStar (dg / 2) := by
      conv_lhs => rw [hdecomp, hsh_exp, show dg = 2 * (dg / 2) by omega]
      exact resultant_expand2 Pe Po g1 dStar (dg / 2) hPe2 hPo2 hg1_deg
    rcases hdvd1 with ⟨h1, hh1⟩
    rcases hdvd2 with ⟨h2, hh2⟩
    have hsh0_deg : (shiftBi x0 y0 (Fpoly.coeff 0)).natDegree ≤ d0 := by
      unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
      have hm : ((Fpoly.coeff 0).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ d0 := Polynomial.natDegree_map_le
      have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
      nlinarith only [hm, hX]
    have hsh1_deg : (shiftBi x0 y0 (Fpoly.coeff 1)).natDegree ≤ (Fpoly.coeff 1).natDegree := by
      unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
      have hm : ((Fpoly.coeff 1).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ (Fpoly.coeff 1).natDegree := Polynomial.natDegree_map_le
      have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
      nlinarith only [hm, hX]
    have hsh2_deg : (shiftBi x0 y0 (Fpoly.coeff 2)).natDegree ≤ (Fpoly.coeff 2).natDegree := by
      unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
      have hm : ((Fpoly.coeff 2).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ (Fpoly.coeff 2).natDegree := Polynomial.natDegree_map_le
      have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
      nlinarith only [hm, hX]
    have hres_eq2 : Polynomial.resultant
        (shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) +
         shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X) +
         shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2)
        (shiftBi x0 y0 g) dStar dg =
        X ^ (2 * dg) * (shiftBi x0 y0 g).leadingCoeff ^ (dStar - d0) *
          Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0)) (shiftBi x0 y0 g) d0 dg := by
      set qmul : BiPoly F := shiftBi x0 y0 h1 * (C X * X) + shiftBi x0 y0 h2 * X ^ 2
      have hrew : shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) +
          shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X) +
          shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2 =
          shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) + qmul * shiftBi x0 y0 g := by
        dsimp [qmul]; rw [hh1, hh2, shiftBi_mul, shiftBi_mul]; ring
      have hdeg0 : (shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2)).natDegree ≤ dStar := by
        refine Polynomial.natDegree_mul_le.trans ?_; simp only [Polynomial.natDegree_C, add_zero]; omega
      have hdegS : (shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) + qmul * shiftBi x0 y0 g).natDegree ≤ dStar := by
        rw [← hrew]
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le hdeg0 ?_)) ?_)
        · refine Polynomial.natDegree_mul_le.trans ?_
          have hCX : (C X * X : BiPoly F).natDegree ≤ 1 :=
            Polynomial.natDegree_mul_le.trans (by simp [Polynomial.natDegree_X])
          omega
        · refine Polynomial.natDegree_mul_le.trans ?_
          have hX2 : (X ^ 2 : BiPoly F).natDegree ≤ 2 :=
            Polynomial.natDegree_pow_le.trans (by simp [Polynomial.natDegree_X])
          omega
      have hneg1 : (-1 : Polynomial F) = 1 := CharTwo.neg_eq 1
      conv_lhs =>
        rw [hrew, resultant_add_mul_right_deg _ _ qmul dStar dg hdeg0 hdegS hshg_deg,
          mul_comm (shiftBi x0 y0 (Fpoly.coeff 0)) (C (X ^ 2)),
          Polynomial.resultant_C_mul_left,
          ← pow_mul, show dStar = d0 + (dStar - d0) by omega,
          Polynomial.resultant_add_left_deg _ _ d0 dg (dStar - d0) hsh0_deg,
          show (shiftBi x0 y0 g).coeff dg = (shiftBi x0 y0 g).leadingCoeff by rw [Polynomial.leadingCoeff, hshg_deg],
          hneg1, one_pow, one_mul]
      ring
    have hdvd_V : X ^ resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 ∣
        Polynomial.resultant (Pe ^ 2 + X * Po ^ 2) g1 dStar (dg / 2) := by
      apply pow_dvd_resultant_of_weighted_ord X (Pe ^ 2 + X * Po ^ 2) g1 dStar (4 * k + 4) (dg / 2) r 2
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact Polynomial.natDegree_pow_le.trans hPe2
        · refine Polynomial.natDegree_mul_le.trans ?_
          rw [Polynomial.natDegree_X]
          have := Polynomial.natDegree_pow_le (p := Po) (n := 2)
          omega
      · exact le_of_eq hg1_deg
      · exact hP_ord
      · exact hg1_ord
    rw [← hres_eq1, hres_eq2] at hdvd_V
    have hdvd_sh : X ^ (resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 - 2 * dg) ∣
        (shiftBi x0 y0 g).leadingCoeff ^ (dStar - d0) *
          Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0)) (shiftBi x0 y0 g) d0 dg := by
      by_cases hle : 2 * dg ≤ resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2
      · have hsplit : (X : Polynomial F) ^ resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 =
            (X : Polynomial F) ^ (2 * dg) * (X : Polynomial F) ^ (resOrdWeighted dStar (4 * k + 4) (dg / 2) r 2 - 2 * dg) := by
          rw [← pow_add, Nat.add_sub_of_le hle]
        rw [hsplit, mul_assoc] at hdvd_V
        exact (mul_dvd_mul_iff_left (pow_ne_zero (2 * dg) Polynomial.X_ne_zero)).mp hdvd_V
      · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle), pow_zero]; exact one_dvd _
    have hlc_sh : (shiftBi x0 y0 g).leadingCoeff = g.leadingCoeff.comp (C x0 + X) := by
      rw [Polynomial.leadingCoeff, hshg_deg]; unfold shiftBi
      have hmap_deg : (g.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ dg := Polynomial.natDegree_map_le
      rw [coeff_comp_C_add_X_top y0 _ dg hmap_deg, Polynomial.coeff_map, Polynomial.leadingCoeff]; rfl
    rw [hlc_sh, resultant_shiftBi x0 y0 (Fpoly.coeff 0) g d0 dg le_rfl le_rfl,
      ← Polynomial.pow_comp, ← Polynomial.mul_comp] at hdvd_sh
    exact X_sub_C_pow_dvd_of_comp_shift x0 _ _ hdvd_sh
  · -- Branch 2: v_pln!
    have h1 := pow_dvd_leadingCoeff_of_biMultGE x0 y0 g dg r rfl hbmg
    have h1p : (X - C x0) ^ ((dStar - d0) * (r - dg)) ∣ g.leadingCoeff ^ (dStar - d0) := by
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h1 (dStar - d0)
    have h2s := pow_dvd_resultant_of_biMultGE x0 y0 (Fpoly.coeff 0) g d0 (2 * k - 2) dg r hbm0 hbmg le_rfl le_rfl
    rw [resultant_shiftBi x0 y0 (Fpoly.coeff 0) g d0 dg le_rfl le_rfl] at h2s
    have h2 := X_sub_C_pow_dvd_of_comp_shift x0 _ _ h2s
    rw [add_comm, pow_add]
    exact mul_dvd_mul h1p h2

/-- Coefficient-wise `X`-derivative on `BiPoly F = (F[X])[Y]`. -/
noncomputable def dXBi {F : Type*} [CommRing F] (p : BiPoly F) : BiPoly F :=
  ∑ j ∈ p.support, Polynomial.monomial j (p.coeff j).derivative

lemma coeff_dXBi {F : Type*} [CommRing F] (p : BiPoly F) (j : ℕ) :
    (dXBi p).coeff j = (p.coeff j).derivative := by
  unfold dXBi; rw [finset_sum_coeff]
  by_cases hj : j ∈ p.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hne; simp [Polynomial.coeff_monomial, hne]
    · intro h; exact absurd hj h
  · rw [Finset.sum_eq_zero, Polynomial.notMem_support_iff.mp hj, map_zero]
    intro k hk; simp [Polynomial.coeff_monomial, show k ≠ j by intro heq; subst heq; exact hj hk]

lemma dXBi_mul {F : Type*} [CommRing F] (p q : BiPoly F) :
    dXBi (p * q) = dXBi p * q + p * dXBi q := by
  rw [Polynomial.ext_iff]; intro j
  rw [coeff_dXBi, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul, Polynomial.coeff_mul,
    map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ⟨a, b⟩ _
  rw [Polynomial.derivative_mul, coeff_dXBi, coeff_dXBi]

lemma dXBi_eq_zero_of_xev {F : Type*} [CommRing F] [CharP F 2] (p : BiPoly F)
    (hxev : ∀ j i, i % 2 = 1 → (p.coeff j).coeff i = 0) : dXBi p = 0 := by
  ext j i
  rw [coeff_dXBi, Polynomial.coeff_derivative, Polynomial.coeff_zero, Polynomial.coeff_zero]
  by_cases hi : (i + 1) % 2 = 1
  · rw [hxev j (i + 1) hi, zero_mul]
  · have h2 : ((i : F) + 1) = 0 := by
      have hdiv : i + 1 = 2 * ((i + 1) / 2) := by omega
      have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
      calc (i : F) + 1 = ((i + 1 : ℕ) : F) := by push_cast; rfl
        _ = ((2 * ((i + 1) / 2) : ℕ) : F) := congrArg Nat.cast hdiv
        _ = (2 : F) * (((i + 1) / 2 : ℕ) : F) := by push_cast; rfl
        _ = 0 := by rw [h2F, zero_mul]
    rw [h2, mul_zero]

lemma natDegree_dXBi_le {F : Type*} [CommRing F] (p : BiPoly F) :
    (dXBi p).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
  rw [coeff_dXBi, Polynomial.coeff_eq_zero_of_natDegree_lt hj, map_zero]

noncomputable def evenPartX {F : Type*} [Semiring F] (p : Polynomial F) : Polynomial F :=
  ∑ i ∈ Finset.range (p.natDegree / 2 + 1), Polynomial.monomial (2 * i) (p.coeff (2 * i))

lemma coeff_evenPartX {F : Type*} [Semiring F] (p : Polynomial F) (n : ℕ) :
    (evenPartX p).coeff n = if n % 2 = 0 then p.coeff n else 0 := by
  unfold evenPartX; rw [finset_sum_coeff]
  split_ifs with hn
  · by_cases hlt : n / 2 < p.natDegree / 2 + 1
    · rw [Finset.sum_eq_single (n / 2)]
      · simp [Polynomial.coeff_monomial, show 2 * (n / 2) = n by omega]
      · intro k _ hne; simp [Polynomial.coeff_monomial, show 2 * k ≠ n by omega]
      · intro h; exact absurd (Finset.mem_range.mpr hlt) h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      apply Finset.sum_eq_zero; intro k hk
      have := Finset.mem_range.mp hk; simp [Polynomial.coeff_monomial, show 2 * k ≠ n by omega]
  · apply Finset.sum_eq_zero; intro k _
    simp [Polynomial.coeff_monomial, show 2 * k ≠ n by omega]

lemma evenPartX_mul_of_xev {F : Type*} [CommRing F] (p q : Polynomial F)
    (hp : ∀ i, i % 2 = 1 → p.coeff i = 0) :
    evenPartX (p * q) = p * evenPartX q := by
  ext n
  rw [coeff_evenPartX, Polynomial.coeff_mul]
  split_ifs with hn
  · rw [Polynomial.coeff_mul]
    apply Finset.sum_congr rfl; intro ⟨a, b⟩ hab
    have hsum : a + b = n := Finset.mem_antidiagonal.mp hab
    rw [coeff_evenPartX]
    by_cases hb : b % 2 = 0
    · rw [if_pos hb]
    · rw [if_neg hb, hp a (by omega), zero_mul, zero_mul]
  · symm; rw [Polynomial.coeff_mul]; apply Finset.sum_eq_zero; intro ⟨a, b⟩ hab
    have hsum : a + b = n := Finset.mem_antidiagonal.mp hab
    rw [coeff_evenPartX]
    by_cases hb : b % 2 = 0
    · rw [hp a (by omega), zero_mul]
    · rw [if_neg hb, mul_zero]

lemma shiftBi_in_X2_Y2 {F : Type*} [Field F] [CharP F 2] (x0 y0 : F) (p : BiPoly F)
    (hp : ∀ j i, (p.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) :
    ∀ j i, ((shiftBi x0 y0 p).coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
  intro j i hnz
  have hpow2X : ∀ u v : Polynomial F, (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
    intro u v
    have h2 : (2 : Polynomial F) = 0 := CharTwo.two_eq_zero
    calc (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
      _ = u ^ 2 + v ^ 2 := by rw [h2]; ring
  have hpow2Y : ∀ u v : BiPoly F, (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
    intro u v
    have h2 : (2 : BiPoly F) = 0 := CharTwo.two_eq_zero
    calc (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
      _ = u ^ 2 + v ^ 2 := by rw [h2]; ring
  have hsh_monom : ∀ (c : F) (a b : ℕ) (j' i' : ℕ),
      ((shiftBi x0 y0 (Polynomial.monomial (2 * b) (Polynomial.monomial (2 * a) c))).coeff j').coeff i' ≠ 0 →
      i' % 2 = 0 ∧ j' % 2 = 0 := by
    intro c a b j' i' hnz'
    have hmon : Polynomial.monomial (2 * b) (Polynomial.monomial (2 * a) c) =
        C (C c) * C (X ^ 2) ^ a * (X ^ 2) ^ b := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
        pow_mul, pow_mul, map_mul, map_pow]
    rw [hmon, shiftBi_mul, shiftBi_mul, shiftBi_C, shiftBi_pow, shiftBi_C, shiftBi_pow, shiftBi_pow, shiftBi_X] at hnz'
    simp only [Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, ← map_pow] at hnz'
    rw [hpow2X (C x0) X, hpow2Y (C (C y0)) X,
      add_pow (C x0 ^ 2) (X ^ 2) a, add_pow (C (C y0) ^ 2) (X ^ 2) b] at hnz'
    have hrew : C (C c) * C (∑ l ∈ Finset.range (a + 1), (C x0 ^ 2) ^ l * (X ^ 2) ^ (a - l) * ((a.choose l : ℕ) : Polynomial F)) *
        (∑ m ∈ Finset.range (b + 1), (C (C y0) ^ 2) ^ m * (X ^ 2) ^ (b - m) * ((b.choose m : ℕ) : BiPoly F)) =
        ∑ m ∈ Finset.range (b + 1),
          C (∑ l ∈ Finset.range (a + 1),
            C (c * (x0 ^ 2) ^ l * (a.choose l : F) * ((y0 ^ 2) ^ m * (b.choose m : F))) * X ^ (2 * (a - l))) *
            X ^ (2 * (b - m)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
      have hm_eq : (C (C y0) ^ 2 : BiPoly F) ^ m * (X ^ 2) ^ (b - m) * ((b.choose m : ℕ) : BiPoly F) =
          C (C ((y0 ^ 2) ^ m * (b.choose m : F))) * X ^ (2 * (b - m)) := by
        simp only [map_mul, map_pow, map_natCast, ← pow_mul]; ring
      rw [hm_eq, ← mul_assoc, ← map_mul, ← map_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1; congr 1
      apply Finset.sum_congr rfl; intro l _
      simp only [map_mul, map_pow, map_natCast, ← pow_mul]; ring
    rw [hrew, finset_sum_coeff, finset_sum_coeff] at hnz'
    obtain ⟨m, _, hmnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz'
    rw [Polynomial.coeff_C_mul_X_pow] at hmnz
    split_ifs at hmnz with hjm
    · rw [finset_sum_coeff] at hmnz
      obtain ⟨l, _, hlnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmnz
      rw [Polynomial.coeff_C_mul_X_pow] at hlnz
      split_ifs at hlnz with hil
      · omega
      · exact absurd rfl hlnz
    · simp at hmnz
  have hp_sum : p = ∑ b ∈ p.support, ∑ a ∈ (p.coeff b).support,
      Polynomial.monomial b (Polynomial.monomial a ((p.coeff b).coeff a)) := by
    conv_lhs => rw [p.as_sum_support]
    apply Finset.sum_congr rfl; intro b _
    conv_lhs => rw [(p.coeff b).as_sum_support]
    rw [map_sum]
  rw [hp_sum] at hnz
  have hsh_sum : shiftBi x0 y0 (∑ b ∈ p.support, ∑ a ∈ (p.coeff b).support,
      Polynomial.monomial b (Polynomial.monomial a ((p.coeff b).coeff a))) =
      ∑ b ∈ p.support, ∑ a ∈ (p.coeff b).support,
        shiftBi x0 y0 (Polynomial.monomial b (Polynomial.monomial a ((p.coeff b).coeff a))) := by
    unfold shiftBi; simp only [Polynomial.map_sum, Polynomial.sum_comp]
  rw [hsh_sum, finset_sum_coeff, finset_sum_coeff] at hnz
  obtain ⟨b, _, hbnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  rw [finset_sum_coeff, finset_sum_coeff] at hbnz
  obtain ⟨a, ha, hanz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hbnz
  have hpar := hp b a (Polynomial.mem_support_iff.mp ha)
  have hb2 : b = 2 * (b / 2) := by omega
  have ha2 : a = 2 * (a / 2) := by omega
  rw [hb2, ha2] at hanz
  exact hsh_monom _ (a / 2) (b / 2) j i hanz

lemma shiftBi_zero_zero {F : Type*} [Field F] (p : BiPoly F) :
    shiftBi (0 : F) 0 p = p := by
  unfold shiftBi
  have hcomp : Polynomial.compRingHom (C (0 : F) + X) = RingHom.id (Polynomial F) := by
    ext <;> simp [Polynomial.compRingHom]
  rw [hcomp, Polynomial.map_id, map_zero, map_zero, zero_add, Polynomial.comp_X]

/-- **Table 3 Subcase 2A Local Resultant Divisibility (`kerD2_resY_f0_g_2A_ord`):**
When `g = C qX * gPrim` with `gPrim ∈ F[X^2, Y^2]` dividing `f1, f2`, let `A0` be the even-`Y` part
of `Fpoly.coeff 0` (`f0 = expand 2 A0 + Y * expand 2 C0`). Then for any even `dStarEff = 2 * halfDs`
with `2 * A0.natDegree ≤ dStarEff`, `(Fpoly.coeff 1).natDegree ≤ dStarEff`, and `(Fpoly.coeff 2).natDegree + 2 ≤ dStarEff`:
`(X - C x0) ^ t3Vrf0Ord 3 g.natDegree dStarEff k (biMult x0 y0 g) ∣ g.leadingCoeff ^ (dStarEff - 2 * A0.natDegree) * Res_Y(expand 2 A0, g)`! -/
theorem kerD2_resY_f0_g_2A_ord {F : Type*} [Field F] [CharP F 2] {wY W_F k : ℕ} (hwY : 0 < wY)
    (x0 y0 : F) (f_coord : KerDIdx wY W_F 2 → F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) k)
    (qX : Polynomial F) (gPrim A0 : BiPoly F)
    (hqX_ne : qX ≠ 0) (hgP_ne : gPrim ≠ 0)
    (hgP_X2Y2 : ∀ j i, (gPrim.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0)
    (hA0_c : ∀ j, A0.coeff j = ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 0).coeff (2 * j))
    (hdvd1 : gPrim ∣ (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1)
    (hdvd2 : gPrim ∣ (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2)
    (dStarEff : ℕ) (hds_ev : dStarEff % 2 = 0)
    (hA0_d : 2 * A0.natDegree ≤ dStarEff)
    (hf1_d : ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree ≤ dStarEff)
    (hf2_d : ((∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 2).natDegree + 2 ≤ dStarEff) :
    let g : BiPoly F := C qX * gPrim
    let dg := g.natDegree
    let dA := (Polynomial.expand (Polynomial F) 2 A0).natDegree
    (X - C x0) ^ t3Vrf0Ord 3 dg dStarEff k (biMult x0 y0 g) ∣
      g.leadingCoeff ^ (dStarEff - dA) *
        Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) g dA dg := by
  intro g dg dA
  by_cases hk0 : k = 0
  · subst hk0; simp [t3Vrf0Ord]
  set Fpoly : ContactPoly F := ∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1
  set rr : ℕ := biMult x0 y0 g
  set rq : ℕ := biMult x0 y0 (C qX)
  set rre : ℕ := biMult x0 y0 gPrim
  have hrr_eq : rr = rq + rre := biMult_mul x0 y0 (Polynomial.C_ne_zero.mpr hqX_ne) hgP_ne
  have hrre_ev : rre % 2 = 0 := biMult_even_of_in_X2_Y2 x0 y0 gPrim hgP_X2Y2
  have hdg_eq : dg = gPrim.natDegree := by
    dsimp [dg, g]; rw [Polynomial.natDegree_C_mul hqX_ne]
  have hdA_eq : dA = 2 * A0.natDegree := by
    dsimp [dA]; rw [Polynomial.natDegree_expand, mul_comm]
  have hfold_le_mem : ∀ (l : List ℕ) (f : ℕ → ℕ) (init x : ℕ), x ∈ l →
      l.foldl (fun acc y => Nat.min acc (f y)) init ≤ f x := by
    intro l f; induction l with
    | nil => intro _ _ hx; cases hx
    | cons a t ih =>
        intro init x hx; simp only [List.foldl_cons, List.mem_cons] at hx ⊢
        rcases hx with rfl | ht
        · have hle : ∀ (l' : List ℕ) (z : ℕ), l'.foldl (fun acc y => Nat.min acc (f y)) z ≤ z := by
            intro l'; induction l' with
            | nil => intro _; exact le_rfl
            | cons b bs ih' => intro z; simp only [List.foldl_cons]; exact (ih' _).trans (Nat.min_le_left _ _)
          exact (hle t _).trans (Nat.min_le_right _ _)
        · exact ih _ x ht
  have hrq_mem : rq ∈ (List.range (rr + 1)).filter (fun q => (rr - q) % 2 == 0) := by
    rw [List.mem_filter]; refine ⟨List.mem_range.mpr (by omega), ?_⟩
    simp only [beq_iff_eq, show rr - rq = rre by omega]; exact hrre_ev
  have hk0b : (k == 0) = false := beq_false_of_ne hk0
  have hle_evalRq : t3Vrf0Ord 3 dg dStarEff k rr ≤
      max ((2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2 - 2 * dg) + dStarEff * rq)
        (((List.range (dStarEff + 1)).map (fun d0 =>
          resOrdExact d0 (2 * k - 2) dg rre + (dStarEff - d0) * (rre - dg))).foldl Nat.min
            (resOrdExact 0 (2 * k - 2) dg rre + dStarEff * (rre - dg)) + dStarEff * rq) := by
    unfold t3Vrf0Ord; simp only [hk0b, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, resOrdWeighted2Fast_eq]
    let evalRqFn : ℕ → ℕ := fun q =>
      max ((2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) (rr - q) 2 - 2 * dg) + dStarEff * q)
        (((List.range (dStarEff + 1)).map (fun d0 =>
          resOrdExact d0 (2 * k - 2) dg (rr - q) + (dStarEff - d0) * ((rr - q) - dg))).foldl Nat.min
            (resOrdExact 0 (2 * k - 2) dg (rr - q) + dStarEff * ((rr - q) - dg)) + dStarEff * q)
    have h := hfold_le_mem ((List.range (rr + 1)).filter (fun q => (rr - q) % 2 == 0))
      evalRqFn (evalRqFn rr) rq hrq_mem
    simpa only [evalRqFn, show rr - rq = rre by omega] using h
  refine (pow_dvd_pow (X - C x0) hle_evalRq).trans ?_
  have hfac_q : g.leadingCoeff ^ (dStarEff - dA) *
      Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) g dA dg =
      qX ^ dStarEff * (gPrim.leadingCoeff ^ (dStarEff - dA) *
        Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg) := by
    have hlc_g : g.leadingCoeff = qX * gPrim.leadingCoeff := by
      dsimp [g]; rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    have hres_g : Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) g dA dg =
        qX ^ dA * Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg := by
      dsimp [g]; rw [Polynomial.resultant_C_mul_right]
    rw [hlc_g, mul_pow, hres_g]
    have hsum_d : (dStarEff - dA) + dA = dStarEff := by omega
    calc qX ^ (dStarEff - dA) * gPrim.leadingCoeff ^ (dStarEff - dA) *
          (qX ^ dA * Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg)
        = (qX ^ (dStarEff - dA) * qX ^ dA) * (gPrim.leadingCoeff ^ (dStarEff - dA) *
            Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg) := by ring
      _ = _ := by rw [← pow_add, hsum_d]
  rw [hfac_q]
  have hqX_dvd : (X - C x0) ^ (dStarEff * rq) ∣ qX ^ dStarEff := by
    have h1 := pow_dvd_leadingCoeff_of_biMultGE x0 y0 (C qX) 0 rq (Polynomial.natDegree_C qX) (biMultGE_biMult x0 y0 (C qX))
    simp only [Nat.sub_zero, Polynomial.leadingCoeff_C] at h1
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h1 dStarEff
  -- Shared setup for BOTH Branch 1 and Branch 2:
  -- Express Fpoly.coeff 0, 1, 2 explicitly from kerDBasisPoly to extract C0 = dXBi(f1) and parities!
  have hf_terms :
      (Fpoly.coeff 0 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 0 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0) ∧
      (Fpoly.coeff 1 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 1 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 1 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0) ∧
      (Fpoly.coeff 2 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 2 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 1 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0) := by
    refine ⟨?_, ?_, ?_⟩ <;>
    · dsimp [Fpoly]; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
      have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
      rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
        ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      · simp only [true_and, false_and, and_false, zero_ne_one, one_ne_zero,
          show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, show (0:ℕ) ≠ 2 by omega, show (1:ℕ) ≠ 2 by omega, ↓reduceIte]
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        first
        | (rw [pow_zero, pow_zero, one_mul, one_mul,
            show C (C (C (f_coord ⟨(0,0,b1,a1),he⟩))) * ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(0,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
            Polynomial.coeff_C]; simp)
        | (rw [pow_one, pow_zero, mul_one,
            show C (C (C (f_coord ⟨(1,0,b1,a1),he⟩))) * (X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              X * C (C (C (f_coord ⟨(1,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring];
            first | exact Polynomial.coeff_X_mul_zero _ | (rw [Polynomial.coeff_X_mul, Polynomial.coeff_C]; simp))
        | (rw [pow_zero, mul_one, sq,
            show C (C (C (f_coord ⟨(2,0,b1,a1),he⟩))) * (X * X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              X * (X * C (C (C (f_coord ⟨(2,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)) by simp only [map_mul, map_pow]; ring];
            first | exact Polynomial.coeff_X_mul_zero _
                  | (rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero])
                  | (rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul, Polynomial.coeff_C]; simp))
        | (rw [pow_zero, pow_one, one_mul,
            show C (C (C (f_coord ⟨(0,1,b1,a1),he⟩))) * ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
              X * C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow, map_add]; ring,
            Polynomial.coeff_add, Polynomial.coeff_C];
            simp only [Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul, Polynomial.coeff_C,
              one_ne_zero, zero_ne_one, show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, ↓reduceIte,
              add_zero, zero_add])
        | (rw [pow_one, pow_one,
            show C (C (C (f_coord ⟨(1,1,b1,a1),he⟩))) * (X * (C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              X * C (C (C (f_coord ⟨(1,1,b1,a1),he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
              X * (X * C (C (C (f_coord ⟨(1,1,b1,a1),he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)) by simp only [map_mul, map_pow, map_add]; ring,
            Polynomial.coeff_add];
            simp only [Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul, Polynomial.coeff_C,
              one_ne_zero, zero_ne_one, show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, ↓reduceIte,
              add_zero, zero_add])
  -- Define C0_exp = dXBi (Fpoly.coeff 1) and C1_exp = odd-Y part of Fpoly.coeff 1 = dXBi (Fpoly.coeff 2)!
  set C0_exp : BiPoly F := dXBi (Fpoly.coeff 1)
  have hC0_sum : C0_exp = ∑ e : KerDIdx wY W_F 2,
      if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0 := by
    have hmon_xev : ∀ (c : F) (a1 b1 : ℕ), dXBi (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) = 0 := by
      intro c a1 b1; apply dXBi_eq_zero_of_xev; intro j i hi
      rw [show C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C (C c * X ^ (2 * a1)) * X ^ (2 * b1) by
        simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      · simp
    have hmon_Y_xev : ∀ (c : F) (a1 b1 : ℕ), dXBi (C (C c) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) = 0 := by
      intro c a1 b1; apply dXBi_eq_zero_of_xev; intro j i hi
      rw [show C (C c) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C (C c * X ^ (2 * a1)) * X ^ (2 * b1 + 1) by
        simp only [map_mul, map_pow, ← pow_mul, pow_succ]; ring, Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      · simp
    have hmon_X_dX : ∀ (c : F) (a1 b1 : ℕ),
        dXBi (C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) =
          C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 := by
      intro c a1 b1
      rw [show C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C X * (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by ring,
        dXBi_mul, hmon_xev, mul_zero, add_zero]
      have hdCX : dXBi (C X : BiPoly F) = 1 := by
        rw [Polynomial.ext_iff]; intro j; rw [coeff_dXBi, Polynomial.coeff_C, Polynomial.coeff_one]; split_ifs <;> simp
      rw [hdCX, one_mul]
    rw [Polynomial.ext_iff]; intro j; rw [coeff_dXBi, hf_terms.2.1, finset_sum_coeff, map_sum, finset_sum_coeff]
    apply Finset.sum_congr rfl; intro e _
    by_cases h1 : e.1.1 = 1 ∧ e.1.2.1 = 0
    · rw [if_pos h1, if_neg (by omega), ← coeff_dXBi, hmon_xev, Polynomial.coeff_zero]
    · rw [if_neg h1]
      by_cases h2 : e.1.1 = 0 ∧ e.1.2.1 = 1
      · rw [if_pos h2, if_pos h2, ← coeff_dXBi, hmon_X_dX]
      · rw [if_neg h2, if_neg h2]
        by_cases h3 : e.1.1 = 1 ∧ e.1.2.1 = 1
        · rw [if_pos h3, ← coeff_dXBi, hmon_Y_xev, Polynomial.coeff_zero]
        · rw [if_neg h3, Polynomial.coeff_zero, Polynomial.derivative_zero]
  have hf0_decomp : Fpoly.coeff 0 = Polynomial.expand (Polynomial F) 2 A0 + X * C0_exp := by
    have hA0_sum : Polynomial.expand (Polynomial F) 2 A0 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 0 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0 := by
      rw [Polynomial.ext_iff]; intro j; rw [Polynomial.coeff_expand (by norm_num : 0 < 2)]
      split_ifs with hj
      · rw [hA0_c, show 2 * (j / 2) = j by omega, hf_terms.1, finset_sum_coeff, finset_sum_coeff]
        apply Finset.sum_congr rfl; intro e _
        by_cases he1 : e.1.1 = 0 ∧ e.1.2.1 = 0
        · rw [if_pos he1, if_pos he1]
        · rw [if_neg he1, if_neg he1]
          by_cases he2 : e.1.1 = 0 ∧ e.1.2.1 = 1
          · rw [if_pos he2,
              show C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
                C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1 + 1) by
                simp only [map_mul, map_pow, ← pow_mul, pow_succ]; ring,
              Polynomial.coeff_C_mul_X_pow, if_neg (by omega), Polynomial.coeff_zero]
          · rw [if_neg he2]
      · symm; rw [finset_sum_coeff]; apply Finset.sum_eq_zero; intro e _
        split_ifs
        · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
              C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
              simp only [map_mul, map_pow, ← pow_mul],
            Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
        · simp
    rw [hf_terms.1, hA0_sum, hC0_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _
    by_cases h1 : e.1.1 = 0 ∧ e.1.2.1 = 0
    · rw [if_pos h1, if_pos h1, if_neg (by omega), mul_zero, add_zero]
    · rw [if_neg h1, if_neg h1, zero_add]
      by_cases h2 : e.1.1 = 0 ∧ e.1.2.1 = 1
      · rw [if_pos h2, if_pos h2]; ring
      · rw [if_neg h2, if_neg h2, mul_zero]
  have hdvd_C0 : gPrim ∣ C0_exp := by
    rcases hdvd1 with ⟨q1, hq1⟩
    refine ⟨dXBi q1, ?_⟩
    dsimp [C0_exp]; rw [hq1, dXBi_mul, dXBi_eq_zero_of_xev gPrim (fun j i hi => by
      by_contra hnz; have := hgP_X2Y2 j i hnz; omega), zero_mul, zero_add]
  have hC0_deg : C0_exp.natDegree ≤ dStarEff := (natDegree_dXBi_le (Fpoly.coeff 1)).trans hf1_d
  have hA0_X2Y2 : ∀ j i, ((Polynomial.expand (Polynomial F) 2 A0).coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    intro j i hnz
    rw [Polynomial.coeff_expand (by norm_num : 0 < 2)] at hnz
    split_ifs at hnz with hj
    · rw [hA0_c, hf_terms.1, finset_sum_coeff, finset_sum_coeff] at hnz
      obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
      split_ifs at henz
      · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
            C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
            simp only [map_mul, map_pow, ← pow_mul],
          Polynomial.coeff_C_mul_X_pow] at henz
        split_ifs at henz
        · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
        · simp at henz
      · rw [show C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
            C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1 + 1) by
            simp only [map_mul, map_pow, ← pow_mul, pow_succ]; ring,
          Polynomial.coeff_C_mul_X_pow, if_neg (by omega)] at henz; simp at henz
      · simp at henz
    · simp at hnz
  have hC0_X2Y2 : ∀ j i, (C0_exp.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    intro j i hnz
    rw [hC0_sum, finset_sum_coeff, finset_sum_coeff] at hnz
    obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    split_ifs at henz
    · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
          C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
          simp only [map_mul, map_pow, ← pow_mul],
        Polynomial.coeff_C_mul_X_pow] at henz
      split_ifs at henz
      · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
      · simp at henz
    · simp at henz
  -- Define A0_sh_eff = even-t part of shiftBi x0 y0 (Fpoly.coeff 0)!
  set A0_sh_eff : BiPoly F :=
    shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0) + C (C y0) * shiftBi x0 y0 C0_exp
  have hsh0_split : shiftBi x0 y0 (Fpoly.coeff 0) = A0_sh_eff + X * shiftBi x0 y0 C0_exp := by
    dsimp [A0_sh_eff]; rw [hf0_decomp, shiftBi_add, shiftBi_mul, shiftBi_X]; ring
  have hA0sh_X2Y2 : ∀ j i, (A0_sh_eff.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    intro j i hnz
    dsimp [A0_sh_eff] at hnz
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul] at hnz
    by_cases h1 : ((shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0)).coeff j).coeff i ≠ 0
    · exact shiftBi_in_X2_Y2 x0 y0 _ hA0_X2Y2 j i h1
    · push Not at h1; rw [h1, zero_add] at hnz
      exact shiftBi_in_X2_Y2 x0 y0 _ hC0_X2Y2 j i (right_ne_zero_of_mul hnz)
  have hsh_deg_le : ∀ p : BiPoly F, (shiftBi x0 y0 p).natDegree ≤ p.natDegree := by
    intro p; unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
    have hm : (p.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ p.natDegree := Polynomial.natDegree_map_le
    have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
      (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
    nlinarith only [hm, hX]
  have hshg_deg : (shiftBi x0 y0 gPrim).natDegree = dg := by
    rw [hdg_eq]; unfold shiftBi
    have hinj : Function.Injective (Polynomial.compRingHom (C x0 + X) : Polynomial F →+* Polynomial F) := by
      intro p q hpq; have := congrArg (fun r => r.comp (X - C x0)) hpq
      simpa [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.comp_X] using this
    have h1 : (gPrim.map (Polynomial.compRingHom (C x0 + X))).natDegree = gPrim.natDegree :=
      Polynomial.natDegree_map_eq_of_injective hinj _
    have hcomp : ∀ (p : BiPoly F) (c : Polynomial F), (p.comp (C c + X)).natDegree = p.natDegree := by
      intro p c; apply le_antisymm
      · refine Polynomial.natDegree_comp_le.trans ?_
        have h2 : (C c + X : BiPoly F).natDegree ≤ 1 :=
          (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
        nlinarith only [h2]
      · have hb : ((p.comp (C c + X)).comp (C (-c) + X)).natDegree = p.natDegree := by
          rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
            show C c + (C (-c) + X) = X by rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add],
            Polynomial.comp_X]
        rw [← hb]; refine Polynomial.natDegree_comp_le.trans ?_
        have h2 : (C (-c) + X : BiPoly F).natDegree ≤ 1 :=
          (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
        nlinarith only [h2]
    rw [hcomp, h1]
  have hlc_sh : (shiftBi x0 y0 gPrim).leadingCoeff = gPrim.leadingCoeff.comp (C x0 + X) := by
    rw [Polynomial.leadingCoeff, hshg_deg]; unfold shiftBi
    have hmap_deg : (gPrim.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ dg := by
      rw [hdg_eq]; exact Polynomial.natDegree_map_le
    rw [coeff_comp_C_add_X_top y0 _ dg hmap_deg, Polynomial.coeff_map, Polynomial.leadingCoeff, hdg_eq]; rfl
  have hA0sh_deg : A0_sh_eff.natDegree ≤ dStarEff := by
    dsimp [A0_sh_eff]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (hsh_deg_le _).trans (by omega)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans ((hsh_deg_le _).trans hC0_deg)
  -- Key resultant invariance: Res_t(A0_sh_eff, shiftBi gPrim; dStarEff, dg) = (shiftBi gPrim).lc^(dStarEff - dA) * Res_t(shiftBi(expand 2 A0), shiftBi gPrim; dA, dg)!
  have hres_eff : Polynomial.resultant A0_sh_eff (shiftBi x0 y0 gPrim) dStarEff dg =
      (gPrim.leadingCoeff ^ (dStarEff - dA) *
        Polynomial.resultant (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg).comp (C x0 + X) := by
    rcases hdvd_C0 with ⟨qC, hqC⟩
    have hA0_mod : A0_sh_eff = shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0) +
        (C (C y0) * shiftBi x0 y0 qC) * shiftBi x0 y0 gPrim := by
      dsimp [A0_sh_eff]; rw [hqC, shiftBi_mul]; ring
    have hdeg_shA : (shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0)).natDegree ≤ dStarEff :=
      (hsh_deg_le _).trans (by omega)
    have hneg1 : (-1 : Polynomial F) = 1 := CharTwo.neg_eq 1
    conv_lhs => rw [hA0_mod,
      resultant_add_mul_right_deg _ _ _ dStarEff dg hdeg_shA (by rwa [← hA0_mod]) hshg_deg,
      show dStarEff = dA + (dStarEff - dA) by omega,
      Polynomial.resultant_add_left_deg _ _ dA dg (dStarEff - dA) (hsh_deg_le _),
      show (shiftBi x0 y0 gPrim).coeff dg = (shiftBi x0 y0 gPrim).leadingCoeff by rw [Polynomial.leadingCoeff, hshg_deg],
      hlc_sh, resultant_shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 A0) gPrim dA dg le_rfl (le_of_eq hdg_eq.symm),
      hneg1, one_pow, one_mul, ← Polynomial.pow_comp, ← Polynomial.mul_comp]
  have hdvd_max : ∀ (a b : ℕ) (R : Polynomial F),
      (X - C x0) ^ a ∣ R → (X - C x0) ^ b ∣ R → (X - C x0) ^ max a b ∣ R := by
    intro a b R ha hb; rcases le_total a b with h | h
    · rwa [Nat.max_eq_right h]
    · rwa [Nat.max_eq_left h]
  obtain ⟨hbm0, _, _, Pe, Po, hdecomp, _, _, hPe_ord, _, _⟩ := kerD2_local_ords hwY x0 y0 f_coord hvan
  apply hdvd_max
  · -- Branch 1: vk_part + dStarEff * rq!
    rw [add_comm, pow_add]; apply mul_dvd_mul hqX_dvd
    apply X_sub_C_pow_dvd_of_comp_shift x0 _ _
    rw [← hres_eff]
    -- Write A0_sh_eff = expand 2 A0_loc and shiftBi gPrim = expand 2 g1!
    obtain ⟨A0_loc, hA0_loc_eq, hA0_loc_deg, hA0_loc_c⟩ :=
      exists_expand2_of_even_Y A0_sh_eff (fun j hj => by ext i; by_contra hnz; have := hA0sh_X2Y2 j i hnz; omega)
    have hgP_sh_X2Y2 := shiftBi_in_X2_Y2 x0 y0 gPrim hgP_X2Y2
    obtain ⟨g1, hg1_eq, _, hg1_c⟩ :=
      exists_expand2_of_even_Y (shiftBi x0 y0 gPrim) (fun j hj => by ext i; by_contra hnz; have := hgP_sh_X2Y2 j i hnz; omega)
    have hdg_ev : dg % 2 = 0 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hg1_eq, hshg_deg] at h2; omega
    have hg1_deg : g1.natDegree = dg / 2 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hg1_eq, hshg_deg] at h2; omega
    have hg1_ord : weightedOrdGE 2 rre g1 := by
      intro j; rw [hg1_c j]
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one x0 y0 gPrim rre).mp (biMultGE_biMult x0 y0 gPrim) (2 * j)
    -- Construct A2_loc = evenPartX of the even-t coefficients of shiftBi f2, and prove g1 ∣ A2_loc!
    have hf2_evY : ∀ j, j % 2 = 1 → (Fpoly.coeff 2).coeff j = 0 := by
      intro j hj; rw [hf_terms.2.2, finset_sum_coeff]
      apply Finset.sum_eq_zero; intro e _; split_ifs
      · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
            C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
            simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      · rw [show C (C (f_coord e)) * C X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
            C (C (f_coord e) * X * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
            simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      · simp
    have hshf2_evY : ∀ j, j % 2 = 1 → (shiftBi x0 y0 (Fpoly.coeff 2)).coeff j = 0 := by
      obtain ⟨f2h, hf2h_eq, _, _⟩ := exists_expand2_of_even_Y (Fpoly.coeff 2) hf2_evY
      have hsh_exp : shiftBi x0 y0 (Fpoly.coeff 2) =
          Polynomial.expand (Polynomial F) 2
            ((f2h.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)) := by
        rw [hf2h_eq, shiftBi_expand2]
      intro j hj; rw [hsh_exp, Polynomial.coeff_expand (by norm_num : 0 < 2), if_neg (by omega)]
    obtain ⟨f2_loc, hf2_loc_eq, _, hf2_loc_c⟩ := exists_expand2_of_even_Y (shiftBi x0 y0 (Fpoly.coeff 2)) hshf2_evY
    set A2_loc : BiPoly F := ∑ j ∈ f2_loc.support, Polynomial.monomial j (evenPartX (f2_loc.coeff j))
    have hA2_loc_c : ∀ j, A2_loc.coeff j = evenPartX (f2_loc.coeff j) := by
      intro j; dsimp [A2_loc]; rw [finset_sum_coeff]
      by_cases hj : j ∈ f2_loc.support
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hne; simp [Polynomial.coeff_monomial, hne]
        · intro h; exact absurd hj h
      · rw [Finset.sum_eq_zero, Polynomial.notMem_support_iff.mp hj]
        · ext n; rw [coeff_evenPartX]; split_ifs <;> simp
        · intro k hk; simp [Polynomial.coeff_monomial, show k ≠ j by intro heq; subst heq; exact hj hk]
    have hg1_dvd_A2 : g1 ∣ A2_loc := by
      rcases hdvd2 with ⟨h2, hh2⟩
      have hsh2_eq : shiftBi x0 y0 (Fpoly.coeff 2) = shiftBi x0 y0 gPrim * shiftBi x0 y0 h2 := by
        rw [hh2, shiftBi_mul]
      -- Show shiftBi h2 also has only even Y-powers (since shiftBi gPrim ≠ 0 and shiftBi f2 have only even Y-powers)!
      have hshh2_ev : ∀ j, j % 2 = 1 → (shiftBi x0 y0 h2).coeff j = 0 := by
        by_contra hne; push Not at hne
        let oddS := (shiftBi x0 y0 h2).support.filter fun j => j % 2 = 1
        have hodd_ne : oddS.Nonempty := by
          obtain ⟨j, hj1, hj2⟩ := hne
          exact ⟨j, Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr hj2, hj1⟩⟩
        let jm := oddS.max' hodd_ne
        have hjm_m := Finset.mem_filter.mp (Finset.max'_mem oddS hodd_ne)
        have hjm_nz : (shiftBi x0 y0 h2).coeff jm ≠ 0 := Polynomial.mem_support_iff.mp hjm_m.1
        have hjm_odd : jm % 2 = 1 := hjm_m.2
        have hprod_nz : (shiftBi x0 y0 gPrim * shiftBi x0 y0 h2).coeff (dg + jm) ≠ 0 := by
          rw [Polynomial.coeff_mul, Finset.sum_eq_single (dg, jm)]
          have hlc : (shiftBi x0 y0 gPrim).coeff dg ≠ 0 := by
            rw [← hshg_deg]; exact Polynomial.leadingCoeff_ne_zero.mpr
              (fun h => hgP_ne ((shiftBi_eq_zero_iff x0 y0 gPrim).mp h))
          exact mul_ne_zero hlc hjm_nz
          · intro ⟨a, b⟩ hab hneq
            have hsum : a + b = dg + jm := Finset.mem_antidiagonal.mp hab
            by_cases ha : dg < a
            · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
            · by_cases ha_odd : a % 2 = 1
              · have : (shiftBi x0 y0 gPrim).coeff a = 0 := by
                  ext i; by_contra hnz; have := hgP_sh_X2Y2 a i hnz; omega
                rw [this, zero_mul]
              · have hb_gt : jm < b := by by_contra hle; apply hneq; ext <;> dsimp <;> omega
                have hb_odd : b % 2 = 1 := by omega
                have hb_z : (shiftBi x0 y0 h2).coeff b = 0 := by
                  by_contra hbnz
                  have hbm : b ∈ oddS := Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr hbnz, hb_odd⟩
                  have := Finset.le_max' oddS b hbm; omega
                rw [hb_z, mul_zero]
          · intro h; simp at h
        rw [← hsh2_eq] at hprod_nz
        exact hprod_nz (hshf2_evY (dg + jm) (by omega))
      obtain ⟨h2_loc, hh2_loc_eq, _, _⟩ := exists_expand2_of_even_Y (shiftBi x0 y0 h2) hshh2_ev
      have hf2_fac : f2_loc = g1 * h2_loc := by
        have h1 : Polynomial.expand (Polynomial F) 2 f2_loc = Polynomial.expand (Polynomial F) 2 (g1 * h2_loc) := by
          rw [map_mul, ← hf2_loc_eq, ← hg1_eq, ← hh2_loc_eq, hsh2_eq]
        rw [Polynomial.ext_iff]; intro j
        have := congrArg (fun p : BiPoly F => p.coeff (2 * j)) h1
        simp only [Polynomial.coeff_expand (by norm_num : 0 < 2), dvd_mul_right, ↓reduceIte,
          Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at this
        exact this
      refine ⟨∑ j ∈ h2_loc.support, Polynomial.monomial j (evenPartX (h2_loc.coeff j)), ?_⟩
      rw [Polynomial.ext_iff]; intro j
      rw [hA2_loc_c, hf2_fac, Polynomial.coeff_mul, Polynomial.coeff_mul]
      have hlin : ∀ (S : Finset (ℕ × ℕ)) (fn : ℕ × ℕ → Polynomial F),
          evenPartX (∑ x ∈ S, fn x) = ∑ x ∈ S, evenPartX (fn x) := by
        intro S fn; ext n; rw [coeff_evenPartX, finset_sum_coeff, finset_sum_coeff]
        split_ifs with hn
        · apply Finset.sum_congr rfl; intro x _; rw [coeff_evenPartX, if_pos hn]
        · symm; apply Finset.sum_eq_zero; intro x _; rw [coeff_evenPartX, if_neg hn]
      rw [hlin]
      apply Finset.sum_congr rfl; intro ⟨a, b⟩ _
      have hg1_xev : ∀ i, i % 2 = 1 → (g1.coeff a).coeff i = 0 := fun i hi => by
        rw [hg1_c a]; by_contra hnz; have := hgP_sh_X2Y2 (2 * a) i hnz; omega
      rw [evenPartX_mul_of_xev _ _ hg1_xev]
      congr 1; rw [finset_sum_coeff]
      by_cases hb : b ∈ h2_loc.support
      · rw [Finset.sum_eq_single b]
        · simp
        · intro k _ hne; simp [Polynomial.coeff_monomial, hne]
        · intro h; exact absurd hb h
      · rw [Finset.sum_eq_zero, Polynomial.notMem_support_iff.mp hb]
        · ext n; rw [coeff_evenPartX]; split_ifs <;> simp
        · intro k hk; simp [Polynomial.coeff_monomial, show k ≠ b by intro heq; subst heq; exact hb hk]
    -- Prove the EXACT identity Pe = C (X^2) * A0_loc + X * A2_loc directly from hdecomp!
    have hPe_exact : Pe = C (X ^ 2) * A0_loc + X * A2_loc := by
      -- First prove the char-2 cancellation between odd-Y of f1 and odd-X of f2!
      set C1_exp : BiPoly F := dXBi (Fpoly.coeff 2)
      have hC1_sum : C1_exp = ∑ e : KerDIdx wY W_F 2,
          if e.1.1 = 1 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0 := by
        have hmon_xev : ∀ (c : F) (a1 b1 : ℕ), dXBi (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) = 0 := by
          intro c a1 b1; apply dXBi_eq_zero_of_xev; intro j i hi
          rw [show C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C (C c * X ^ (2 * a1)) * X ^ (2 * b1) by
            simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow]
          split_ifs; · rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
          · simp
        have hmon_X_dX : ∀ (c : F) (a1 b1 : ℕ),
            dXBi (C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) =
              C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 := by
          intro c a1 b1
          rw [show C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 = C X * (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by ring,
            dXBi_mul, hmon_xev, mul_zero, add_zero]
          have hdCX : dXBi (C X : BiPoly F) = 1 := by
            rw [Polynomial.ext_iff]; intro j; rw [coeff_dXBi, Polynomial.coeff_C, Polynomial.coeff_one]; split_ifs <;> simp
          rw [hdCX, one_mul]
        rw [Polynomial.ext_iff]; intro j; rw [coeff_dXBi, hf_terms.2.2, finset_sum_coeff, map_sum, finset_sum_coeff]
        apply Finset.sum_congr rfl; intro e _
        by_cases h1 : e.1.1 = 2 ∧ e.1.2.1 = 0
        · rw [if_pos h1, if_neg (by omega), ← coeff_dXBi, hmon_xev, Polynomial.coeff_zero]
        · rw [if_neg h1]
          by_cases h2 : e.1.1 = 1 ∧ e.1.2.1 = 1
          · rw [if_pos h2, if_pos h2, ← coeff_dXBi, hmon_X_dX]
          · rw [if_neg h2, if_neg h2, Polynomial.coeff_zero, Polynomial.derivative_zero]
      have hC1_X2Y2 : ∀ j i, (C1_exp.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
        intro j i hnz
        rw [hC1_sum, finset_sum_coeff, finset_sum_coeff] at hnz
        obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
        split_ifs at henz
        · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
              C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
              simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow] at henz
          split_ifs at henz
          · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
          · simp at henz
        · simp at henz
      have hshC1_X2Y2 := shiftBi_in_X2_Y2 x0 y0 C1_exp hC1_X2Y2
      -- Odd-t part of shiftBi f1 = shiftBi C1_exp, and odd-s part of shiftBi f2 = shiftBi C1_exp!
      have hf1_odd_t : ∀ j i, ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff (2 * j + 1)).coeff i =
          ((shiftBi x0 y0 C1_exp).coeff (2 * j)).coeff i := by
        intro j i
        set A1_sum : BiPoly F := ∑ e : KerDIdx wY W_F 2,
          if e.1.1 = 1 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0
        have hf1_sp : Fpoly.coeff 1 = A1_sum + C X * C0_exp + X * C1_exp := by
          rw [hf_terms.2.1, hC0_sum, hC1_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e _
          by_cases h1 : e.1.1 = 1 ∧ e.1.2.1 = 0
          · rw [if_pos h1, if_pos h1, if_neg (by omega), if_neg (by omega), mul_zero, mul_zero, add_zero, add_zero]
          · rw [if_neg h1, if_neg h1, zero_add]
            by_cases h2 : e.1.1 = 0 ∧ e.1.2.1 = 1
            · rw [if_pos h2, if_pos h2, if_neg (by omega), mul_zero, add_zero]; ring
            · rw [if_neg h2, if_neg h2, mul_zero, zero_add]
              by_cases h3 : e.1.1 = 1 ∧ e.1.2.1 = 1
              · rw [if_pos h3, if_pos h3]; ring
              · rw [if_neg h3, if_neg h3, mul_zero]
        have hA1_X2Y2 : ∀ j' i', (A1_sum.coeff j').coeff i' ≠ 0 → i' % 2 = 0 ∧ j' % 2 = 0 := by
          intro j' i' hnz
          rw [finset_sum_coeff, finset_sum_coeff] at hnz
          obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
          split_ifs at henz
          · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
                C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
                simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow] at henz
            split_ifs at henz
            · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
            · simp at henz
          · simp at henz
        rw [hf1_sp, shiftBi_add, shiftBi_add, shiftBi_mul, shiftBi_mul, shiftBi_C, Polynomial.X_comp, shiftBi_X,
          add_mul (C (C y0))]
        have hz1 : (shiftBi x0 y0 A1_sum).coeff (2 * j + 1) = 0 := by
          ext i'; by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 A1_sum hA1_X2Y2 (2 * j + 1) i' hnz; omega
        have hz2 : (shiftBi x0 y0 C0_exp).coeff (2 * j + 1) = 0 := by
          ext i'; by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 C0_exp hC0_X2Y2 (2 * j + 1) i' hnz; omega
        have hz3 : (shiftBi x0 y0 C1_exp).coeff (2 * j + 1) = 0 := by
          ext i'; by_contra hnz; have := hshC1_X2Y2 (2 * j + 1) i' hnz; omega
        simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
          hz1, hz2, hz3, mul_zero, zero_add, Polynomial.coeff_zero]
      have hf2_odd_s : ∀ j i, ((shiftBi x0 y0 (Fpoly.coeff 2)).coeff (2 * j)).coeff (2 * i + 1) =
          ((shiftBi x0 y0 C1_exp).coeff (2 * j)).coeff (2 * i) := by
        intro j i
        set A2_sum : BiPoly F := ∑ e : KerDIdx wY W_F 2,
          if e.1.1 = 2 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 else 0
        have hf2_sp : Fpoly.coeff 2 = A2_sum + C X * C1_exp := by
          rw [hf_terms.2.2, hC1_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e _
          by_cases h1 : e.1.1 = 2 ∧ e.1.2.1 = 0
          · rw [if_pos h1, if_pos h1, if_neg (by omega), mul_zero, add_zero]
          · rw [if_neg h1, if_neg h1, zero_add]
            by_cases h2 : e.1.1 = 1 ∧ e.1.2.1 = 1
            · rw [if_pos h2, if_pos h2]; ring
            · rw [if_neg h2, if_neg h2, mul_zero]
        have hA2_X2Y2 : ∀ j' i', (A2_sum.coeff j').coeff i' ≠ 0 → i' % 2 = 0 ∧ j' % 2 = 0 := by
          intro j' i' hnz
          rw [finset_sum_coeff, finset_sum_coeff] at hnz
          obtain ⟨e, _, henz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
          split_ifs at henz
          · rw [show C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1 =
                C (C (f_coord e) * X ^ (2 * e.1.2.2.2)) * X ^ (2 * e.1.2.2.1) by
                simp only [map_mul, map_pow, ← pow_mul], Polynomial.coeff_C_mul_X_pow] at henz
            split_ifs at henz
            · rw [Polynomial.coeff_C_mul_X_pow] at henz; split_ifs at henz <;> [omega; exact absurd rfl henz]
            · simp at henz
          · simp at henz
        rw [hf2_sp, shiftBi_add, shiftBi_mul, shiftBi_C, Polynomial.X_comp, Polynomial.coeff_add,
          Polynomial.coeff_C_mul, add_mul, Polynomial.coeff_add, Polynomial.coeff_add,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
        have hz1 : ((shiftBi x0 y0 A2_sum).coeff (2 * j)).coeff (2 * i + 1) = 0 := by
          by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 A2_sum hA2_X2Y2 (2 * j) (2 * i + 1) hnz; omega
        have hz2 : ((shiftBi x0 y0 C1_exp).coeff (2 * j)).coeff (2 * i + 1) = 0 := by
          by_contra hnz; have := hshC1_X2Y2 (2 * j) (2 * i + 1) hnz; omega
        rw [hz1, hz2, mul_zero, zero_add, zero_add]
      ext j i
      have hc := congrArg (fun p : BiPoly F => (p.coeff (2 * j)).coeff i) hdecomp
      have hRHS_Pe : ((Polynomial.expand (Polynomial F) 2 Pe + X * Polynomial.expand (Polynomial F) 2 Po).coeff (2 * j)).coeff i =
          (Pe.coeff j).coeff i := by
        rw [Polynomial.coeff_add, Polynomial.coeff_expand (by norm_num : 0 < 2), if_pos ⟨j, rfl⟩,
          Nat.mul_div_cancel_left j (by norm_num)]
        have hXPo : (X * Polynomial.expand (Polynomial F) 2 Po).coeff (2 * j) = 0 := by
          cases j with
          | zero => rw [Polynomial.coeff_X_mul_zero]
          | succ j' => rw [show 2 * (j' + 1) = (2 * j' + 1) + 1 by omega, Polynomial.coeff_X_mul,
              Polynomial.coeff_expand (by norm_num : 0 < 2), if_neg (by omega)]
        rw [hXPo, add_zero]
      rw [hRHS_Pe] at hc
      rw [← hc]
      -- Evaluate LHS at (2 * j, i) vs (C (X^2) * A0_loc + X * A2_loc) at (j, i)!
      have hL1 : ((shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2)).coeff (2 * j)).coeff i =
          ((C (X ^ 2) * A0_loc).coeff j).coeff i := by
        rw [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, mul_comm _ (X ^ 2), Polynomial.coeff_X_pow_mul',
          Polynomial.coeff_X_pow_mul']
        split_ifs with hi2
        · rw [hsh0_split, Polynomial.coeff_add, hA0_loc_c j]
          have hXC0 : (X * shiftBi x0 y0 C0_exp).coeff (2 * j) = 0 := by
            cases j with
            | zero => rw [Polynomial.coeff_X_mul_zero]
            | succ j' =>
                rw [show 2 * (j' + 1) = (2 * j' + 1) + 1 by omega, Polynomial.coeff_X_mul]
                ext i'; by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 C0_exp hC0_X2Y2 (2 * j' + 1) i' hnz; omega
          rw [hXC0, add_zero]
        · rfl
      rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.coeff_add, Polynomial.coeff_add, hL1]
      -- Now match (shiftBi f1 * (C X * X) + shiftBi f2 * X^2) at (2*j, i) with (X * A2_loc) at (j, i)!
      cases j with
      | zero =>
          have hz1 : ((shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X)).coeff 0) = 0 := by
            rw [← mul_assoc, Polynomial.coeff_mul_X_zero]
          have hz2 : ((shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2).coeff 0) = 0 := by
            rw [mul_comm, Polynomial.coeff_X_pow_mul']; simp
          rw [mul_zero, hz1, hz2, Polynomial.coeff_X_mul_zero, Polynomial.coeff_zero, add_zero, add_zero]
      | succ j' =>
          have h1 : ((shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X)).coeff (2 * (j' + 1))).coeff i =
              if i = 0 then 0 else ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff (2 * j' + 1)).coeff (i - 1) := by
            rw [← mul_assoc, show 2 * (j' + 1) = (2 * j' + 1) + 1 by omega, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]
            cases i with
            | zero => rw [Polynomial.coeff_mul_X_zero]; rfl
            | succ i' => rw [Polynomial.coeff_mul_X]; simp
          have h2 : ((shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2).coeff (2 * (j' + 1))).coeff i =
              ((shiftBi x0 y0 (Fpoly.coeff 2)).coeff (2 * j')).coeff i := by
            rw [mul_comm, Polynomial.coeff_X_pow_mul', if_pos (by omega), show 2 * (j' + 1) - 2 = 2 * j' by omega]
          rw [h1, h2, Polynomial.coeff_X_mul, hA2_loc_c, hf2_loc_c, coeff_evenPartX]
          by_cases hi : i % 2 = 0
          · rw [if_pos hi]
            have hf1_z : (if i = 0 then 0 else ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff (2 * j' + 1)).coeff (i - 1)) = 0 := by
              split_ifs with hi0
              · rfl
              · rw [hf1_odd_t]; by_contra hnz; have := hshC1_X2Y2 (2 * j') (i - 1) hnz; omega
            rw [hf1_z, add_zero]
          · rw [if_neg hi, add_zero, if_neg (by omega), hf1_odd_t]
            set m := i / 2
            have hi_eq : i = 2 * m + 1 := by omega
            have hi_sub : i - 1 = 2 * m := by omega
            conv_lhs => rw [hi_sub, hi_eq, hf2_odd_s]
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, ← hi_eq]
    -- Now Pe = C (X^2) * A0_loc + X * A2_loc with g1 ∣ A2_loc! Compute Res_V(Pe, g1; dStarEff/2, dg/2)!
    rcases hg1_dvd_A2 with ⟨q2_loc, hq2_loc⟩
    have hPe_mod : Pe = C (X ^ 2) * A0_loc + (X * q2_loc) * g1 := by
      rw [hPe_exact, hq2_loc]; ring
    have hA0_loc_d : A0_loc.natDegree ≤ dStarEff / 2 := by omega
    have hA2_loc_d : A2_loc.natDegree ≤ (Fpoly.coeff 2).natDegree / 2 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
      rw [hA2_loc_c, hf2_loc_c]
      have hle := hsh_deg_le (Fpoly.coeff 2)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      ext n; rw [coeff_evenPartX]; split_ifs <;> simp
    have hPe_d : Pe.natDegree ≤ dStarEff / 2 := by
      rw [hPe_exact]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C_mul_le _ _).trans hA0_loc_d
      · refine Polynomial.natDegree_mul_le.trans ?_; rw [Polynomial.natDegree_X]; omega
    have hres_V : Polynomial.resultant Pe g1 (dStarEff / 2) (dg / 2) =
        X ^ dg * Polynomial.resultant A0_loc g1 (dStarEff / 2) (dg / 2) := by
      rw [hPe_mod,
        resultant_add_mul_right_deg _ _ _ (dStarEff / 2) (dg / 2)
          ((Polynomial.natDegree_C_mul_le _ _).trans hA0_loc_d) (by rwa [← hPe_mod]) hg1_deg,
        Polynomial.resultant_C_mul_left,
        ← pow_mul, show 2 * (dg / 2) = dg by omega]
    have hdvd_V : X ^ resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2 ∣
        Polynomial.resultant Pe g1 (dStarEff / 2) (dg / 2) :=
      pow_dvd_resultant_of_weighted_ord X Pe g1 (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2
        hPe_d (le_of_eq hg1_deg) hPe_ord hg1_ord
    -- Square BOTH sides and apply resultant_expand2_even!
    have hdvd_sq : X ^ (2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2) ∣
        X ^ (2 * dg) * Polynomial.resultant A0_sh_eff (shiftBi x0 y0 gPrim) dStarEff dg := by
      have hsq := pow_dvd_pow_of_dvd hdvd_V 2
      rw [← pow_mul, mul_comm _ 2, hres_V, mul_pow, ← pow_mul, mul_comm dg 2] at hsq
      have hexp2 := resultant_expand2_even A0_loc g1 (dStarEff / 2) (dg / 2) hA0_loc_d hg1_deg
      rw [← hA0_loc_eq, ← hg1_eq, show 2 * (dStarEff / 2) = dStarEff by omega,
        show 2 * (dg / 2) = dg by omega] at hexp2
      rwa [← hexp2] at hsq
    by_cases hle : 2 * dg ≤ 2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2
    · have hsplit : (X : Polynomial F) ^ (2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2) =
          (X : Polynomial F) ^ (2 * dg) * (X : Polynomial F) ^ (2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) rre 2 - 2 * dg) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
      rw [hsplit] at hdvd_sq
      exact (mul_dvd_mul_iff_left (pow_ne_zero (2 * dg) Polynomial.X_ne_zero)).mp hdvd_sq
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle), pow_zero]; exact one_dvd _
  · -- Branch 2: vp_part + dStarEff * rq!
    rw [add_comm, pow_add]; apply mul_dvd_mul hqX_dvd
    apply X_sub_C_pow_dvd_of_comp_shift x0 _ _
    rw [← hres_eff]
    set d0' : ℕ := A0_sh_eff.natDegree
    have hd0'_mem : d0' ∈ List.range (dStarEff + 1) := List.mem_range.mpr (by omega)
    have hmin_le : ((List.range (dStarEff + 1)).map (fun d0 =>
        resOrdExact d0 (2 * k - 2) dg rre + (dStarEff - d0) * (rre - dg))).foldl Nat.min
          (resOrdExact 0 (2 * k - 2) dg rre + dStarEff * (rre - dg)) ≤
        resOrdExact d0' (2 * k - 2) dg rre + (dStarEff - d0') * (rre - dg) := by
      have hfold_map : ∀ (l : List ℕ) (f : ℕ → ℕ) (init : ℕ),
          (l.map f).foldl Nat.min init = l.foldl (fun acc y => Nat.min acc (f y)) init := by
        intro l f; induction l with
        | nil => intro _; rfl
        | cons a t ih => intro init; simp only [List.map_cons, List.foldl_cons]; exact ih _
      rw [hfold_map]
      exact hfold_le_mem (List.range (dStarEff + 1)) _ _ d0' hd0'_mem
    refine (pow_dvd_pow X hmin_le).trans ?_
    have hA0sh_bm : biMultGE (0 : F) 0 A0_sh_eff (2 * k - 2) := by
      intro i j hij; rw [shiftBi_zero_zero]
      by_cases hj : j % 2 = 0
      · have heq := congrArg (fun p : BiPoly F => (p.coeff j).coeff i) hsh0_split
        have hXC0 : (X * shiftBi x0 y0 C0_exp).coeff j = 0 := by
          cases j with
          | zero => rw [Polynomial.coeff_X_mul_zero]
          | succ j' =>
              rw [Polynomial.coeff_X_mul]
              ext i'; by_contra hnz; have := shiftBi_in_X2_Y2 x0 y0 C0_exp hC0_X2Y2 j' i' hnz; omega
        rw [Polynomial.coeff_add, hXC0, add_zero] at heq
        rw [← heq]; exact hbm0 i j hij
      · by_contra hnz; have := hA0sh_X2Y2 j i hnz; omega
    have hgPsh_bm : biMultGE (0 : F) 0 (shiftBi x0 y0 gPrim) rre := by
      intro i j hij; rw [shiftBi_zero_zero]; exact biMultGE_biMult x0 y0 gPrim i j hij
    have hres_split : Polynomial.resultant A0_sh_eff (shiftBi x0 y0 gPrim) dStarEff dg =
        (shiftBi x0 y0 gPrim).leadingCoeff ^ (dStarEff - d0') *
          Polynomial.resultant A0_sh_eff (shiftBi x0 y0 gPrim) d0' dg := by
      have hneg1 : (-1 : Polynomial F) = 1 := CharTwo.neg_eq 1
      conv_lhs =>
        rw [show dStarEff = d0' + (dStarEff - d0') by omega,
          Polynomial.resultant_add_left_deg _ _ d0' dg (dStarEff - d0') le_rfl,
          show (shiftBi x0 y0 gPrim).coeff dg = (shiftBi x0 y0 gPrim).leadingCoeff by
            rw [Polynomial.leadingCoeff, hshg_deg],
          hneg1, one_pow, one_mul]
    rw [hres_split, add_comm, pow_add]
    apply mul_dvd_mul
    · have hlc_dvd : X ^ (rre - dg) ∣ (shiftBi x0 y0 gPrim).leadingCoeff := by
        have h1 := pow_dvd_leadingCoeff_of_biMultGE (0 : F) 0 (shiftBi x0 y0 gPrim) dg rre hshg_deg hgPsh_bm
        simpa using h1
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hlc_dvd (dStarEff - d0')
    · have h2 := pow_dvd_resultant_of_biMultGE (0 : F) 0 A0_sh_eff (shiftBi x0 y0 gPrim) d0' (2 * k - 2) dg rre
        hA0sh_bm hgPsh_bm le_rfl (le_of_eq hshg_deg)
      rwa [shiftBi_zero_zero, shiftBi_zero_zero] at h2

end KerDResultants

/-! ### Part 4: Char-2 `ker(D)` PDE Parity, Primitive GCD Decomposition & `2A`/`2B` Dichotomy -/

section KerD2UFD

variable {F : Type*} [Field F] [CharP F 2]

end KerD2UFD
end B6402SmallAlg
end ProximityPrize.SubmissionBinaryLower
