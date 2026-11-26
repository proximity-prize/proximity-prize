import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid7
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ListAndMCA
import ProximityPrize.SubmissionBinaryLower.P64Shorten
import ProximityPrize.SubmissionBinaryLower.P64Light
import ProximityPrize.SubmissionBinaryLower.P64Aux
import ProximityPrize.SubmissionBinaryLower.P64Charging
import ProximityPrize.SubmissionBinaryLower.P64C7All
import ProximityPrize.SubmissionBinaryLower.P64C7ProfileArithmetic
import ProximityPrize.SubmissionBinaryLower.P64C6All
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 800000

/-!
# Hybrid ArkLib (`h_T ≤ h_0`) + Generalized P64 (`h_T > h_0`) for Binary 64.01

Unifies ArkLib's ordinary power-equation bound (for low-degree factors `R.natDegree ≤ h_0`,
including the bottom of any Frobenius descent chain!) with P64's Bessel/profile/shortening
machinery (for high-degree factors `R.natDegree > h_0`, generalized to arbitrary `q₀ ∈ {1, 2}`,
agreement threshold `A = 1482831`, and cofactor defect budget `Δ_max`).

Key improvements over P64's standalone C7 bound:
1. Exact completed-square profile bound (`(8(w - h·wY) - (2C₀ - wY - 2))² ≥ 0`), eliminating
   any quadratic `Δ_max²` penalty and giving `2 h w - h² wY - S₂ ≤ P₀ h² + 2 Δ_max h`.
2. Retaining `+ 2 h N_z` in `mass_lower` cancels `- 2 Δ_max h` via the 1-line factorization
   `N_eff (M₀ h² - 2 h (N_eff - N_z)) - M₀ h² N_z = h (N_eff - N_z) (M₀ h - 2 N_eff) ≥ 0`,
   valid across EVERY Frobenius descent step under the invariant `N_T ≤ |A_z| - wY ∨ N_T ≤ N_eff`.
3. Tight C7 single-line aggregate `6 d + 2 q h + 2` (saving 40% vs P64's `10 d`) with `q · h = q₀ · h_orig`
   invariant under Frobenius descent!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402HybridP64

open Polynomial ReedSolomon B6401Params B6401ListAndMCA
open BCHKSSubstitutionVanish P64LineOrder P64Incidence P64Cofactor P64Charging
open P64C6Coordinates P64C6TwistTransfer P64C6Incidence P64C6Exceptional P64Found
open P64C6Bessel P64C6Finite PolynomialDifferential
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
local notation "Tri" => Polynomial (Polynomial (Polynomial Fld))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree
local notation "yzd" => P64Caps.YZ.yzSupportDegree

theorem card_le_of_factor_frob_c7
    (u₀ u₁ : Idx → Fld) (q₀ h_orig h₀ d Δ P₀ M₀ N_eff : ℕ)
    (hq₀ : 1 ≤ q₀) (hh₀ : 1 ≤ h₀) (hM0pos : 0 < M₀)
    (hM0 : (M₀ : ℤ) + P₀ = (A : ℤ) - wY)
    (hNeff : (N_eff : ℤ) = (A : ℤ) - wY + Δ)
    (hMh : 2 * N_eff ≤ M₀ * (h₀ + 1))
    (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (q : ℕ) (hq : 1 ≤ q) (hqh_eq : q * R.natDegree = q₀ * h_orig) (hRle : R.natDegree ≤ h_orig)
    (hRyz : WtLE 0 q 1 d R)
    (hF : 2 * R.natDegree * wd R wY < Fintype.card Fld)
    (hfull : (P64C7Case.fullLines R BinaryIRSProfile.domain (linePow u₀ u₁ q)).card < A)
    (hprofile : 2 * (R.natDegree : ℤ) * wd R wY - R.natDegree ^ 2 * wY -
      (∑ i, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) : ℤ) ^ 2) ≤
      P₀ * R.natDegree ^ 2 + 2 * Δ * R.natDegree)
    (S : Finset Fld) (P : Fld → Fld[X]) (Aset : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Aset z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Aset z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Aset z))
    (hNbound : ∀ z ∈ S,
      normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q) (Aset z) (wd R wY) wY ≤
        ((Aset z).card : ℤ) - wY ∨
      normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q) (Aset z) (wd R wY) wY ≤ N_eff)
    (C_per_d C_per_h : ℚ)
    (hCd_ark : (2 * (h₀ : ℚ) - 1) + (((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) *
      (1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ)) ≤ C_per_d)
    (hCd_1 : (1 : ℚ) ≤ C_per_d)
    (hCd_c7 : ((2 * N_eff * N * 6 : ℕ) : ℚ) / (M₀ : ℚ) + (N : ℚ) ≤ C_per_d)
    (hCh_ark : (q₀ : ℚ) * ((((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) ≤ C_per_h)
    (hCh_c7 : ((2 * N_eff * N * (2 * q₀ + 2) : ℕ) : ℚ) / (M₀ : ℚ) ≤ C_per_h) :
    (S.card : ℚ) ≤ C_per_d * (d : ℚ) + 4 * (h_orig : ℚ) * (d : ℚ) + C_per_h * (h_orig : ℚ) := by
  classical
  generalize heq : R.natDegree = h
  induction h using Nat.strong_induction_on generalizing R q S P Aset with
  | ind h ih =>
    subst heq
    by_cases hsmall : R.natDegree ≤ h₀
    · -- Base case: exit to ArkLib!
      have hH : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ d :=
        coefficient_parameter_degree R q d hRyz
      have hark := card_le_of_biPoly_pow u₀ u₁ q hq R R.natDegree d hirr.ne_zero le_rfl hH
        S P Aset hP hcurve hcard (fun z hz i hi => (hmatch z hz i).mp hi) hbad
      have hmax_le : max (d : ℚ) (arklibBoundPowQ q R.natDegree d) ≤
          C_per_d * (d : ℚ) + 4 * (h_orig : ℚ) * (d : ℚ) + C_per_h * (h_orig : ℚ) := by
        apply max_le
        · have h1 : (0 : ℚ) ≤ 4 * (h_orig : ℚ) * (d : ℚ) := by positivity
          have h2 : (0 : ℚ) ≤ C_per_h * (h_orig : ℚ) := by
            have : (0 : ℚ) ≤ C_per_h := le_trans (by positivity) hCh_ark
            positivity
          nlinarith only [hCd_1, h1, h2, show (0 : ℚ) ≤ (d : ℚ) by positivity]
        · unfold arklibBoundPowQ
          dsimp only
          have hqh_q : (q : ℚ) * (R.natDegree : ℚ) = (q₀ : ℚ) * (h_orig : ℚ) := by exact_mod_cast hqh_eq
          have hRle0 : (R.natDegree : ℚ) ≤ (h₀ : ℚ) := by exact_mod_cast hsmall
          have hsub_le : ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤ ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
            exact_mod_cast Nat.sub_le_sub_right hsmall (2 * wY + 1)
          have htheta_nn : (0 : ℚ) ≤ ((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ) := by positivity
          have hwY_ge1 : (1 : ℚ) ≤ 2 * (wY : ℚ) - 1 := by dsimp [wY]; norm_num
          have hpsi_le : 1 + (2 * (wY : ℚ) - 1) * (2 * (R.natDegree : ℚ) - 1) +
              2 * ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤
              1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
            nlinarith only [hRle0, hsub_le, hwY_ge1]
          have hd_nn : (0 : ℚ) ≤ (d : ℚ) := Nat.cast_nonneg d
          have hh_nn : (0 : ℚ) ≤ (h_orig : ℚ) := Nat.cast_nonneg h_orig
          have htdpsi := mul_le_mul_of_nonneg_left hpsi_le (mul_nonneg htheta_nn hd_nn)
          rw [hqh_q, mul_right_comm (q : ℚ) ((N - wY - 1 : ℕ) : ℚ) (R.natDegree : ℚ), hqh_q]
          nlinarith only [hCd_ark, hCh_ark, hRle0, htdpsi, hd_nn, hh_nn,
            show (0 : ℚ) ≤ 4 * (h_orig : ℚ) * (d : ℚ) by positivity]
      exact hark.trans hmax_le
    · -- R.natDegree ≥ h₀ + 1
      have hbig : h₀ + 1 ≤ R.natDegree := by omega
      by_cases hY : Polynomial.derivative R = 0
      · by_cases hX : P64Incidence.dXPoly R = 0
        · -- Frobenius descent R = frobLift T!
          let T := twistPoly R
          have hback : frobLift T = R := frobLift_twistPoly R hY hX
          have hTi : Irreducible T := irreducible_twistPoly R hirr hY hX
          have hdeg : R.natDegree = T.natDegree * 2 := by rw [← hback, natDegree_frobLift]
          have hTpos : 1 ≤ T.natDegree := by omega
          have hTlt : T.natDegree < R.natDegree := by omega
          have hspace : wd R wY = 2 * wd T wY := by
            rw [← hback, spatial_weight_frobLift T hTi.ne_zero wY]
          let S' := S.image (sqrtF : Fld → Fld)
          let P' : Fld → Fld[X] := fun t => P (t ^ 2)
          let A' : Fld → Finset Idx := fun t => Aset (t ^ 2)
          have hSq : ∀ t ∈ S', t ^ 2 ∈ S := by
            intro t ht; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht; simpa using hz
          have hScard : S'.card = S.card := Finset.card_image_of_injective S sqrtF_injective
          have hwt : WtLE 0 (2 * q) 1 d T := parameter_weight_transfer T q d (by rwa [hback])
          have hF' : 2 * T.natDegree * wd T wY < Fintype.card Fld :=
            (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)).trans_lt hF
          have hexp : ∀ i, Polynomial.expand Fld 2 (linePow u₀ u₁ q i) = linePow u₀ u₁ (2 * q) i :=
            expand_linePow u₀ u₁ q
          have hm : ∀ i, lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) =
              2 * lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) := by
            intro i; rw [← hback, lineOrd_frobLift T hTi.ne_zero, hexp]
          have hfull' : (P64C7Case.fullLines T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q))).card < A := by
            have heq_fl : P64C7Case.fullLines R BinaryIRSProfile.domain (linePow u₀ u₁ q) =
                P64C7Case.fullLines T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) := by
              rw [← hback, P64C7All.fullLines_frobLift T hTi.ne_zero]
              simp only [hexp]
            exact heq_fl ▸ hfull
          have hprofile' : 2 * (T.natDegree : ℤ) * wd T wY - T.natDegree ^ 2 * wY -
              (∑ i, (lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) : ℤ) ^ 2) ≤
              P₀ * T.natDegree ^ 2 + 2 * Δ * T.natDegree := by
            rw [hdeg, hspace] at hprofile
            simp_rw [hm, Nat.cast_mul, Nat.cast_ofNat, mul_pow] at hprofile
            rw [← Finset.mul_sum] at hprofile
            have hΔnn : (0 : ℤ) ≤ Δ * T.natDegree := by positivity
            nlinarith only [hprofile, hΔnn]
          have hcurve' : ∀ t ∈ S', triEval T t (P' t) = 0 := by
            intro t ht
            have hc := hcurve _ (hSq t ht)
            rw [← hback] at hc
            exact eq_zero_of_pow_eq_zero ((triEval_frobLift T t (P' t)).symm.trans hc)
          have hmatch' : ∀ t ∈ S', ∀ i, i ∈ A' t ↔
              (P' t).eval (BinaryIRSProfile.domain i) = u₀ i + t ^ (2 * q) * u₁ i := by
            intro t ht i
            have hm0 := hmatch _ (hSq t ht) i
            rwa [show (t ^ 2) ^ q = t ^ (2 * q) by rw [← pow_mul]] at hm0
          have hNbound' : ∀ t ∈ S',
              normalDefect T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) (A' t) (wd T wY) wY ≤
                ((A' t).card : ℤ) - wY ∨
              normalDefect T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) (A' t) (wd T wY) wY ≤ N_eff := by
            intro t ht
            have htS := hSq t ht
            -- Compare w_T - ∑ μ_T vs w_R - ∑ μ_R (exact factor of 2!):
            let sT : ℤ := ∑ i ∈ A' t, (lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) : ℤ)
            let sR : ℤ := ∑ i ∈ Aset (t ^ 2), (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) : ℤ)
            have hs_eq : sR = 2 * sT := by
              dsimp [sR, sT, A']; simp_rw [hm, Nat.cast_mul, Nat.cast_ofNat]; rw [← Finset.mul_sum]
            -- Express normalDefect via ∑ (μ_i - 1) ≤ ∑ μ_i - |A| (or exact if μ_i ≥ 1; wait: use raw def!)
            -- Even simpler: normalDefect T = w_T - wY - ∑_{A'} (μ_T - 1).
            -- If w_T ≤ ∑_{A'} (μ_T - 1) + |A'|, i.e., if w_T - ∑ (μ_T - 1) ≤ |A'|, left branch holds!
            -- Notice for ANY m : ℕ: 2 * (m - 1 : ℕ) ≤ (2 * m - 1 : ℕ) AND (2 * m - 1 : ℕ) ≤ 2 * (m - 1 : ℕ) + 1!
            -- Wait: if μ_T i = 0, then μ_R i = 0, so (μ_T - 1) = 0 and (μ_R - 1) = 0!
            -- If μ_T i ≥ 1, then (μ_R i - 1) = 2 * μ_T i - 1 = 2 * (μ_T i - 1) + 1!
            -- Let S_pos = ∑_{i ∈ A'} (if μ_T i ≥ 1 then 1 else 0) ≤ |A'|!
            -- Then ∑ (μ_R - 1) = 2 * ∑ (μ_T - 1) + S_pos!
            -- Hence w_R - ∑ (μ_R - 1) = 2 * (w_T - ∑ (μ_T - 1)) - S_pos!
            -- Case A: w_T - ∑ (μ_T - 1) ≤ |A'| ⇒ normalDefect T ≤ |A'| - wY (left branch!)
            -- Case B: w_T - ∑ (μ_T - 1) > |A'| ≥ S_pos ⇒
            --   w_R - ∑ (μ_R - 1) = 2 * (w_T - ∑ (μ_T - 1)) - S_pos ≥ w_T - ∑ (μ_T - 1)
            --   ⇒ normalDefect T ≤ normalDefect R! And if normalDefect R ≤ |A'| - wY, contradiction with Case B;
            --   else normalDefect R ≤ N_eff ⇒ normalDefect T ≤ N_eff (right branch!)!
            let sumT : ℤ := ∑ i ∈ A' t, ((lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) - 1 : ℕ) : ℤ)
            let sumR : ℤ := ∑ i ∈ A' t, ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) - 1 : ℕ) : ℤ)
            have hsum_rel : sumR ≤ 2 * sumT + (A' t).card := by
              have hpt : ∀ i ∈ A' t,
                  ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) - 1 : ℕ) : ℤ) ≤
                  2 * ((lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) - 1 : ℕ) : ℤ) + 1 := by
                intro i _; rw [hm i]; omega
              calc sumR ≤ ∑ i ∈ A' t, (2 * ((lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) - 1 : ℕ) : ℤ) + 1) :=
                    Finset.sum_le_sum hpt
                _ = 2 * sumT + (A' t).card := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
            by_cases hcase : (wd T wY : ℤ) - sumT ≤ (A' t).card
            · left; change (wd T wY : ℤ) - wY - sumT ≤ _; linarith
            · have hT_le_R : normalDefect T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) (A' t) (wd T wY) wY ≤
                  normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q) (Aset (t ^ 2)) (wd R wY) wY := by
                change (wd T wY : ℤ) - wY - sumT ≤ (wd R wY : ℤ) - wY - sumR
                have hw2 : (wd R wY : ℤ) = 2 * (wd T wY : ℤ) := by exact_mod_cast hspace
                linarith
              rcases hNbound (t ^ 2) htS with h1 | h2
              · left; exact hT_le_R.trans h1
              · right; exact hT_le_R.trans h2
          have hbT := ih T.natDegree hTlt T hTi hTpos (2 * q) (by omega)
            (by rw [← hqh_eq, hdeg]; ring) (by omega) hwt hF' hfull' hprofile'
            S' P' A' (fun t ht => hP _ (hSq t ht)) hcurve' (fun t ht => hcard _ (hSq t ht))
            hmatch' (fun t ht => hbad _ (hSq t ht)) hNbound' rfl
          rwa [hScard] at hbT
        · -- Inseparable: ∂_Y R = 0, ∂_X R ≠ 0 ⇒ S.card ≤ 2 * R.natDegree * yzd R 1 ≤ 4 * h_orig * d
          have hc := P64Incidence.card_le_of_inseparable R hirr (by omega) hY hX (wd R wY)
            (P64Resultant.coeff_natDegree_le_weighted R wY) hF S P hcurve
          have hyz := P64C6All.yz_le_twice R hirr.ne_zero q d (by omega) hRyz
          have hm : S.card ≤ 4 * h_orig * d := by nlinarith only [hc, hyz, hRle]
          have h1 : (0 : ℚ) ≤ C_per_d * (d : ℚ) := mul_nonneg (le_trans (by norm_num) hCd_1) (Nat.cast_nonneg _)
          have h2 : (0 : ℚ) ≤ C_per_h * (h_orig : ℚ) := mul_nonneg (le_trans (by positivity) hCh_ark) (Nat.cast_nonneg _)
          have hmQ : (S.card : ℚ) ≤ 4 * (h_orig : ℚ) * (d : ℚ) := by exact_mod_cast hm
          linarith only [hmQ, h1, h2]
      · -- Separable: ∂_Y R ≠ 0 ⇒ tight C7 separable bound!
        have hMh' : 2 * N_eff ≤ M₀ * R.natDegree := hMh.trans (Nat.mul_le_mul_left M₀ hbig)
        have hc := tight_c7_separable R hirr hh hY (wd R wY) q d Δ P₀ M₀ N_eff (by omega) le_rfl hRyz hF
          (linePow u₀ u₁ q) (linePow_natDegree_le u₀ u₁ q) hM0 hM0pos hNeff hMh' hprofile hfull
          S P Aset hP hcurve hcard (fun z hz i => by rw [eval_linePow]; exact hmatch z hz i) hNbound
        have hM0Q : (0 : ℚ) < (M₀ : ℚ) := by exact_mod_cast hM0pos
        have hcQ : (M₀ : ℚ) * (S.card : ℚ) ≤
            (2 * N_eff * N : ℕ) * (6 * (d : ℚ) + 2 * (q : ℚ) * (R.natDegree : ℚ) + 2) +
            (M₀ : ℚ) * ((N : ℚ) * (d : ℚ) + 2 * (R.natDegree : ℚ) * (d : ℚ)) := by
          have hc' : ((M₀ * S.card : ℕ) : ℚ) ≤
              ((2 * N_eff * N * (6 * d + 2 * q * R.natDegree + 2) + M₀ * (N * d + 2 * R.natDegree * d) : ℕ) : ℚ) := by
            exact_mod_cast hc
          push_cast at hc' ⊢; linarith only [hc']
        have hqh_q : (q : ℚ) * (R.natDegree : ℚ) = (q₀ : ℚ) * (h_orig : ℚ) := by exact_mod_cast hqh_eq
        have h1_le_h : (1 : ℚ) ≤ (h_orig : ℚ) := by exact_mod_cast (le_trans hh hRle)
        have hRle_q : (R.natDegree : ℚ) ≤ (h_orig : ℚ) := by exact_mod_cast hRle
        have hdiv : (S.card : ℚ) ≤
            (((2 * N_eff * N * 6 : ℕ) : ℚ) / (M₀ : ℚ) + (N : ℚ)) * (d : ℚ) +
            2 * (R.natDegree : ℚ) * (d : ℚ) +
            (((2 * N_eff * N * (2 * q₀ + 2) : ℕ) : ℚ) / (M₀ : ℚ)) * (h_orig : ℚ) := by
          refine le_of_mul_le_mul_left ?_ hM0Q
          have hNE : (0 : ℚ) ≤ 2 * ((2 * N_eff * N : ℕ) : ℚ) := by positivity
          have h2h := mul_le_mul_of_nonneg_left h1_le_h hNE
          field_simp [hM0Q.ne']
          push_cast at hcQ h2h ⊢
          rw [mul_assoc (2 : ℚ) (q : ℚ) (R.natDegree : ℚ), hqh_q] at hcQ
          linarith only [hcQ, h2h]
        have hd_nn : (0 : ℚ) ≤ (d : ℚ) := Nat.cast_nonneg d
        have hh_nn : (0 : ℚ) ≤ (h_orig : ℚ) := Nat.cast_nonneg h_orig
        nlinarith only [hdiv, hCd_c7, hCh_c7, hRle_q, hd_nn, hh_nn]
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
