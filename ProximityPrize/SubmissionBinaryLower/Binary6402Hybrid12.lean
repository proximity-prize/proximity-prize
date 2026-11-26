import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid11
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

theorem hybrid_p64_card_le
    (u₀ u₁ : Idx → Fld) (q₀ : ℕ) (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (Φ : Tri) (B H W_Φ m Δ_max : ℕ)
    (hΦ : Φ ≠ 0) (hB : Φ.natDegree ≤ B)
    (hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ H)
    (hWΦ : wd Φ wY ≤ W_Φ)
    (hFΦ : 2 * B * W_Φ < Fintype.card Fld)
    (hFaux : (4 * W_Φ / wY + B) * (4 * W_Φ) < Fintype.card Fld)
    (S : Finset Fld) (P : Fld → Fld[X]) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval Φ z (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z))
    (hΦgap : ∀ z ∈ S,
      (wd Φ wY : ℤ) - (∑ i ∈ Az z, (lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
        (2 * m : ℤ) * ((Az z).card - (A : ℤ)) ≤ Δ_max)
    -- Shortening Johnson cert at A = 1482831 (λ* = 208984)
    (m_j B_j H_j count_j : ℕ)
    (hcert : ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate 1888168 839591 1273766 m_j B_j H_j)
    (hcnt : ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount 1888168 839591 1273766 B_j H_j ≤ count_j)
    (hB_j : B_j ≤ 2 * 839591 + 1)
    -- Hybrid P64 tuning parameters (checked by norm_num / exact arithmetic!)
    (h₀ q_aux slack P₀ M₀ N_eff : ℕ)
    (hh₀ : 1 ≤ h₀) (hq_aux : 1 ≤ q_aux) (hM0pos : 0 < M₀)
    (hB_mul : B ≤ 2 * m * (h₀ + 1))
    (hC0_h : A + 4 * Δ_max + 1 ≤ 4 * (h₀ + 1) * wY)
    (h4B_q : 4 * B ≤ q_aux)
    (hslack : (4 * W_Φ / wY) * (8 * N) ≤ q_aux * slack)
    (hP₀ : 8 * (wY : ℤ) * slack * (h₀ + 1 : ℤ) ^ 2 +
      16 * (wY : ℤ) * ((A : ℤ) - wY + 10000) * (h₀ + 1 : ℤ) + ((wY : ℤ) + 2) ^ 2 ≤
      64 * (wY : ℤ) * P₀ * (h₀ + 1 : ℤ) ^ 2)
    (hM0 : (M₀ : ℤ) + P₀ = (A : ℤ) - wY)
    (hNeff : (N_eff : ℤ) = (A : ℤ) - wY + Δ_max)
    (hMh : 2 * N_eff ≤ M₀ * (h₀ + 1))
    (C_per_d C_per_h : ℚ)
    (hCd_ark : (2 * (h₀ : ℚ) - 1) + (((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) *
      (1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ)) ≤ C_per_d)
    (hCd_light : (208984 : ℚ) ≤ C_per_d)
    (hCd_c7 : ((2 * N_eff * N * 6 : ℕ) : ℚ) / (M₀ : ℚ) + (N : ℚ) ≤ C_per_d)
    (hCd_c6 : ((16 * N_eff * N : ℕ) : ℚ) / (10000 ^ 2 : ℚ) + (N : ℚ) ≤ C_per_d)
    (hCh_aux : (q₀ : ℚ) * ((q_aux : ℚ) + (4 * W_Φ / wY : ℕ)) ≤ C_per_h)
    (hCh_light : (count_j : ℚ) / ((h₀ + 1 : ℕ) : ℚ) ≤ C_per_h)
    (hCh_ark : (q₀ : ℚ) * ((((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) ≤ C_per_h)
    (hCh_c7 : ((2 * N_eff * N * (2 * q₀ + 2) : ℕ) : ℚ) / (M₀ : ℚ) ≤ C_per_h)
    (hCh_c6 : ((2 * N_eff * (4 * q₀ + 1) : ℕ) : ℚ) / (10000 : ℚ) ≤ C_per_h) :
    let D_tot : ℚ := (H : ℚ) + (q₀ : ℚ) * (B : ℚ)
    (S.card : ℚ) ≤ C_per_d * D_tot +
      (max (4 * W_Φ / wY : ℕ) (4 * B) + B : ℚ) * D_tot + C_per_h * (B : ℚ) + (H : ℚ) := by
  classical
  have hq₀pos : 1 ≤ q₀ := by rcases hq₀ with rfl | rfl <;> omega
  have hCd_1 : (1 : ℚ) ≤ C_per_d := le_trans (by norm_num) hCd_light
  have hcover := card_le_cover Φ hΦ S P hcurve
  have hY0 := card_caseY0_le Φ hΦ H hH S
  have hΦ_yz : yzd Φ q₀ ≤ H + q₀ * B := by
    unfold P64Caps.YZ.yzSupportDegree
    apply Finset.sup_le
    intro j hj
    have hjB : j ≤ B := (Polynomial.le_natDegree_of_ne_zero (mem_support_iff.mp hj)).trans hB
    have hdX : Polynomial.Bivariate.degreeX (Φ.coeff j) ≤ H := by
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le; intro a _; exact hH j a
    have hqj := Nat.mul_le_mul_left q₀ hjB
    omega
  have hΦ_yz1 : yzd Φ 1 ≤ H + q₀ * B := by
    have hle : yzd Φ 1 ≤ yzd Φ q₀ := by
      change Φ.support.sup _ ≤ yzd Φ q₀
      apply Finset.sup_le; intro j hj
      calc Polynomial.Bivariate.degreeX (Φ.coeff j) + 1 * j
          ≤ Polynomial.Bivariate.degreeX (Φ.coeff j) + q₀ * j := by rcases hq₀ with rfl | rfl <;> omega
        _ ≤ yzd Φ q₀ := P64Caps.YZ.coeffWeight_le_of_ne Φ q₀ j (mem_support_iff.mp hj)
    exact hle.trans hΦ_yz
  have hpair : (casePair Φ S P).card ≤ B * (H + q₀ * B) := by
    have hF' : 2 * Φ.natDegree * wd Φ wY < Fintype.card Fld :=
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hB) hWΦ).trans_lt hFΦ
    exact (P64Resultant.card_casePair_le Φ hΦ wY hF' S P).trans
      (Nat.mul_le_mul hB hΦ_yz1)
  let M_B : ℕ := max (4 * W_Φ / wY) (4 * B)
  -- Per-factor bound for every R ∈ factors Φ!
  have hfac : ∀ R ∈ factors Φ,
      ((caseSingle Φ S P R).card : ℚ) ≤
        C_per_d * (yzd R q₀ : ℚ) + (M_B : ℚ) * (yzd R q₀ : ℚ) + C_per_h * (R.natDegree : ℚ) := by
    intro R hR
    have hirr : Irreducible R :=
      (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Tri) R (Multiset.mem_toFinset.mp hR)).irreducible
    have hR0 : R ≠ 0 := hirr.ne_zero
    have hdvd : R ∣ Φ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hR)
    by_cases hdeg0 : R.natDegree = 0
    · rw [caseSingle_eq_empty_of_natDegree_eq_zero Φ S P R hR hdeg0]; simp
      have : (0 : ℚ) ≤ C_per_d := le_trans (by norm_num) hCd_1
      have : (0 : ℚ) ≤ C_per_h := le_trans (by positivity) hCh_ark
      positivity
    have hRpos : 1 ≤ R.natDegree := by omega
    have hRleB : R.natDegree ≤ B := (Polynomial.natDegree_le_of_dvd hdvd hΦ).trans hB
    have hRw_le : wd R wY ≤ W_Φ := by
      obtain ⟨C, hC⟩ := hdvd
      have hC0 : C ≠ 0 := by rintro rfl; exact hΦ (by simpa using hC)
      have hmul := P64Caps.Weighted.weightedSupportDegree_mul R C wY hR0 hC0
      rw [← hC] at hmul
      omega
    have hRyz : WtLE 0 q₀ 1 (yzd R q₀) R := wtLE_of_yzSupportDegree R q₀
    have h1d : yzd R 1 ≤ yzd R q₀ := by
      change R.support.sup _ ≤ yzd R q₀
      apply Finset.sup_le; intro j hj
      calc Polynomial.Bivariate.degreeX (R.coeff j) + 1 * j
          ≤ Polynomial.Bivariate.degreeX (R.coeff j) + q₀ * j := by rcases hq₀ with rfl | rfl <;> omega
        _ ≤ yzd R q₀ := P64Caps.YZ.coeffWeight_le_of_ne R q₀ j (mem_support_iff.mp hj)
    let Vs := caseSingle Φ S P R
    have hVsS : ∀ z ∈ Vs, z ∈ S := fun z hz => (Finset.mem_filter.mp hz).1
    have hVsR : ∀ z ∈ Vs, triEval R z (P z) = 0 := fun z hz => (Finset.mem_filter.mp hz).2.2.1
    by_cases hsmall : R.natDegree ≤ h₀
    · -- Low-degree factor: direct ArkLib (Section 1)!
      have hHR : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ yzd R q₀ :=
        coefficient_parameter_degree R q₀ (yzd R q₀) hRyz
      have hark := card_le_of_biPoly_pow u₀ u₁ q₀ hq₀pos R R.natDegree (yzd R q₀) hR0 le_rfl hHR
        Vs P Az (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
        (fun z hz i hi => (hmatch z (hVsS z hz) i).mp hi) (fun z hz => hbad z (hVsS z hz))
      refine hark.trans (max_le ?_ ?_)
      · have h1 : (0 : ℚ) ≤ (M_B : ℚ) * (yzd R q₀ : ℚ) := by positivity
        have h2 : (0 : ℚ) ≤ C_per_h * (R.natDegree : ℚ) :=
          mul_nonneg (le_trans (by positivity) hCh_ark) (Nat.cast_nonneg _)
        nlinarith only [hCd_1, h1, h2, show (0 : ℚ) ≤ (yzd R q₀ : ℚ) by positivity]
      · unfold arklibBoundPowQ
        dsimp only
        have hRle0 : (R.natDegree : ℚ) ≤ (h₀ : ℚ) := by exact_mod_cast hsmall
        have hsub_le : ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤ ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
          exact_mod_cast Nat.sub_le_sub_right hsmall (2 * wY + 1)
        have htheta_nn : (0 : ℚ) ≤ ((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ) := by positivity
        have hwY_ge1 : (1 : ℚ) ≤ 2 * (wY : ℚ) - 1 := by dsimp [wY]; norm_num
        have hpsi_le : 1 + (2 * (wY : ℚ) - 1) * (2 * (R.natDegree : ℚ) - 1) +
            2 * ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤
            1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
          nlinarith only [hRle0, hsub_le, hwY_ge1]
        have hd_nn : (0 : ℚ) ≤ (yzd R q₀ : ℚ) := Nat.cast_nonneg _
        have hh_nn : (0 : ℚ) ≤ (R.natDegree : ℚ) := Nat.cast_nonneg _
        have htdpsi := mul_le_mul_of_nonneg_left hpsi_le (mul_nonneg htheta_nn hd_nn)
        nlinarith only [hCd_ark, hCh_ark, hRle0, htdpsi, hd_nn, hh_nn,
          show (0 : ℚ) ≤ (M_B : ℚ) * (yzd R q₀ : ℚ) by positivity]
    · -- High-degree factor: R.natDegree ≥ h₀ + 1!
      have hbig : h₀ + 1 ≤ R.natDegree := by omega
      -- First check afLight (Section 2):
      by_cases hlight : 208984 ≤ (P64C7Case.fullLines R BinaryIRSProfile.domain (linePow u₀ u₁ q₀)).card ∨
          (lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R).card ≤ 208983
      · have hl := fullLines_subset_eq hirr hRpos q₀ (yzd R q₀) hq₀ hRyz u₀ u₁ Vs P Az
          (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
          (fun z hz => hmatch z (hVsS z hz)) (fun z hz => hbad z (hVsS z hz))
          m_j B_j H_j count_j hcert hcnt hB_j hlight
        have hlQ : (Vs.card : ℚ) ≤ 208984 * (yzd R q₀ : ℚ) + (count_j : ℚ) := by exact_mod_cast hl
        have hcnt_le : (count_j : ℚ) ≤ C_per_h * (R.natDegree : ℚ) := by
          have h1 : ((h₀ + 1 : ℕ) : ℚ) ≤ (R.natDegree : ℚ) := by exact_mod_cast hbig
          have hpos : (0 : ℚ) < ((h₀ + 1 : ℕ) : ℚ) := by positivity
          have h2 : (count_j : ℚ) ≤ C_per_h * ((h₀ + 1 : ℕ) : ℚ) := (div_le_iff₀ hpos).mp hCh_light
          have hCh_nn : (0 : ℚ) ≤ C_per_h := le_trans (by positivity) hCh_light
          nlinarith only [h1, h2, hCh_nn]
        have : (0 : ℚ) ≤ (M_B : ℚ) * (yzd R q₀ : ℚ) := by positivity
        nlinarith only [hlQ, hCd_light, hcnt_le, this, show (0 : ℚ) ≤ (yzd R q₀ : ℚ) by positivity]
      · push_neg at hlight
        have hfull_lt : (P64C7Case.fullLines R BinaryIRSProfile.domain (linePow u₀ u₁ q₀)).card < A :=
          lt_of_lt_of_le hlight.1 (by norm_num [A])
        -- Prove cofactor defect bound for every z ∈ Vs!
        have hdef_R : ∀ z ∈ Vs,
            ((wd R wY : ℤ) - ∑ i ∈ Az z, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
              ((Az z).card - (A : ℤ)) ≤ Δ_max :=
          cofactor_defect_of_single_factor Φ R hΦ hR q₀ u₀ u₁ m Δ_max S P Az hP hcard
            (fun z hz i hi => (hmatch z hz i).mp hi) hΦgap (fun a Q'' hΦeq _ => by
              have hQ''0 : Q'' ≠ 0 := by rintro rfl; exact hΦ (by rw [hΦeq, mul_zero])
              have hd : a * R.natDegree ≤ Φ.natDegree := by
                rw [hΦeq, natDegree_mul (pow_ne_zero a hR0) hQ''0, natDegree_pow]; omega
              have : a * (h₀ + 1) ≤ 2 * m * (h₀ + 1) :=
                (Nat.mul_le_mul_left a hbig).trans (hd.trans (hB.trans hB_mul))
              exact Nat.le_of_mul_le_mul_right this (by omega))
        have hNbound : ∀ z ∈ Vs,
            normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q₀) (Az z) (wd R wY) wY ≤
              ((Az z).card : ℤ) - wY ∨
            normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q₀) (Az z) (wd R wY) wY ≤ N_eff := by
          intro z hz
          right
          -- normalDefect = w - wY - ∑ (μ - 1) ≤ w - wY - (∑ μ - |A_z|) = (w - ∑ μ) + (|A_z| - wY)
          -- = (A - wY) + (w - ∑ μ) + (|A_z| - A) ≤ (A - wY) + Δ_max = N_eff!
          have hsum_ge : ∑ i ∈ Az z, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ) - (Az z).card ≤
              ∑ i ∈ Az z, ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 : ℕ) : ℤ) := by
            have hpt : ∀ i ∈ Az z, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ) - 1 ≤
                ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 : ℕ) : ℤ) := fun i _ => by omega
            calc _ = ∑ i ∈ Az z, ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ) - 1) := by
                    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
              _ ≤ _ := Finset.sum_le_sum hpt
          have hd0 := hdef_R z hz
          change (wd R wY : ℤ) - wY - _ ≤ _
          linarith only [hsum_ge, hd0, hNeff]
        have hFR : 2 * R.natDegree * wd R wY < Fintype.card Fld :=
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hRleB) hRw_le).trans_lt hFΦ
        -- Split on positive bias vs low bias!
        by_cases hbias : 10000 * R.natDegree ≤
            R.natDegree * A - ∑ i, lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i)
        · -- Positive bias C6 with Frobenius descent & ArkLib cutoff!
          have hc6 := card_le_of_factor_frob_c6 u₀ u₁ q₀ R.natDegree h₀ (yzd R q₀) Δ_max N_eff
            hq₀pos hh₀ hNeff R hirr hRpos q₀ hq₀pos rfl le_rfl hRyz hFR hbias Vs P Az
            (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
            (fun z hz i hi => (hmatch z (hVsS z hz) i).mp hi) (fun z hz => hbad z (hVsS z hz))
            hNbound C_per_d C_per_h hCd_ark hCd_1 hCd_c6 hCh_ark hCh_c6
          have h4le : (4 * R.natDegree : ℚ) ≤ (M_B : ℚ) := by
            exact_mod_cast (Nat.mul_le_mul_left 4 hRleB).trans (le_max_right _ _)
          nlinarith only [hc6, h4le, show (0 : ℚ) ≤ (yzd R q₀ : ℚ) by positivity]
        · -- Low bias: either S_4 auxiliary succeeds (Section 3) or fails ⇒ profile ⇒ C7 (Section 6)!
          let W := 4 * wd R wY - (A + 4 * Δ_max + 1)
          let J := W / wY
          let c4 := ∑ i, (4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1) *
            (4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 + 1) / 2
          have hw_low : R.natDegree * wY ≤ wd R wY := by
            have := natDegree_mul_le_weightedSupportDegree R hR0 wY; rwa [mul_comm] at this
          have hC0 : A + 4 * Δ_max + 1 ≤ 4 * wd R wY := by
            have : 4 * (h₀ + 1) * wY ≤ 4 * wd R wY := by nlinarith only [hbig, hw_low]
            omega
          have hφ : ∀ i, 4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 ≤ q_aux + J := by
            intro i
            have hμh := lineOrd_le_natDegree_of_irreducible hirr hRpos (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i)
            calc 4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1
                ≤ 4 * B := by omega
              _ ≤ q_aux := h4B_q
              _ ≤ q_aux + J := Nat.le_add_right _ _
          have hJ_le : J ≤ 4 * W_Φ / wY := Nat.div_le_div_right (by dsimp [W]; omega)
          by_cases hcrit : (q_aux + J) * c4 < q_aux * P64Surf.Mbox W
          · -- S_4 succeeds!
            have hFR_aux : (J + R.natDegree) * (4 * wd R wY) < Fintype.card Fld :=
              (Nat.mul_le_mul (Nat.add_le_add hJ_le hRleB) (Nat.mul_le_mul_left 4 hRw_le)).trans_lt hFaux
            have haux := aux_card_le_pow u₀ u₁ q₀ hq₀ hirr hRpos
              (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
              (fun z hz i hi => (hmatch z (hVsS z hz) i).mp hi) Δ_max hdef_R q_aux hq_aux hC0 hφ hcrit hFR_aux
            have hJ_MB : J ≤ M_B := hJ_le.trans (le_max_left _ _)
            have haux2 : Vs.card ≤ M_B * yzd R q₀ + R.natDegree * (q₀ * (q_aux + 4 * W_Φ / wY)) := by
              have h1 := Nat.mul_le_mul hJ_MB h1d
              have h2 : q₀ * (q_aux + J - 1) ≤ q₀ * (q_aux + 4 * W_Φ / wY) :=
                Nat.mul_le_mul_left q₀ ((Nat.sub_le _ _).trans (Nat.add_le_add_left hJ_le q_aux))
              have h3 := Nat.mul_le_mul_left R.natDegree h2
              exact haux.trans (Nat.add_le_add h1 h3)
            have hauxQ : (Vs.card : ℚ) ≤ (M_B : ℚ) * (yzd R q₀ : ℚ) +
                (R.natDegree : ℚ) * ((q₀ : ℚ) * ((q_aux : ℚ) + (4 * W_Φ / wY : ℕ))) := by
              exact_mod_cast haux2
            have hCd_nn : (0 : ℚ) ≤ C_per_d * (yzd R q₀ : ℚ) :=
              mul_nonneg (le_trans (by norm_num) hCd_1) (Nat.cast_nonneg _)
            nlinarith only [hauxQ, hCh_aux, hCd_nn, show (0 : ℚ) ≤ (R.natDegree : ℚ) by positivity]
          · -- S_4 fails ⇒ profile bound ⇒ C7 Frobenius descent with ArkLib cutoff!
            push_neg at hcrit
            let μ : Idx → ℕ := fun i => lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i)
            have hc4_eq : (c4 : ℤ) = 8 * (∑ i, (μ i : ℤ) ^ 2) - 2 * (∑ i, (μ i : ℤ)) := by
              dsimp [c4, μ]; rw [Nat.cast_sum]; simp_rw [P64C7ProfileArithmetic.con_term]
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            have hS₂ : (∑ i, (μ i : ℤ) ^ 2) ≤ (R.natDegree : ℤ) ^ 2 * N := by
              calc _ ≤ ∑ _ : Idx, (R.natDegree : ℤ) ^ 2 := Finset.sum_le_sum fun i _ =>
                    by exact_mod_cast Nat.pow_le_pow_left (lineOrd_le_natDegree_of_irreducible hirr hRpos _ _) 2
                _ = (R.natDegree : ℤ) ^ 2 * N := by
                    rw [Finset.sum_const, Finset.card_univ, BinaryIRSProfile.card_index, nsmul_eq_mul]
                    change ((2097152 : ℕ) : ℤ) * _ = _; dsimp only [N]; push_cast; ring
            have hS₁nn : (0 : ℤ) ≤ ∑ i, (μ i : ℤ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
            have hc4_le : c4 ≤ 8 * R.natDegree ^ 2 * N := by
              exact_mod_cast (show (c4 : ℤ) ≤ 8 * R.natDegree ^ 2 * N by nlinarith only [hc4_eq, hS₂, hS₁nn])
            have hJc : J * c4 ≤ q_aux * (slack * R.natDegree ^ 2) := by
              have h1 := Nat.mul_le_mul hJ_le hc4_le
              calc J * c4 ≤ (4 * W_Φ / wY) * (8 * R.natDegree ^ 2 * N) := h1
                _ = ((4 * W_Φ / wY) * (8 * N)) * R.natDegree ^ 2 := by ring
                _ ≤ (q_aux * slack) * R.natDegree ^ 2 := Nat.mul_le_mul_right _ hslack
                _ = q_aux * (slack * R.natDegree ^ 2) := by ring
            have hM := count_slack_gen R.natDegree J c4 (P64Surf.Mbox W) q_aux slack (by omega) hJc hcrit
            have hM' : (P64Surf.Mbox W : ℤ) ≤ 8 * (∑ i, (μ i : ℤ) ^ 2) - 2 * (∑ i, (μ i : ℤ)) +
                slack * R.natDegree ^ 2 := by
              have : (P64Surf.Mbox W : ℤ) ≤ c4 + slack * R.natDegree ^ 2 := by exact_mod_cast hM
              rwa [hc4_eq] at this
            have hWcast : (W : ℤ) = 4 * wd R wY - ((A : ℤ) + 4 * Δ_max + 1) := by
              dsimp [W]; rw [Nat.cast_sub hC0]; push_cast; ring
            have hm_low := P64C7ProfileArithmetic.mbox_quadratic_lower W
            rw [hWcast] at hm_low
            have hcount : (4 * (wd R wY : ℤ) - ((A : ℤ) + 4 * Δ_max + 1)) ^ 2 +
                ((wY : ℤ) + 2) * (4 * (wd R wY : ℤ) - ((A : ℤ) + 4 * Δ_max + 1)) ≤
                2 * (wY : ℤ) * (8 * (∑ i, (μ i : ℤ) ^ 2) - 2 * (∑ i, (μ i : ℤ)) + slack * R.natDegree ^ 2) := by
              have h2wY : (2 * (wY : ℤ)) = 2097150 := by dsimp [wY]
              have hwY2 : ((wY : ℤ) + 2) = 1048577 := by dsimp [wY]
              rw [h2wY, hwY2]
              exact hm_low.trans (mul_le_mul_of_nonneg_left hM' (by norm_num))
            have hS₁ : (R.natDegree : ℤ) * ((A : ℤ) - 10000) ≤ ∑ i, (μ i : ℤ) := by
              have : R.natDegree * (A - 10000) ≤ ∑ i, μ i := by
                have : R.natDegree * A - ∑ i, μ i < 10000 * R.natDegree := by dsimp only [μ]; omega
                have : R.natDegree * A = R.natDegree * (A - 10000) + 10000 * R.natDegree := by
                  dsimp [A]; ring
                omega
              have hsubA : ((A - 10000 : ℕ) : ℤ) = (A : ℤ) - 10000 := by dsimp [A]
              rw [← hsubA]; exact_mod_cast this
            have hprof := profile_algebra_delta R.natDegree (wd R wY) (∑ i, (μ i : ℤ)) (∑ i, (μ i : ℤ) ^ 2)
              Δ_max slack 10000 (h₀ + 1) P₀ (by exact_mod_cast hbig) (by omega) (Nat.cast_nonneg _)
              (by norm_num) hS₁ hP₀ hcount
            have hc7 := card_le_of_factor_frob_c7 u₀ u₁ q₀ R.natDegree h₀ (yzd R q₀) Δ_max P₀ M₀ N_eff
              hq₀pos hh₀ hM0pos hM0 hNeff hMh R hirr hRpos q₀ hq₀pos rfl le_rfl hRyz hFR hfull_lt hprof
              Vs P Az (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
              (fun z hz => hmatch z (hVsS z hz)) (fun z hz => hbad z (hVsS z hz)) hNbound
              C_per_d C_per_h hCd_ark hCd_1 hCd_c7 hCh_ark hCh_c7
            have h4le : (4 * R.natDegree : ℚ) ≤ (M_B : ℚ) := by
              exact_mod_cast (Nat.mul_le_mul_left 4 hRleB).trans (le_max_right _ _)
            nlinarith only [hc7, h4le, show (0 : ℚ) ≤ (yzd R q₀ : ℚ) by positivity]
  -- Sum over all normalized factors of Φ!
  have hsum_d : ∑ R ∈ factors Φ, yzd R q₀ ≤ H + q₀ * B :=
    (sum_yz_le Φ hΦ q₀).trans hΦ_yz
  have hsum_h : ∑ R ∈ factors Φ, R.natDegree ≤ B := (sum_natDegree_le Φ hΦ).trans hB
  have hsum_fac : (∑ R ∈ factors Φ, ((caseSingle Φ S P R).card : ℚ)) ≤
      (C_per_d + (M_B : ℚ)) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) + C_per_h * (B : ℚ) := by
    calc _ ≤ ∑ R ∈ factors Φ, (C_per_d * (yzd R q₀ : ℚ) + (M_B : ℚ) * (yzd R q₀ : ℚ) +
              C_per_h * (R.natDegree : ℚ)) := Finset.sum_le_sum hfac
      _ = (C_per_d + (M_B : ℚ)) * (∑ R ∈ factors Φ, (yzd R q₀ : ℚ)) +
          C_per_h * (∑ R ∈ factors Φ, (R.natDegree : ℚ)) := by
            simp_rw [← add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (C_per_d + (M_B : ℚ)) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) + C_per_h * (B : ℚ) := by
            have hdQ : (∑ R ∈ factors Φ, (yzd R q₀ : ℚ)) ≤ (H : ℚ) + (q₀ : ℚ) * (B : ℚ) := by
              exact_mod_cast hsum_d
            have hhQ : (∑ R ∈ factors Φ, (R.natDegree : ℚ)) ≤ (B : ℚ) := by exact_mod_cast hsum_h
            have h1 : (0 : ℚ) ≤ C_per_d + (M_B : ℚ) := by
              have := le_trans (by norm_num : (0 : ℚ) ≤ 1) hCd_1; positivity
            have h2 : (0 : ℚ) ≤ C_per_h := le_trans (by positivity) hCh_ark
            nlinarith only [hdQ, hhQ, h1, h2]
  have hcovQ : (S.card : ℚ) ≤ (caseY0 Φ S).card + (casePair Φ S P).card +
      ∑ R ∈ factors Φ, ((caseSingle Φ S P R).card : ℚ) := by exact_mod_cast hcover
  have hY0Q : ((caseY0 Φ S).card : ℚ) ≤ (H : ℚ) := by exact_mod_cast hY0
  have hpairQ : ((casePair Φ S P).card : ℚ) ≤ (B : ℚ) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) := by
    exact_mod_cast hpair
  have hM_B_cast : (M_B : ℚ) = max ((4 * W_Φ / wY : ℕ) : ℚ) (4 * (B : ℚ)) := by
    dsimp only [M_B]; rw [Nat.cast_max]; push_cast; rfl
  nlinarith only [hcovQ, hY0Q, hpairQ, hsum_fac, hM_B_cast]
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower

#print axioms ProximityPrize.SubmissionBinaryLower.B6402HybridP64.hybrid_p64_card_le
