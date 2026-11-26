import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid1
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

theorem profile_algebra_delta (h w S₁ S₂ Δ slack β₀ h_top P₀ : ℤ)
    (hh : h_top ≤ h) (h_top_pos : 1 ≤ h_top) (hΔ : 0 ≤ Δ) (hβ0_nn : 0 ≤ β₀)
    (hS₁ : h * (A - β₀) ≤ S₁)
    (hP₀ : 8 * (wY : ℤ) * slack * h_top ^ 2 +
      16 * (wY : ℤ) * ((A : ℤ) - wY + β₀) * h_top + ((wY : ℤ) + 2) ^ 2 ≤
      64 * (wY : ℤ) * P₀ * h_top ^ 2)
    (hcount : (4 * w - ((A : ℤ) + 4 * Δ + 1)) ^ 2 + ((wY : ℤ) + 2) * (4 * w - ((A : ℤ) + 4 * Δ + 1)) ≤
      2 * (wY : ℤ) * (8 * S₂ - 2 * S₁ + slack * h ^ 2)) :
    2 * h * w - h ^ 2 * (wY : ℤ) - S₂ ≤ P₀ * h ^ 2 + 2 * Δ * h := by
  let D : ℤ := (wY : ℤ)
  let C₀ : ℤ := (A : ℤ) + 4 * Δ + 1
  have hsq : 0 ≤ (8 * (w - h * D) - (2 * C₀ - D - 2)) ^ 2 := sq_nonneg _
  have hid : 4 * ((4 * w - C₀) ^ 2 + (D + 2) * (4 * w - C₀)) =
      64 * D * (2 * h * w - h ^ 2 * D) + (8 * (w - h * D) - (2 * C₀ - D - 2)) ^ 2 -
        (D + 2) ^ 2 - 16 * D * (2 * C₀ - D - 2) * h := by ring
  have hDpos : (0 : ℤ) < D := by dsimp [D, wY]; norm_num
  have hstep1 : 64 * D * (2 * h * w - h ^ 2 * D - S₂) ≤
      8 * D * slack * h ^ 2 + 16 * D * ((A : ℤ) - D + β₀ + 8 * Δ) * h + (D + 2) ^ 2 := by
    have h4 : 4 * ((4 * w - C₀) ^ 2 + (D + 2) * (4 * w - C₀)) ≤
        8 * D * (8 * S₂ - 2 * S₁ + slack * h ^ 2) := by
      dsimp [D, C₀]; linarith
    have hC0eq : 2 * C₀ - D - 2 = 2 * (A : ℤ) - D + 8 * Δ := by dsimp [C₀]; ring
    have hS1' : 16 * D * (h * (A - β₀)) ≤ 16 * D * S₁ :=
      mul_le_mul_of_nonneg_left hS₁ (by positivity)
    nlinarith only [hid, hsq, h4, hC0eq, hS1']
  -- Scale hP₀ by h² / h_top² using h_top ≤ h:
  have hht_pos : 0 < h_top := by omega
  have hh_pos : 0 < h := by omega
  have hscale1 : h_top * h ≤ h ^ 2 := by nlinarith
  have hscale2 : h_top ^ 2 ≤ h ^ 2 := by nlinarith
  have hP0_h : 8 * D * slack * h ^ 2 + 16 * D * ((A : ℤ) - D + β₀) * h + (D + 2) ^ 2 ≤
      64 * D * P₀ * h ^ 2 := by
    have hmul : (8 * D * slack * h_top ^ 2 + 16 * D * ((A : ℤ) - D + β₀) * h_top + (D + 2) ^ 2) * h ^ 2 ≤
        (64 * D * P₀ * h_top ^ 2) * h ^ 2 :=
      mul_le_mul_of_nonneg_right hP₀ (sq_nonneg h)
    have hA_ge : 0 ≤ 16 * D * ((A : ℤ) - D + β₀) := by
      have : (0 : ℤ) ≤ (A : ℤ) - D := by dsimp [D, A, wY]; norm_num
      nlinarith
    have hterm1 : (16 * D * ((A : ℤ) - D + β₀) * h) * h_top ^ 2 ≤
        (16 * D * ((A : ℤ) - D + β₀) * h_top) * h ^ 2 := by
      calc (16 * D * ((A : ℤ) - D + β₀) * h) * h_top ^ 2
          = (16 * D * ((A : ℤ) - D + β₀)) * (h_top * h) * h_top := by ring
        _ ≤ (16 * D * ((A : ℤ) - D + β₀)) * (h_top * h) * h :=
            mul_le_mul_of_nonneg_left hh (mul_nonneg hA_ge (mul_nonneg hht_pos.le hh_pos.le))
        _ = (16 * D * ((A : ℤ) - D + β₀) * h_top) * h ^ 2 := by ring
    have hterm2 : (D + 2) ^ 2 * h_top ^ 2 ≤ (D + 2) ^ 2 * h ^ 2 :=
      mul_le_mul_of_nonneg_left hscale2 (sq_nonneg _)
    have htot : (8 * D * slack * h ^ 2 + 16 * D * ((A : ℤ) - D + β₀) * h + (D + 2) ^ 2) * h_top ^ 2 ≤
        (64 * D * P₀ * h ^ 2) * h_top ^ 2 := by nlinarith only [hmul, hterm1, hterm2]
    exact le_of_mul_le_mul_right htot (pow_pos hht_pos 2)
  have hfin : 64 * D * (2 * h * w - h ^ 2 * D - S₂) ≤ 64 * D * (P₀ * h ^ 2 + 2 * Δ * h) := by
    nlinarith only [hstep1, hP0_h]
  exact le_of_mul_le_mul_left hfin (by positivity)

lemma count_slack_gen (h J c m q_aux slack : ℕ) (hqpos : 0 < q_aux)
    (hJc : J * c ≤ q_aux * (slack * h ^ 2))
    (hcrit : q_aux * m ≤ (q_aux + J) * c) : m ≤ c + slack * h ^ 2 := by
  by_contra hn
  have hm : c + slack * h ^ 2 + 1 ≤ m := by omega
  have hm' := Nat.mul_le_mul_left q_aux hm
  nlinarith only [hcrit, hJc, hm', hqpos]
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
