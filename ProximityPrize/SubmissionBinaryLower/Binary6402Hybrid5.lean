import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid4
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

theorem mass_lower_frob_exact (h w Nz Δ P₀ M₀ N_eff : ℕ) (μ : Idx → ℕ) (Aset : Finset Idx)
    (hμh : ∀ i, μ i ≤ h) (hμ : ∀ i ∈ Aset, 1 ≤ μ i)
    (hcard : A ≤ Aset.card)
    (hN : (Nz : ℤ) = (w : ℤ) - wY - ∑ i ∈ Aset, ((μ i - 1 : ℕ) : ℤ))
    (hM0 : (M₀ : ℤ) + P₀ = (A : ℤ) - wY)
    (hNeff : (N_eff : ℤ) = (A : ℤ) - wY + Δ)
    (hMh : 2 * N_eff ≤ M₀ * h)
    (hNbound : (Nz : ℤ) ≤ (Aset.card : ℤ) - wY ∨ (Nz : ℤ) ≤ N_eff)
    (hprofile : 2 * (h : ℤ) * w - h ^ 2 * wY - (∑ i, (μ i : ℤ) ^ 2) ≤ P₀ * h ^ 2 + 2 * Δ * h) :
    M₀ * h ^ 2 * Nz ≤ N_eff * P64C7Aggregate.mass h μ Aset := by
  have hm := P64C7Mass.mass_identity h μ Aset hμh
  have hN' : (Nz : ℤ) = (w : ℤ) - wY - (∑ i ∈ Aset, (μ i : ℤ)) + Aset.card :=
    hN.trans (P64C7Mass.defect_identity μ Aset w wY hμ)
  have he : (P64C7Aggregate.mass h μ Aset : ℤ) =
      ((h : ℤ) ^ 2 - 2 * h) * ((Aset.card : ℤ) - wY) + 2 * h * Nz -
        (2 * h * w - h ^ 2 * wY - (∑ i, (μ i : ℤ) ^ 2)) := by
    nlinarith only [hm, congrArg (fun t : ℤ => 2 * h * t) hN']
  have hmass_lb : (P64C7Aggregate.mass h μ Aset : ℤ) ≥
      ((h : ℤ) ^ 2 - 2 * h) * ((Aset.card : ℤ) - wY) + 2 * h * Nz - P₀ * h ^ 2 - 2 * Δ * h := by
    linarith
  have hMhZ : 2 * (N_eff : ℤ) ≤ (M₀ : ℤ) * h := by exact_mod_cast hMh
  have hcardZ : (A : ℤ) ≤ Aset.card := by exact_mod_cast hcard
  have hE_nn : (0 : ℤ) ≤ (Aset.card : ℤ) - A := by linarith
  have hh_nn : (0 : ℤ) ≤ h := Nat.cast_nonneg h
  have hPΔ_nn : (0 : ℤ) ≤ (P₀ : ℤ) + Δ := by positivity
  have hgoal : (M₀ : ℤ) * h ^ 2 * Nz ≤ N_eff * P64C7Aggregate.mass h μ Aset := by
    rcases hNbound with hbr1 | hbr2
    · set δ : ℤ := ((Aset.card : ℤ) - wY) - Nz
      set E : ℤ := (Aset.card : ℤ) - A
      have hδ_nn : 0 ≤ δ := by dsimp [δ]; linarith
      have h1 : 0 ≤ (h : ℤ) * ((Δ : ℤ) + δ) * ((M₀ : ℤ) * h - 2 * N_eff) :=
        mul_nonneg (mul_nonneg hh_nn (by linarith)) (by linarith)
      have h2 : 0 ≤ (h : ℤ) ^ 2 * E * ((P₀ : ℤ) + Δ) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hE_nn) hPΔ_nn
      have hNeff_nn : (0 : ℤ) ≤ N_eff := Nat.cast_nonneg N_eff
      have hm1 := mul_le_mul_of_nonneg_left hmass_lb hNeff_nn
      have hid : (N_eff : ℤ) * (((h : ℤ) ^ 2 - 2 * h) * ((Aset.card : ℤ) - wY) + 2 * h * Nz - P₀ * h ^ 2 - 2 * Δ * h) -
          (M₀ : ℤ) * h ^ 2 * Nz =
          (h : ℤ) * ((Δ : ℤ) + δ) * ((M₀ : ℤ) * h - 2 * N_eff) + (h : ℤ) ^ 2 * E * ((P₀ : ℤ) + Δ) := by
        have hP0 : (P₀ : ℤ) = (A : ℤ) - wY - M₀ := by linarith
        rw [hP0, hNeff]; dsimp [δ, E]; ring
      linarith
    · have h1 : 0 ≤ (h : ℤ) * ((N_eff : ℤ) - Nz) * ((M₀ : ℤ) * h - 2 * N_eff) :=
        mul_nonneg (mul_nonneg hh_nn (by linarith)) (by linarith)
      have hNeff_pos : (0 : ℤ) < N_eff := by
        have : (0 : ℤ) < (A : ℤ) - wY := by dsimp [A, wY]; norm_num
        linarith
      have h2 : 0 ≤ (N_eff : ℤ) * (((h : ℤ) ^ 2 - 2 * h) * ((Aset.card : ℤ) - A)) := by
        have hMle : (M₀ : ℤ) ≤ N_eff := by linarith
        have hh2 : (2 : ℤ) ≤ h := by nlinarith only [hMhZ, hMle, hNeff_pos]
        exact mul_nonneg hNeff_pos.le (mul_nonneg (by nlinarith only [hh2]) hE_nn)
      have hm1 := mul_le_mul_of_nonneg_left hmass_lb hNeff_pos.le
      have hid2 : (N_eff : ℤ) * (((h : ℤ) ^ 2 - 2 * h) * ((Aset.card : ℤ) - wY) + 2 * h * Nz - P₀ * h ^ 2 - 2 * Δ * h) -
          (M₀ : ℤ) * h ^ 2 * Nz =
          (h : ℤ) * ((N_eff : ℤ) - Nz) * ((M₀ : ℤ) * h - 2 * N_eff) +
            (N_eff : ℤ) * (((h : ℤ) ^ 2 - 2 * h) * ((Aset.card : ℤ) - A)) := by
        have hP0 : (P₀ : ℤ) = (A : ℤ) - wY - M₀ := by linarith
        rw [hP0, hNeff]; ring
      linarith
  exact_mod_cast hgoal
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
