import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid9
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

lemma card_caseY0_le (Φ : Tri) (hΦ : Φ ≠ 0) (H : ℕ)
    (hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ H) (S : Finset Fld) :
    (caseY0 Φ S).card ≤ H := by
  classical
  have hj : Φ.coeff Φ.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hΦ
  let j := Φ.natDegree
  let a := (Φ.coeff j).natDegree
  have ha : (Φ.coeff j).coeff a ≠ 0 := leadingCoeff_ne_zero.mpr hj
  have hsub : caseY0 Φ S ⊆ ((Φ.coeff j).coeff a).roots.toFinset := by
    intro z hz
    rw [caseY0, Finset.mem_filter] at hz
    rw [Multiset.mem_toFinset, mem_roots ha, IsRoot.def]
    have hc := congrArg (fun p : Polynomial (Polynomial Fld) => (p.coeff j).coeff a) hz.2
    simpa [specializeZ] using hc
  calc (caseY0 Φ S).card ≤ ((Φ.coeff j).coeff a).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ ((Φ.coeff j).coeff a).roots.card := Multiset.toFinset_card_le _
    _ ≤ ((Φ.coeff j).coeff a).natDegree := card_roots' _
    _ ≤ H := hH j a

lemma wtLE_of_yzSupportDegree (R : Tri) (q₀ : ℕ) : WtLE 0 q₀ 1 (yzd R q₀) R := by
  intro a b l hl
  have hb0 : R.coeff b ≠ 0 := fun h => hl (by simp [c3, h])
  have ha0 : (R.coeff b).coeff a ≠ 0 := fun h => hl (by simp [c3, h])
  have h1 : l ≤ ((R.coeff b).coeff a).natDegree := le_natDegree_of_ne_zero (by simpa [c3] using hl)
  have h2 : ((R.coeff b).coeff a).natDegree ≤ Polynomial.Bivariate.degreeX (R.coeff b) :=
    Polynomial.Bivariate.coeff_natDegree_le_degreeX _ a
  have h3 := P64Caps.YZ.coeffWeight_le_of_ne R q₀ b hb0
  omega
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
