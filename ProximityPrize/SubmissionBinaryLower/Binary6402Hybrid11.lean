import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid10
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

theorem cofactor_defect_of_single_factor
    (Φ R : Tri) (hΦ : Φ ≠ 0) (hR : R ∈ factors Φ) (q₀ : ℕ) (u₀ u₁ : Idx → Fld)
    (m Δ_max : ℕ) (S : Finset Fld) (P : Fld → Fld[X]) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hΦgap : ∀ z ∈ S,
      (wd Φ wY : ℤ) - (∑ i ∈ Az z, (lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
        (2 * m : ℤ) * ((Az z).card - (A : ℤ)) ≤ Δ_max)
    (ham : ∀ a Q'', Φ = R ^ a * Q'' → ¬ R ∣ Q'' → a ≤ 2 * m) :
    ∀ z ∈ caseSingle Φ S P R,
      ((wd R wY : ℤ) - ∑ i ∈ Az z, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
        ((Az z).card - (A : ℤ)) ≤ Δ_max := by
  classical
  intro z hz
  rw [caseSingle, Finset.mem_filter] at hz
  obtain ⟨hzS, _, hRz, hsingle⟩ := hz
  have hirr : Irreducible R :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Tri) R (Multiset.mem_toFinset.mp hR)).irreducible
  obtain ⟨a, Q'', hndvd, hΦeq⟩ := WfDvdMonoid.max_power_factor (α := Tri) hΦ hirr
  have hR0 : R ≠ 0 := hirr.ne_zero
  have hQ''0 : Q'' ≠ 0 := by rintro rfl; exact hΦ (by rw [hΦeq, mul_zero])
  have hapos : 1 ≤ a := by
    by_contra h0; have ha0 : a = 0 := by omega
    subst ha0; rw [pow_zero, one_mul] at hΦeq
    exact hndvd (hΦeq ▸ UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hR))
  have ha_le : a ≤ 2 * m := ham a Q'' hΦeq hndvd
  have hQ''ne : triEval Q'' z (P z) ≠ 0 := by
    intro h0
    obtain ⟨R', hR'mem, hR'0⟩ := exists_normalizedFactor_triEval_eq_zero Q'' hQ''0 z (P z) h0
    have hR'irr : Irreducible R' :=
      (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Tri) R' hR'mem).irreducible
    have hd1 := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (α := Tri) hR'mem
    obtain ⟨q', hq'mem, hR'q'⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd (α := Tri)
      hΦ hR'irr (hΦeq ▸ dvd_mul_of_dvd_right hd1 (R ^ a))
    have hq'0 : triEval q' z (P z) = 0 := by
      obtain ⟨u, hu⟩ := hR'q'
      rw [← hu]
      exact (P64Cofactor.triEval_mul z (P z) R' u).trans (by rw [hR'0, zero_mul])
    have heqR := hsingle q' (Multiset.mem_toFinset.mpr hq'mem) hq'0
    subst heqR
    exact hndvd (hR'q'.symm.dvd.trans hd1)
  have hmult : ∀ i ∈ Az z,
      lineOrd Q'' (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) ≤
        (triEval Q'' z (P z)).rootMultiplicity (BinaryIRSProfile.domain i) := fun i hi =>
    le_rootMultiplicity_triEval Q'' (BinaryIRSProfile.domain i) z (linePow u₀ u₁ q₀ i) (P z) _
      ((ordGE_iff hQ''0 _ _ _).mpr le_rfl) (by rw [eval_linePow]; exact hmatch z hzS i hi) hQ''ne
  have hsumQ'' : ∑ i ∈ Az z, lineOrd Q'' (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) ≤ wd Q'' wY :=
    (Finset.sum_le_sum hmult).trans ((sum_rootMultiplicity_le_natDegree _ _ (Az z)).trans
      (natDegree_triEval_le Q'' z (P z) wY (hP z hzS)))
  have hw_add : wd Φ wY = a * wd R wY + wd Q'' wY := by
    rw [hΦeq, P64Caps.Weighted.weightedSupportDegree_mul _ _ _ (pow_ne_zero a hR0) hQ''0,
      weightedSupportDegree_pow R hR0]
  have hord_add : ∀ i, lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) =
      a * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) +
        lineOrd Q'' (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) := by
    intro i; rw [hΦeq, lineOrd_mul (pow_ne_zero a hR0) hQ''0, lineOrd_pow hR0]
  have hgap := hΦgap z hzS
  simp_rw [hord_add, Nat.cast_add, Nat.cast_mul] at hgap
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hgap
  have hwZ : (wd Φ wY : ℤ) = a * wd R wY + wd Q'' wY := by exact_mod_cast hw_add
  have hQ''Z : (∑ i ∈ Az z, (lineOrd Q'' (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) ≤ wd Q'' wY := by
    exact_mod_cast hsumQ''
  have hAcard : (A : ℤ) ≤ (Az z).card := by exact_mod_cast hcard z hzS
  have haZ1 : (1 : ℤ) ≤ a := by exact_mod_cast hapos
  have haZ2 : (a : ℤ) ≤ 2 * m := by exact_mod_cast ha_le
  have hterm : (a : ℤ) * (((wd R wY : ℤ) - ∑ i ∈ Az z, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
      ((Az z).card - (A : ℤ))) ≤ Δ_max := by
    nlinarith only [hgap, hwZ, hQ''Z, hAcard, haZ2]
  have hΔnn : (0 : ℤ) ≤ Δ_max := Nat.cast_nonneg Δ_max
  nlinarith only [hterm, haZ1, hΔnn]
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
