import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid5
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

theorem tight_c7_separable (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (hsep : Polynomial.derivative R ≠ 0) (w q d Δ P₀ M₀ N_eff : ℕ) (hq : 0 < q)
    (hRw : wd R wY ≤ w) (hRyz : WtLE 0 q 1 d R)
    (hF : 2 * R.natDegree * w < Fintype.card Fld)
    (y : Idx → Fld[X]) (hy : ∀ i, (y i).natDegree ≤ q)
    (hM0 : (M₀ : ℤ) + P₀ = (A : ℤ) - wY) (hM0pos : 0 < M₀)
    (hNeff : (N_eff : ℤ) = (A : ℤ) - wY + Δ)
    (hMh : 2 * N_eff ≤ M₀ * R.natDegree)
    (hprofile : 2 * (R.natDegree : ℤ) * w - R.natDegree ^ 2 * wY -
      (∑ i, (lineOrd R (BinaryIRSProfile.domain i) (y i) : ℤ) ^ 2) ≤
      P₀ * R.natDegree ^ 2 + 2 * Δ * R.natDegree)
    (hfull : (P64C7Case.fullLines R BinaryIRSProfile.domain y).card < A)
    (S : Finset Fld) (P : Fld → Fld[X]) (Aset : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Aset z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Aset z ↔ (P z).eval (BinaryIRSProfile.domain i) = (y i).eval z)
    (hNbound : ∀ z ∈ S,
      normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤ ((Aset z).card : ℤ) - wY ∨
      normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤ N_eff) :
    M₀ * S.card ≤ 2 * N_eff * N * (6 * d + 2 * q * R.natDegree + 2) +
      M₀ * (N * d + 2 * R.natDegree * d) := by
  classical
  let good := S.filter fun z => Aset z ⊆ lam BinaryIRSProfile.domain y R ∧ derivativeAlong R (P z) z ≠ 0
  let missing := S.filter fun z => ¬ Aset z ⊆ lam BinaryIRSProfile.domain y R
  let dead := S.filter fun z => derivativeAlong R (P z) z = 0
  have hqh := P64C6Retained.outer_weight_le R hirr.ne_zero q d hRyz
  have hd : 1 ≤ d := by have := Nat.mul_pos hq (by omega : 0 < R.natDegree); omega
  have hμgood : ∀ z ∈ good, ∀ i ∈ Aset z, 1 ≤ lineOrd R (BinaryIRSProfile.domain i) (y i) := by
    intro z hz i hi
    have hline := (Finset.mem_filter.mp hz).2.1 hi
    have hp := (Finset.mem_filter.mp hline).2; omega
  have hproper : ∀ z ∈ good, ∃ i ∈ Aset z, lineOrd R (BinaryIRSProfile.domain i) (y i) < R.natDegree := by
    intro z hz; by_contra hn; push_neg at hn
    have hsub : Aset z ⊆ P64C7Case.fullLines R BinaryIRSProfile.domain y := by
      intro i hi; apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, le_antisymm (lineOrd_le_natDegree_of_irreducible hirr hh _ _) (hn i hi)⟩
    have := (Finset.card_le_card hsub).trans_lt hfull
    have := hcard z (Finset.mem_filter.mp hz).1; omega
  have hgood : M₀ * good.card ≤ 2 * N_eff * N * (6 * d + 2 * q * R.natDegree + 2) := by
    let h := R.natDegree
    let μ : Idx → ℕ := fun i => lineOrd R (BinaryIRSProfile.domain i) (y i)
    let Nz : Fld → ℕ := fun z => (normalDefect R BinaryIRSProfile.domain y (Aset z) w wY).toNat
    have hN : ∀ z ∈ good, 0 < normalDefect R BinaryIRSProfile.domain y (Aset z) w wY := by
      intro z hz; obtain ⟨i, hi, hin⟩ := hproper z hz
      exact P64C7Aggregate.positive_defect R hirr hh wY w q d hd hqh hRw hRyz
        BinaryIRSProfile.domain y hy z (P z) (Aset z)
        (hP z (Finset.mem_filter.mp hz).1) (hcurve z (Finset.mem_filter.mp hz).1)
        (Finset.mem_filter.mp hz).2.2 (hμgood z hz)
        (fun j hj => (hmatch z (Finset.mem_filter.mp hz).1 j).mp hj) i hi hin
    have hNeq : ∀ z ∈ good, (Nz z : ℤ) = normalDefect R BinaryIRSProfile.domain y (Aset z) w wY :=
      fun z hz => Int.toNat_of_nonneg (hN z hz).le
    have hNp : ∀ z ∈ good, 0 < Nz z := fun z hz => by have := hNeq z hz; have := hN z hz; omega
    let C := ∏ z ∈ good, (2 * Nz z)
    let τ : Fld → ℕ := fun z => C / (2 * Nz z)
    have hC : 0 < C := Finset.prod_pos (fun z hz => Nat.mul_pos (by norm_num) (hNp z hz))
    have hτeq : ∀ z ∈ good, 2 * τ z * Nz z = C := by
      intro z hz
      have hdvd : 2 * Nz z ∣ C := Finset.dvd_prod_of_mem (fun z => 2 * Nz z) hz
      have he := Nat.mul_div_cancel' hdvd
      change 2 * (C / (2 * Nz z)) * Nz z = C; nlinarith only [he]
    have hτ : ∀ z ∈ good, 2 * (τ z : ℤ) * normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤ C := by
      intro z hz; rw [← hNeq z hz]; exact_mod_cast (hτeq z hz).le
    have hc := tight_weighted_mass_le R hirr hh w q d C hqh hC hRw hRyz y hy good P Aset τ
      (fun z hz => hP z (Finset.mem_filter.mp hz).1)
      (fun z hz => hcurve z (Finset.mem_filter.mp hz).1)
      (fun _ hz => (Finset.mem_filter.mp hz).2.2) hμgood
      (fun z hz => hmatch z (Finset.mem_filter.mp hz).1) hτ
    have hμh : ∀ i, μ i ≤ h := fun i => lineOrd_le_natDegree_of_irreducible hirr hh _ _
    have hpoint : ∀ z ∈ good, M₀ * (C * h ^ 2) ≤ 2 * N_eff * (τ z * P64C7Aggregate.mass h μ (Aset z)) := by
      intro z hz
      have hzS := (Finset.mem_filter.mp hz).1
      have hNb : (Nz z : ℤ) ≤ ((Aset z).card : ℤ) - wY ∨ (Nz z : ℤ) ≤ N_eff := by
        rw [hNeq z hz]; exact hNbound z hzS
      have hl := mass_lower_frob_exact h w (Nz z) Δ P₀ M₀ N_eff μ (Aset z) hμh (hμgood z hz)
        (hcard z hzS) (hNeq z hz) hM0 hNeff hMh hNb hprofile
      have hm := Nat.mul_le_mul_left (2 * τ z) hl
      have he := congrArg (fun k : ℕ => M₀ * k * h ^ 2) (hτeq z hz)
      nlinarith only [hm, he]
    have hs := Finset.sum_le_sum hpoint
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
    have htot : (C * h ^ 2) * (M₀ * good.card) ≤
        (C * h ^ 2) * (2 * N_eff * N * (6 * d + 2 * q * h + 2)) := by
      nlinarith only [hc, hs]
    exact Nat.le_of_mul_le_mul_left htot (Nat.mul_pos hC (pow_pos (by dsimp [h]; omega) 2))
  have hmissing : missing.card ≤ N * d := card_missing_le R hirr.ne_zero q d N hRyz
    (by rw [BinaryIRSProfile.card_index]; rfl) BinaryIRSProfile.domain y hy S P Aset hcurve
    (fun z hz i hi => (hmatch z hz i).mp hi)
  have hdead : dead.card ≤ 2 * R.natDegree * d :=
    card_derivative_zero_le R hirr (by omega) hsep wY w q d hRw hRyz hF S P hcurve
  have hcover : S ⊆ good ∪ missing ∪ dead := by
    intro z hz
    by_cases ha : Aset z ⊆ lam BinaryIRSProfile.domain y R
    · by_cases hd0 : derivativeAlong R (P z) z = 0
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hd0⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, ha, hd0⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, ha⟩))
  have hScard : S.card ≤ good.card + missing.card + dead.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  nlinarith only [hScard, hgood, hmissing, hdead]
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
