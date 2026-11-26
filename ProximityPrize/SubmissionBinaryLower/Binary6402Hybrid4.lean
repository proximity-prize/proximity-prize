import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid3
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

theorem tight_single_line_missing (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (w q d C : ℕ) (hqh : q * R.natDegree ≤ d) (hC : 0 < C)
    (hRw : wd R wY ≤ w) (hRyz : WtLE 0 q 1 d R)
    (y : Idx → Fld[X]) (i : Idx) (hy : (y i).natDegree ≤ q)
    (S : Finset Fld) (P : Fld → Fld[X]) (Aset : Fld → Finset Idx) (τ : Fld → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ j ∈ Aset z, 1 ≤ lineOrd R (BinaryIRSProfile.domain j) (y j))
    (hmatch : ∀ z ∈ S, ∀ j ∈ Aset z, (P z).eval (BinaryIRSProfile.domain j) = (y j).eval z)
    (hmiss : ∀ z ∈ S, (P z).eval (BinaryIRSProfile.domain i) ≠ (y i).eval z)
    (hτ : ∀ z ∈ S, 2 * (τ z : ℤ) * normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤ C) :
    ∑ z ∈ S, τ z * lineOrd R (BinaryIRSProfile.domain i) (y i) ^ 2 ≤
      C * R.natDegree ^ 2 * (4 * d + 1) := by
  classical
  let h := R.natDegree
  let μ := lineOrd R (BinaryIRSProfile.domain i) (y i)
  change ∑ z ∈ S, τ z * μ ^ 2 ≤ C * h ^ 2 * (4 * d + 1)
  by_cases hμ0 : μ = 0
  · simp [hμ0]
  have hμpos : 0 < μ := Nat.pos_of_ne_zero hμ0
  have hμh : μ ≤ h := lineOrd_le_natDegree_of_irreducible hirr hh (BinaryIRSProfile.domain i) (y i)
  have hqd : q * μ ≤ d := (Nat.mul_le_mul_left q hμh).trans hqh
  obtain ⟨ν, R'', _, hR0, hu⟩ := P64C7Slice.exists_slice R hirr hh (BinaryIRSProfile.domain i) (y i)
  let E := P64C7Parameters.negativeParameter h d μ
  have hc := P64C7Bessel.weighted_orders_le R hirr wY w q d (2 * h - μ) E (2 * h) (C * μ) ν
    hRw hRyz BinaryIRSProfile.domain y i hy R'' hR0 hu hμh hqd (by omega) (Nat.succ_pos _)
    (Nat.mul_pos hC hμpos) (by omega) (P64C7Parameters.negative_leading h q d μ (by omega) hμpos hμh)
    S P Aset (fun z => τ z * μ ^ 2) hP hcurve hderiv hμ hmatch hmiss (fun z hz => ?_)
  · have hμE : μ * E ≤ 4 * h * d + h := by
      have he := Nat.mul_div_le (4 * h * d) μ
      unfold E P64C7Parameters.negativeParameter
      rw [Nat.mul_add, Nat.mul_one]
      omega
    calc ∑ z ∈ S, τ z * μ ^ 2 ≤ h * (C * μ) * E := hc
      _ = C * h * (μ * E) := by ring
      _ ≤ C * h * (4 * h * d + h) := Nat.mul_le_mul_left _ hμE
      _ = C * h ^ 2 * (4 * d + 1) := by ring
  · have he : ((2 * h : ℕ) : ℤ) - (2 * h - μ : ℕ) = μ := by
      rw [Nat.cast_sub (by omega : μ ≤ 2 * h)]; omega
    rw [he]
    have ht := mul_le_mul_of_nonneg_right (hτ z hz) (show 0 ≤ (μ : ℤ) ^ 2 by positivity)
    push_cast; nlinarith only [ht]

theorem tight_single_line_matched (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (w q d C : ℕ) (hC : 0 < C)
    (hRw : wd R wY ≤ w) (hRyz : WtLE 0 q 1 d R)
    (y : Idx → Fld[X]) (hy : ∀ j, (y j).natDegree ≤ q) (i : Idx)
    (S : Finset Fld) (P : Fld → Fld[X]) (Aset : Fld → Finset Idx) (τ : Fld → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ j ∈ Aset z, 1 ≤ lineOrd R (BinaryIRSProfile.domain j) (y j))
    (hmatch : ∀ z ∈ S, ∀ j ∈ Aset z, (P z).eval (BinaryIRSProfile.domain j) = (y j).eval z)
    (hi : ∀ z ∈ S, i ∈ Aset z)
    (hτ : ∀ z ∈ S, 2 * (τ z : ℤ) * normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤ C) :
    ∑ z ∈ S, τ z * (R.natDegree - lineOrd R (BinaryIRSProfile.domain i) (y i)) ^ 2 ≤
      C * R.natDegree ^ 2 * (2 * d + 2 * q * R.natDegree + 1) := by
  classical
  let h := R.natDegree
  let μ := lineOrd R (BinaryIRSProfile.domain i) (y i)
  change ∑ z ∈ S, τ z * (h - μ) ^ 2 ≤ C * h ^ 2 * (2 * d + 2 * q * h + 1)
  have hμh : μ ≤ h := lineOrd_le_natDegree_of_irreducible hirr hh (BinaryIRSProfile.domain i) (y i)
  by_cases hfull : μ = h
  · simp [hfull]
  have hμlt : μ < h := by omega
  let σ : Idx → ℕ := fun j => if j = i then 2 * h else 0
  let U := h + μ
  let E := P64C7Parameters.positiveParameter h q d μ
  have hσ : ∀ j, q * σ j < E := by
    intro j; by_cases hj : j = i
    · simpa [σ, hj] using P64C7Parameters.positive_weight h q d μ
    · simp only [σ, if_neg hj, Nat.mul_zero]; exact Nat.succ_pos _
  have hlead : (∑ j, P64C6Scale.quadraticCost q d E (σ j) (lineOrd R (BinaryIRSProfile.domain j) (y j))) <
      6 * (h : ℤ) * U * E := by
    have he : (∑ j, P64C6Scale.quadraticCost q d E (σ j) (lineOrd R (BinaryIRSProfile.domain j) (y j))) =
        P64C6Scale.quadraticCost q d E (2 * h) μ := by
      have ht : ∀ j, P64C6Scale.quadraticCost q d E (σ j) (lineOrd R (BinaryIRSProfile.domain j) (y j)) =
          if j = i then P64C6Scale.quadraticCost q d E (2 * h) μ else 0 := by
        intro j; by_cases hj : j = i <;> simp [σ, hj, μ, P64C6Scale.quadraticCost]
      simp_rw [ht]; simp
    rw [he]
    exact P64C7Parameters.positive_leading h q d μ (by omega) hμlt
  have hb : ∀ z ∈ S, P64C6Bessel.bias σ (Aset z) U = (h - μ : ℕ) := by
    intro z hz
    have hs : ∑ j ∈ Aset z, σ j = 2 * h := by simp [σ, hi z hz]
    have hs' : ∑ j ∈ Aset z, (σ j : ℤ) = 2 * h := by exact_mod_cast hs
    unfold P64C6Bessel.bias
    rw [hs', Nat.cast_sub hμh]; dsimp [U]; push_cast; ring
  have hc := P64C6Bessel.weighted_orders_le R hirr wY w q d U E (C * (h - μ)) hRw hRyz
    BinaryIRSProfile.domain y hy σ (by dsimp [U, h]; omega) (Nat.succ_pos _)
    (Nat.mul_pos hC (Nat.sub_pos_of_lt hμlt)) hσ hlead S P Aset
    (fun z => τ z * (h - μ) ^ 2) hP hcurve hderiv hμ hmatch (fun z hz => ?_) (fun z hz => ?_)
  · have hE : (h - μ) * E ≤ 2 * h * d + 2 * q * h ^ 2 + h := by
      have he := Nat.mul_div_le (2 * h * d) (h - μ)
      have ht : h - μ ≤ h := Nat.sub_le _ _
      have hm := Nat.mul_le_mul_right (2 * q * h) ht
      unfold E P64C7Parameters.positiveParameter
      nlinarith
    calc ∑ z ∈ S, τ z * (h - μ) ^ 2 ≤ h * (C * (h - μ)) * E := hc
      _ = C * h * ((h - μ) * E) := by ring
      _ ≤ C * h * (2 * h * d + 2 * q * h ^ 2 + h) := Nat.mul_le_mul_left _ hE
      _ = C * h ^ 2 * (2 * d + 2 * q * h + 1) := by ring
  · rw [hb z hz]; exact_mod_cast Nat.sub_pos_of_lt hμlt
  · rw [hb z hz]
    have ht := mul_le_mul_of_nonneg_right (hτ z hz)
      (show 0 ≤ ((h - μ : ℕ) : ℤ) ^ 2 by positivity)
    push_cast; nlinarith only [ht]

theorem tight_weighted_mass_le (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (w q d C : ℕ) (hqh : q * R.natDegree ≤ d) (hC : 0 < C)
    (hRw : wd R wY ≤ w) (hRyz : WtLE 0 q 1 d R)
    (y : Idx → Fld[X]) (hy : ∀ j, (y j).natDegree ≤ q)
    (S : Finset Fld) (P : Fld → Fld[X]) (Aset : Fld → Finset Idx) (τ : Fld → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ j ∈ Aset z, 1 ≤ lineOrd R (BinaryIRSProfile.domain j) (y j))
    (hmatch : ∀ z ∈ S, ∀ j, j ∈ Aset z ↔ (P z).eval (BinaryIRSProfile.domain j) = (y j).eval z)
    (hτ : ∀ z ∈ S, 2 * (τ z : ℤ) * normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤ C) :
    ∑ z ∈ S, τ z * P64C7Aggregate.mass R.natDegree
        (fun i => lineOrd R (BinaryIRSProfile.domain i) (y i)) (Aset z) ≤
      C * R.natDegree ^ 2 * N * (6 * d + 2 * q * R.natDegree + 2) := by
  classical
  let μ : Idx → ℕ := fun i => lineOrd R (BinaryIRSProfile.domain i) (y i)
  have hline : ∀ i, (∑ z ∈ S, τ z * (if i ∈ Aset z then (R.natDegree - μ i) ^ 2 else μ i ^ 2)) ≤
      C * R.natDegree ^ 2 * (6 * d + 2 * q * R.natDegree + 2) := by
    intro i
    let Sm := S.filter fun z => i ∈ Aset z
    let Su := S.filter fun z => i ∉ Aset z
    have hm := tight_single_line_matched R hirr hh w q d C hC hRw hRyz y hy i Sm P Aset τ
      (fun z hz => hP z (Finset.mem_filter.mp hz).1)
      (fun z hz => hcurve z (Finset.mem_filter.mp hz).1)
      (fun z hz => hderiv z (Finset.mem_filter.mp hz).1)
      (fun z hz => hμ z (Finset.mem_filter.mp hz).1)
      (fun z hz j hj => (hmatch z (Finset.mem_filter.mp hz).1 j).mp hj)
      (fun _ hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hτ z (Finset.mem_filter.mp hz).1)
    have hu := tight_single_line_missing R hirr hh w q d C hqh hC hRw hRyz y i (hy i) Su P Aset τ
      (fun z hz => hP z (Finset.mem_filter.mp hz).1)
      (fun z hz => hcurve z (Finset.mem_filter.mp hz).1)
      (fun z hz => hderiv z (Finset.mem_filter.mp hz).1)
      (fun z hz => hμ z (Finset.mem_filter.mp hz).1)
      (fun z hz j hj => (hmatch z (Finset.mem_filter.mp hz).1 j).mp hj)
      (fun z hz he => (Finset.mem_filter.mp hz).2 ((hmatch z (Finset.mem_filter.mp hz).1 i).mpr he))
      (fun z hz => hτ z (Finset.mem_filter.mp hz).1)
    have he : (∑ z ∈ S, τ z * (if i ∈ Aset z then (R.natDegree - μ i) ^ 2 else μ i ^ 2)) =
        (∑ z ∈ Sm, τ z * (R.natDegree - μ i) ^ 2) + (∑ z ∈ Su, τ z * μ i ^ 2) := by
      simp only [Sm, Su, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro z _; split_ifs <;> simp_all
    rw [he]; dsimp only [μ]; nlinarith only [hm, hu]
  simp only [P64C7Aggregate.mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _ : Idx, C * R.natDegree ^ 2 * (6 * d + 2 * q * R.natDegree + 2) :=
        Finset.sum_le_sum (fun i _ => hline i)
    _ = C * R.natDegree ^ 2 * N * (6 * d + 2 * q * R.natDegree + 2) := by
        rw [Finset.sum_const, Finset.card_univ, BinaryIRSProfile.card_index, smul_eq_mul]
        change 2097152 * _ = _; dsimp only [N]; ring
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
