import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid6
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

theorem c6_separable_general (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (hsep : Polynomial.derivative R ≠ 0) (w q d Δ N_eff β : ℕ) (hq : 0 < q)
    (hRw : wd R wY ≤ w) (hRyz : WtLE 0 q 1 d R)
    (hF : 2 * R.natDegree * w < Fintype.card Fld)
    (hNeff : (N_eff : ℤ) = (A : ℤ) - wY + Δ)
    (hβ : 10000 * R.natDegree ≤ β)
    (y : Idx → Fld[X]) (hy : ∀ i, (y i).natDegree ≤ q)
    (hβeq : (∑ i, lineOrd R (BinaryIRSProfile.domain i) (y i)) + β = R.natDegree * A)
    (S : Finset Fld) (P : Fld → Fld[X]) (Aset : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Aset z).card)
    (hmatch : ∀ z ∈ S, ∀ i ∈ Aset z, (P z).eval (BinaryIRSProfile.domain i) = (y i).eval z)
    (hNbound : ∀ z ∈ S,
      normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤ ((Aset z).card : ℤ) - wY ∨
      normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤ N_eff) :
    10000 ^ 2 * S.card ≤ 2 * N_eff * (8 * N * d + 10000 * (4 * q * R.natDegree + 1)) +
      10000 ^ 2 * (N * d + 2 * R.natDegree * d) := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hS
    let h := R.natDegree
    let μ : Idx → ℕ := fun i => lineOrd R (BinaryIRSProfile.domain i) (y i)
    let good := S.filter fun z => Aset z ⊆ lam BinaryIRSProfile.domain y R ∧ derivativeAlong R (P z) z ≠ 0
    let missing := S.filter fun z => ¬ Aset z ⊆ lam BinaryIRSProfile.domain y R
    let dead := S.filter fun z => derivativeAlong R (P z) z = 0
    have hμgood : ∀ z ∈ good, ∀ i ∈ Aset z, 1 ≤ μ i := by
      intro z hz i hi
      have hline := (Finset.mem_filter.mp hz).2.1 hi
      have hp := (Finset.mem_filter.mp hline).2; dsimp only [μ]; omega
    have hgood : 10000 ^ 2 * good.card ≤ 2 * N_eff * (8 * N * d + 10000 * (4 * q * h + 1)) := by
      by_cases hgne : good.Nonempty
      · obtain ⟨zg, hzg⟩ := hgne
        have hzgS := (Finset.mem_filter.mp hzg).1
        have hwlow : h * wY ≤ w := by
          have := natDegree_mul_le_weightedSupportDegree R hirr.ne_zero wY
          rw [mul_comm] at this
          exact this.trans hRw
        have hdef_eq : normalDefect R BinaryIRSProfile.domain y (Aset zg) w wY =
            (w : ℤ) - wY - (∑ i ∈ Aset zg, (μ i : ℤ)) + (Aset zg).card :=
          P64C7Mass.defect_identity μ (Aset zg) w wY (hμgood zg hzg)
        have hsum_le : ∑ i ∈ Aset zg, μ i ≤ ∑ i, μ i :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
        have hN_le : (w : ℤ) - ∑ i ∈ Aset zg, (μ i : ℤ) ≤ Δ := by
          rcases hNbound zg hzgS with h1 | h2
          · rw [hdef_eq] at h1; linarith
          · rw [hdef_eq] at h2; have : (A : ℤ) ≤ (Aset zg).card := by exact_mod_cast hcard zg hzgS
            linarith
        have hβN' : β ≤ 4 * h * N_eff := by
          have h1 : (h : ℤ) * wY ≤ w := by exact_mod_cast hwlow
          have h2 : (∑ i ∈ Aset zg, (μ i : ℤ)) ≤ ∑ i, (μ i : ℤ) := by exact_mod_cast hsum_le
          have h3 : (∑ i, (μ i : ℤ)) + β = h * A := by exact_mod_cast hβeq
          have hh1 : (1 : ℤ) ≤ h := by exact_mod_cast hh
          have hΔnn : (0 : ℤ) ≤ Δ := Nat.cast_nonneg Δ
          have hAD : (0 : ℤ) ≤ (A : ℤ) - wY := by dsimp [A, wY]; norm_num
          exact_mod_cast (show (β : ℤ) ≤ 4 * h * N_eff by nlinarith only [h1, h2, h3, hN_le, hh1, hΔnn, hAD, hNeff])
        let Q := ∑ i, (d - q * μ i)
        let U := 4 * (∑ i, μ i) + β
        let E := P64C6Uniform.parameter h q Q β
        have hqh : q * h ≤ d := P64C6Retained.outer_weight_le R hirr.ne_zero q d hRyz
        have hqd : ∀ i, q * μ i ≤ d := fun i =>
          (Nat.mul_le_mul_left q (lineOrd_le_natDegree_of_irreducible hirr hh _ _)).trans hqh
        have hQ : (Q : ℤ) = ∑ i, ((d : ℤ) - q * μ i) := by
          dsimp only [Q]; rw [Nat.cast_sum]
          apply Finset.sum_congr rfl; intro i _; rw [Nat.cast_sub (hqd i), Nat.cast_mul]
        have hQle : Q ≤ N * d := by
          calc Q ≤ ∑ _ : Idx, d := Finset.sum_le_sum fun i _ => Nat.sub_le _ _
            _ = Fintype.card Idx * d := by simp
            _ = N * d := by rw [BinaryIRSProfile.card_index]; rfl
        have hβpos : 0 < β := by clear * - hh hβ; omega
        have hU : 0 < U := by dsimp [U]; omega
        have hbias : ∀ z ∈ good, (β : ℤ) + 4 * h * ((Aset z).card - A : ℕ) ≤
            P64C6Bessel.bias (fun _ => 4 * h) (Aset z) U := by
          intro z hz
          have hzS := (Finset.mem_filter.mp hz).1
          have hcz := hcard z hzS
          unfold P64C6Bessel.bias
          simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_sub hcz]
          have h3 : (∑ i, (μ i : ℤ)) + β = h * A := by exact_mod_cast hβeq
          dsimp [U]; push_cast; linarith only [h3]
        have hdefect : ∀ z ∈ good,
            normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤
              N_eff + ((Aset z).card - A : ℕ) := by
          intro z hz
          have hzS := (Finset.mem_filter.mp hz).1
          have hcz := hcard z hzS
          rw [Nat.cast_sub hcz]
          rcases hNbound z hzS with h1 | h2
          · linarith
          · linarith
        have hb : ∀ z ∈ good, 0 < P64C6Bessel.bias (fun _ => 4 * h) (Aset z) U := fun z hz => by
          have hb0 := hbias z hz
          have hx : (0 : ℤ) ≤ 4 * h * ((Aset z).card - A : ℕ) := by positivity
          have hβ0 : (0 : ℤ) < β := by exact_mod_cast hβpos
          linarith
        have hslope : ∀ z ∈ good, 2 * (β : ℤ) * normalDefect R BinaryIRSProfile.domain y (Aset z) w wY ≤
            (2 * N_eff : ℕ) * P64C6Bessel.bias (fun _ => 4 * h) (Aset z) U := by
          intro z hz
          have hn0 := hdefect z hz
          have hb0 := hbias z hz
          have hβN'' : (β : ℤ) ≤ 4 * h * N_eff := by exact_mod_cast hβN'
          have h1 := mul_le_mul_of_nonneg_left hn0 (show 0 ≤ 2 * (β : ℤ) by positivity)
          have h2 := mul_le_mul_of_nonneg_right hβN'' (Nat.cast_nonneg ((Aset z).card - A))
          have h3 := mul_le_mul_of_nonneg_left hb0 (show 0 ≤ 2 * (N_eff : ℤ) by positivity)
          push_cast; linarith only [h1, h2, h3]
        have hNeff_pos : 0 < N_eff := by
          have : (0 : ℤ) < (A : ℤ) - wY := by dsimp [A, wY]; norm_num
          omega
        have hc := P64C6Bessel.weighted_orders_le R hirr wY w q d U E (2 * N_eff) hRw hRyz
          BinaryIRSProfile.domain y hy (fun _ => 4 * h) hU
          (P64C6Uniform.parameter_pos h q Q β) (by positivity)
          (fun _ => P64C6Uniform.parameter_weight h q Q β)
          (P64C6Uniform.leading_positive h q d Q β μ (by omega) hβpos hQ)
          good P Aset (fun _ => β)
          (fun z hz => hP z (Finset.mem_filter.mp hz).1)
          (fun z hz => hcurve z (Finset.mem_filter.mp hz).1)
          (fun _ hz => (Finset.mem_filter.mp hz).2.2) hμgood
          (fun z hz => hmatch z (Finset.mem_filter.mp hz).1) hb hslope
        have hc' : good.card * β ≤ h * (2 * N_eff) * E := by simpa using hc
        have hcard1 : 10000 * good.card ≤ 2 * N_eff * E := by
          apply le_of_mul_le_mul_left (a := h) ?_ (by omega)
          calc h * (10000 * good.card) = good.card * (10000 * h) := by ring
            _ ≤ good.card * β := Nat.mul_le_mul_left _ hβ
            _ ≤ h * (2 * N_eff) * E := hc'
            _ = h * (2 * N_eff * E) := by ring
        have hk : 10000 * (8 * h * Q / β) ≤ 8 * Q := by
          apply le_of_mul_le_mul_left (a := h) ?_ (by omega)
          calc h * (10000 * (8 * h * Q / β)) = (10000 * h) * (8 * h * Q / β) := by ring
            _ ≤ β * (8 * h * Q / β) := Nat.mul_le_mul_right _ hβ
            _ ≤ 8 * h * Q := Nat.mul_div_le _ _
            _ = h * (8 * Q) := by ring
        have hE : 10000 * E ≤ 8 * N * d + 10000 * (4 * q * h + 1) := by
          change 10000 * (8 * h * Q / β + 4 * q * h + 1) ≤ _
          rw [Nat.add_assoc, Nat.mul_add]
          exact Nat.add_le_add_right (hk.trans (by
            simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 8 hQle)) _
        calc 10000 ^ 2 * good.card = 10000 * (10000 * good.card) := by ring
          _ ≤ 10000 * (2 * N_eff * E) := Nat.mul_le_mul_left 10000 hcard1
          _ = 2 * N_eff * (10000 * E) := by ring
          _ ≤ 2 * N_eff * (8 * N * d + 10000 * (4 * q * h + 1)) := Nat.mul_le_mul_left _ hE
      · rw [Finset.not_nonempty_iff_eq_empty.mp hgne]; simp
    have hmissing : missing.card ≤ N * d := card_missing_le R hirr.ne_zero q d N hRyz
      (by rw [BinaryIRSProfile.card_index]; rfl) BinaryIRSProfile.domain y hy S P Aset hcurve hmatch
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
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]; simp
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
