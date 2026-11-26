import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid2
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

theorem aux_card_le_pow (u₀ u₁ : Idx → Fld) (q₀ : ℕ) (hq₀ : q₀ = 1 ∨ q₀ = 2)
    {R : Tri} (hirr : Irreducible R) (hpos : 1 ≤ R.natDegree)
    {Vs : Finset Fld} {P : Fld → Fld[X]} {Az : Fld → Finset Idx}
    (hP : ∀ z ∈ Vs, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ Vs, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ Vs, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ Vs, ∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (Δ_max : ℕ)
    (hdefect : ∀ z ∈ Vs,
      ((wd R wY : ℤ) - ∑ i ∈ Az z, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
        ((Az z).card - (A : ℤ)) ≤ Δ_max)
    (q_aux : ℕ) (hq_aux : 1 ≤ q_aux)
    (hC0 : A + 4 * Δ_max + 1 ≤ 4 * wd R wY)
    (hφ : ∀ i, 4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 ≤
      q_aux + (4 * wd R wY - (A + 4 * Δ_max + 1)) / wY)
    (hcrit : (q_aux + (4 * wd R wY - (A + 4 * Δ_max + 1)) / wY) *
      (∑ i, (4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1) *
            (4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 + 1) / 2) <
      q_aux * P64Surf.Mbox (4 * wd R wY - (A + 4 * Δ_max + 1)))
    (hF : ((4 * wd R wY - (A + 4 * Δ_max + 1)) / wY + R.natDegree) * (4 * wd R wY) <
      Fintype.card Fld) :
    let J := (4 * wd R wY - (A + 4 * Δ_max + 1)) / wY
    Vs.card ≤ J * yzd R 1 + R.natDegree * (q₀ * (q_aux + J - 1)) := by
  classical
  let w := wd R wY
  let C₀ := A + 4 * Δ_max + 1
  let W := 4 * w - C₀
  let J := W / wY
  let μ : Idx → ℕ := fun i => lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i)
  have hR0 : R ≠ 0 := hirr.ne_zero
  let p := P64Aux.auxParams (fun i => 4 * μ i - 1) W q_aux hφ hq_aux
  have hcard_gs : Fintype.card (P64GS.ConIndex p) < Fintype.card (P64GS.VarIndex p) := by
    have h1 := P64Aux.card_conIndex_le p
    have h2 : q_aux * P64Surf.Mbox W ≤ Fintype.card (P64GS.VarIndex p) :=
      P64Aux.card_var_ge (fun i => 4 * μ i - 1) W q_aux hφ hq_aux
    change Fintype.card (P64GS.ConIndex p) ≤ (q_aux + J) * (∑ i, (4 * μ i - 1) * (4 * μ i - 1 + 1) / 2) at h1
    dsimp only [J, W, C₀, w, μ] at h1 h2
    omega
  obtain ⟨Ψ₀, hΨ₀0, hvan₀, hcaps₀⟩ := P64GS.exists_interpolant_gen hcard_gs BinaryIRSProfile.domain u₀ u₁
  change ∀ j a, ((Ψ₀.coeff j).coeff a) ≠ 0 →
    j < J + 1 ∧ a + wY * j < W + 1 ∧ ((Ψ₀.coeff j).coeff a).natDegree + j < q_aux + J at hcaps₀
  -- Define Ψ = Ψ₀ (for q₀ = 1) or Ψ = paramSquare Ψ₀ (for q₀ = 2)!
  let Ψ : Tri := if q₀ = 1 then Ψ₀ else paramSquare Ψ₀
  have hexp_inj : Function.Injective ((Polynomial.expand Fld 2).toRingHom : Fld[X] → Fld[X]) :=
    Polynomial.expand_injective (by norm_num)
  have hΨ0 : Ψ ≠ 0 := by
    dsimp [Ψ]; split_ifs
    · exact hΨ₀0
    · exact (Polynomial.map_ne_zero_iff (Polynomial.map_injective _ hexp_inj)).mpr hΨ₀0
  have hord : ∀ i, OrdGE Ψ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) (4 * μ i - 1) := by
    intro i
    rcases hq₀ with rfl | rfl
    · simp only [Ψ, ↓reduceIte, linePow_one_eq_lineOf]
      exact fun a b hab => hvan₀ i a b hab
    · simp only [Ψ, show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
      have h1 : OrdGE Ψ₀ (BinaryIRSProfile.domain i) (P64Light.lineOf u₀ u₁ i) (4 * μ i - 1) :=
        fun a b hab => hvan₀ i a b hab
      have hΨ0' : paramSquare Ψ₀ ≠ 0 := by simpa [Ψ] using hΨ0
      rw [ordGE_iff hΨ0']
      rw [ordGE_iff hΨ₀0] at h1
      have heq : (lineShift Ψ₀ (BinaryIRSProfile.domain i) (P64Light.lineOf u₀ u₁ i)).map
          (Polynomial.mapRingHom (Polynomial.expand Fld 2).toRingHom) =
          lineShift (paramSquare Ψ₀) (BinaryIRSProfile.domain i) (linePow u₀ u₁ 2 i) := by
        change (Polynomial.Bivariate.shift Ψ₀ (Polynomial.C (BinaryIRSProfile.domain i))
          (P64Light.lineOf u₀ u₁ i)).map (Polynomial.mapRingHom (Polynomial.expand Fld 2).toRingHom) = _
        rw [shift_map]
        have hx : (Polynomial.expand Fld 2).toRingHom (Polynomial.C (BinaryIRSProfile.domain i)) =
            Polynomial.C (BinaryIRSProfile.domain i) := by simp
        have hy : (Polynomial.expand Fld 2).toRingHom (P64Light.lineOf u₀ u₁ i) = linePow u₀ u₁ 2 i := by
          simpa [linePow_one_eq_lineOf] using expand_linePow u₀ u₁ 1 i
        rw [hx, hy]; rfl
      have ht := tord_map (Polynomial.expand Fld 2).toRingHom hexp_inj
        (lineShift Ψ₀ (BinaryIRSProfile.domain i) (P64Light.lineOf u₀ u₁ i))
        ((lineShift_eq_zero_iff _ _ _).not.mpr hΨ₀0)
      rw [heq] at ht
      change 4 * μ i - 1 ≤ lineOrd (paramSquare Ψ₀) _ _
      change lineOrd (paramSquare Ψ₀) _ _ = lineOrd Ψ₀ _ _ at ht
      rw [ht]; exact h1
  have hΨw : wd Ψ wY ≤ W := by
    have h0 : wd Ψ₀ wY ≤ W := by
      have := P64Caps.Weighted.weightedSupportDegree_lt_of_coeff_cap Ψ₀ wY (W + 1) hΨ₀0
        (fun j a ha => (hcaps₀ j a ha).2.1)
      omega
    dsimp [Ψ]; split_ifs
    · exact h0
    · change wd (Ψ₀.map (Polynomial.mapRingHom (Polynomial.expand Fld 2).toRingHom)) wY ≤ W
      rwa [weighted_map _ hexp_inj]
  have hΨdeg : Ψ.natDegree ≤ J := by
    have h0 : Ψ₀.natDegree ≤ J := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj; by_contra hne
      have ha := (hcaps₀ j (Ψ₀.coeff j).natDegree (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hne)).1
      omega
    dsimp [Ψ]; split_ifs
    · exact h0
    · exact natDegree_map_le.trans h0
  have hΨz : ∀ j a, ((Ψ.coeff j).coeff a).natDegree ≤ q₀ * (q_aux + J - 1) := by
    intro j a
    rcases hq₀ with rfl | rfl
    · simp only [Ψ, ↓reduceIte, one_mul]
      by_cases h0 : (Ψ₀.coeff j).coeff a = 0
      · simp [h0]
      · have := (hcaps₀ j a h0).2.2; omega
    · simp only [Ψ, show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
      have hcoeff : ((paramSquare Ψ₀).coeff j).coeff a = Polynomial.expand Fld 2 ((Ψ₀.coeff j).coeff a) := by
        simp [paramSquare, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      rw [hcoeff]
      by_cases h0 : (Ψ₀.coeff j).coeff a = 0
      · simp [h0]
      · rw [Polynomial.natDegree_expand]
        have := (hcaps₀ j a h0).2.2
        omega
  -- Cofactor Ψ = R^a * Ψ'
  obtain ⟨a, Ψ', hndvd, hΨeq⟩ := WfDvdMonoid.max_power_factor (α := Tri) hΨ0 hirr
  have hRa : R ^ a ≠ 0 := pow_ne_zero a hR0
  have hΨ'0 : Ψ' ≠ 0 := by rintro rfl; exact hΨ0 (by rw [hΨeq, mul_zero])
  have hwmul : wd Ψ wY = a * w + wd Ψ' wY := by
    rw [hΨeq, P64Caps.Weighted.weightedSupportDegree_mul _ _ _ hRa hΨ'0,
      weightedSupportDegree_pow R hR0]
  have hat : a < 4 := by
    have h4w : 0 < 4 * w := by omega
    have : a * w < 4 * w := by omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hw'le : wd Ψ' wY + a * w + C₀ ≤ 4 * w := by omega
  have hdeg' : Ψ'.natDegree ≤ J := by
    have : Ψ.natDegree = (R ^ a).natDegree + Ψ'.natDegree := by rw [hΨeq, natDegree_mul hRa hΨ'0]
    omega
  have hyz' : ∀ j a_idx, ((Ψ'.coeff j).coeff a_idx).natDegree ≤ q₀ * (q_aux + J - 1) := by
    -- Use yzSupportDegree Ψ 0 (pure Z-degree) which is additive over products!
    have hΨ0cap : yzd Ψ 0 ≤ q₀ * (q_aux + J - 1) := by
      unfold P64Caps.YZ.yzSupportDegree
      apply Finset.sup_le
      intro j _
      simp only [Nat.zero_mul, add_zero]
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro a_idx _
      exact hΨz j a_idx
    have hyz_mul : yzd Ψ 0 = yzd (R ^ a) 0 + yzd Ψ' 0 := by
      rw [hΨeq, P64Caps.YZ.yzSupportDegree_mul _ _ 0 hRa hΨ'0]
    intro j a_idx
    by_cases hj : Ψ'.coeff j = 0
    · simp [hj]
    · have h1 := Polynomial.Bivariate.coeff_natDegree_le_degreeX (Ψ'.coeff j) a_idx
      have h2 := P64Caps.YZ.coeffWeight_le_of_ne Ψ' 0 j hj
      omega
  -- Every z ∈ Vs kills Ψ'!
  have hkill : ∀ z ∈ Vs, triEval Ψ' z (P z) = 0 := by
    intro z hz
    by_contra hne
    have hmult : ∀ i ∈ Az z, 4 * μ i - 1 - a * μ i ≤
        (triEval Ψ' z (P z)).rootMultiplicity (BinaryIRSProfile.domain i) := by
      intro i hi
      have h1 := ordGE_cofactor hRa hΨ'0 (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) _
        (hΨeq ▸ hord i)
      rw [lineOrd_pow hR0] at h1
      exact le_rootMultiplicity_triEval Ψ' (BinaryIRSProfile.domain i) z (linePow u₀ u₁ q₀ i) (P z) _
        h1 (by rw [eval_linePow]; exact hmatch z hz i hi) hne
    have hsum : ∑ i ∈ Az z, (4 * μ i - 1 - a * μ i) ≤ wd Ψ' wY :=
      (Finset.sum_le_sum hmult).trans ((sum_rootMultiplicity_le_natDegree _ _ (Az z)).trans
        (natDegree_triEval_le Ψ' z (P z) wY (hP z hz)))
    have hsumZ : ∑ i ∈ Az z, ((4 : ℤ) * μ i - 1 - a * μ i) ≤ wd Ψ' wY := by
      have h1 : ∑ i ∈ Az z, ((4 : ℤ) * μ i - 1 - a * μ i) ≤
          ∑ i ∈ Az z, ((4 * μ i - 1 - a * μ i : ℕ) : ℤ) :=
        Finset.sum_le_sum fun i _ => by
          have := P64Aux.sub_cast_ge (4 * μ i) (a * μ i); push_cast at this; exact this
      exact h1.trans (by exact_mod_cast hsum)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsumZ
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum] at hsumZ
    have hAz : (A : ℤ) ≤ (Az z).card := by exact_mod_cast hcard z hz
    have hw'Z : ((wd Ψ' wY : ℕ) : ℤ) + a * w + (A + 4 * Δ_max + 1) ≤ 4 * w := by
      exact_mod_cast hw'le
    have hatZ : (a : ℤ) + 1 ≤ 4 := by exact_mod_cast hat
    have hdefZ := hdefect z hz
    have hp1 : 0 ≤ (3 - (a : ℤ)) * ((Az z).card - (A : ℤ)) :=
      mul_nonneg (by omega) (by linarith)
    have hp2 : 0 ≤ (4 - (a : ℤ)) * ((Δ_max : ℤ) - ((w : ℤ) - ∑ i ∈ Az z, (μ i : ℤ) + ((Az z).card - (A : ℤ)))) :=
      mul_nonneg (by omega) (by linarith)
    have hp3 : 0 ≤ (a : ℤ) * (Δ_max : ℤ) := by positivity
    linarith only [hsumZ, hw'Z, hp1, hp2, hp3]
  have hXR : ∀ j, (R.coeff j).natDegree ≤ 4 * w := fun j =>
    (P64Resultant.coeff_natDegree_le_weighted R wY j).trans (by dsimp only [w]; omega)
  have hXG : ∀ j, (Ψ'.coeff j).natDegree ≤ 4 * w := fun j =>
    (P64Resultant.coeff_natDegree_le_weighted Ψ' wY j).trans (by omega)
  have hF' : (Ψ'.natDegree + R.natDegree) * (4 * w) < Fintype.card Fld :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by dsimp only [J, W, C₀, w] at hdeg'; omega)) hF
  have hRes := P64Resultant.card_common_le R Ψ' hirr (by omega) hndvd
    (yzd R 1) (q₀ * (q_aux + J - 1)) (4 * w)
    (fun j a_idx => P64Resultant.coeff_natDegree_le_yz R j a_idx) hyz' hXR hXG hF' Vs P
    (fun z hz => ⟨hcurve z hz, hkill z hz⟩)
  calc Vs.card ≤ Ψ'.natDegree * yzd R 1 + R.natDegree * (q₀ * (q_aux + J - 1)) := hRes
    _ ≤ J * yzd R 1 + R.natDegree * (q₀ * (q_aux + J - 1)) := by gcongr
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
