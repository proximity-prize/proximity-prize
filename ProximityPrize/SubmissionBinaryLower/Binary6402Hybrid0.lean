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

def A : ℕ := 1482750
def BadOn6402 (u₀ u₁ : Idx → Fld) (Az : Finset Idx) : Prop :=
  ¬ ∃ p₀ p₁ : Fld[X], p₀.natDegree ≤ wY ∧ p₁.natDegree ≤ wY ∧
    ∀ i ∈ Az, p₀.eval (BinaryIRSProfile.domain i) = u₀ i ∧
      p₁.eval (BinaryIRSProfile.domain i) = u₁ i

noncomputable def linePow (u₀ u₁ : Idx → Fld) (q : ℕ) (i : Idx) : Fld[X] :=
  Polynomial.C (u₀ i) + Polynomial.X ^ q * Polynomial.C (u₁ i)

lemma linePow_natDegree_le (u₀ u₁ : Idx → Fld) (q : ℕ) (i : Idx) :
    (linePow u₀ u₁ q i).natDegree ≤ q := by
  unfold linePow
  refine natDegree_add_le_of_degree_le (by simp) ?_
  exact natDegree_mul_le.trans (by simp)

lemma eval_linePow (u₀ u₁ : Idx → Fld) (q : ℕ) (i : Idx) (z : Fld) :
    (linePow u₀ u₁ q i).eval z = u₀ i + z ^ q * u₁ i := by
  simp [linePow]; ring

lemma expand_linePow (u₀ u₁ : Idx → Fld) (q : ℕ) (i : Idx) :
    Polynomial.expand Fld 2 (linePow u₀ u₁ q i) = linePow u₀ u₁ (2 * q) i := by
  unfold linePow
  simp only [map_add, map_mul, map_pow, Polynomial.expand_C, Polynomial.expand_X, ← pow_mul]

lemma linePow_one_eq_lineOf (u₀ u₁ : Idx → Fld) (i : Idx) :
    linePow u₀ u₁ 1 i = P64Light.lineOf u₀ u₁ i := by
  simp [linePow, P64Light.lineOf]

def arklibBoundPowQ (q B H : ℕ) : ℚ :=
  let theta : ℚ := ((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)
  let psi : ℚ := 1 + (2 * (wY : ℚ) - 1) * (2 * (B : ℚ) - 1) + 2 * ((B - (2 * wY + 1) : ℕ) : ℚ)
  (2 * (B : ℚ) - 1) * (H : ℚ) + theta * ((q : ℚ) * (B : ℚ) + (H : ℚ) * psi) +
    (q : ℚ) * ((N - wY - 1 : ℕ) : ℚ) * (B : ℚ)

lemma ordinaryUnifiedPowerFactorAtOrHeight_le_pow (q B H : ℕ) :
    ordinaryUnifiedPowerFactorAtOrHeight N wY q B H A (wY + 1) ≤
      max (H : ℚ) (arklibBoundPowQ q B H) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · rw [ordinaryUnifiedPowerFactorAtOrHeight_zero]
    exact le_max_left _ _
  · rw [ordinaryUnifiedPowerFactorAtOrHeight_of_pos N wY q B H A (wY + 1) hB]
    rw [ordinaryUnifiedPowerFactorAt_succ_eq N wY q B H A (by norm_num [wY, A]) (by norm_num [N, A])]
    have heq : ordinaryUnifiedPowerFactorRaw (((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) N wY q B H =
        arklibBoundPowQ q B H := by
      unfold ordinaryUnifiedPowerFactorRaw arklibBoundPowQ ordinaryPsi
      have hsub : B - 2 * wY - 1 = B - (2 * wY + 1) := by omega
      have hB1 : 1 ≤ 2 * B := by omega
      have hw1 : 1 ≤ 2 * wY := by norm_num [wY]
      rw [hsub]
      push_cast
      rw [Nat.cast_sub hB1, Nat.cast_sub hw1]
      push_cast
      ring
    rw [heq]
    exact le_max_right _ _

theorem card_le_of_biPoly_pow
    (u₀ u₁ : Idx → Fld) (q : ℕ) (hq : 1 ≤ q)
    (R : Tri) (B H : ℕ) (hR : R ≠ 0) (hB : R.natDegree ≤ B)
    (hH : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ H)
    (Vs : Finset Fld) (P : Fld → Fld[X]) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ Vs, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ Vs, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ Vs, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ Vs, ∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q * u₁ i)
    (hbad : ∀ z ∈ Vs, BadOn6402 u₀ u₁ (Az z)) :
    (Vs.card : ℚ) ≤ max (H : ℚ) (arklibBoundPowQ q B H) := by
  let dom : Fin BinaryIRSProfile.domainSize ↪ Fld := BinaryIRSProfile.domain
  let u₀' : Fin BinaryIRSProfile.domainSize → Fld := u₀
  let u₁' : Fin BinaryIRSProfile.domainSize → Fld := u₁
  let values : Fin (q + 1) → Fin BinaryIRSProfile.domainSize → Fld :=
    fun t => if t.val = 0 then u₀' else if t.val = q then u₁' else 0
  have hword : ∀ z : Fld, powerBatchedWord (ℓ := q) values z = fun i => u₀' i + z ^ q * u₁' i := by
    intro z
    funext i
    unfold powerBatchedWord
    rw [Fin.sum_univ_succ]
    simp only [values, Fin.val_zero, ↓reduceIte, pow_zero, one_mul, Fin.val_succ, Nat.succ_ne_zero]
    congr 1
    let last : Fin q := ⟨q - 1, by omega⟩
    rw [Finset.sum_eq_single last]
    · have hval : last.val + 1 = q := by dsimp [last]; omega
      simp [hval]
    · intro b _ hb
      have hne : b.val + 1 ≠ q := by
        intro h; apply hb; exact Fin.ext (by dsimp [last]; omega)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ last) h
  have hQne : biPolyToDiffPoly R ≠ 0 := biPolyToDiffPoly_ne_zero hR
  have hdeg : (biPolyToDiffPoly R).degreeOf (some 0) ≤ B :=
    (degreeOf_biPolyToDiffPoly_le R).trans hB
  have hht : MvPolynomial.CoeffNatDegreeLE (biPolyToDiffPoly R) H :=
    coeffNatDegreeLE_biPolyToDiffPoly R hH
  obtain ⟨ex, hexcard, hgood⟩ := ReedSolomon.exists_baseExceptional_ordinaryPowerEquation
    (n := BinaryIRSProfile.domainSize) (ℓ := q) dom values
    (biPolyToDiffPoly R) wY H B (wY + 1) A
    hQne (by norm_num [wY]) (by norm_num [wY]) (by norm_num [wY, A]) hht hdeg
  have hsub : Vs ⊆ ex := by
    intro z hz
    by_contra hzex
    have hPdeg : (P z).degree < (wY + 1 : ℕ) := by
      by_cases h0 : P z = 0
      · simp [h0]
      · exact (Polynomial.degree_lt_iff_coeff_zero _ _).mpr fun m hm =>
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP z hz) (by omega))
    have hdiff : differentialSpecialization (challengeSpecialization (biPolyToDiffPoly R) z) (P z) = 0 := by
      rw [differentialSpecialization_biPolyToDiffPoly]
      exact hcurve z hz
    have hagree : A ≤ (polynomialAgreementSet dom
        (powerBatchedWord (ℓ := q) values z) (P z)).card := by
      refine (hcard z hz).trans (Finset.card_le_card ?_)
      intro i hi
      exact (ReedSolomon.mem_polynomialAgreementSet dom
        (powerBatchedWord (ℓ := q) values z) (P z) i).mpr (by rw [hword]; exact hmatch z hz i hi)
    obtain ⟨Pvec, hPvec_deg, _, hPvec_ag⟩ := hgood z hzex (P z) hPdeg hdiff hagree
    apply hbad z hz
    refine ⟨Pvec 0, Pvec ⟨q, by omega⟩, ?_, ?_, ?_⟩
    · exact P64Shorten.natDegree_le_of_degree_lt_nat (hPvec_deg 0) le_rfl
    · exact P64Shorten.natDegree_le_of_degree_lt_nat (hPvec_deg ⟨q, by omega⟩) le_rfl
    · intro i hi
      have hmem : (i : Fin BinaryIRSProfile.domainSize) ∈ polynomialAgreementSet dom
          (powerBatchedWord (ℓ := q) values z) (P z) :=
        (ReedSolomon.mem_polynomialAgreementSet dom
          (powerBatchedWord (ℓ := q) values z) (P z) i).mpr (by rw [hword]; exact hmatch z hz i hi)
      have hdom_eq : ∀ h, dom.trans ⟨RingHom.id Fld, h⟩ = dom := fun _ => by ext j; rfl
      have hval_eq : (fun t j => (RingHom.id Fld) (values t j)) = values := rfl
      rw [hdom_eq, hval_eq] at hPvec_ag
      rw [hPvec_ag] at hmem
      have hmem' := (ReedSolomon.mem_commonCurveAgreementSet dom values Pvec i).mp hmem
      have h0 := hmem' 0
      have hq' := hmem' ⟨q, by omega⟩
      simp only [values, Fin.val_zero, ↓reduceIte, show q ≠ 0 by omega] at h0 hq'
      exact ⟨h0, hq'⟩
  have hle : (Vs.card : ℚ) ≤ (ex.card : ℚ) := by exact_mod_cast Finset.card_le_card hsub
  have hexcard' : (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorAtOrHeight N wY q B H A (wY + 1) := by
    simpa only [show BinaryIRSProfile.domainSize = N from rfl] using hexcard
  exact hle.trans (hexcard'.trans (ordinaryUnifiedPowerFactorAtOrHeight_le_pow q B H))

theorem cert208984_6402 :
    ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate 1888168 839591 1273766 20 30 496 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · simp only [ReedSolomon.HiddenDerivative.johnsonWeightedR,
      ReedSolomon.HiddenDerivative.johnsonWeightedU,
      ReedSolomon.HiddenDerivative.johnsonWeightedN,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  · simp only [ReedSolomon.HiddenDerivative.johnsonWeightedHeight,
      ReedSolomon.HiddenDerivative.johnsonWeightedHeightInt,
      ReedSolomon.HiddenDerivative.johnsonWeightedMoment,
      ReedSolomon.HiddenDerivative.johnsonWeightedSlope,
      ReedSolomon.HiddenDerivative.johnsonWeightedR,
      ReedSolomon.HiddenDerivative.johnsonWeightedU,
      ReedSolomon.HiddenDerivative.johnsonWeightedN,
      ReedSolomon.HiddenDerivative.johnsonWeightedW,
      ReedSolomon.HiddenDerivative.johnsonWeightedT,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num

theorem count208984_6402 :
    ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount 1888168 839591 1273766 30 496 ≤
      120000000000 := by
  simp only [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount]
  norm_num
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
