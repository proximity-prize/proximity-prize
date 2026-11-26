import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid0
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

lemma fullLines_subset_eq {R : Tri} (hirr : Irreducible R) (hpos : 1 ≤ R.natDegree)
    (q₀ d : ℕ) (hq₀ : q₀ = 1 ∨ q₀ = 2) (hRyz : WtLE 0 q₀ 1 d R)
    (u₀ u₁ : Idx → Fld) (Vs : Finset Fld) (P : Fld → Fld[X]) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ Vs, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ Vs, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ Vs, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ Vs, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ Vs, BadOn6402 u₀ u₁ (Az z))
    (m_j B_j H_j count_j : ℕ)
    (hcert : ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate 1888168 839591 1273766 m_j B_j H_j)
    (hcnt : ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount 1888168 839591 1273766 B_j H_j ≤ count_j)
    (hB_j : B_j ≤ 2 * 839591 + 1)
    (hlight : 208984 ≤ (P64C7Case.fullLines R BinaryIRSProfile.domain (linePow u₀ u₁ q₀)).card ∨
              (lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R).card ≤ 208983) :
    Vs.card ≤ 208984 * d + count_j := by
  classical
  have h1d : yzd R 1 ≤ d := by
    unfold P64Caps.YZ.yzSupportDegree
    apply Finset.sup_le
    intro j hj
    have hj0 : R.coeff j ≠ 0 := mem_support_iff.mp hj
    have hdegX : Polynomial.Bivariate.degreeX (R.coeff j) + q₀ * j ≤ d := by
      unfold Polynomial.Bivariate.degreeX
      obtain ⟨a₀, ha₀⟩ := Polynomial.support_nonempty.mpr hj0
      have hqj : q₀ * j ≤ d := by
        have hl := leadingCoeff_ne_zero.mpr (mem_support_iff.mp ha₀)
        have hw := hRyz a₀ j ((R.coeff j).coeff a₀).natDegree hl
        omega
      have hsup : (R.coeff j).support.sup (fun a => ((R.coeff j).coeff a).natDegree) ≤ d - q₀ * j := by
        apply Finset.sup_le
        intro a ha
        have hl := leadingCoeff_ne_zero.mpr (mem_support_iff.mp ha)
        have hw := hRyz a j ((R.coeff j).coeff a).natDegree hl
        omega
      omega
    rcases hq₀ with rfl | rfl <;> omega
  rcases hlight with hf | hl
  · obtain ⟨Λs, hΛsub, hΛcard⟩ := Finset.exists_subset_card_eq hf
    have hcover : Vs ⊆ Λs.biUnion (fun i => Vs.filter fun z => i ∉ Az z) ∪
        Vs.filter fun z => Λs ⊆ Az z := by
      intro z hz
      by_cases hsub : Λs ⊆ Az z
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hsub⟩)
      · apply Finset.mem_union_left
        rw [Finset.not_subset] at hsub
        obtain ⟨i, hi, hiA⟩ := hsub
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hz, hiA⟩⟩
    have hline : ∀ i ∈ Λs, (Vs.filter fun z => i ∉ Az z).card ≤ d := by
      intro i hi
      have hfull : lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) = R.natDegree :=
        (Finset.mem_filter.mp (hΛsub hi)).2
      exact (card_filter_not_mem_le_of_full BinaryIRSProfile.domain (linePow u₀ u₁ q₀) hirr hpos i
        hfull Vs P Az hcurve (fun z hz h => (hmatch z hz i).mpr (by rwa [eval_linePow] at h))).trans h1d
    have hfilt : (Vs.filter fun z => Λs ⊆ Az z).card ≤ count_j := by
      have hn' : (Finset.univ \ Λs).card = 1888168 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          BinaryIRSProfile.card_index, hΛcard]
      rcases hq₀ with rfl | rfl
      · have hsh := P64Shorten.card_filter_subset_le BinaryIRSProfile.domain u₀ u₁ Λs wY A
          1888168 839591 1273766 m_j B_j H_j hn' (by norm_num [wY, hΛcard]) (by norm_num [A, hΛcard])
          hcert (by norm_num) (by norm_num) (by norm_num) hB_j Vs P Az hP hcard
          (fun z hz i hi => by simpa using (hmatch z hz i).mp hi) hbad
        exact_mod_cast hsh.trans hcnt
      · -- q₀ = 2: reindex via injective Frobenius map z ↦ z^2!
        let sq : Fld → Fld := fun z => z ^ 2
        have hsq_inj : Function.Injective sq := fun a b hab =>
          frobenius_inj Fld 2 (by simpa [frobenius_def, sq] using hab)
        have hsqrt_sq : ∀ z : Fld, sqrtF (z ^ 2) = z := fun z =>
          hsq_inj (by simp [sq, sqrtF_sq])
        let Vs' := Vs.image sq
        let P' : Fld → Fld[X] := fun w => P (sqrtF w)
        let Az' : Fld → Finset Idx := fun w => Az (sqrtF w)
        have hmem_sq : ∀ w ∈ Vs', sqrtF w ∈ Vs ∧ (sqrtF w) ^ 2 = w := by
          intro w hw
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
          exact ⟨by simpa [sq, hsqrt_sq] using hz, by simp [sq, sqrtF_sq]⟩
        have hsh := P64Shorten.card_filter_subset_le BinaryIRSProfile.domain u₀ u₁ Λs wY A
          1888168 839591 1273766 m_j B_j H_j hn' (by norm_num [wY, hΛcard]) (by norm_num [A, hΛcard])
          hcert (by norm_num) (by norm_num) (by norm_num) hB_j Vs' P' Az'
          (fun w hw => hP _ (hmem_sq w hw).1)
          (fun w hw => hcard _ (hmem_sq w hw).1)
          (fun w hw i hi => by
            have := (hmatch _ (hmem_sq w hw).1 i).mp hi
            rwa [(hmem_sq w hw).2] at this)
          (fun w hw => hbad _ (hmem_sq w hw).1)
        have hbij : (Vs.filter fun z => Λs ⊆ Az z).card ≤ (Vs'.filter fun w => Λs ⊆ Az' w).card := by
          have hsub' : (Vs.filter fun z => Λs ⊆ Az z).image sq ⊆ Vs'.filter fun w => Λs ⊆ Az' w := by
            intro w hw
            obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
            rw [Finset.mem_filter] at hz ⊢
            refine ⟨Finset.mem_image_of_mem sq hz.1, ?_⟩
            simpa [Az', sq, hsqrt_sq] using hz.2
          rw [← Finset.card_image_of_injective _ hsq_inj]
          exact Finset.card_le_card hsub'
        have hle' : ((Vs'.filter fun w => Λs ⊆ Az' w).card : ℚ) ≤ (count_j : ℚ) := hsh.trans hcnt
        exact hbij.trans (by exact_mod_cast hle')
    calc Vs.card ≤ _ := Finset.card_le_card hcover
      _ ≤ (Λs.biUnion (fun i => Vs.filter fun z => i ∉ Az z)).card +
            (Vs.filter fun z => Λs ⊆ Az z).card := Finset.card_union_le _ _
      _ ≤ (∑ i ∈ Λs, (Vs.filter fun z => i ∉ Az z).card) + count_j :=
            Nat.add_le_add Finset.card_biUnion_le hfilt
      _ ≤ (∑ _i ∈ Λs, d) + count_j := Nat.add_le_add_right (Finset.sum_le_sum hline) _
      _ = 208984 * d + count_j := by rw [Finset.sum_const, smul_eq_mul, hΛcard]
  · -- Few lines: |lam| ≤ 208983 ⇒ |Az z \ lam| ≥ A - 208983 = 1273767, total ≤ N * d ⇒ |Vs| ≤ 2 * d
    have hO := sum_card_sdiff_le_of_degree BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R hirr.ne_zero d
      (fun i => lineEval_degree R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) q₀ d hRyz
        (linePow_natDegree_le u₀ u₁ q₀ i))
      Vs P Az hcurve (fun z hz i hi => by rw [eval_linePow]; exact (hmatch z hz i).mp hi)
    have hcompl : (Finset.univ \ lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R).card ≤ N := by
      have : Fintype.card Idx = N := BinaryIRSProfile.card_index
      rw [← this]; exact Finset.card_le_univ _
    have hlow : ∀ z ∈ Vs, 1273767 ≤ (Az z \ lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R).card := by
      intro z hz
      have h1 := Finset.le_card_sdiff (lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R) (Az z)
      have h2 := hcard z hz
      dsimp only [A] at h2
      omega
    have hsum : Vs.card * 1273767 ≤ ∑ z ∈ Vs, (Az z \ lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R).card := by
      rw [← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum hlow
    have hN : N = 2097152 := rfl
    have := Nat.mul_le_mul_right d hcompl
    nlinarith only [hO, hsum, hN, this]
end B6402HybridP64
end ProximityPrize.SubmissionBinaryLower
