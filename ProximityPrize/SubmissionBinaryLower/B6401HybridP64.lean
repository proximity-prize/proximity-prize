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
namespace B6401HybridP64

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

/-- Pair `(u₀, u₁)` has no simultaneous degree-`≤ wY` agreement on `Az`. -/
def BadOn6401 (u₀ u₁ : Idx → Fld) (Az : Finset Idx) : Prop :=
  ¬ ∃ p₀ p₁ : Fld[X], p₀.natDegree ≤ wY ∧ p₁.natDegree ≤ wY ∧
    ∀ i ∈ Az, p₀.eval (BinaryIRSProfile.domain i) = u₀ i ∧
      p₁.eval (BinaryIRSProfile.domain i) = u₁ i

/-- Polynomial line `y_i(Z) = u₀ i + Z^q · u₁ i`. -/
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

/-! ### Section 1: Generalized ArkLib power-equation bridge for arbitrary `q ≥ 1` -/

/-- Exact ArkLib rational exception bound at power degree `q ≥ 1`, `Y`-degree `B`, `Z`-height `H`. -/
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

/-- **Section 1 theorem**: For ANY `q ≥ 1` and ANY nonzero `R : Tri` with `deg_Y R ≤ B` and
`deg_Z ≤ H`, the number of bad slopes on `R` for `u₀ + z^q u₁` is at most `max H (arklibBoundPowQ q B H)`. -/
theorem card_le_of_biPoly_pow
    (u₀ u₁ : Idx → Fld) (q : ℕ) (hq : 1 ≤ q)
    (R : Tri) (B H : ℕ) (hR : R ≠ 0) (hB : R.natDegree ≤ B)
    (hH : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ H)
    (Vs : Finset Fld) (P : Fld → Fld[X]) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ Vs, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ Vs, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ Vs, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ Vs, ∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q * u₁ i)
    (hbad : ∀ z ∈ Vs, BadOn6401 u₀ u₁ (Az z)) :
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

/-! ### Section 2: Generalized `afLight` (shortening + few-lines) for `q₀ ∈ {1, 2}` at `A = 1482831` -/

theorem cert208984_6401 :
    ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate 1888168 839591 1273847 20 30 488 := by
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

theorem count208984_6401 :
    ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount 1888168 839591 1273847 30 488 ≤
      116772604471 := by
  simp only [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount]
  norm_num

lemma fullLines_subset_eq {R : Tri} (hirr : Irreducible R) (hpos : 1 ≤ R.natDegree)
    (q₀ d : ℕ) (hq₀ : q₀ = 1 ∨ q₀ = 2) (hRyz : WtLE 0 q₀ 1 d R)
    (u₀ u₁ : Idx → Fld) (Vs : Finset Fld) (P : Fld → Fld[X]) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ Vs, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ Vs, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ Vs, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ Vs, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ Vs, BadOn6401 u₀ u₁ (Az z))
    (m_j B_j H_j count_j : ℕ)
    (hcert : ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate 1888168 839591 1273847 m_j B_j H_j)
    (hcnt : ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount 1888168 839591 1273847 B_j H_j ≤ count_j)
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
          1888168 839591 1273847 m_j B_j H_j hn' (by norm_num [wY, hΛcard]) (by norm_num [A, hΛcard])
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
          1888168 839591 1273847 m_j B_j H_j hn' (by norm_num [wY, hΛcard]) (by norm_num [A, hΛcard])
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
  · -- Few lines: |lam| ≤ 208983 ⇒ |Az z \ lam| ≥ A - 208983 = 1273848, total ≤ N * d ⇒ |Vs| ≤ 2 * d
    have hO := sum_card_sdiff_le_of_degree BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R hirr.ne_zero d
      (fun i => lineEval_degree R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) q₀ d hRyz
        (linePow_natDegree_le u₀ u₁ q₀ i))
      Vs P Az hcurve (fun z hz i hi => by rw [eval_linePow]; exact (hmatch z hz i).mp hi)
    have hcompl : (Finset.univ \ lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R).card ≤ N := by
      have : Fintype.card Idx = N := BinaryIRSProfile.card_index
      rw [← this]; exact Finset.card_le_univ _
    have hlow : ∀ z ∈ Vs, 1273848 ≤ (Az z \ lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R).card := by
      intro z hz
      have h1 := Finset.le_card_sdiff (lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R) (Az z)
      have h2 := hcard z hz
      dsimp only [A] at h2
      omega
    have hsum : Vs.card * 1273848 ≤ ∑ z ∈ Vs, (Az z \ lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R).card := by
      rw [← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum hlow
    have hN : N = 2097152 := rfl
    have := Nat.mul_le_mul_right d hcompl
    nlinarith only [hO, hsum, hN, this]

/-! ### Section 3: Generalized `S_4` auxiliary (`q₀ ∈ {1, 2}`) + exact completed-square profile bound -/

/-- Exact completed-square profile inequality with zero `Δ²` loss! -/
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

/-- Generalized `S_4` auxiliary for `q₀ ∈ {1, 2}` and defect budget `Δ_max`. -/
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

/-! ### Section 4: Tight C7 retained & separable bound (Frobenius-descent-exact!) -/

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

/-- Frobenius-descent-EXACT mass lower bound keeping `+ 2 h N_z`! -/
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

/-- **Section 4 theorem**: Tight C7 separable bound at arbitrary `M₀, N_eff, Δ`. -/
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

/-! ### Section 5: Generalized positive-bias C6 bound at `β₀ = 10000` and arbitrary `N_eff` -/

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
        have hβpos : 0 < β := by dsimp [h] at *; omega
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
          have : 8 * Q ≤ 8 * N * d := by nlinarith only [hQle]
          change 10000 * (8 * h * Q / β + 4 * q * h + 1) ≤ _
          omega
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

/-! ### Section 6: Strong-induction Frobenius descent with ArkLib cutoff `h_T ≤ h_0` -/

/-- Main per-factor Frobenius descent bound (used for BOTH low-bias C7 and positive-bias C6!).
When descent hits `R.natDegree ≤ h_0`, exits directly to ArkLib (`Section 1`) using the
exact Frobenius invariant `q * R.natDegree = q₀ * h_orig`! -/
theorem card_le_of_factor_frob_c7
    (u₀ u₁ : Idx → Fld) (q₀ h_orig h₀ d Δ P₀ M₀ N_eff : ℕ)
    (hq₀ : 1 ≤ q₀) (hh₀ : 1 ≤ h₀) (hM0pos : 0 < M₀)
    (hM0 : (M₀ : ℤ) + P₀ = (A : ℤ) - wY)
    (hNeff : (N_eff : ℤ) = (A : ℤ) - wY + Δ)
    (hMh : 2 * N_eff ≤ M₀ * (h₀ + 1))
    (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (q : ℕ) (hq : 1 ≤ q) (hqh_eq : q * R.natDegree = q₀ * h_orig) (hRle : R.natDegree ≤ h_orig)
    (hRyz : WtLE 0 q 1 d R)
    (hF : 2 * R.natDegree * wd R wY < Fintype.card Fld)
    (hfull : (P64C7Case.fullLines R BinaryIRSProfile.domain (linePow u₀ u₁ q)).card < A)
    (hprofile : 2 * (R.natDegree : ℤ) * wd R wY - R.natDegree ^ 2 * wY -
      (∑ i, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) : ℤ) ^ 2) ≤
      P₀ * R.natDegree ^ 2 + 2 * Δ * R.natDegree)
    (S : Finset Fld) (P : Fld → Fld[X]) (Aset : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Aset z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Aset z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6401 u₀ u₁ (Aset z))
    (hNbound : ∀ z ∈ S,
      normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q) (Aset z) (wd R wY) wY ≤
        ((Aset z).card : ℤ) - wY ∨
      normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q) (Aset z) (wd R wY) wY ≤ N_eff)
    (C_per_d C_per_h : ℚ)
    (hCd_ark : (2 * (h₀ : ℚ) - 1) + (((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) *
      (1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ)) ≤ C_per_d)
    (hCd_1 : (1 : ℚ) ≤ C_per_d)
    (hCd_c7 : ((2 * N_eff * N * 6 : ℕ) : ℚ) / (M₀ : ℚ) + (N : ℚ) ≤ C_per_d)
    (hCh_ark : (q₀ : ℚ) * ((((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) ≤ C_per_h)
    (hCh_c7 : ((2 * N_eff * N * (2 * q₀ + 2) : ℕ) : ℚ) / (M₀ : ℚ) ≤ C_per_h) :
    (S.card : ℚ) ≤ C_per_d * (d : ℚ) + 4 * (h_orig : ℚ) * (d : ℚ) + C_per_h * (h_orig : ℚ) := by
  classical
  generalize heq : R.natDegree = h
  induction h using Nat.strong_induction_on generalizing R q S P Aset with
  | ind h ih =>
    subst heq
    by_cases hsmall : R.natDegree ≤ h₀
    · -- Base case: exit to ArkLib!
      have hH : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ d :=
        coefficient_parameter_degree R q d hRyz
      have hark := card_le_of_biPoly_pow u₀ u₁ q hq R R.natDegree d hirr.ne_zero le_rfl hH
        S P Aset hP hcurve hcard (fun z hz i hi => (hmatch z hz i).mp hi) hbad
      have hmax_le : max (d : ℚ) (arklibBoundPowQ q R.natDegree d) ≤
          C_per_d * (d : ℚ) + 4 * (h_orig : ℚ) * (d : ℚ) + C_per_h * (h_orig : ℚ) := by
        apply max_le
        · have h1 : (0 : ℚ) ≤ 4 * (h_orig : ℚ) * (d : ℚ) := by positivity
          have h2 : (0 : ℚ) ≤ C_per_h * (h_orig : ℚ) := by
            have : (0 : ℚ) ≤ C_per_h := le_trans (by positivity) hCh_ark
            positivity
          nlinarith only [hCd_1, h1, h2, show (0 : ℚ) ≤ (d : ℚ) by positivity]
        · unfold arklibBoundPowQ
          dsimp only
          have hqh_q : (q : ℚ) * (R.natDegree : ℚ) = (q₀ : ℚ) * (h_orig : ℚ) := by exact_mod_cast hqh_eq
          have hRle0 : (R.natDegree : ℚ) ≤ (h₀ : ℚ) := by exact_mod_cast hsmall
          have hsub_le : ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤ ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
            exact_mod_cast Nat.sub_le_sub_right hsmall (2 * wY + 1)
          have htheta_nn : (0 : ℚ) ≤ ((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ) := by positivity
          have hwY_ge1 : (1 : ℚ) ≤ 2 * (wY : ℚ) - 1 := by dsimp [wY]; norm_num
          have hpsi_le : 1 + (2 * (wY : ℚ) - 1) * (2 * (R.natDegree : ℚ) - 1) +
              2 * ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤
              1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
            nlinarith only [hRle0, hsub_le, hwY_ge1]
          have hd_nn : (0 : ℚ) ≤ (d : ℚ) := Nat.cast_nonneg d
          have hh_nn : (0 : ℚ) ≤ (h_orig : ℚ) := Nat.cast_nonneg h_orig
          have htdpsi := mul_le_mul_of_nonneg_left hpsi_le (mul_nonneg htheta_nn hd_nn)
          rw [hqh_q, mul_right_comm (q : ℚ) ((N - wY - 1 : ℕ) : ℚ) (R.natDegree : ℚ), hqh_q]
          nlinarith only [hCd_ark, hCh_ark, hRle0, htdpsi, hd_nn, hh_nn,
            show (0 : ℚ) ≤ 4 * (h_orig : ℚ) * (d : ℚ) by positivity]
      exact hark.trans hmax_le
    · -- R.natDegree ≥ h₀ + 1
      have hbig : h₀ + 1 ≤ R.natDegree := by omega
      by_cases hY : Polynomial.derivative R = 0
      · by_cases hX : P64Incidence.dXPoly R = 0
        · -- Frobenius descent R = frobLift T!
          let T := twistPoly R
          have hback : frobLift T = R := frobLift_twistPoly R hY hX
          have hTi : Irreducible T := irreducible_twistPoly R hirr hY hX
          have hdeg : R.natDegree = T.natDegree * 2 := by rw [← hback, natDegree_frobLift]
          have hTpos : 1 ≤ T.natDegree := by omega
          have hTlt : T.natDegree < R.natDegree := by omega
          have hspace : wd R wY = 2 * wd T wY := by
            rw [← hback, spatial_weight_frobLift T hTi.ne_zero wY]
          let S' := S.image (sqrtF : Fld → Fld)
          let P' : Fld → Fld[X] := fun t => P (t ^ 2)
          let A' : Fld → Finset Idx := fun t => Aset (t ^ 2)
          have hSq : ∀ t ∈ S', t ^ 2 ∈ S := by
            intro t ht; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht; simpa using hz
          have hScard : S'.card = S.card := Finset.card_image_of_injective S sqrtF_injective
          have hwt : WtLE 0 (2 * q) 1 d T := parameter_weight_transfer T q d (by rwa [hback])
          have hF' : 2 * T.natDegree * wd T wY < Fintype.card Fld :=
            (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)).trans_lt hF
          have hexp : ∀ i, Polynomial.expand Fld 2 (linePow u₀ u₁ q i) = linePow u₀ u₁ (2 * q) i :=
            expand_linePow u₀ u₁ q
          have hm : ∀ i, lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) =
              2 * lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) := by
            intro i; rw [← hback, lineOrd_frobLift T hTi.ne_zero, hexp]
          have hfull' : (P64C7Case.fullLines T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q))).card < A := by
            have heq_fl : P64C7Case.fullLines R BinaryIRSProfile.domain (linePow u₀ u₁ q) =
                P64C7Case.fullLines T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) := by
              rw [← hback, P64C7All.fullLines_frobLift T hTi.ne_zero]
              simp only [hexp]
            exact heq_fl ▸ hfull
          have hprofile' : 2 * (T.natDegree : ℤ) * wd T wY - T.natDegree ^ 2 * wY -
              (∑ i, (lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) : ℤ) ^ 2) ≤
              P₀ * T.natDegree ^ 2 + 2 * Δ * T.natDegree := by
            rw [hdeg, hspace] at hprofile
            simp_rw [hm, Nat.cast_mul, Nat.cast_ofNat, mul_pow] at hprofile
            rw [← Finset.mul_sum] at hprofile
            have hΔnn : (0 : ℤ) ≤ Δ * T.natDegree := by positivity
            nlinarith only [hprofile, hΔnn]
          have hcurve' : ∀ t ∈ S', triEval T t (P' t) = 0 := by
            intro t ht
            have hc := hcurve _ (hSq t ht)
            rw [← hback] at hc
            exact eq_zero_of_pow_eq_zero ((triEval_frobLift T t (P' t)).symm.trans hc)
          have hmatch' : ∀ t ∈ S', ∀ i, i ∈ A' t ↔
              (P' t).eval (BinaryIRSProfile.domain i) = u₀ i + t ^ (2 * q) * u₁ i := by
            intro t ht i
            have hm0 := hmatch _ (hSq t ht) i
            rwa [show (t ^ 2) ^ q = t ^ (2 * q) by rw [← pow_mul]] at hm0
          have hNbound' : ∀ t ∈ S',
              normalDefect T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) (A' t) (wd T wY) wY ≤
                ((A' t).card : ℤ) - wY ∨
              normalDefect T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) (A' t) (wd T wY) wY ≤ N_eff := by
            intro t ht
            have htS := hSq t ht
            -- Compare w_T - ∑ μ_T vs w_R - ∑ μ_R (exact factor of 2!):
            let sT : ℤ := ∑ i ∈ A' t, (lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) : ℤ)
            let sR : ℤ := ∑ i ∈ Aset (t ^ 2), (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) : ℤ)
            have hs_eq : sR = 2 * sT := by
              dsimp [sR, sT, A']; simp_rw [hm, Nat.cast_mul, Nat.cast_ofNat]; rw [← Finset.mul_sum]
            -- Express normalDefect via ∑ (μ_i - 1) ≤ ∑ μ_i - |A| (or exact if μ_i ≥ 1; wait: use raw def!)
            -- Even simpler: normalDefect T = w_T - wY - ∑_{A'} (μ_T - 1).
            -- If w_T ≤ ∑_{A'} (μ_T - 1) + |A'|, i.e., if w_T - ∑ (μ_T - 1) ≤ |A'|, left branch holds!
            -- Notice for ANY m : ℕ: 2 * (m - 1 : ℕ) ≤ (2 * m - 1 : ℕ) AND (2 * m - 1 : ℕ) ≤ 2 * (m - 1 : ℕ) + 1!
            -- Wait: if μ_T i = 0, then μ_R i = 0, so (μ_T - 1) = 0 and (μ_R - 1) = 0!
            -- If μ_T i ≥ 1, then (μ_R i - 1) = 2 * μ_T i - 1 = 2 * (μ_T i - 1) + 1!
            -- Let S_pos = ∑_{i ∈ A'} (if μ_T i ≥ 1 then 1 else 0) ≤ |A'|!
            -- Then ∑ (μ_R - 1) = 2 * ∑ (μ_T - 1) + S_pos!
            -- Hence w_R - ∑ (μ_R - 1) = 2 * (w_T - ∑ (μ_T - 1)) - S_pos!
            -- Case A: w_T - ∑ (μ_T - 1) ≤ |A'| ⇒ normalDefect T ≤ |A'| - wY (left branch!)
            -- Case B: w_T - ∑ (μ_T - 1) > |A'| ≥ S_pos ⇒
            --   w_R - ∑ (μ_R - 1) = 2 * (w_T - ∑ (μ_T - 1)) - S_pos ≥ w_T - ∑ (μ_T - 1)
            --   ⇒ normalDefect T ≤ normalDefect R! And if normalDefect R ≤ |A'| - wY, contradiction with Case B;
            --   else normalDefect R ≤ N_eff ⇒ normalDefect T ≤ N_eff (right branch!)!
            let sumT : ℤ := ∑ i ∈ A' t, ((lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) - 1 : ℕ) : ℤ)
            let sumR : ℤ := ∑ i ∈ A' t, ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) - 1 : ℕ) : ℤ)
            have hsum_rel : sumR ≤ 2 * sumT + (A' t).card := by
              have hpt : ∀ i ∈ A' t,
                  ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) - 1 : ℕ) : ℤ) ≤
                  2 * ((lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) - 1 : ℕ) : ℤ) + 1 := by
                intro i _; rw [hm i]; omega
              calc sumR ≤ ∑ i ∈ A' t, (2 * ((lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) - 1 : ℕ) : ℤ) + 1) :=
                    Finset.sum_le_sum hpt
                _ = 2 * sumT + (A' t).card := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
            by_cases hcase : (wd T wY : ℤ) - sumT ≤ (A' t).card
            · left; change (wd T wY : ℤ) - wY - sumT ≤ _; linarith
            · have hT_le_R : normalDefect T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) (A' t) (wd T wY) wY ≤
                  normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q) (Aset (t ^ 2)) (wd R wY) wY := by
                change (wd T wY : ℤ) - wY - sumT ≤ (wd R wY : ℤ) - wY - sumR
                have hw2 : (wd R wY : ℤ) = 2 * (wd T wY : ℤ) := by exact_mod_cast hspace
                linarith
              rcases hNbound (t ^ 2) htS with h1 | h2
              · left; exact hT_le_R.trans h1
              · right; exact hT_le_R.trans h2
          have hbT := ih T.natDegree hTlt T hTi hTpos (2 * q) (by omega)
            (by rw [← hqh_eq, hdeg]; ring) (by omega) hwt hF' hfull' hprofile'
            S' P' A' (fun t ht => hP _ (hSq t ht)) hcurve' (fun t ht => hcard _ (hSq t ht))
            hmatch' (fun t ht => hbad _ (hSq t ht)) hNbound' rfl
          rwa [hScard] at hbT
        · -- Inseparable: ∂_Y R = 0, ∂_X R ≠ 0 ⇒ S.card ≤ 2 * R.natDegree * yzd R 1 ≤ 4 * h_orig * d
          have hc := P64Incidence.card_le_of_inseparable R hirr (by omega) hY hX (wd R wY)
            (P64Resultant.coeff_natDegree_le_weighted R wY) hF S P hcurve
          have hyz := P64C6All.yz_le_twice R hirr.ne_zero q d (by omega) hRyz
          have hm : S.card ≤ 4 * h_orig * d := by nlinarith only [hc, hyz, hRle]
          have h1 : (0 : ℚ) ≤ C_per_d * (d : ℚ) := mul_nonneg (le_trans (by norm_num) hCd_1) (Nat.cast_nonneg _)
          have h2 : (0 : ℚ) ≤ C_per_h * (h_orig : ℚ) := mul_nonneg (le_trans (by positivity) hCh_ark) (Nat.cast_nonneg _)
          have hmQ : (S.card : ℚ) ≤ 4 * (h_orig : ℚ) * (d : ℚ) := by exact_mod_cast hm
          linarith only [hmQ, h1, h2]
      · -- Separable: ∂_Y R ≠ 0 ⇒ tight C7 separable bound!
        have hMh' : 2 * N_eff ≤ M₀ * R.natDegree := hMh.trans (Nat.mul_le_mul_left M₀ hbig)
        have hc := tight_c7_separable R hirr hh hY (wd R wY) q d Δ P₀ M₀ N_eff (by omega) le_rfl hRyz hF
          (linePow u₀ u₁ q) (linePow_natDegree_le u₀ u₁ q) hM0 hM0pos hNeff hMh' hprofile hfull
          S P Aset hP hcurve hcard (fun z hz i => by rw [eval_linePow]; exact hmatch z hz i) hNbound
        have hM0Q : (0 : ℚ) < (M₀ : ℚ) := by exact_mod_cast hM0pos
        have hcQ : (M₀ : ℚ) * (S.card : ℚ) ≤
            (2 * N_eff * N : ℕ) * (6 * (d : ℚ) + 2 * (q : ℚ) * (R.natDegree : ℚ) + 2) +
            (M₀ : ℚ) * ((N : ℚ) * (d : ℚ) + 2 * (R.natDegree : ℚ) * (d : ℚ)) := by
          have hc' : ((M₀ * S.card : ℕ) : ℚ) ≤
              ((2 * N_eff * N * (6 * d + 2 * q * R.natDegree + 2) + M₀ * (N * d + 2 * R.natDegree * d) : ℕ) : ℚ) := by
            exact_mod_cast hc
          push_cast at hc' ⊢; linarith only [hc']
        have hqh_q : (q : ℚ) * (R.natDegree : ℚ) = (q₀ : ℚ) * (h_orig : ℚ) := by exact_mod_cast hqh_eq
        have h1_le_h : (1 : ℚ) ≤ (h_orig : ℚ) := by exact_mod_cast (le_trans hh hRle)
        have hRle_q : (R.natDegree : ℚ) ≤ (h_orig : ℚ) := by exact_mod_cast hRle
        have hdiv : (S.card : ℚ) ≤
            (((2 * N_eff * N * 6 : ℕ) : ℚ) / (M₀ : ℚ) + (N : ℚ)) * (d : ℚ) +
            2 * (R.natDegree : ℚ) * (d : ℚ) +
            (((2 * N_eff * N * (2 * q₀ + 2) : ℕ) : ℚ) / (M₀ : ℚ)) * (h_orig : ℚ) := by
          refine le_of_mul_le_mul_left ?_ hM0Q
          have hNE : (0 : ℚ) ≤ 2 * ((2 * N_eff * N : ℕ) : ℚ) := by positivity
          have h2h := mul_le_mul_of_nonneg_left h1_le_h hNE
          field_simp [hM0Q.ne']
          push_cast at hcQ h2h ⊢
          rw [mul_assoc (2 : ℚ) (q : ℚ) (R.natDegree : ℚ), hqh_q] at hcQ
          linarith only [hcQ, h2h]
        have hd_nn : (0 : ℚ) ≤ (d : ℚ) := Nat.cast_nonneg d
        have hh_nn : (0 : ℚ) ≤ (h_orig : ℚ) := Nat.cast_nonneg h_orig
        nlinarith only [hdiv, hCd_c7, hCh_c7, hRle_q, hd_nn, hh_nn]

/-- Same Frobenius descent with ArkLib cutoff `h_T ≤ h_0` for positive-bias C6 (`β ≥ 10000 * h`)! -/
theorem card_le_of_factor_frob_c6
    (u₀ u₁ : Idx → Fld) (q₀ h_orig h₀ d Δ N_eff : ℕ)
    (hq₀ : 1 ≤ q₀) (hh₀ : 1 ≤ h₀)
    (hNeff : (N_eff : ℤ) = (A : ℤ) - wY + Δ)
    (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (q : ℕ) (hq : 1 ≤ q) (hqh_eq : q * R.natDegree = q₀ * h_orig) (hRle : R.natDegree ≤ h_orig)
    (hRyz : WtLE 0 q 1 d R)
    (hF : 2 * R.natDegree * wd R wY < Fintype.card Fld)
    (hβ : 10000 * R.natDegree ≤ R.natDegree * A - ∑ i, lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i))
    (S : Finset Fld) (P : Fld → Fld[X]) (Aset : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Aset z).card)
    (hmatch : ∀ z ∈ S, ∀ i ∈ Aset z, (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6401 u₀ u₁ (Aset z))
    (hNbound : ∀ z ∈ S,
      normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q) (Aset z) (wd R wY) wY ≤
        ((Aset z).card : ℤ) - wY ∨
      normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q) (Aset z) (wd R wY) wY ≤ N_eff)
    (C_per_d C_per_h : ℚ)
    (hCd_ark : (2 * (h₀ : ℚ) - 1) + (((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) *
      (1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ)) ≤ C_per_d)
    (hCd_1 : (1 : ℚ) ≤ C_per_d)
    (hCd_c6 : ((16 * N_eff * N : ℕ) : ℚ) / (10000 ^ 2 : ℚ) + (N : ℚ) ≤ C_per_d)
    (hCh_ark : (q₀ : ℚ) * ((((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) ≤ C_per_h)
    (hCh_c6 : ((2 * N_eff * (4 * q₀ + 1) : ℕ) : ℚ) / (10000 : ℚ) ≤ C_per_h) :
    (S.card : ℚ) ≤ C_per_d * (d : ℚ) + 4 * (h_orig : ℚ) * (d : ℚ) + C_per_h * (h_orig : ℚ) := by
  classical
  generalize heq : R.natDegree = h
  induction h using Nat.strong_induction_on generalizing R q S P Aset with
  | ind h ih =>
    subst heq
    by_cases hsmall : R.natDegree ≤ h₀
    · have hH : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ d :=
        coefficient_parameter_degree R q d hRyz
      have hark := card_le_of_biPoly_pow u₀ u₁ q hq R R.natDegree d hirr.ne_zero le_rfl hH
        S P Aset hP hcurve hcard hmatch hbad
      have hmax_le : max (d : ℚ) (arklibBoundPowQ q R.natDegree d) ≤
          C_per_d * (d : ℚ) + 4 * (h_orig : ℚ) * (d : ℚ) + C_per_h * (h_orig : ℚ) := by
        apply max_le
        · have h1 : (0 : ℚ) ≤ 4 * (h_orig : ℚ) * (d : ℚ) := by positivity
          have h2 : (0 : ℚ) ≤ C_per_h * (h_orig : ℚ) := mul_nonneg (le_trans (by positivity) hCh_ark) (Nat.cast_nonneg _)
          nlinarith only [hCd_1, h1, h2, show (0 : ℚ) ≤ (d : ℚ) by positivity]
        · unfold arklibBoundPowQ
          dsimp only
          have hqh_q : (q : ℚ) * (R.natDegree : ℚ) = (q₀ : ℚ) * (h_orig : ℚ) := by exact_mod_cast hqh_eq
          have hRle0 : (R.natDegree : ℚ) ≤ (h₀ : ℚ) := by exact_mod_cast hsmall
          have hsub_le : ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤ ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
            exact_mod_cast Nat.sub_le_sub_right hsmall (2 * wY + 1)
          have htheta_nn : (0 : ℚ) ≤ ((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ) := by positivity
          have hwY_ge1 : (1 : ℚ) ≤ 2 * (wY : ℚ) - 1 := by dsimp [wY]; norm_num
          have hpsi_le : 1 + (2 * (wY : ℚ) - 1) * (2 * (R.natDegree : ℚ) - 1) +
              2 * ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤
              1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
            nlinarith only [hRle0, hsub_le, hwY_ge1]
          have hd_nn : (0 : ℚ) ≤ (d : ℚ) := Nat.cast_nonneg d
          have hh_nn : (0 : ℚ) ≤ (h_orig : ℚ) := Nat.cast_nonneg h_orig
          have htdpsi := mul_le_mul_of_nonneg_left hpsi_le (mul_nonneg htheta_nn hd_nn)
          rw [hqh_q, mul_right_comm (q : ℚ) ((N - wY - 1 : ℕ) : ℚ) (R.natDegree : ℚ), hqh_q]
          nlinarith only [hCd_ark, hCh_ark, hRle0, htdpsi, hd_nn, hh_nn,
            show (0 : ℚ) ≤ 4 * (h_orig : ℚ) * (d : ℚ) by positivity]
      exact hark.trans hmax_le
    · by_cases hY : Polynomial.derivative R = 0
      · by_cases hX : P64Incidence.dXPoly R = 0
        · let T := twistPoly R
          have hback : frobLift T = R := frobLift_twistPoly R hY hX
          have hTi : Irreducible T := irreducible_twistPoly R hirr hY hX
          have hdeg : R.natDegree = T.natDegree * 2 := by rw [← hback, natDegree_frobLift]
          have hTpos : 1 ≤ T.natDegree := by omega
          have hTlt : T.natDegree < R.natDegree := by omega
          have hspace : wd R wY = 2 * wd T wY := by
            rw [← hback, spatial_weight_frobLift T hTi.ne_zero wY]
          let S' := S.image (sqrtF : Fld → Fld)
          let P' : Fld → Fld[X] := fun t => P (t ^ 2)
          let A' : Fld → Finset Idx := fun t => Aset (t ^ 2)
          have hSq : ∀ t ∈ S', t ^ 2 ∈ S := by
            intro t ht; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht; simpa using hz
          have hScard : S'.card = S.card := Finset.card_image_of_injective S sqrtF_injective
          have hwt : WtLE 0 (2 * q) 1 d T := parameter_weight_transfer T q d (by rwa [hback])
          have hF' : 2 * T.natDegree * wd T wY < Fintype.card Fld :=
            (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)).trans_lt hF
          have hexp : ∀ i, Polynomial.expand Fld 2 (linePow u₀ u₁ q i) = linePow u₀ u₁ (2 * q) i :=
            expand_linePow u₀ u₁ q
          have hm : ∀ i, lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) =
              2 * lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) := by
            intro i; rw [← hback, lineOrd_frobLift T hTi.ne_zero, hexp]
          have hβ' : 10000 * T.natDegree ≤ T.natDegree * A -
              ∑ i, lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) := by
            simp_rw [hm] at hβ
            rw [← Finset.mul_sum, hdeg, show T.natDegree * 2 * A = 2 * (T.natDegree * A) by ring,
              ← Nat.mul_sub_left_distrib] at hβ
            omega
          have hcurve' : ∀ t ∈ S', triEval T t (P' t) = 0 := by
            intro t ht; have hc := hcurve _ (hSq t ht); rw [← hback] at hc
            exact eq_zero_of_pow_eq_zero ((triEval_frobLift T t (P' t)).symm.trans hc)
          have hmatch' : ∀ t ∈ S', ∀ i ∈ A' t,
              (P' t).eval (BinaryIRSProfile.domain i) = u₀ i + t ^ (2 * q) * u₁ i := by
            intro t ht i hi
            have hm0 := hmatch _ (hSq t ht) i hi
            rwa [show (t ^ 2) ^ q = t ^ (2 * q) by rw [← pow_mul]] at hm0
          have hNbound' : ∀ t ∈ S',
              normalDefect T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) (A' t) (wd T wY) wY ≤
                ((A' t).card : ℤ) - wY ∨
              normalDefect T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) (A' t) (wd T wY) wY ≤ N_eff := by
            intro t ht
            have htS := hSq t ht
            let sumT : ℤ := ∑ i ∈ A' t, ((lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) - 1 : ℕ) : ℤ)
            let sumR : ℤ := ∑ i ∈ A' t, ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) - 1 : ℕ) : ℤ)
            have hsum_rel : sumR ≤ 2 * sumT + (A' t).card := by
              have hpt : ∀ i ∈ A' t,
                  ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) - 1 : ℕ) : ℤ) ≤
                  2 * ((lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) - 1 : ℕ) : ℤ) + 1 := by
                intro i _; rw [hm i]; omega
              calc sumR ≤ ∑ i ∈ A' t, (2 * ((lineOrd T (BinaryIRSProfile.domain i) (linePow u₀ u₁ (2 * q) i) - 1 : ℕ) : ℤ) + 1) :=
                    Finset.sum_le_sum hpt
                _ = 2 * sumT + (A' t).card := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
            by_cases hcase : (wd T wY : ℤ) - sumT ≤ (A' t).card
            · left; change (wd T wY : ℤ) - wY - sumT ≤ _; linarith
            · have hT_le_R : normalDefect T BinaryIRSProfile.domain (linePow u₀ u₁ (2 * q)) (A' t) (wd T wY) wY ≤
                  normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q) (Aset (t ^ 2)) (wd R wY) wY := by
                change (wd T wY : ℤ) - wY - sumT ≤ (wd R wY : ℤ) - wY - sumR
                have hw2 : (wd R wY : ℤ) = 2 * (wd T wY : ℤ) := by exact_mod_cast hspace
                linarith
              rcases hNbound (t ^ 2) htS with h1 | h2
              · left; exact hT_le_R.trans h1
              · right; exact hT_le_R.trans h2
          have hbT := ih T.natDegree hTlt T hTi hTpos (2 * q) (by omega)
            (by rw [← hqh_eq, hdeg]; ring) (by omega) hwt hF' hβ'
            S' P' A' (fun t ht => hP _ (hSq t ht)) hcurve' (fun t ht => hcard _ (hSq t ht))
            hmatch' (fun t ht => hbad _ (hSq t ht)) hNbound' rfl
          rwa [hScard] at hbT
        · have hc := P64Incidence.card_le_of_inseparable R hirr (by omega) hY hX (wd R wY)
            (P64Resultant.coeff_natDegree_le_weighted R wY) hF S P hcurve
          have hyz := P64C6All.yz_le_twice R hirr.ne_zero q d (by omega) hRyz
          have hm : S.card ≤ 4 * h_orig * d := by nlinarith only [hc, hyz, hRle]
          have h1 : (0 : ℚ) ≤ C_per_d * (d : ℚ) := mul_nonneg (le_trans (by norm_num) hCd_1) (Nat.cast_nonneg _)
          have h2 : (0 : ℚ) ≤ C_per_h * (h_orig : ℚ) := mul_nonneg (le_trans (by positivity) hCh_ark) (Nat.cast_nonneg _)
          have hmQ : (S.card : ℚ) ≤ 4 * (h_orig : ℚ) * (d : ℚ) := by exact_mod_cast hm
          linarith only [hmQ, h1, h2]
      · let β := R.natDegree * A - ∑ i, lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i)
        have hβpos : 0 < β := by dsimp [β]; omega
        have hβeq : (∑ i, lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i)) + β = R.natDegree * A := by
          dsimp [β] at hβpos ⊢; omega
        have hc := c6_separable_general R hirr hh hY (wd R wY) q d Δ N_eff β (by omega) le_rfl hRyz hF
          hNeff hβ (linePow u₀ u₁ q) (linePow_natDegree_le u₀ u₁ q) hβeq S P Aset hP hcurve hcard
          (fun z hz i hi => by rw [eval_linePow]; exact hmatch z hz i hi) hNbound
        have hcQ : (10000 ^ 2 : ℚ) * (S.card : ℚ) ≤
            (2 * N_eff : ℕ) * (8 * (N : ℚ) * (d : ℚ) + 10000 * (4 * (q : ℚ) * (R.natDegree : ℚ) + 1)) +
            (10000 ^ 2 : ℚ) * ((N : ℚ) * (d : ℚ) + 2 * (R.natDegree : ℚ) * (d : ℚ)) := by
          have hc' : ((10000 ^ 2 * S.card : ℕ) : ℚ) ≤
              ((2 * N_eff * (8 * N * d + 10000 * (4 * q * R.natDegree + 1)) +
                10000 ^ 2 * (N * d + 2 * R.natDegree * d) : ℕ) : ℚ) := by exact_mod_cast hc
          push_cast at hc' ⊢; linarith only [hc']
        have hqh_q : (q : ℚ) * (R.natDegree : ℚ) = (q₀ : ℚ) * (h_orig : ℚ) := by exact_mod_cast hqh_eq
        have h1_le_h : (1 : ℚ) ≤ (h_orig : ℚ) := by exact_mod_cast (le_trans hh hRle)
        have hRle_q : (R.natDegree : ℚ) ≤ (h_orig : ℚ) := by exact_mod_cast hRle
        have hdiv : (S.card : ℚ) ≤
            (((16 * N_eff * N : ℕ) : ℚ) / (10000 ^ 2 : ℚ) + (N : ℚ)) * (d : ℚ) +
            2 * (R.natDegree : ℚ) * (d : ℚ) +
            (((2 * N_eff * (4 * q₀ + 1) : ℕ) : ℚ) / (10000 : ℚ)) * (h_orig : ℚ) := by
          have hpos10 : (0 : ℚ) < (10000 ^ 2 : ℚ) := by norm_num
          refine le_of_mul_le_mul_left ?_ hpos10
          have hNE : (0 : ℚ) ≤ (N_eff : ℚ) := Nat.cast_nonneg N_eff
          field_simp [hpos10.ne']
          push_cast at hcQ ⊢
          nlinarith only [hcQ, hqh_q, h1_le_h, hNE]
        have hd_nn : (0 : ℚ) ≤ (d : ℚ) := Nat.cast_nonneg d
        have hh_nn : (0 : ℚ) ≤ (h_orig : ℚ) := Nat.cast_nonneg h_orig
        nlinarith only [hdiv, hCd_c6, hCh_c6, hRle_q, hd_nn, hh_nn]

/-! ### Section 7: Top-level charging over `Φ` (`hybrid_p64_card_le`) -/

/-- `(caseY0 Φ S).card ≤ H` whenever `Φ ≠ 0` has all `Z`-coefficients of degree `≤ H`. -/
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

/-- `WtLE 0 q₀ 1 (yzd R q₀) R` holds tautologically for every `R : Tri`! -/
lemma wtLE_of_yzSupportDegree (R : Tri) (q₀ : ℕ) : WtLE 0 q₀ 1 (yzd R q₀) R := by
  intro a b l hl
  have hb0 : R.coeff b ≠ 0 := fun h => hl (by simp [c3, h])
  have ha0 : (R.coeff b).coeff a ≠ 0 := fun h => hl (by simp [c3, h])
  have h1 : l ≤ ((R.coeff b).coeff a).natDegree := le_natDegree_of_ne_zero (by simpa [c3] using hl)
  have h2 : ((R.coeff b).coeff a).natDegree ≤ Polynomial.Bivariate.degreeX (R.coeff b) :=
    Polynomial.Bivariate.coeff_natDegree_le_degreeX _ a
  have h3 := P64Caps.YZ.coeffWeight_le_of_ne R q₀ b hb0
  omega

/-- Cofactor defect bound for `Φ = R^a * Q''` on `caseSingle Φ S P R`:
if `w_Φ - ∑_{A_z} μ_Φ + 2*m*(|A_z| - A) ≤ Δ_max` and `a ≤ 2 * m`, then
`(w_R - ∑_{A_z} μ_R) + (|A_z| - A) ≤ Δ_max`! -/
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

/-- **Section 7 Master Theorem**: Complete Hybrid ArkLib + Generalized P64 exception bound
for ANY nonzero trivariate `Φ : Tri` (`deg_Y ≤ B`, `deg_Z ≤ H`, `wdeg Φ wY ≤ W_Φ`, `q₀ ∈ {1, 2}`),
given verified parameters `(h₀, slack, P₀, M₀, N_eff, C_per_d, C_per_h)`! -/
theorem hybrid_p64_card_le
    (u₀ u₁ : Idx → Fld) (q₀ : ℕ) (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (Φ : Tri) (B H W_Φ m Δ_max : ℕ)
    (hΦ : Φ ≠ 0) (hB : Φ.natDegree ≤ B)
    (hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ H)
    (hWΦ : wd Φ wY ≤ W_Φ)
    (hFΦ : 2 * B * W_Φ < Fintype.card Fld)
    (hFaux : (4 * W_Φ / wY + B) * (4 * W_Φ) < Fintype.card Fld)
    (S : Finset Fld) (P : Fld → Fld[X]) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval Φ z (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6401 u₀ u₁ (Az z))
    (hΦgap : ∀ z ∈ S,
      (wd Φ wY : ℤ) - (∑ i ∈ Az z, (lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
        (2 * m : ℤ) * ((Az z).card - (A : ℤ)) ≤ Δ_max)
    -- Shortening Johnson cert at A = 1482831 (λ* = 208984)
    (m_j B_j H_j count_j : ℕ)
    (hcert : ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate 1888168 839591 1273847 m_j B_j H_j)
    (hcnt : ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount 1888168 839591 1273847 B_j H_j ≤ count_j)
    (hB_j : B_j ≤ 2 * 839591 + 1)
    -- Hybrid P64 tuning parameters (checked by norm_num / exact arithmetic!)
    (h₀ q_aux slack P₀ M₀ N_eff : ℕ)
    (hh₀ : 1 ≤ h₀) (hq_aux : 1 ≤ q_aux) (hM0pos : 0 < M₀)
    (hB_mul : B ≤ 2 * m * (h₀ + 1))
    (hC0_h : A + 4 * Δ_max + 1 ≤ 4 * (h₀ + 1) * wY)
    (h4B_q : 4 * B ≤ q_aux)
    (hslack : (4 * W_Φ / wY) * (8 * N) ≤ q_aux * slack)
    (hP₀ : 8 * (wY : ℤ) * slack * (h₀ + 1 : ℤ) ^ 2 +
      16 * (wY : ℤ) * ((A : ℤ) - wY + 10000) * (h₀ + 1 : ℤ) + ((wY : ℤ) + 2) ^ 2 ≤
      64 * (wY : ℤ) * P₀ * (h₀ + 1 : ℤ) ^ 2)
    (hM0 : (M₀ : ℤ) + P₀ = (A : ℤ) - wY)
    (hNeff : (N_eff : ℤ) = (A : ℤ) - wY + Δ_max)
    (hMh : 2 * N_eff ≤ M₀ * (h₀ + 1))
    (C_per_d C_per_h : ℚ)
    (hCd_ark : (2 * (h₀ : ℚ) - 1) + (((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) *
      (1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ)) ≤ C_per_d)
    (hCd_light : (208984 : ℚ) ≤ C_per_d)
    (hCd_c7 : ((2 * N_eff * N * 6 : ℕ) : ℚ) / (M₀ : ℚ) + (N : ℚ) ≤ C_per_d)
    (hCd_c6 : ((16 * N_eff * N : ℕ) : ℚ) / (10000 ^ 2 : ℚ) + (N : ℚ) ≤ C_per_d)
    (hCh_aux : (q₀ : ℚ) * ((q_aux : ℚ) + (4 * W_Φ / wY : ℕ)) ≤ C_per_h)
    (hCh_light : (count_j : ℚ) / ((h₀ + 1 : ℕ) : ℚ) ≤ C_per_h)
    (hCh_ark : (q₀ : ℚ) * ((((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) ≤ C_per_h)
    (hCh_c7 : ((2 * N_eff * N * (2 * q₀ + 2) : ℕ) : ℚ) / (M₀ : ℚ) ≤ C_per_h)
    (hCh_c6 : ((2 * N_eff * (4 * q₀ + 1) : ℕ) : ℚ) / (10000 : ℚ) ≤ C_per_h) :
    let D_tot : ℚ := (H : ℚ) + (q₀ : ℚ) * (B : ℚ)
    (S.card : ℚ) ≤ C_per_d * D_tot +
      (max (4 * W_Φ / wY : ℕ) (4 * B) + B : ℚ) * D_tot + C_per_h * (B : ℚ) + (H : ℚ) := by
  classical
  have hq₀pos : 1 ≤ q₀ := by rcases hq₀ with rfl | rfl <;> omega
  have hCd_1 : (1 : ℚ) ≤ C_per_d := le_trans (by norm_num) hCd_light
  have hcover := card_le_cover Φ hΦ S P hcurve
  have hY0 := card_caseY0_le Φ hΦ H hH S
  have hΦ_yz : yzd Φ q₀ ≤ H + q₀ * B := by
    unfold P64Caps.YZ.yzSupportDegree
    apply Finset.sup_le
    intro j hj
    have hjB : j ≤ B := (Polynomial.le_natDegree_of_ne_zero (mem_support_iff.mp hj)).trans hB
    have hdX : Polynomial.Bivariate.degreeX (Φ.coeff j) ≤ H := by
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le; intro a _; exact hH j a
    have hqj := Nat.mul_le_mul_left q₀ hjB
    omega
  have hΦ_yz1 : yzd Φ 1 ≤ H + q₀ * B := by
    have hle : yzd Φ 1 ≤ yzd Φ q₀ := by
      change Φ.support.sup _ ≤ yzd Φ q₀
      apply Finset.sup_le; intro j hj
      calc Polynomial.Bivariate.degreeX (Φ.coeff j) + 1 * j
          ≤ Polynomial.Bivariate.degreeX (Φ.coeff j) + q₀ * j := by rcases hq₀ with rfl | rfl <;> omega
        _ ≤ yzd Φ q₀ := P64Caps.YZ.coeffWeight_le_of_ne Φ q₀ j (mem_support_iff.mp hj)
    exact hle.trans hΦ_yz
  have hpair : (casePair Φ S P).card ≤ B * (H + q₀ * B) := by
    have hF' : 2 * Φ.natDegree * wd Φ wY < Fintype.card Fld :=
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hB) hWΦ).trans_lt hFΦ
    exact (P64Resultant.card_casePair_le Φ hΦ wY hF' S P).trans
      (Nat.mul_le_mul hB hΦ_yz1)
  let M_B : ℕ := max (4 * W_Φ / wY) (4 * B)
  -- Per-factor bound for every R ∈ factors Φ!
  have hfac : ∀ R ∈ factors Φ,
      ((caseSingle Φ S P R).card : ℚ) ≤
        C_per_d * (yzd R q₀ : ℚ) + (M_B : ℚ) * (yzd R q₀ : ℚ) + C_per_h * (R.natDegree : ℚ) := by
    intro R hR
    have hirr : Irreducible R :=
      (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Tri) R (Multiset.mem_toFinset.mp hR)).irreducible
    have hR0 : R ≠ 0 := hirr.ne_zero
    have hdvd : R ∣ Φ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hR)
    by_cases hdeg0 : R.natDegree = 0
    · rw [caseSingle_eq_empty_of_natDegree_eq_zero Φ S P R hR hdeg0]; simp
      have : (0 : ℚ) ≤ C_per_d := le_trans (by norm_num) hCd_1
      have : (0 : ℚ) ≤ C_per_h := le_trans (by positivity) hCh_ark
      positivity
    have hRpos : 1 ≤ R.natDegree := by omega
    have hRleB : R.natDegree ≤ B := (Polynomial.natDegree_le_of_dvd hdvd hΦ).trans hB
    have hRw_le : wd R wY ≤ W_Φ := by
      obtain ⟨C, hC⟩ := hdvd
      have hC0 : C ≠ 0 := by rintro rfl; exact hΦ (by simpa using hC)
      have hmul := P64Caps.Weighted.weightedSupportDegree_mul R C wY hR0 hC0
      rw [← hC] at hmul
      omega
    have hRyz : WtLE 0 q₀ 1 (yzd R q₀) R := wtLE_of_yzSupportDegree R q₀
    have h1d : yzd R 1 ≤ yzd R q₀ := by
      change R.support.sup _ ≤ yzd R q₀
      apply Finset.sup_le; intro j hj
      calc Polynomial.Bivariate.degreeX (R.coeff j) + 1 * j
          ≤ Polynomial.Bivariate.degreeX (R.coeff j) + q₀ * j := by rcases hq₀ with rfl | rfl <;> omega
        _ ≤ yzd R q₀ := P64Caps.YZ.coeffWeight_le_of_ne R q₀ j (mem_support_iff.mp hj)
    let Vs := caseSingle Φ S P R
    have hVsS : ∀ z ∈ Vs, z ∈ S := fun z hz => (Finset.mem_filter.mp hz).1
    have hVsR : ∀ z ∈ Vs, triEval R z (P z) = 0 := fun z hz => (Finset.mem_filter.mp hz).2.2.1
    by_cases hsmall : R.natDegree ≤ h₀
    · -- Low-degree factor: direct ArkLib (Section 1)!
      have hHR : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ yzd R q₀ :=
        coefficient_parameter_degree R q₀ (yzd R q₀) hRyz
      have hark := card_le_of_biPoly_pow u₀ u₁ q₀ hq₀pos R R.natDegree (yzd R q₀) hR0 le_rfl hHR
        Vs P Az (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
        (fun z hz i hi => (hmatch z (hVsS z hz) i).mp hi) (fun z hz => hbad z (hVsS z hz))
      refine hark.trans (max_le ?_ ?_)
      · have h1 : (0 : ℚ) ≤ (M_B : ℚ) * (yzd R q₀ : ℚ) := by positivity
        have h2 : (0 : ℚ) ≤ C_per_h * (R.natDegree : ℚ) :=
          mul_nonneg (le_trans (by positivity) hCh_ark) (Nat.cast_nonneg _)
        nlinarith only [hCd_1, h1, h2, show (0 : ℚ) ≤ (yzd R q₀ : ℚ) by positivity]
      · unfold arklibBoundPowQ
        dsimp only
        have hRle0 : (R.natDegree : ℚ) ≤ (h₀ : ℚ) := by exact_mod_cast hsmall
        have hsub_le : ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤ ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
          exact_mod_cast Nat.sub_le_sub_right hsmall (2 * wY + 1)
        have htheta_nn : (0 : ℚ) ≤ ((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ) := by positivity
        have hwY_ge1 : (1 : ℚ) ≤ 2 * (wY : ℚ) - 1 := by dsimp [wY]; norm_num
        have hpsi_le : 1 + (2 * (wY : ℚ) - 1) * (2 * (R.natDegree : ℚ) - 1) +
            2 * ((R.natDegree - (2 * wY + 1) : ℕ) : ℚ) ≤
            1 + (2 * (wY : ℚ) - 1) * (2 * (h₀ : ℚ) - 1) + 2 * ((h₀ - (2 * wY + 1) : ℕ) : ℚ) := by
          nlinarith only [hRle0, hsub_le, hwY_ge1]
        have hd_nn : (0 : ℚ) ≤ (yzd R q₀ : ℚ) := Nat.cast_nonneg _
        have hh_nn : (0 : ℚ) ≤ (R.natDegree : ℚ) := Nat.cast_nonneg _
        have htdpsi := mul_le_mul_of_nonneg_left hpsi_le (mul_nonneg htheta_nn hd_nn)
        nlinarith only [hCd_ark, hCh_ark, hRle0, htdpsi, hd_nn, hh_nn,
          show (0 : ℚ) ≤ (M_B : ℚ) * (yzd R q₀ : ℚ) by positivity]
    · -- High-degree factor: R.natDegree ≥ h₀ + 1!
      have hbig : h₀ + 1 ≤ R.natDegree := by omega
      -- First check afLight (Section 2):
      by_cases hlight : 208984 ≤ (P64C7Case.fullLines R BinaryIRSProfile.domain (linePow u₀ u₁ q₀)).card ∨
          (lam BinaryIRSProfile.domain (linePow u₀ u₁ q₀) R).card ≤ 208983
      · have hl := fullLines_subset_eq hirr hRpos q₀ (yzd R q₀) hq₀ hRyz u₀ u₁ Vs P Az
          (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
          (fun z hz => hmatch z (hVsS z hz)) (fun z hz => hbad z (hVsS z hz))
          m_j B_j H_j count_j hcert hcnt hB_j hlight
        have hlQ : (Vs.card : ℚ) ≤ 208984 * (yzd R q₀ : ℚ) + (count_j : ℚ) := by exact_mod_cast hl
        have hcnt_le : (count_j : ℚ) ≤ C_per_h * (R.natDegree : ℚ) := by
          have h1 : ((h₀ + 1 : ℕ) : ℚ) ≤ (R.natDegree : ℚ) := by exact_mod_cast hbig
          have hpos : (0 : ℚ) < ((h₀ + 1 : ℕ) : ℚ) := by positivity
          have h2 : (count_j : ℚ) ≤ C_per_h * ((h₀ + 1 : ℕ) : ℚ) := (div_le_iff₀ hpos).mp hCh_light
          have hCh_nn : (0 : ℚ) ≤ C_per_h := le_trans (by positivity) hCh_light
          nlinarith only [h1, h2, hCh_nn]
        have : (0 : ℚ) ≤ (M_B : ℚ) * (yzd R q₀ : ℚ) := by positivity
        nlinarith only [hlQ, hCd_light, hcnt_le, this, show (0 : ℚ) ≤ (yzd R q₀ : ℚ) by positivity]
      · push_neg at hlight
        have hfull_lt : (P64C7Case.fullLines R BinaryIRSProfile.domain (linePow u₀ u₁ q₀)).card < A :=
          lt_of_lt_of_le hlight.1 (by norm_num [A])
        -- Prove cofactor defect bound for every z ∈ Vs!
        have hdef_R : ∀ z ∈ Vs,
            ((wd R wY : ℤ) - ∑ i ∈ Az z, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
              ((Az z).card - (A : ℤ)) ≤ Δ_max :=
          cofactor_defect_of_single_factor Φ R hΦ hR q₀ u₀ u₁ m Δ_max S P Az hP hcard
            (fun z hz i hi => (hmatch z hz i).mp hi) hΦgap (fun a Q'' hΦeq _ => by
              have hQ''0 : Q'' ≠ 0 := by rintro rfl; exact hΦ (by rw [hΦeq, mul_zero])
              have hd : a * R.natDegree ≤ Φ.natDegree := by
                rw [hΦeq, natDegree_mul (pow_ne_zero a hR0) hQ''0, natDegree_pow]; omega
              have : a * (h₀ + 1) ≤ 2 * m * (h₀ + 1) :=
                (Nat.mul_le_mul_left a hbig).trans (hd.trans (hB.trans hB_mul))
              exact Nat.le_of_mul_le_mul_right this (by omega))
        have hNbound : ∀ z ∈ Vs,
            normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q₀) (Az z) (wd R wY) wY ≤
              ((Az z).card : ℤ) - wY ∨
            normalDefect R BinaryIRSProfile.domain (linePow u₀ u₁ q₀) (Az z) (wd R wY) wY ≤ N_eff := by
          intro z hz
          right
          -- normalDefect = w - wY - ∑ (μ - 1) ≤ w - wY - (∑ μ - |A_z|) = (w - ∑ μ) + (|A_z| - wY)
          -- = (A - wY) + (w - ∑ μ) + (|A_z| - A) ≤ (A - wY) + Δ_max = N_eff!
          have hsum_ge : ∑ i ∈ Az z, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ) - (Az z).card ≤
              ∑ i ∈ Az z, ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 : ℕ) : ℤ) := by
            have hpt : ∀ i ∈ Az z, (lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ) - 1 ≤
                ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 : ℕ) : ℤ) := fun i _ => by omega
            calc _ = ∑ i ∈ Az z, ((lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ) - 1) := by
                    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
              _ ≤ _ := Finset.sum_le_sum hpt
          have hd0 := hdef_R z hz
          change (wd R wY : ℤ) - wY - _ ≤ _
          linarith only [hsum_ge, hd0, hNeff]
        have hFR : 2 * R.natDegree * wd R wY < Fintype.card Fld :=
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hRleB) hRw_le).trans_lt hFΦ
        -- Split on positive bias vs low bias!
        by_cases hbias : 10000 * R.natDegree ≤
            R.natDegree * A - ∑ i, lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i)
        · -- Positive bias C6 with Frobenius descent & ArkLib cutoff!
          have hc6 := card_le_of_factor_frob_c6 u₀ u₁ q₀ R.natDegree h₀ (yzd R q₀) Δ_max N_eff
            hq₀pos hh₀ hNeff R hirr hRpos q₀ hq₀pos rfl le_rfl hRyz hFR hbias Vs P Az
            (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
            (fun z hz i hi => (hmatch z (hVsS z hz) i).mp hi) (fun z hz => hbad z (hVsS z hz))
            hNbound C_per_d C_per_h hCd_ark hCd_1 hCd_c6 hCh_ark hCh_c6
          have h4le : (4 * R.natDegree : ℚ) ≤ (M_B : ℚ) := by
            exact_mod_cast (Nat.mul_le_mul_left 4 hRleB).trans (le_max_right _ _)
          nlinarith only [hc6, h4le, show (0 : ℚ) ≤ (yzd R q₀ : ℚ) by positivity]
        · -- Low bias: either S_4 auxiliary succeeds (Section 3) or fails ⇒ profile ⇒ C7 (Section 6)!
          let W := 4 * wd R wY - (A + 4 * Δ_max + 1)
          let J := W / wY
          let c4 := ∑ i, (4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1) *
            (4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 + 1) / 2
          have hw_low : R.natDegree * wY ≤ wd R wY := by
            have := natDegree_mul_le_weightedSupportDegree R hR0 wY; rwa [mul_comm] at this
          have hC0 : A + 4 * Δ_max + 1 ≤ 4 * wd R wY := by
            have : 4 * (h₀ + 1) * wY ≤ 4 * wd R wY := by nlinarith only [hbig, hw_low]
            omega
          have hφ : ∀ i, 4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1 ≤ q_aux + J := by
            intro i
            have hμh := lineOrd_le_natDegree_of_irreducible hirr hRpos (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i)
            calc 4 * lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) - 1
                ≤ 4 * B := by omega
              _ ≤ q_aux := h4B_q
              _ ≤ q_aux + J := Nat.le_add_right _ _
          have hJ_le : J ≤ 4 * W_Φ / wY := Nat.div_le_div_right (by dsimp [W]; omega)
          by_cases hcrit : (q_aux + J) * c4 < q_aux * P64Surf.Mbox W
          · -- S_4 succeeds!
            have hFR_aux : (J + R.natDegree) * (4 * wd R wY) < Fintype.card Fld :=
              (Nat.mul_le_mul (Nat.add_le_add hJ_le hRleB) (Nat.mul_le_mul_left 4 hRw_le)).trans_lt hFaux
            have haux := aux_card_le_pow u₀ u₁ q₀ hq₀ hirr hRpos
              (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
              (fun z hz i hi => (hmatch z (hVsS z hz) i).mp hi) Δ_max hdef_R q_aux hq_aux hC0 hφ hcrit hFR_aux
            have hJ_MB : J ≤ M_B := hJ_le.trans (le_max_left _ _)
            have haux2 : Vs.card ≤ M_B * yzd R q₀ + R.natDegree * (q₀ * (q_aux + 4 * W_Φ / wY)) := by
              have h1 := Nat.mul_le_mul hJ_MB h1d
              have h2 : q₀ * (q_aux + J - 1) ≤ q₀ * (q_aux + 4 * W_Φ / wY) :=
                Nat.mul_le_mul_left q₀ ((Nat.sub_le _ _).trans (Nat.add_le_add_left hJ_le q_aux))
              have h3 := Nat.mul_le_mul_left R.natDegree h2
              exact haux.trans (Nat.add_le_add h1 h3)
            have hauxQ : (Vs.card : ℚ) ≤ (M_B : ℚ) * (yzd R q₀ : ℚ) +
                (R.natDegree : ℚ) * ((q₀ : ℚ) * ((q_aux : ℚ) + (4 * W_Φ / wY : ℕ))) := by
              exact_mod_cast haux2
            have hCd_nn : (0 : ℚ) ≤ C_per_d * (yzd R q₀ : ℚ) :=
              mul_nonneg (le_trans (by norm_num) hCd_1) (Nat.cast_nonneg _)
            nlinarith only [hauxQ, hCh_aux, hCd_nn, show (0 : ℚ) ≤ (R.natDegree : ℚ) by positivity]
          · -- S_4 fails ⇒ profile bound ⇒ C7 Frobenius descent with ArkLib cutoff!
            push_neg at hcrit
            let μ : Idx → ℕ := fun i => lineOrd R (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i)
            have hc4_eq : (c4 : ℤ) = 8 * (∑ i, (μ i : ℤ) ^ 2) - 2 * (∑ i, (μ i : ℤ)) := by
              dsimp [c4, μ]; rw [Nat.cast_sum]; simp_rw [P64C7ProfileArithmetic.con_term]
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            have hS₂ : (∑ i, (μ i : ℤ) ^ 2) ≤ (R.natDegree : ℤ) ^ 2 * N := by
              calc _ ≤ ∑ _ : Idx, (R.natDegree : ℤ) ^ 2 := Finset.sum_le_sum fun i _ =>
                    by exact_mod_cast Nat.pow_le_pow_left (lineOrd_le_natDegree_of_irreducible hirr hRpos _ _) 2
                _ = (R.natDegree : ℤ) ^ 2 * N := by
                    rw [Finset.sum_const, Finset.card_univ, BinaryIRSProfile.card_index, nsmul_eq_mul]
                    change ((2097152 : ℕ) : ℤ) * _ = _; dsimp only [N]; push_cast; ring
            have hS₁nn : (0 : ℤ) ≤ ∑ i, (μ i : ℤ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
            have hc4_le : c4 ≤ 8 * R.natDegree ^ 2 * N := by
              exact_mod_cast (show (c4 : ℤ) ≤ 8 * R.natDegree ^ 2 * N by nlinarith only [hc4_eq, hS₂, hS₁nn])
            have hJc : J * c4 ≤ q_aux * (slack * R.natDegree ^ 2) := by
              have h1 := Nat.mul_le_mul hJ_le hc4_le
              calc J * c4 ≤ (4 * W_Φ / wY) * (8 * R.natDegree ^ 2 * N) := h1
                _ = ((4 * W_Φ / wY) * (8 * N)) * R.natDegree ^ 2 := by ring
                _ ≤ (q_aux * slack) * R.natDegree ^ 2 := Nat.mul_le_mul_right _ hslack
                _ = q_aux * (slack * R.natDegree ^ 2) := by ring
            have hM := count_slack_gen R.natDegree J c4 (P64Surf.Mbox W) q_aux slack (by omega) hJc hcrit
            have hM' : (P64Surf.Mbox W : ℤ) ≤ 8 * (∑ i, (μ i : ℤ) ^ 2) - 2 * (∑ i, (μ i : ℤ)) +
                slack * R.natDegree ^ 2 := by
              have : (P64Surf.Mbox W : ℤ) ≤ c4 + slack * R.natDegree ^ 2 := by exact_mod_cast hM
              rwa [hc4_eq] at this
            have hWcast : (W : ℤ) = 4 * wd R wY - ((A : ℤ) + 4 * Δ_max + 1) := by
              dsimp [W]; rw [Nat.cast_sub hC0]; push_cast; ring
            have hm_low := P64C7ProfileArithmetic.mbox_quadratic_lower W
            rw [hWcast] at hm_low
            have hcount : (4 * (wd R wY : ℤ) - ((A : ℤ) + 4 * Δ_max + 1)) ^ 2 +
                ((wY : ℤ) + 2) * (4 * (wd R wY : ℤ) - ((A : ℤ) + 4 * Δ_max + 1)) ≤
                2 * (wY : ℤ) * (8 * (∑ i, (μ i : ℤ) ^ 2) - 2 * (∑ i, (μ i : ℤ)) + slack * R.natDegree ^ 2) := by
              have h2wY : (2 * (wY : ℤ)) = 2097150 := by dsimp [wY]
              have hwY2 : ((wY : ℤ) + 2) = 1048577 := by dsimp [wY]
              rw [h2wY, hwY2]
              exact hm_low.trans (mul_le_mul_of_nonneg_left hM' (by norm_num))
            have hS₁ : (R.natDegree : ℤ) * ((A : ℤ) - 10000) ≤ ∑ i, (μ i : ℤ) := by
              have : R.natDegree * (A - 10000) ≤ ∑ i, μ i := by
                have : R.natDegree * A - ∑ i, μ i < 10000 * R.natDegree := by dsimp only [μ]; omega
                have : R.natDegree * A = R.natDegree * (A - 10000) + 10000 * R.natDegree := by
                  dsimp [A]; ring
                omega
              have hsubA : ((A - 10000 : ℕ) : ℤ) = (A : ℤ) - 10000 := by dsimp [A]
              rw [← hsubA]; exact_mod_cast this
            have hprof := profile_algebra_delta R.natDegree (wd R wY) (∑ i, (μ i : ℤ)) (∑ i, (μ i : ℤ) ^ 2)
              Δ_max slack 10000 (h₀ + 1) P₀ (by exact_mod_cast hbig) (by omega) (Nat.cast_nonneg _)
              (by norm_num) hS₁ hP₀ hcount
            have hc7 := card_le_of_factor_frob_c7 u₀ u₁ q₀ R.natDegree h₀ (yzd R q₀) Δ_max P₀ M₀ N_eff
              hq₀pos hh₀ hM0pos hM0 hNeff hMh R hirr hRpos q₀ hq₀pos rfl le_rfl hRyz hFR hfull_lt hprof
              Vs P Az (fun z hz => hP z (hVsS z hz)) hVsR (fun z hz => hcard z (hVsS z hz))
              (fun z hz => hmatch z (hVsS z hz)) (fun z hz => hbad z (hVsS z hz)) hNbound
              C_per_d C_per_h hCd_ark hCd_1 hCd_c7 hCh_ark hCh_c7
            have h4le : (4 * R.natDegree : ℚ) ≤ (M_B : ℚ) := by
              exact_mod_cast (Nat.mul_le_mul_left 4 hRleB).trans (le_max_right _ _)
            nlinarith only [hc7, h4le, show (0 : ℚ) ≤ (yzd R q₀ : ℚ) by positivity]
  -- Sum over all normalized factors of Φ!
  have hsum_d : ∑ R ∈ factors Φ, yzd R q₀ ≤ H + q₀ * B :=
    (sum_yz_le Φ hΦ q₀).trans hΦ_yz
  have hsum_h : ∑ R ∈ factors Φ, R.natDegree ≤ B := (sum_natDegree_le Φ hΦ).trans hB
  have hsum_fac : (∑ R ∈ factors Φ, ((caseSingle Φ S P R).card : ℚ)) ≤
      (C_per_d + (M_B : ℚ)) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) + C_per_h * (B : ℚ) := by
    calc _ ≤ ∑ R ∈ factors Φ, (C_per_d * (yzd R q₀ : ℚ) + (M_B : ℚ) * (yzd R q₀ : ℚ) +
              C_per_h * (R.natDegree : ℚ)) := Finset.sum_le_sum hfac
      _ = (C_per_d + (M_B : ℚ)) * (∑ R ∈ factors Φ, (yzd R q₀ : ℚ)) +
          C_per_h * (∑ R ∈ factors Φ, (R.natDegree : ℚ)) := by
            simp_rw [← add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (C_per_d + (M_B : ℚ)) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) + C_per_h * (B : ℚ) := by
            have hdQ : (∑ R ∈ factors Φ, (yzd R q₀ : ℚ)) ≤ (H : ℚ) + (q₀ : ℚ) * (B : ℚ) := by
              exact_mod_cast hsum_d
            have hhQ : (∑ R ∈ factors Φ, (R.natDegree : ℚ)) ≤ (B : ℚ) := by exact_mod_cast hsum_h
            have h1 : (0 : ℚ) ≤ C_per_d + (M_B : ℚ) := by
              have := le_trans (by norm_num : (0 : ℚ) ≤ 1) hCd_1; positivity
            have h2 : (0 : ℚ) ≤ C_per_h := le_trans (by positivity) hCh_ark
            nlinarith only [hdQ, hhQ, h1, h2]
  have hcovQ : (S.card : ℚ) ≤ (caseY0 Φ S).card + (casePair Φ S P).card +
      ∑ R ∈ factors Φ, ((caseSingle Φ S P R).card : ℚ) := by exact_mod_cast hcover
  have hY0Q : ((caseY0 Φ S).card : ℚ) ≤ (H : ℚ) := by exact_mod_cast hY0
  have hpairQ : ((casePair Φ S P).card : ℚ) ≤ (B : ℚ) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) := by
    exact_mod_cast hpair
  have hM_B_cast : (M_B : ℚ) = max ((4 * W_Φ / wY : ℕ) : ℚ) (4 * (B : ℚ)) := by
    dsimp only [M_B]; rw [Nat.cast_max]; push_cast; rfl
  nlinarith only [hcovQ, hY0Q, hpairQ, hsum_fac, hM_B_cast]

end B6401HybridP64
end ProximityPrize.SubmissionBinaryLower
