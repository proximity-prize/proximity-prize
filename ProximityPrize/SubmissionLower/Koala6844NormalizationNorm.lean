import ProximityPrize.SubmissionLower.Koala6844NormalizationData
import Mathlib.Tactic.LinearCombination


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial

variable {K : Type*} [Field K]

theorem homogeneous_difference (σ : K →+* K) {d0 d1 P Q E : Polynomial K}
    (hP : d1 * P.map σ - d0.map σ * P = E)
    (hQ : d1 * Q.map σ - d0.map σ * Q = E) :
    d1 * (P - Q).map σ = d0.map σ * (P - Q) := by
  rw [Polynomial.map_sub]
  linear_combination hP - hQ

theorem content_degree_eq (σ : K →+* K) {d0 d1 R : Polynomial K}
    (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0) (hR : R ≠ 0)
    (h : d1 * R.map σ = d0.map σ * R) : d1.natDegree = d0.natDegree := by
  have hdeg := congrArg Polynomial.natDegree h
  rw [natDegree_mul hd1 ((Polynomial.map_ne_zero_iff σ.injective).2 hR),
    natDegree_mul ((Polynomial.map_ne_zero_iff σ.injective).2 hd0) hR,
    natDegree_map, natDegree_map] at hdeg
  omega

theorem content_eval_ne_zero (σ : K →+* K) {d0 d1 R : Polynomial K}
    (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0) (hR : R ≠ 0)
    (hCoprime : IsCoprime d0 d1)
    (h : d1 * R.map σ = d0.map σ * R) {x : K} (hx : σ x = x) :
    d0.eval x ≠ 0 ∧ d1.eval x ≠ 0 := by
  have hmult := congrArg (rootMultiplicity x) h
  have hm1 := mul_ne_zero hd1 ((Polynomial.map_ne_zero_iff σ.injective).2 hR)
  have hm0 := mul_ne_zero ((Polynomial.map_ne_zero_iff σ.injective).2 hd0) hR
  have hmR : (R.map σ).rootMultiplicity x = R.rootMultiplicity x := by
    simpa only [hx] using (eq_rootMultiplicity_map (p := R) σ.injective x).symm
  have hmD : (d0.map σ).rootMultiplicity x = d0.rootMultiplicity x := by
    simpa only [hx] using (eq_rootMultiplicity_map (p := d0) σ.injective x).symm
  rw [rootMultiplicity_mul hm1, rootMultiplicity_mul hm0, hmR, hmD] at hmult
  have heq : d1.rootMultiplicity x = d0.rootMultiplicity x := by omega
  obtain ⟨u, v, hBezout⟩ := hCoprime
  have hNoCommon : ¬ (d0.eval x = 0 ∧ d1.eval x = 0) := by
    rintro ⟨h0, h1⟩
    have hunit := congrArg (eval x) hBezout
    simp [h0, h1] at hunit
  constructor
  · intro hz
    have h1 : IsRoot d1 x := by
      rw [← rootMultiplicity_pos hd1, heq, rootMultiplicity_pos hd0]
      exact hz
    exact hNoCommon ⟨hz, h1⟩
  · intro hz
    have h0 : IsRoot d0 x := by
      rw [← rootMultiplicity_pos hd0, ← heq, rootMultiplicity_pos hd1]
      exact hz
    exact hNoCommon ⟨h0, hz⟩

theorem leadingCoeff_ratio_fixed (σ : K →+* K) {d0 d1 R T : Polynomial K}
    (hd1 : d1 ≠ 0) (hT : T ≠ 0)
    (hR : d1 * R.map σ = d0.map σ * R)
    (hTrel : d1 * T.map σ = d0.map σ * T) :
    σ (R.leadingCoeff / T.leadingCoeff) = R.leadingCoeff / T.leadingCoeff := by
  have hr := congrArg leadingCoeff hR
  have ht := congrArg leadingCoeff hTrel
  simp only [leadingCoeff_mul, leadingCoeff_map] at hr ht
  have hTlc : T.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hT
  have hd1lc : d1.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd1
  rw [map_div₀]
  apply (div_eq_div_iff ((_root_.map_ne_zero σ).2 hTlc) hTlc).2
  apply mul_left_cancel₀ hd1lc
  linear_combination T.leadingCoeff * hr - R.leadingCoeff * ht

end ProximityPrize.SubmissionLower.Koala6844Normalization
