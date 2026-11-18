import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartCuts
import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartWitness

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped BigOperators
open MvPolynomial RCN002 RCN065 RCN135 RCN136 RCN229 RCN234 RCN347

noncomputable section

set_option maxHeartbeats 2600000
set_option maxRecDepth 18000
set_option linter.style.haveILetI false

variable {K L : Type} [Field K] [Field L]

def persistentAgreementNumerator (F : Carrier K) (w : ℕ) (x u₀ u₁ : K) : Carrier K :=
  let S := implicitRegularity F
  S ^ (2 * w) * (MvPolynomial.X 1 - MvPolynomial.C u₀ - MvPolynomial.C u₁ * MvPolynomial.X 2) +
    ∑ j ∈ Finset.range w,
      S ^ (2 * w - (2 * j + 1)) * tailNumerator F j *
        (MvPolynomial.C x - MvPolynomial.X 0) ^ (j + 1) *
        MvPolynomial.C (((j + 1).factorial : K)⁻¹)

theorem persistentAgreementNumerator_eval_div
    (F : Carrier K) (w : ℕ) (x u₀ u₁ : K)
    (coeff : K →+* L) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coeff v F = 0)
    (hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0) :
    MvPolynomial.eval₂Hom coeff v (persistentAgreementNumerator F w x u₀ u₁) /
        (MvPolynomial.eval₂Hom coeff v (implicitRegularity F)) ^ (2 * w) =
      (pointTaylorPolynomial F coeff v hF hS w).eval (coeff x - v 0) - coeff u₀ - coeff u₁ * v 2 := by
  let P := pointTaylorPolynomial F coeff v hF hS w
  let S := MvPolynomial.eval₂Hom coeff v (implicitRegularity F)
  let t := coeff x - v 0
  have hEval : P.eval t = v 1 + ∑ j ∈ Finset.range w, P.coeff (j + 1) * t ^ (j + 1) := by
    rw [Polynomial.eval_eq_sum_range' ((pointTaylorPolynomial_natDegree_le F coeff v hF hS w).trans_lt
      (Nat.lt_succ_self w)), Finset.sum_range_succ']
    simp [P, pointTaylorPolynomial_coeff_zero, add_comm]
  have hterm (j : ℕ) (hj : j ∈ Finset.range w) :
      S ^ (2 * w - (2 * j + 1)) * MvPolynomial.eval₂Hom coeff v (tailNumerator F j) *
          t ^ (j + 1) * coeff (((j + 1).factorial : K)⁻¹) =
        S ^ (2 * w) * (P.coeff (j + 1) * t ^ (j + 1)) := by
    have hjw : j + 1 ≤ w := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hs : S ^ (2 * j + 1) ≠ 0 := pow_ne_zero _ hS
    have hpow : S ^ (2 * w) = S ^ (2 * w - (2 * j + 1)) * S ^ (2 * j + 1) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [show P.coeff (j + 1) = (MvPolynomial.eval₂Hom coeff v (tailNumerator F j) /
        S ^ (2 * j + 1)) / ((j + 1).factorial : L) from
      pointTaylorPolynomial_coeff_succ F coeff v hF hS w j hjw, hpow, map_inv₀, map_natCast,
      div_eq_mul_inv, div_eq_mul_inv]
    calc
      _ = S ^ (2 * w - (2 * j + 1)) * MvPolynomial.eval₂Hom coeff v (tailNumerator F j) *
          t ^ (j + 1) * ((j + 1).factorial : L)⁻¹ * (S ^ (2 * j + 1) * (S ^ (2 * j + 1))⁻¹) :=
        by rw [mul_inv_cancel₀ hs, mul_one]
      _ = _ := by ring
  apply (div_eq_iff (pow_ne_zero (2 * w) hS)).2
  change MvPolynomial.eval₂Hom coeff v (persistentAgreementNumerator F w x u₀ u₁) =
    (P.eval t - coeff u₀ - coeff u₁ * v 2) * S ^ (2 * w)
  rw [hEval]
  simp only [persistentAgreementNumerator, map_add, map_sub, map_mul, map_pow, map_sum,
    MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
  change S ^ (2 * w) * (v 1 - coeff u₀ - coeff u₁ * v 2) +
      (∑ j ∈ Finset.range w, S ^ (2 * w - (2 * j + 1)) *
        MvPolynomial.eval₂Hom coeff v (tailNumerator F j) * t ^ (j + 1) *
        coeff (((j + 1).factorial : K)⁻¹)) = _
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

private theorem polynomial_eval_generic (φ : Polynomial K →+* L) (P : Polynomial K) :
    (P.map (φ.comp Polynomial.C)).eval (φ Polynomial.X) = φ P := by
  have heq : (Polynomial.evalRingHom (φ Polynomial.X)).comp
      (Polynomial.mapRingHom (φ.comp Polynomial.C)) = φ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  exact DFunLike.congr_fun heq P

private theorem pointTaylorPolynomial_eq_taylor_at_genericX
    (φ : Polynomial K →+* L) (F : Carrier K) (P : Polynomial K) (z₀ z₁ : K)
    (hsol : graphSpecialize P z₀ z₁ F = 0)
    (v : Fin 4 → L) (hv : v = Fin.cases (φ Polynomial.X) (polynomialGraphSurfacePoint φ P z₀ z₁))
    (hF : MvPolynomial.eval₂Hom (φ.comp Polynomial.C) v F = 0)
    (hS : MvPolynomial.eval₂Hom (φ.comp Polynomial.C) v (implicitRegularity F) ≠ 0)
    (p w : ℕ) [CharP L p] (hchar : w < p) (hP : P.natDegree ≤ w) :
    pointTaylorPolynomial F (φ.comp Polynomial.C) v hF hS w =
      Polynomial.taylor (φ Polynomial.X) (P.map (φ.comp Polynomial.C)) := by
  have heval (Q : Carrier K) : MvPolynomial.eval₂Hom (φ.comp Polynomial.C) v Q =
      φ (graphSpecialize P z₀ z₁ Q) := by
    rw [hv, ← eval_surfaceMap, eval_polynomialGraphSurfacePoint]
  ext j
  by_cases hj : j ≤ w
  · cases j with
    | zero =>
      rw [pointTaylorPolynomial_coeff_zero, Polynomial.taylor_coeff_zero, polynomial_eval_generic, hv]
      rfl
    | succ j =>
      have hfact : ((j + 1).factorial : L) ≠ 0 :=
        factorial_cast_ne_zero_below_characteristic p _ (hj.trans_lt hchar)
      have hsep : φ (graphSpecialize P z₀ z₁ (implicitRegularity F)) ≠ 0 := by
        rwa [heval] at hS
      rw [pointTaylorPolynomial_coeff_succ F (φ.comp Polynomial.C) v hF hS w j hj,
        taylor_coeff_eq_derivative_div_factorial _ _ _ hfact, Polynomial.iterate_derivative_map,
        polynomial_eval_generic, heval, graphSpecialize_tailNumerator F P z₀ z₁ hsol,
        map_mul, map_pow, heval, mul_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hsep)]
  · have hleft := (pointTaylorPolynomial_natDegree_le F (φ.comp Polynomial.C) v hF hS w).trans_lt
      (Nat.lt_of_not_ge hj)
    have hright : (Polynomial.taylor (φ Polynomial.X) (P.map (φ.comp Polynomial.C))).natDegree < j := by
      rw [Polynomial.natDegree_taylor]
      exact (Polynomial.natDegree_map_le.trans hP).trans_lt (Nat.lt_of_not_ge hj)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hleft,
      Polynomial.coeff_eq_zero_of_natDegree_lt hright]

theorem persistentAgreementNumerator_selected_zero_iff
    (φ : Polynomial K →+* L) (F : Carrier K) (P : Polynomial K) (z₀ z₁ : K)
    (hsol : graphSpecialize P z₀ z₁ F = 0)
    (hreg : MvPolynomial.eval (polynomialGraphSurfacePoint φ P z₀ z₁)
      (surfaceMap φ (implicitRegularity F)) ≠ 0)
    (p w : ℕ) [CharP L p] (hchar : w < p) (hP : P.natDegree ≤ w) (x u₀ u₁ : K) :
    MvPolynomial.eval (polynomialGraphSurfacePoint φ P z₀ z₁)
        (surfaceMap φ (persistentAgreementNumerator F w x u₀ u₁)) = 0 ↔
      P.eval x = u₀ + u₁ * z₀ := by
  let coeff := φ.comp Polynomial.C
  let v : Fin 4 → L := Fin.cases (φ Polynomial.X) (polynomialGraphSurfacePoint φ P z₀ z₁)
  have hF : MvPolynomial.eval₂Hom coeff v F = 0 := by
    rw [← eval_surfaceMap, eval_polynomialGraphSurfacePoint, hsol, map_zero]
  have hS : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0 := by
    rwa [eval_surfaceMap] at hreg
  have h := persistentAgreementNumerator_eval_div F w x u₀ u₁ coeff v hF hS
  have ht := pointTaylorPolynomial_eq_taylor_at_genericX φ F P z₀ z₁ hsol v rfl hF hS p w hchar hP
  have hv₀ : v 0 = φ Polynomial.X := rfl
  have hv₂ : v 2 = coeff z₀ := rfl
  have hTaylor : (Polynomial.taylor (φ Polynomial.X) (P.map coeff)).eval
      (coeff x - φ Polynomial.X) = coeff (P.eval x) := by
    rw [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, sub_add_cancel, Polynomial.eval_map_apply]
  rw [ht, hv₀, hv₂, hTaylor, ← map_mul, ← map_sub, ← map_sub, ← eval_surfaceMap] at h
  constructor
  · intro hz
    have hdiff : coeff (P.eval x - u₀ - u₁ * z₀) = 0 := by rw [← h, hz, zero_div]
    have hdiff' : P.eval x - u₀ - u₁ * z₀ = 0 := coeff.injective (hdiff.trans coeff.map_zero.symm)
    linear_combination hdiff'
  · intro hz
    have hdiff : P.eval x - u₀ - u₁ * z₀ = 0 := by linear_combination hz
    have hzero : MvPolynomial.eval (polynomialGraphSurfacePoint φ P z₀ z₁)
        (surfaceMap φ (persistentAgreementNumerator F w x u₀ u₁)) /
        (MvPolynomial.eval₂Hom coeff v (implicitRegularity F)) ^ (2 * w) = 0 := by
      rw [h, hdiff, map_zero]
    exact (div_eq_zero_iff.mp hzero).resolve_right (pow_ne_zero (2 * w) hS)

theorem curve_persistent_uncentered_witness
    (F : Carrier K) (w bound p : ℕ) [CharP (GenericField K) p]
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (hF : surfaceMap (polynomialEmbedding K) F ∈ C)
    (hS : surfaceMap (polynomialEmbedding K) (implicitRegularity F) ∉ C)
    (htail : ∀ delay, surfaceMap (polynomialEmbedding K) (tailNumerator F (w + delay)) ∈ C)
    (hbound : 2 ≤ bound) (hw : w + 1 ≤ bound) (hchar : bound < p)
    (hweight : wt (![1, w, 0, 0] : Fin 4 → ℕ) F < bound) :
    ∃ P : Polynomial (CoordinateField (GenericField K) C), P.natDegree ≤ w ∧
      MvPolynomial.eval₂Hom (Polynomial.C.comp (componentCoefficients (polynomialEmbedding K) C))
        ![Polynomial.X, P, Polynomial.C (coordinate (GenericField K) C 1),
          Polynomial.C (coordinate (GenericField K) C 2)] F = 0 ∧
      ∀ x u₀ u₁ : K,
        coordinateEvaluation (GenericField K) C
            (surfaceMap (polynomialEmbedding K) (persistentAgreementNumerator F w x u₀ u₁)) /
          (coordinateEvaluation (GenericField K) C
            (surfaceMap (polynomialEmbedding K) (implicitRegularity F))) ^ (2 * w) =
          P.eval (componentCoefficients (polynomialEmbedding K) C x) -
            componentCoefficients (polynomialEmbedding K) C u₀ -
            componentCoefficients (polynomialEmbedding K) C u₁ * coordinate (GenericField K) C 1 := by
  let Ω := GenericField K
  let E := CoordinateField Ω C
  letI : CharP E p := charP_of_injective_algebraMap (algebraMap Ω E).injective p
  let φ := polynomialEmbedding K
  let coeff := componentCoefficients φ C
  let v := componentPoint φ C
  have hF' : MvPolynomial.eval₂Hom coeff v F = 0 := (component_evaluation_zero_iff φ C F).2 hF
  have hS' : MvPolynomial.eval₂Hom coeff v (implicitRegularity F) ≠ 0 :=
    fun hz => hS ((component_evaluation_zero_iff φ C _).1 hz)
  let P₀ := pointTaylorPolynomial F coeff v hF' hS' w
  let P := Polynomial.taylor (-(v 0)) P₀
  have hP₀ : MvPolynomial.eval₂Hom (Polynomial.C.comp coeff) (centeredGraph v P₀) F = 0 := by
    apply pointTaylorPolynomial_relation_of_persistent F coeff v w bound p hF' hS'
      _ hbound hw hchar hweight
    intro j hj
    obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact (component_evaluation_zero_iff φ C _).2 (htail delay)
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_taylor]
    exact pointTaylorPolynomial_natDegree_le F coeff v hF' hS' w
  · let shift := Polynomial.compRingHom (Polynomial.X + Polynomial.C (-(v 0)))
    have hshift (i : Fin 4) : shift (centeredGraph v P₀ i) =
        (![Polynomial.X, P, Polynomial.C (v 2), Polynomial.C (v 3)] : Fin 4 → Polynomial E) i := by
      fin_cases i
      · change (Polynomial.C (v 0) + Polynomial.X).comp (Polynomial.X + Polynomial.C (-(v 0))) =
          Polynomial.X
        rw [Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp, Polynomial.C_neg]
        abel
      · rfl
      · exact Polynomial.C_comp
      · exact Polynomial.C_comp
    have hhom : shift.comp (MvPolynomial.eval₂Hom (Polynomial.C.comp coeff) (centeredGraph v P₀)) =
        MvPolynomial.eval₂Hom (Polynomial.C.comp coeff)
          ![Polynomial.X, P, Polynomial.C (v 2), Polynomial.C (v 3)] := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [shift, Polynomial.coe_compRingHom_apply]
      · intro i
        simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X'] using hshift i
    have hz := congrArg shift hP₀
    rw [map_zero] at hz
    exact (DFunLike.congr_fun hhom F).symm.trans hz
  · intro x u₀ u₁
    have he := persistentAgreementNumerator_eval_div F w x u₀ u₁ coeff v hF' hS'
    have hsh : P.eval (coeff x) = P₀.eval (coeff x - v 0) := by
      simp [P, Polynomial.taylor_apply, Polynomial.eval_comp, sub_eq_add_neg]
    rw [← hsh, component_evaluation φ C, component_evaluation φ C] at he
    exact he

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
