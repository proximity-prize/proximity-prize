import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.SmallInseparableProjection
import ProximityPrize.SubmissionLower.LocalMathlib_FieldTheory_RatFunc_Valuation

/-!
# Valuations in purely inseparable extensions

A valuation has at most one extension, up to valuation equivalence,
through a purely inseparable field extension.  The proof is elementary:
some positive characteristic power of every upstairs element lies in
the base, and taking a positive power reflects comparison with one.
-/

namespace ProximityPrize.SubmissionLower.PurelyInseparableValuation

noncomputable section

variable {F E Γ₁ Γ₂ : Type*}
variable [Field F] [Field E] [Algebra F E]
variable [LinearOrderedCommGroupWithZero Γ₁]
variable [LinearOrderedCommGroupWithZero Γ₂]

namespace RatFunc

open Polynomial Valuation

lemma value_eq_X_zpow_intDegree_of_one_lt_X
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    {v : Valuation (RatFunc K) Γ} [v.IsTrivialOn K]
    {f : RatFunc K} (hX : 1 < v RatFunc.X) (hf : f ≠ 0) :
    v f = v RatFunc.X ^ f.intDegree := by
  induction f using RatFunc.induction_on with
  | f a b hb =>
      rw [RatFunc.intDegree_div (by grind only) (by grind only),
        v.map_div, zpow_sub₀ (ne_zero_of_lt hX)]
      simp_rw [RatFunc.intDegree_polynomial, zpow_natCast,
        ← RatFunc.coePolynomial_eq_algebraMap]
      have ha : a ≠ 0 := by contrapose hf; simp [hf]
      rw [RatFunc.coePolynomial_eq_algebraMap,
        RatFunc.coePolynomial_eq_algebraMap,
        ← RatFunc.aeval_X_left_eq_algebraMap,
        ← RatFunc.aeval_X_left_eq_algebraMap]
      rw [valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          _ hX ha,
        valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          _ hX hb]

lemma isEquiv_of_one_lt_X
    {K Γ Δ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ]
    [LinearOrderedCommGroupWithZero Δ]
    (v : Valuation (RatFunc K) Γ) (w : Valuation (RatFunc K) Δ)
    [v.IsTrivialOn K] [w.IsTrivialOn K]
    (hv : 1 < v RatFunc.X) (hw : 1 < w RatFunc.X) : v.IsEquiv w := by
  refine Valuation.isEquiv_iff_val_lt_one.mpr fun {f} ↦ ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [value_eq_X_zpow_intDegree_of_one_lt_X hv hf,
      value_eq_X_zpow_intDegree_of_one_lt_X hw hf]
    grind [one_le_zpow_iff_right₀]

end RatFunc

/-- Two valuations upstairs are equivalent as soon as their restrictions
are equivalent downstairs through a purely inseparable extension. -/
theorem isEquiv_of_isPurelyInseparable
    (p : ℕ) [ExpChar F p] (hp : p.Prime)
    [IsPurelyInseparable F E]
    (v₁ : Valuation E Γ₁) (v₂ : Valuation E Γ₂)
    (hbase : (v₁.comap (algebraMap F E)).IsEquiv
      (v₂.comap (algebraMap F E))) :
    v₁.IsEquiv v₂ := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F p x
  have hpow : p ^ n ≠ 0 := (pow_pos hp.pos n).ne'
  have h₁pow : v₁ x ^ p ^ n = v₁ (algebraMap F E a) := by
    rw [← v₁.map_pow, ha]
  have h₂pow : v₂ x ^ p ^ n = v₂ (algebraMap F E a) := by
    rw [← v₂.map_pow, ha]
  calc
    v₁ x ≤ 1 ↔ v₁ x ^ p ^ n ≤ 1 ^ p ^ n := by
      rw [pow_le_pow_iff_left₀
        (show (0 : Γ₁) ≤ v₁ x from zero_le)
        (show (0 : Γ₁) ≤ 1 from zero_le) hpow]
    _ ↔ v₁ (algebraMap F E a) ≤ 1 := by rw [h₁pow, one_pow]
    _ ↔ v₂ (algebraMap F E a) ≤ 1 := by
      exact hbase.le_one_iff_le_one
    _ ↔ v₂ x ^ p ^ n ≤ 1 ^ p ^ n := by rw [h₂pow, one_pow]
    _ ↔ v₂ x ≤ 1 := by
      rw [pow_le_pow_iff_left₀
        (show (0 : Γ₂) ≤ v₂ x from zero_le)
        (show (0 : Γ₂) ≤ 1 from zero_le) hpow]

end

end ProximityPrize.SubmissionLower.PurelyInseparableValuation

#print axioms ProximityPrize.SubmissionLower.PurelyInseparableValuation.isEquiv_of_isPurelyInseparable
