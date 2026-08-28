import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Unramified_Field

/-!
# The rigid inseparable case below twice the characteristic

For a finite extension in prime characteristic `p`, a nontrivial
inseparable degree is a positive power of `p`.  Consequently an
inseparable extension of degree strictly below `2 * p` has degree
exactly `p` and is purely inseparable.  This is the arithmetic
dichotomy needed by the characteristic-free base-`R` projection.
-/

namespace ProximityPrize.SubmissionLower.SmallInseparableProjection

noncomputable section

open Field
open Polynomial
open scoped IntermediateField

universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

lemma isSeparable_iff_finInsepDegree_eq_one :
    Algebra.IsSeparable F E ↔ finInsepDegree F E = 1 := by
  rw [← separableClosure.eq_top_iff,
    ← IntermediateField.finrank_eq_one_iff_eq_top, finInsepDegree]

/-- The degree of a finite purely inseparable extension is a power of
the exponential characteristic.  This is the small fragment of the
general purely-inseparable degree theory needed below. -/
lemma finrank_eq_pow_of_purelyInseparable
    (E : Type u) [Field E] [Algebra F E]
    (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E]
    [FiniteDimensional F E] : ∃ n, Module.finrank F E = q ^ n := by
  suffices ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
      (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E]
      [FiniteDimensional F E], ∃ n, Module.finrank F E = q ^ n by
    simpa using this (⊥ : IntermediateField F E) E q
  intro F E _ _ _ q _ _ _
  generalize hd : Module.finrank F E = d
  induction d using Nat.strongRecOn generalizing F with
  | ind d IH =>
      by_cases h : (⊥ : IntermediateField F E) = ⊤
      · rw [← IntermediateField.finrank_top', ← h,
          IntermediateField.finrank_bot] at hd
        exact ⟨0, ((pow_zero q).trans hd).symm⟩
      obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_of_le_of_ne bot_le h)
      obtain ⟨m, y, e⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x
      have hsimple : Module.finrank F F⟮x⟯ = q ^ m := by
        rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x),
          e, natDegree_sub_C, natDegree_X_pow]
      obtain ⟨n, hn⟩ := IH _ (by
        rw [← hd, ← Module.finrank_mul_finrank F F⟮x⟯,
          Nat.lt_mul_iff_one_lt_left Module.finrank_pos, hsimple]
        by_contra! H
        refine hx (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp
          (le_antisymm (hsimple ▸ H) ?_))
        exact Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne')
          F⟮x⟯ rfl
      exact ⟨m + n, by
        rw [← hd, ← Module.finrank_mul_finrank F F⟮x⟯,
          hn, pow_add, hsimple]⟩

lemma finInsepDegree_eq_pow
    (q : ℕ) [ExpChar F q] [FiniteDimensional F E] :
    ∃ n, finInsepDegree F E = q ^ n := by
  exact finrank_eq_pow_of_purelyInseparable
    (F := separableClosure F E) E q

/-- Below twice the prime characteristic, failure of separability has
only one possible shape: a purely inseparable extension of degree `p`. -/
theorem finrank_eq_prime_and_purelyInseparable_of_not_separable
    (p : ℕ) [ExpChar F p] [FiniteDimensional F E]
    (hp : p.Prime) (hsep : ¬ Algebra.IsSeparable F E)
    (hsmall : Module.finrank F E < 2 * p) :
    Module.finrank F E = p ∧ IsPurelyInseparable F E := by
  have hinsep_ne_one : finInsepDegree F E ≠ 1 := by
    exact (isSeparable_iff_finInsepDegree_eq_one.not.mp hsep)
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow (F := F) (E := E) p
  have hn_ne_zero : n ≠ 0 := by
    intro hnzero
    apply hinsep_ne_one
    simpa [hnzero] using hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne_zero
  have hp_dvd_insep : p ∣ finInsepDegree F E := by
    rw [hn, pow_succ]
    exact dvd_mul_left p (p ^ k)
  have hproduct := Field.finSepDegree_mul_finInsepDegree F E
  have hinsep_dvd_finrank : finInsepDegree F E ∣ Module.finrank F E := by
    refine ⟨finSepDegree F E, ?_⟩
    simpa [Nat.mul_comm] using hproduct.symm
  have hp_dvd_finrank : p ∣ Module.finrank F E := hp_dvd_insep.trans hinsep_dvd_finrank
  obtain ⟨q, hq⟩ := hp_dvd_finrank
  have hqpos : 0 < q := by
    by_contra hqzero
    have : q = 0 := Nat.eq_zero_of_not_pos hqzero
    rw [this, mul_zero] at hq
    exact Module.finrank_pos.ne' hq
  have hqlt : q < 2 := by
    by_contra hnot
    have htwo : 2 ≤ q := Nat.le_of_not_gt hnot
    have hmul : 2 * p ≤ q * p := Nat.mul_le_mul_right p htwo
    have hmul' : 2 * p ≤ p * q := by simpa [Nat.mul_comm] using hmul
    rw [← hq] at hmul'
    exact (Nat.not_lt_of_ge hmul') hsmall
  have hqone : q = 1 := by omega
  have hfinrank : Module.finrank F E = p := by
    simp [hq, hqone]
  have hinsep_le : finInsepDegree F E ≤ Module.finrank F E :=
    Nat.le_of_dvd Module.finrank_pos hinsep_dvd_finrank
  have hp_le_insep : p ≤ finInsepDegree F E := by
    rw [hn, pow_succ]
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left p (pow_pos hp.pos k)
  have hinsep_eq : finInsepDegree F E = p := by omega
  have hsepDegree : finSepDegree F E = 1 := by
    rw [hinsep_eq, hfinrank] at hproduct
    exact Nat.mul_right_cancel hp.pos (by simpa using hproduct)
  exact ⟨hfinrank, isPurelyInseparable_of_finSepDegree_eq_one hsepDegree⟩

end

end ProximityPrize.SubmissionLower.SmallInseparableProjection

#print axioms ProximityPrize.SubmissionLower.SmallInseparableProjection.finrank_eq_prime_and_purelyInseparable_of_not_separable
