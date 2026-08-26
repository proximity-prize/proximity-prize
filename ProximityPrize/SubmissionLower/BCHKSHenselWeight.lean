import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.FiniteHenselWeight
open Polynomial
universe u v
noncomputable section
def denominatorExponent (t : ℕ) : ℕ :=
  max 0 (2 * t - 1)
@[simp] lemma denominatorExponent_zero : denominatorExponent 0 = 0 := by
  simp [denominatorExponent]
@[simp] lemma denominatorExponent_one : denominatorExponent 1 = 1 := by
  simp [denominatorExponent]
lemma denominatorExponent_succ (t : ℕ) :
    denominatorExponent (t + 1) = 2 * t + 1 := by
  simp [denominatorExponent]
  omega
variable {L : Type u} [Field L]
variable {O : Type v} [CommRing O]
def coefficientDenominator (ι : O →+* L) (W xi : O) (t : ℕ) : L :=
  ι W ^ (t + 1) * ι xi ^ denominatorExponent t
lemma coefficientDenominator_ne_zero (ι : O →+* L) (W xi : O)
    (hW : ι W ≠ 0) (hxi : ι xi ≠ 0) (t : ℕ) :
    coefficientDenominator ι W xi t ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hxi)
noncomputable def betaSequence (β₀ : O) (B : ℕ → O → O) : ℕ → O
  | 0 => β₀
  | t + 1 => B t (betaSequence β₀ B t)
omit [CommRing O] in
@[simp] lemma betaSequence_zero (β₀ : O) (B : ℕ → O → O) :
    betaSequence β₀ B 0 = β₀ := rfl
omit [CommRing O] in
@[simp] lemma betaSequence_succ (β₀ : O) (B : ℕ → O → O) (t : ℕ) :
    betaSequence β₀ B (t + 1) = B t (betaSequence β₀ B t) := rfl
structure NumeratorRecurrence (ι : O →+* L) (W xi : O)
    (α : ℕ → L) (β₀ : O) (B : ℕ → O → O) : Prop where
  base : α 0 = ι β₀ / coefficientDenominator ι W xi 0
  step : ∀ t b,
    α t = ι b / coefficientDenominator ι W xi t →
    α (t + 1) = ι (B t b) / coefficientDenominator ι W xi (t + 1)
theorem betaSequence_representation
    (ι : O →+* L) (W xi : O) (α : ℕ → L) (β₀ : O) (B : ℕ → O → O)
    (hrec : NumeratorRecurrence ι W xi α β₀ B) :
    ∀ t, α t = ι (betaSequence β₀ B t) /
      (ι W ^ (t + 1) * ι xi ^ max 0 (2 * t - 1)) := by
  intro t
  induction t with
  | zero => simpa [coefficientDenominator, denominatorExponent] using hrec.base
  | succ t ih =>
      simpa [coefficientDenominator, denominatorExponent] using
        hrec.step t (betaSequence β₀ B t) ih
structure WeightRecurrence (Λ : O → ℕ) (D : ℕ)
    (β₀ : O) (B : ℕ → O → O) : Prop where
  base : Λ β₀ ≤ D
  step : ∀ t b, Λ (B t b) ≤ Λ b + 2 * D
omit [CommRing O] in
theorem betaSequence_weight_bound
    (Λ : O → ℕ) (D : ℕ) (β₀ : O) (B : ℕ → O → O)
    (hw : WeightRecurrence Λ D β₀ B) :
    ∀ t, Λ (betaSequence β₀ B t) ≤ (2 * t + 1) * D := by
  intro t
  induction t with
  | zero => simpa using hw.base
  | succ t ih =>
      rw [betaSequence_succ]
      calc
        Λ (B t (betaSequence β₀ B t))
            ≤ Λ (betaSequence β₀ B t) + 2 * D := hw.step t _
        _ ≤ (2 * t + 1) * D + 2 * D := Nat.add_le_add_right ih _
        _ = (2 * (t + 1) + 1) * D := by ring
theorem betaSequence_shape_and_weight
    (ι : O →+* L) (W xi : O) (α : ℕ → L) (β₀ : O) (B : ℕ → O → O)
    (Λ : O → ℕ) (D : ℕ)
    (hrec : NumeratorRecurrence ι W xi α β₀ B)
    (hw : WeightRecurrence Λ D β₀ B) :
    ∀ t,
      α t = ι (betaSequence β₀ B t) /
          (ι W ^ (t + 1) * ι xi ^ max 0 (2 * t - 1)) ∧
      Λ (betaSequence β₀ B t) ≤ (2 * t + 1) * D := by
  intro t
  exact ⟨betaSequence_representation ι W xi α β₀ B hrec t,
    betaSequence_weight_bound Λ D β₀ B hw t⟩
noncomputable def betaSequenceFull (β₀ : O) (B : ℕ → (ℕ → O) → O) : ℕ → O
  | 0 => β₀
  | t + 1 => B t (fun i => if i ≤ t then betaSequenceFull β₀ B i else 0)
termination_by t => t
decreasing_by omega
structure FullNumeratorRecurrence (ι : O →+* L) (W xi : O)
    (α : ℕ → L) (β₀ : O) (B : ℕ → (ℕ → O) → O) : Prop where
  base : α 0 = ι β₀ / coefficientDenominator ι W xi 0
  step : ∀ t prior,
    (∀ i, i ≤ t → α i = ι (prior i) / coefficientDenominator ι W xi i) →
    α (t + 1) = ι (B t prior) / coefficientDenominator ι W xi (t + 1)
theorem betaSequenceFull_representation
    (ι : O →+* L) (W xi : O) (α : ℕ → L) (β₀ : O)
    (B : ℕ → (ℕ → O) → O)
    (hrec : FullNumeratorRecurrence ι W xi α β₀ B) :
    ∀ t, α t = ι (betaSequenceFull β₀ B t) /
      (ι W ^ (t + 1) * ι xi ^ max 0 (2 * t - 1)) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      cases t with
      | zero =>
          simpa [coefficientDenominator, denominatorExponent, betaSequenceFull] using hrec.base
      | succ t =>
          let prior : ℕ → O := fun i => if i ≤ t then betaSequenceFull β₀ B i else 0
          have hpref : ∀ i, i ≤ t →
              α i = ι (prior i) / coefficientDenominator ι W xi i := by
            intro i hi
            simp only [prior, if_pos hi]
            simpa [coefficientDenominator, denominatorExponent] using ih i (by omega)
          have hs := hrec.step t prior hpref
          simpa [prior, betaSequenceFull, coefficientDenominator, denominatorExponent] using hs
structure FullWeightRecurrence (Λ : O → ℕ) (D : ℕ)
    (β₀ : O) (B : ℕ → (ℕ → O) → O) : Prop where
  base : Λ β₀ ≤ D
  step : ∀ t prior,
    (∀ i, i ≤ t → Λ (prior i) ≤ (2 * i + 1) * D) →
    Λ (B t prior) ≤ (2 * (t + 1) + 1) * D
theorem betaSequenceFull_weight_bound
    (Λ : O → ℕ) (D : ℕ) (β₀ : O) (B : ℕ → (ℕ → O) → O)
    (hw : FullWeightRecurrence Λ D β₀ B) :
    ∀ t, Λ (betaSequenceFull β₀ B t) ≤ (2 * t + 1) * D := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      cases t with
      | zero => simpa [betaSequenceFull] using hw.base
      | succ t =>
          let prior : ℕ → O := fun i => if i ≤ t then betaSequenceFull β₀ B i else 0
          have hpref : ∀ i, i ≤ t → Λ (prior i) ≤ (2 * i + 1) * D := by
            intro i hi
            simp only [prior, if_pos hi]
            exact ih i (by omega)
          simpa [prior, betaSequenceFull] using hw.step t prior hpref
variable {F : Type u} [Field F]
abbrev RatFuncAdjoinRoot (q : Polynomial (RatFunc F)) := AdjoinRoot q
theorem adjoinRoot_betaSequence_representation
    (q : Polynomial (RatFunc F)) [Fact (Irreducible q)]
    {O : Type v} [CommRing O]
    (ι : O →+* RatFuncAdjoinRoot q) (W xi : O)
    (α : ℕ → RatFuncAdjoinRoot q) (β₀ : O) (B : ℕ → O → O)
    (hrec : NumeratorRecurrence ι W xi α β₀ B) :
    ∀ t, α t = ι (betaSequence β₀ B t) /
      (ι W ^ (t + 1) * ι xi ^ max 0 (2 * t - 1)) :=
  betaSequence_representation ι W xi α β₀ B hrec
end
end ProximityPrize.SubmissionLower.FiniteHenselWeight
