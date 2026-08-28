import ProximityPrize.Benchmark.TargetLower

/-!
A finite numerator/denominator core for Hensel coefficients.  This file uses
only finite sequences.  In applications `L` is an `AdjoinRoot` over a rational
function field and `O` is the chosen ring of regular numerators.
-/

namespace ProximityPrize.SubmissionLower.FiniteHenselWeight

open Polynomial

universe u v

noncomputable section

/-- The exponent `max(0,2t-1)` occurring in Claim A.2.  Natural subtraction
already performs the truncation at zero. -/
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

/-- The Claim A.2 denominator `W^(t+1) * xi^max(0,2t-1)`. -/
def coefficientDenominator (ι : O →+* L) (W xi : O) (t : ℕ) : L :=
  ι W ^ (t + 1) * ι xi ^ denominatorExponent t

lemma coefficientDenominator_ne_zero (ι : O →+* L) (W xi : O)
    (hW : ι W ≠ 0) (hxi : ι xi ≠ 0) (t : ℕ) :
    coefficientDenominator ι W xi t ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hxi)

/-- `B t b` is the cleared numerator expression at the next Hensel step.
It is left as an algebraic parameter: concrete applications instantiate it
with the finite residual expansion (`B_{i,lambda}` terms). -/
noncomputable def betaSequence (β₀ : O) (B : ℕ → O → O) : ℕ → O
  | 0 => β₀
  | t + 1 => B t (betaSequence β₀ B t)

omit [CommRing O] in
@[simp] lemma betaSequence_zero (β₀ : O) (B : ℕ → O → O) :
    betaSequence β₀ B 0 = β₀ := rfl

omit [CommRing O] in
@[simp] lemma betaSequence_succ (β₀ : O) (B : ℕ → O → O) (t : ℕ) :
    betaSequence β₀ B (t + 1) = B t (betaSequence β₀ B t) := rfl

/-- The finite algebraic recurrence required from the cleared residual.  Its
successor clause says that if `b` represents coefficient `t`, the actual
cleared Hensel expression `B t b` represents coefficient `t+1`.

Taking `alpha` to be `FiniteHensel.liftCoeff ... N` connects this interface to
the finite existence construction. -/
structure NumeratorRecurrence (ι : O →+* L) (W xi : O)
    (α : ℕ → L) (β₀ : O) (B : ℕ → O → O) : Prop where
  base : α 0 = ι β₀ / coefficientDenominator ι W xi 0
  step : ∀ t b,
    α t = ι b / coefficientDenominator ι W xi t →
    α (t + 1) = ι (B t b) / coefficientDenominator ι W xi (t + 1)

/-- Actual numerator induction: every recursively constructed `beta_t`
represents the corresponding finite Hensel coefficient with exactly the
Claim A.2 denominator. -/
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

/-- Coarse degree/weight assumptions for the cleared numerator recursion.
The concrete `Lambda` may be polynomial degree, weighted degree, or the
regular-representative weight used for an adjoin-root numerator ring. -/
structure WeightRecurrence (Λ : O → ℕ) (D : ℕ)
    (β₀ : O) (B : ℕ → O → O) : Prop where
  base : Λ β₀ ≤ D
  step : ∀ t b, Λ (B t b) ≤ Λ b + 2 * D

omit [CommRing O] in
/-- Coarse Claim A.2-style weight bound.  Each actual numerator recursion step
costs at most `2D`, hence `Lambda(beta_t) ≤ (2t+1)D`. -/
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

/-- Combined finite numerator shape and weight conclusion. -/
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


/-! A prior-dependent version, suitable when `B_{i,lambda}` uses all earlier
numerators rather than only the immediately preceding one. -/

/-- Actual recursive numerator sequence whose cleared expression may inspect
the complete already-constructed prior. -/
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

/-- Prefix-dependent actual numerator induction. -/
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

/-- Prefix-dependent coarse weight induction. -/
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

/-! ### Specialization to an adjoin root over a rational-function field -/

variable {F : Type u} [Field F]

/-- The ambient field shape used by the Hensel-numerator application. -/
abbrev RatFuncAdjoinRoot (q : Polynomial (RatFunc F)) := AdjoinRoot q

/-- Named specialization of the representation theorem to
`L = AdjoinRoot q` over `RatFunc F`. -/
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
