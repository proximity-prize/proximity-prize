import ProximityPrize.SubmissionLower.BCHKSLinearYInterpolation6401
import ProximityPrize.SubmissionLower.BCHKSJ0ConcreteGlobalInput6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSJ0LinearYInterpolation6401
open ProximityPrize.Benchmark
open Polynomial
open BCHKSSubstitutionVanish
open BCHKSJ0ConcreteGlobalInput6400
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
abbrev Field := IRSProfile.Field
abbrev Index := IRSProfile.Index
abbrev TriPoly := Polynomial (Polynomial (Polynomial Field))
theorem J0BenchmarkInterpolant.exists_linearY_interpolant_residual6401
    {received : Fin 2 → Index → Field}
    {S : Finset Field} {A : Field → Finset Index}
    (J : J0BenchmarkInterpolant received S A)
    (hA : ∀ z ∈ S, 185354 ≤ (A z).card) :
    ∃ Q : TriPoly,
      Q ≠ 0 ∧
      (∀ j x, (Q.coeff j).coeff x ≠ 0 →
        j < 2 ∧ x + 131071 * j < 196608 ∧
          ((Q.coeff j).coeff x).natDegree + j < 65538) ∧
      (∀ z ∈ S, ∃ E : Field[X],
        BCHKSSubstitutionVanish.triEval Q z (J.P z) =
          (∏ i ∈ A z,
            (Polynomial.X - Polynomial.C (IRSProfile.domain i))) * E ∧
        E.natDegree ≤ 11253) := by
  classical
  let omega : Fin BCHKSConcreteGSLinearY6401.n ↪ Field := IRSProfile.domain
  let u₀ : Fin BCHKSConcreteGSLinearY6401.n → Field := fun i ↦ received 0 i
  let u₁ : Fin BCHKSConcreteGSLinearY6401.n → Field := fun i ↦ received 1 i
  let Arow : ↥S → Finset (Fin BCHKSConcreteGSLinearY6401.n) := fun z ↦ A z
  have hrow : ∀ z : ↥S, 185354 ≤ (Arow z).card := by
    intro z
    exact hA z z.property
  have hmatch : ∀ z : ↥S, ∀ i ∈ Arow z,
      (J.P z).eval (omega i) = u₀ i + (z : Field) * u₁ i := by
    intro z i hi
    exact J.agrees z z.property i hi
  obtain ⟨Q, hQ, hcaps, hresidual⟩ :=
    BCHKSLinearYInterpolation6401.exists_linearY_interpolant_residual6401
      omega u₀ u₁ S (fun z ↦ J.P z) Arow
      (fun z ↦ J.root_degree z z.property) hrow hmatch
  refine ⟨Q, hQ, hcaps, ?_⟩
  intro z hz
  dsimp [omega, Arow] at hresidual
  exact hresidual ⟨z, hz⟩
end BCHKSJ0LinearYInterpolation6401
end ProximityPrize.SubmissionLower
