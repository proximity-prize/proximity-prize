import ProximityPrize.SubmissionLower.BCHKSPrimitiveLocalizedSelection

namespace ProximityPrize.SubmissionLower

open Polynomial

/-- Coefficientwise localization, regarded as an `F`-linear map. -/
noncomputable def polynomialRatFuncLinearMap (F : Type*) [Field F] :
    (Polynomial (Polynomial F)) →ₗ[F] Polynomial (RatFunc F) :=
  (Polynomial.mapAlgHom (IsScalarTower.toAlgHom F (Polynomial F) (RatFunc F))).toLinearMap

@[simp]
theorem polynomialRatFuncLinearMap_apply
    (F : Type*) [Field F] (p : Polynomial (Polynomial F)) :
    polynomialRatFuncLinearMap F p = p.map (algebraMap (Polynomial F) (RatFunc F)) := by
  rfl

/-- A linear combination of localized vectors can be lifted to a linear
combination of the original vectors.  This is the same-scalar form of
`Submodule.map_span`. -/
theorem exists_span_lift
    {F M N J : Type*} [Semiring F] [AddCommMonoid M] [Module F M]
    [AddCommMonoid N] [Module F N]
    (L : M →ₗ[F] N) (c₀ : J → M) (c : J → N)
    (hc : c = L ∘ c₀) {h : N}
    (hh : h ∈ Submodule.span F (Set.range c)) :
    ∃ h₀ ∈ Submodule.span F (Set.range c₀), L h₀ = h := by
  have hmap : Submodule.map L (Submodule.span F (Set.range c₀)) =
      Submodule.span F (Set.range c) := by
    rw [Submodule.map_span, ← Set.range_comp, ← hc]
  rw [← hmap] at hh
  rcases hh with ⟨h₀, hh₀, rfl⟩
  exact ⟨h₀, hh₀, rfl⟩

end ProximityPrize.SubmissionLower
