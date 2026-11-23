import ProximityPrize.SubmissionLower.R6960CollisionTameDiscriminantLocalization
import ProximityPrize.SubmissionLower.R6960CollisionTameLineDegree

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1250000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Polynomial LineEuler Module Matrix
open scoped Polynomial Matrix

variable {k A F E : Type*} [Field k] [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [IsNoetherianRing A] [Field F] [Field E] [Algebra (Laurent k) E]

local instance finiteLineAlgebra : Algebra k[X] E :=
  ((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom).toAlgebra

variable [Algebra A k[X]] [Algebra A F] [Algebra A E] [Algebra k[X] F] [Algebra F E]
  [IsScalarTower A k[X] F] [IsScalarTower A k[X] E] [IsScalarTower A F E] [IsScalarTower k[X] F E]
  [IsFractionRing A F] [IsFractionRing k[X] F] [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- The degree of the actual affine discriminant after base localization
is bounded by the actual transition determinant of the resulting generic
line. The trace determinant degree is derived from the ideal equality. -/
theorem localized_line_discriminant_degree (S : Submonoid A) [IsLocalization S k[X]]
    (δ : A) (nz : δ≠0) (principal : normalizationDiscriminant (A:=A) (E:=E) F=Ideal.span {δ})
    (bf : Basis (Fin (finrank F E)) k[X] (chartOrder (k:=k) (E:=E) false))
    (bi : Basis (Fin (finrank F E)) k[X] (chartOrder (k:=k) (E:=E) true)) :
    ∃ d : ℤ,(normalizedTransition bf bi).det.degree=(d:WithBot ℤ) ∧
      ((algebraMap A k[X] δ).natDegree:ℤ)≤-2*d := by
  let j := algebraMap A k[X]
  let b : Basis (Fin (finrank F E)) k[X] (integralClosure k[X] E) := bf
  let G := (Algebra.traceMatrix k[X] bf).det
  have h : (Ideal.span {j δ} : Ideal k[X])=Ideal.span {G} := by
    have localEq := normalizationDiscriminant_map (R:=k[X]) (A:=A) (F:=F) (E:=E) S
    rw [principal,Ideal.map_span,Set.image_singleton,normalizationDiscriminant_basis F b] at localEq
    exact localEq
  have associated : Associated (j δ) G := Ideal.span_singleton_eq_span_singleton.mp h
  have inj : Function.Injective j := by
    intro x y eq
    apply IsFractionRing.injective A F
    rw [IsScalarTower.algebraMap_apply A k[X] F,IsScalarTower.algebraMap_apply A k[X] F]
    exact congrArg (algebraMap k[X] F) eq
  have nonzero : G≠0 := by
    intro z
    have div : (j δ)∣0 := z ▸ associated.dvd
    have div' : 0∣j δ := z ▸ associated.dvd'
    exact (map_ne_zero_iff _ inj).mpr nz (zero_dvd_iff.mp div')
  obtain ⟨d,dd,cap⟩ := normalized_line_discriminant_degree bf bi nonzero
  exact ⟨d,dd,(congrArg (fun n : ℕ=>(n:ℤ)) (natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated associated))).trans_le cap⟩

#print axioms localized_line_discriminant_degree
end
end Lower6960.CollisionTame
