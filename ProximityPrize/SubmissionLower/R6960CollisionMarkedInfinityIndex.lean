import ProximityPrize.SubmissionLower.R6960CollisionMarkedIndexSupport
import ProximityPrize.SubmissionLower.R6960CollisionMarkedInfinitySeeds

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open Algebra Polynomial NormalizedFiber Module CollisionTame UniqueFactorizationMonoid
open scoped Polynomial TensorProduct Lower6960.CollisionMarked

variable {k : Type} [Field k] [DecidableEq k]

variable {E : Type} [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]

local instance infinityFibreRing (z:k) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order k E)) ((Order k E).toCommRing) (sliceIdeal E z)

/-- The original reciprocal chart specializes to an order whose index
clears the marked projector and is a unit at abscissa infinity. Each
bad scalar lies in the first nonzero discriminant coefficient. -/
theorem boundary_index (p : ℕ) [CharP k p] [CharP (FractionRing k[X]) p]
    (small : finrank (FractionRing (Plane k)) E<p)
    (δ:Plane k) (nz:δ≠0)
    (principal : normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))=Ideal.span {δ})
    (z:k) [IsReduced (FibreGeneric (E:=E) z)]
    (keep : (Bivariate.swap δ).trailingCoeff.eval z≠0) :
    ∃ d:k[X], d.eval 0≠0 ∧
      ∀ v:FibreGeneric (E:=E) z, IsIntegral k[X] v →
        ∃ u:Fiber E z,(1 ⊗ₜ[k[X]] u : FibreGeneric (E:=E) z)=algebraMap k[X] (FibreGeneric (E:=E) z) d*v := by
  obtain ⟨_,_,test⟩ := boundary_seed_polynomial δ nz
  obtain ⟨_,small0⟩ := test z keep
  obtain ⟨_,d,dn,_,support,clear⟩ := fibre_index_supported p small z δ nz principal
  refine ⟨d,?_,clear⟩
  intro zero
  have bad := support 0 ((mem_roots dn).mpr zero)
  omega

#print axioms boundary_index
end
end Lower6960.CollisionMarked
