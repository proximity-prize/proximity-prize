import ProximityPrize.SubmissionLower.MovingSourcePairStageArithmetic6814

/-! Restrict selected seeds without changing any carrier, source or
support data. All unchanged fields remain definitionally equal. -/
namespace ProximityPrize.SubmissionLower.MovingSourceStageRestriction6814
noncomputable section
set_option autoImplicit false
open RCN135 RCN136 RCN159 RCN174 RCN243 RCN275
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p errorCap d : ℕ} [CharP (GenericField K) p]
  {flag : RCN095.FlagDegree} {support : ResidualSupportParameters}

def restrictStage (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag d support)
    (Delta : Finset K) (hsub : Delta⊆Gamma) :
    ResidualStage (polynomialEmbedding K) Delta x p errorCap flag d support where
  nodes := S.nodes
  u0 := S.u0
  u1 := S.u1
  selected := S.selected
  F := S.F
  G := S.G
  irreducible_G := S.irreducible_G
  G_dvd_surface := S.G_dvd_surface
  y_dependent := S.y_dependent
  regular_proper := S.regular_proper
  flag_support := S.flag_support
  surface_s_weight := S.surface_s_weight
  surface_ys_weight := S.surface_ys_weight
  surface_total_weight := S.surface_total_weight
  x_injective := S.x_injective
  degree_le := fun gamma hg => S.degree_le gamma (hsub hg)
  solution := fun gamma hg => S.solution gamma (hsub hg)
  regular := fun gamma hg => S.regular gamma (hsub hg)
  on_component := fun gamma hg => S.on_component gamma (hsub hg)
  no_large_pencil := noLargeSelectedPencil_mono S.selected Gamma Delta d errorCap hsub S.no_large_pencil
  characteristic_bound := S.characteristic_bound

theorem restrict_agreement (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag d support)
    (Delta : Finset K) (hsub : Delta⊆Gamma) (gamma : K) :
    (restrictStage S Delta hsub).agreementFiber gamma=S.agreementFiber gamma := rfl

#print axioms restrictStage
end
end ProximityPrize.SubmissionLower.MovingSourceStageRestriction6814
