import ProximityPrize.SubmissionLower.MovingSourcePacketLeading6814

/-! The existing checked-packet geometry, with the three audited cell caps
as parameters. No count or price hypothesis is added to the packet. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandGeometry6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN137 RCN156 RCN159 RCN174 RCN198
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN313 RCN319 RCN327 RCN334
open LocatorHybridCells LocatorHybridCellsC1 MovingSourceUniformTail6814 MovingSourceOuterPrimeInjection6814
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

structure Packet (x : I → K) (t y r : ℕ) where
  rlow : 4≤r
  rhigh : r≤13
  ylow : r+2≤y
  yhigh : y≤57
  yt : y≤t
  thigh : t≤3578
  D : ℕ
  Dlow : 131072≤D
  Dchar : D<2130706433
  F : MvPolynomial (Fin 4) K
  irreducible : Irreducible F
  rdegree : 0<F.degreeOf 2
  box : F∈globalCoefficientBox K D w t r
  support : ResidualSupportData (cellSupport t y r) F
  selected : K → Polynomial K
  seeds : Finset K
  nodes : Finset I
  u0 : I → K
  u1 : I → K
  injective : Set.InjOn x nodes
  nodeCount : nodes.card=262144
  degree : ∀ gamma∈seeds, (selected gamma).natDegree≤w
  agreement : ∀ gamma∈seeds, 181255≤
    (nodes.filter (fun i => (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card
  solution : ∀ gamma∈seeds, specialization K (selected gamma) gamma F=0
  regular : ∀ gamma∈seeds, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F)≠0
  noPencil : NoLargeSelectedPencil selected seeds w 80889

namespace Packet
variable {x : I → K} {t y r : ℕ} (P : Packet x t y r)

include P in
theorem support_caps : (cellSupport t y r).s=r ∧ (cellSupport t y r).ys=y ∧
    (cellSupport t y r).total=t := by
  have := P.rlow
  have := P.ylow
  have := P.yt
  dsimp [cellSupport,RCN198.support,cellA,cellB,cellS]
  omega

theorem r_weight : wt residualSWeights P.F≤r := by
  simpa only [P.support_caps.1] using P.support.s_weight

theorem y_weight : wt residualYSWeights P.F≤y := by
  simpa only [P.support_caps.2.1] using P.support.ys_weight

theorem total_weight : wt residualTotalWeights P.F≤t := by
  simpa only [P.support_caps.2.2] using P.support.total_weight

theorem coordinate_bounds : P.F.degreeOf 1≤y ∧ P.F.degreeOf 2≤r ∧ P.F.degreeOf 3≤t := by
  simpa only [P.support_caps.1,P.support_caps.2.1,P.support_caps.2.2] using P.support.coordinate_bounds

def restrict (Delta : Finset K) (hsub : Delta⊆P.seeds) : Packet x t y r :=
  {P with seeds := Delta
          degree := fun gamma hg => P.degree gamma (hsub hg)
          agreement := fun gamma hg => P.agreement gamma (hsub hg)
          solution := fun gamma hg => P.solution gamma (hsub hg)
          regular := fun gamma hg => P.regular gamma (hsub hg)
          noPencil := noLargeSelectedPencil_mono P.selected P.seeds Delta w 80889 hsub P.noPencil}

def stage (g : GeometricFactor K P.F) :
    ResidualStage (polynomialEmbedding K) (geometricSeeds K P.F P.selected P.seeds g) x
      2130706433 80889 (geometricCumulativeFlag K g) w (cellSupport t y r) :=
  reflagResidualStage
    (geometricResidualStageOfSupport K (cellSupport t y r) P.F P.irreducible P.rdegree
      (P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega : r<2130706433)) P.support
      P.selected P.seeds P.nodes x P.u0 P.u1 P.injective P.degree P.solution P.regular P.noPencil (by decide) g)
    (polynomialIn_surfaceCumulativeFlag g.val)

theorem stage_F (g : GeometricFactor K P.F) : (P.stage g).F=P.F := rfl
theorem stage_G (g : GeometricFactor K P.F) : (P.stage g).G=g.val := rfl
theorem stage_nodes (g : GeometricFactor K P.F) : (P.stage g).nodes=P.nodes := rfl
theorem stage_selected (g : GeometricFactor K P.F) : (P.stage g).selected=P.selected := rfl

theorem stage_flag (g : GeometricFactor K P.F) :
    (geometricCumulativeFlag K g).all≤r ∧
      (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all≤y ∧
      (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+
        (geometricCumulativeFlag K g).all≤t := by
  simpa only [P.support_caps.1,P.support_caps.2.1,P.support_caps.2.2] using
    geometricCumulativeFlag_le_support P.F P.irreducible.ne_zero P.support g

theorem stage_agreement (g : GeometricFactor K P.F) :
    ∀ gamma∈geometricSeeds K P.F P.selected P.seeds g, 181255≤((P.stage g).agreementFiber gamma).card :=
  fun gamma hg => P.agreement gamma (geometricSeeds_subset K P.F P.selected P.seeds g hg)

theorem parent_flag (L : Type) [Field L] (phi : Polynomial K →+* L) :
    PolynomialInFlag ⟨t-y,y-r,r⟩ (surfaceMap phi P.F) :=
  MovingSourceReducedGamma6814.surface_flag_of_caps phi P.F r y t (by have := P.ylow; omega) P.yt
    P.r_weight P.y_weight P.total_weight

theorem stage_proper (hproper : ¬P.F∣numerator K P.F (w+1)) (g : GeometricFactor K P.F) :
    ¬(P.stage g).G∣globalTailCut (polynomialEmbedding K) (P.stage g).F (w+1) := by
  intro hg
  exact hproper ((geometric_tail_dvd_iff_original (P.stage g) P.irreducible (w+1)).mp hg)

theorem prime_injective (hproper : ¬P.F∣numerator K P.F (w+1)) :
    Function.Injective (fun a : (g : GeometricFactor K P.F) × FirstTailComponent (P.stage g) => a.2.1) := by
  apply outer_stage_primes_injective (geometricSeeds K P.F P.selected P.seeds)
    (geometricCumulativeFlag K) P.stage P.F P.irreducible.ne_zero P.stage_F
  · intro g
    exact g.property
  · intro g h he
    exact Subtype.ext he
  · exact P.stage_proper hproper

theorem seeds_cover : P.seeds.card≤∑ g : GeometricFactor K P.F,
    (geometricSeeds K P.F P.selected P.seeds g).card :=
  card_le_sum_geometricSeeds K P.F P.irreducible.ne_zero P.selected P.seeds P.solution

end Packet
#print axioms Packet.prime_injective
#print axioms Packet.parent_flag
end
end ProximityPrize.SubmissionLower.MovingSourceBandGeometry6814
