import ProximityPrize.SubmissionLower.MovingSourcePairRetainedStage6814

/-! A proper-first-tail Stage count from actual coprime Sources at the
181255 agreement profile. H-free, tangent, characteristic and both
point-budget suppliers are discharged here, rather than assumed counts. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider LocatorHybridTransportC2
open BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
open HFreeDir6813 MovingSourcePairRetainedStage6814 MovingSourceCoupledClearing6814
open MovingSourcePairMovingDegrees6814 MovingSourceExtendedPointCount6814
open MovingSourceReducedGamma6814
local notation "w" => RCN326.w

def stageScale {K : Type} [Field K] {F : MvPolynomial (Fin 4) K} (SZ : Source F) (delta : ℕ) : ℕ := SZ.d*delta
def pairStageCost {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (SZ SP SQ : Source F) (delta t y r : ℕ) (flag : FlagDegree) : ℕ :=
  pairNumerator (stageScale SZ delta)
    (delta*flagMixed ⟨t-y,y-r,r⟩ unitZFlag SZ.flag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)
    t y r flag/(3*stageScale SZ delta)

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)

theorem regular_pair_stage_bound
    (D t y r : ℕ) (hDlow : 131072≤D) (hDchar : D<2130706433)
    (ht : t≤7501) (hy : y≤142) (hr : r≤31)
    (hr3 : 3≤r) (hry : r+2≤y) (hyt : y≤t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80889 flag w (cellSupport t y r))
    (hnodes : S.nodes.card=262144)
    (hagreement : ∀ gamma∈Gamma, 181255≤(S.agreementFiber gamma).card)
    (hbox : S.F∈globalCoefficientBox K D w t r)
    (hflag : flag.all≤r ∧ flag.yz+flag.all≤y ∧ flag.zOnly+flag.yz+flag.all≤t)
    (hproper : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hpos : 0<S.F.degreeOf 2)
    (SZ SP SQ : Source S.F) (hcop : IsRelPrime SP.P SQ.P)
    (delta : ℕ) (hd : 0<delta) (hP : delta≤SP.d) (hQ : delta≤SQ.d) (hchar : delta≤2130706433)
    (hZchar : SZ.k<2130706433)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433)
    (hgood : ∀ gamma∈Gamma, MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
      (SZ.leading (polynomialEmbedding K))≠0) :
    Gamma.card≤pairStageCost SZ SP SQ delta t y r flag := by
  have hflagChar : flag.yz+flag.all<2130706433 ∧ flag.all<2130706433 ∧ flag.zOnly+flag.yz+flag.all<2130706433 := by omega
  have hmixed := BoundaryTailGates.reduced_gate flag t y r hr3 hr hy hry hyt hflag.1 hflag.2.1
  have htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1) →
      (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card≤
        (80889+1)*(BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixed).yzCost C := by
    intro C hall
    exact tangent_component_card_le S C hproper (BoundaryTailReduced.reducedBaseOrd S hproper hflagChar hmixed C)
      181255 D t r (by simpa using hnodes) hagreement (by decide) (by decide)
      hDlow hDchar hbox (BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixed)
      (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hproper hflagChar hmixed C) hall
      (BoundaryTailReduced.reducedBudgetFamily_yzPole S hproper hflagChar hmixed C)
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
  have hs : cellS r+2=r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3=y := by dsimp [cellB,cellS]; omega
  have htot : cellA t y+cellB y r+cellS r+3=t := by dsimp [cellA,cellB,cellS]; omega
  have hFsmall : S.F.degreeOf 2<2130706433 := by
    have hh := Hsupport.coordinate_bounds.2.1
    change S.F.degreeOf 2≤cellS r+2 at hh
    omega
  have hFne : S.F≠0 := by intro he; simp [he] at hpos
  have hparent (L : Type) [Field L] (phi : Polynomial K →+* L) :
      PolynomialInFlag ⟨t-y,y-r,r⟩ (surfaceMap phi S.F) := by
    apply surface_flag_of_caps phi S.F r y t (by omega) hyt
    · simpa only [cellSupport,RCN198.support,hs] using Hsupport.s_weight
    · simpa only [cellSupport,RCN198.support,hys] using Hsupport.ys_weight
    · simpa only [cellSupport,RCN198.support,htot] using Hsupport.total_weight
  have hunit : 2*((t-y)+(y-r)+r)<2130706433 := by omega
  have hscale : 0<stageScale SZ delta := Nat.mul_pos (by dsimp [Source.d]; omega) hd
  have hfree : HFreeStageDir S := by
    apply hfree_stage_dir_of_gaps S
    change cellA t y+cellB y r+cellS r+3≤9678
    omega
  have hgate : 80889+1≤(cellNormal t y r).yz := by
    unfold cellNormal
    rw [BoundaryTailAlgebra.normalFlag_eq_cell t y r hr3 hry]
    simpa only [add_yz,nsmul_yz,unitAllFlag,mul_zero,add_zero] using
      hybridC1Gate_of_le t y r 80889 hry (by decide)
  apply retained_stage_pair_bound t y r (stageScale SZ delta)
    (delta*flagMixed ⟨t-y,y-r,r⟩ unitZFlag SZ.flag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)
    hr3 hry hyt S SZ hscale hfree hproper hflagChar hmixed (by omega) hgate htangent hgood
  · intro Q A hden hQf hAf
    exact weighted_sources_point_budget S.F hFne hpos hFsmall SP SQ hcop delta hd hP hQ hchar SZ hZchar
      ⟨t-y,y-r,r⟩ (hparent _ _) hunit Q A hden hQf hAf hz hu
  · intro Q A hden hQf hAf
    exact extended_sources_point_budget (algebraMap Ω Ext) S.F hFne hpos hFsmall SP SQ hcop
      delta hd hP hQ hchar SZ hZchar ⟨t-y,y-r,r⟩ (hparent _ _) hunit Q A hden hQf hAf hz hu

#print axioms regular_pair_stage_bound
end
end ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814
