import ProximityPrize.SubmissionLower.MovingSourceZLeadingSeeds6814

/-! Partition all selected Stage seeds into Z-leading-regular and
Z-leading-zero parts, and discharge both cardinality bounds. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePairStageWithLeading6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical
open RCN086 RCN095 RCN135 RCN136 RCN156 RCN159 RCN174 RCN234 RCN243 RCN244 RCN260 RCN264 RCN275
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceZLeadingSeeds6814 MovingSourceStageRestriction6814
open MovingSourcePairStageSupplier6814 MovingSourceCoupledClearing6814
open LocatorHybridCells

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}
local notation "w" => RCN326.w

theorem checked_pair_stage_with_leading
    (D : ℕ) (hDlow : 131072≤D) (hDchar : D<2130706433)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80889 flag w (cellSupport 3561 57 12))
    [Fact (Irreducible S.F)] (hFT : 3429<wt residualTotalWeights S.F)
    (hnodes : S.nodes.card=262144)
    (hagreement : ∀ gamma∈Gamma, 181255≤(S.agreementFiber gamma).card)
    (hbox : S.F∈globalCoefficientBox K D w 3561 12)
    (hflag : flag.all≤12 ∧ flag.yz+flag.all≤57 ∧ flag.zOnly+flag.yz+flag.all≤3561)
    (hproper : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hpos : 0<S.F.degreeOf 2)
    (SZ SP SQ : Source S.F) (hSZ : Profile SZ 53 177 3429 24 6 8)
    (hcop : IsRelPrime SP.P SQ.P)
    (delta : ℕ) (hd : 0<delta) (hP : delta≤SP.d) (hQ : delta≤SQ.d) (hchar : delta≤2130706433)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433) :
    Gamma.card≤pairStageCost SZ SP SQ delta 3561 57 12 flag+23104862107476 := by
  let good := goodSeeds S SZ
  have hsub : good⊆Gamma := Finset.filter_subset _ _
  let SG := restrictStage S good hsub
  have hZchar : SZ.k<2130706433 := by rw [hSZ.2.2.2.2.1]; decide
  have hgood : good.card≤pairStageCost SZ SP SQ delta 3561 57 12 flag := by
    apply regular_pair_stage_bound D 3561 57 12 hDlow hDchar
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      SG hnodes (fun gamma hg => hagreement gamma (hsub hg)) hbox hflag hproper hpos
      SZ SP SQ hcop delta hd hP hQ hchar hZchar hz hu
    intro gamma hg
    exact (Finset.mem_filter.mp hg).2
  have hSflag : PolynomialInFlag ⟨3504,45,12⟩ S.G := by
    intro e he
    have hh := S.flag_support e he
    dsimp only [InFlag] at hh ⊢
    omega
  have hsupport : ResidualSupportData (cellSupport 3561 57 12) S.F :=
    ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
  have hFY : S.F.degreeOf 1≤57 := hsupport.coordinate_bounds.1
  have hFR : S.F.degreeOf 2≤12 := hsupport.coordinate_bounds.2.1
  have hFZ : S.F.degreeOf 3≤3561 := hsupport.coordinate_bounds.2.2
  have hbad := z_leading_seed_count S rfl rfl SZ hSZ hFT hSflag hFY hFR hFZ hnodes hagreement
  rw [good_bad_card S SZ]
  exact Nat.add_le_add hgood hbad

theorem checked_pair_with_exception_fits :
    271825945823618136+23104862107476=271849050685725612 ∧
    271849050685725612<272069082261391681 := by decide +kernel

#print axioms checked_pair_stage_with_leading
end
end ProximityPrize.SubmissionLower.MovingSourcePairStageWithLeading6814
