import ProximityPrize.SubmissionLower.MovingSourceOuterStageFrames6814

/-! The first-tail-identity branch at the same 181255/80889 profile.
This removes the proper-first-tail restriction from the checked Stage
bound; it does not perform the outer geometric packet sum. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCheckedIdentityStage6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider MovingFiberThreeSources6811
open MovingSourcePairEnvelope6814 MovingSourceCheckedPairStage6814 MovingSourceTwoProfiles6814
open MovingSourceCoupledClearing6814
local notation "w" => RCN326.w

theorem checked_identity_degree :
    identityCurveDegree ⟨3504,45,12⟩ (cellA 3561 57) (cellB 57 12) (cellS 12) w=22209795582 := by
  decide +kernel

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

theorem checked_identity_stage
    (D : ℕ) (hDlow : 131072≤D) (hDchar : D<2130706433)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80889 flag w (cellSupport 3561 57 12))
    (hnodes : S.nodes.card=262144)
    (hagreement : ∀ gamma∈Gamma, 181255≤(S.agreementFiber gamma).card)
    (hbox : S.F∈globalCoefficientBox K D w 3561 12)
    (hflag : flag.all≤12 ∧ flag.yz+flag.all≤57 ∧ flag.zOnly+flag.yz+flag.all≤3561)
    (hTail : S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1)) :
    Gamma.card≤4692317191592603 := by
  have hflagChar : flag.yz+flag.all<2130706433 ∧ flag.all<2130706433 ∧
      flag.zOnly+flag.yz+flag.all<2130706433 := by omega
  have hTailNumerator := (globalTailCut_dvd_iff (polynomialEmbedding K)
    (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
  have hmixed := BoundaryTailGates.identity_gate flag 3561 57 12 (by decide) (by decide) (by decide)
    (by decide) (by decide) hflag.1 hflag.2.1
  have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider S 181255
    (by simpa using hnodes) hagreement (by decide) hTailNumerator D 3561 12 (by decide)
    hDlow hDchar hbox hflagChar hmixed
  have hpositive : 1 ≤ identityCurveDegree flag (cellA 3561 57) (cellB 57 12) (cellS 12) w := by
    apply Lower80788.FixedStage.identity_positive
    have hp := S.y_dependent
    have hh := degreeOf_le_flag_total S.G flag S.flag_support 1
    omega
  have hinc := identity_surface_seed_bound S 181255 _ hprovider hagreement
    (by decide) (by rw [hnodes]; decide) hpositive
  have hinc' : Gamma.card*50184≤131073*80890*
      identityCurveDegree flag (cellA 3561 57) (cellB 57 12) (cellS 12) w := by
    simpa only [hnodes,RCN326.w] using hinc
  have hz := mixed_mono_left flag ⟨3504,45,12⟩
    (RCN203.paddedCut (cellA 3561 57) (cellB 57 12) (cellS 12) (w+1)) unitZFlag hflag
  have hu := mixed_mono_left flag ⟨3504,45,12⟩
    (RCN203.paddedCut (cellA 3561 57) (cellB 57 12) (cellS 12) (w+1)) unitYZFlag hflag
  have hbound : identityCurveDegree flag (cellA 3561 57) (cellB 57 12) (cellS 12) w≤22209795582 := by
    rw [←checked_identity_degree]
    exact Nat.add_le_add hz hu
  have hh := hinc'.trans (Nat.mul_le_mul_left (131073*80890) hbound)
  omega

theorem checked_pair_stage_all_tails
    (D : ℕ) (hDlow : 131072≤D) (hDchar : D<2130706433)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80889 flag w (cellSupport 3561 57 12))
    [Fact (Irreducible S.F)] (hFT : 3429<wt residualTotalWeights S.F)
    (hnodes : S.nodes.card=262144)
    (hagreement : ∀ gamma∈Gamma, 181255≤(S.agreementFiber gamma).card)
    (hbox : S.F∈globalCoefficientBox K D w 3561 12)
    (hflag : flag.all≤12 ∧ flag.yz+flag.all≤57 ∧ flag.zOnly+flag.yz+flag.all≤3561)
    (hpos : 0<S.F.degreeOf 2)
    (SZ SP SQ : Source S.F) (hSZ : Profile SZ 53 177 3429 24 6 8)
    (hcop : IsRelPrime SP.P SQ.P)
    (delta : ℕ) (hd : 0<delta) (hd3 : delta≤3) (hP : delta≤SP.d) (hQ : delta≤SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag≤6014)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag≤delta*28420)
    (hv : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag≤delta*98890) :
    Gamma.card≤271849050685725612 := by
  by_cases hTail : S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1)
  · exact (checked_identity_stage D hDlow hDchar S hnodes hagreement hbox hflag hTail).trans (by decide +kernel)
  · exact checked_pair_stage_card D hDlow hDchar S hFT hnodes hagreement hbox hflag hTail hpos
      SZ SP SQ hSZ hcop delta hd hd3 hP hQ hz hu hv

#print axioms checked_pair_stage_all_tails
end
end ProximityPrize.SubmissionLower.MovingSourceCheckedIdentityStage6814
