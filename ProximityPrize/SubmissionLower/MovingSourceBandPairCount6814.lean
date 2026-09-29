import ProximityPrize.SubmissionLower.MovingSourceBandIdentity6814
import ProximityPrize.SubmissionLower.MovingSourceBandLeading6814

/-! Actual whole-packet pair count for variable audited cells and Z
sources. All three local exit cases and the leading exception are counted. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandPairCount6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN334 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider LocatorHybridTailProvider
open MovingFiberThreeSources6811 MovingSourceBandGeometry6814 MovingSourceBandSharedCosts6814
open MovingSourceSuppliedFrame6814 MovingSourceMovingDegrees6814 MovingSourcePairStageSupplier6814
open MovingSourceTwoProfiles6814 MovingSourceCoupledClearing6814 MovingSourceCheckedPairStage6814
open MovingSourceBandIdentity6814 MovingSourceBandLeading6814
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K

theorem regular_pair_packet_count
    (P : Packet x t y r) (hp : ¬P.F∣numerator K P.F (w+1))
    (SZ SP SQ : Source P.F) (hZd : SZ.k<2130706433)
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0<delta) (hd3 : delta≤3)
    (hP : delta≤SP.d) (hQ : delta≤SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag≤6014)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag≤delta*28420)
    (hgood : ∀ gamma∈P.seeds, MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
      (SZ.leading (polynomialEmbedding K))≠0) :
    P.seeds.card≤pairStageCost SZ SP SQ delta t y r ⟨t-y,y-r,r⟩ := by
  have hrlo := P.rlow
  have hylo := P.ylow
  have hyt := P.yt
  obtain ⟨geometry,budget,hcost,hjoint⟩ := exists_shared_packet_cost P hp SZ SP SQ hZd hcop delta hd hd3 hP hQ hz hu
  let normal := cellNormal t y r
  let cost (a : Curve P) := multiplicity P hp a*ordinary P hp geometry a normal+65539*(budget a).movingCost
  let live (g : GeometricFactor K P.F) : Finset (FirstTailComponent (P.stage g)) :=
    Finset.univ.filter (fun C => SZ.leading (polynomialEmbedding K)∉C.1)
  have hsingle (g : GeometricFactor K P.F) :
      (geometricSeeds K P.F P.selected P.seeds g).card≤∑ C∈live g, cost ⟨g,C⟩ := by
    let S := P.stage g
    let B := suppliedBudget S (P.stage_proper hp g) (geometry g)
    let base := suppliedBase S (geometry g)
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1) →
        (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) (geometricSeeds K P.F P.selected P.seeds g)
          (selectedPoint (polynomialEmbedding K) S.selected) C).card≤(80889+1)*B.yzCost C := by
      intro C hall
      exact tangent_component_card_le S C (P.stage_proper hp g) (base C)
        181255 P.D t r P.nodeCount (P.stage_agreement g) (by decide) (by decide)
        P.Dlow P.Dchar P.box B
        (suppliedBudget_yzPositive S (P.stage_proper hp g) (geometry g) C) hall
        (suppliedBudget_yzPole S (P.stage_proper hp g) (geometry g) C)
    have hinactive : ∀ C : FirstTailComponent S, C∉live g →
        (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) (geometricSeeds K P.F P.selected P.seeds g)
          (selectedPoint (polynomialEmbedding K) S.selected) C).card=0 := by
      intro C hC
      have hmem : SZ.leading (polynomialEmbedding K)∈C.1 := by
        simpa only [live,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hC
      exact SecondJetExceptionalComponents.component_empty_of_nonvanishing _ _ _
        (SZ.leading (polynomialEmbedding K)) (geometricSeeds K P.F P.selected P.seeds g)
        (selectedPoint (polynomialEmbedding K) S.selected) C hmem
        (fun gamma hg => hgood gamma (geometricSeeds_subset K P.F P.selected P.seeds g hg))
    obtain ⟨provider⟩ := BoundaryTailJointBudget6807.exists_provider_of_joint_curve_budget
      t y r (by omega) (by omega) (by omega) (by decide) S (P.stage_proper hp g)
      (cellFirstTail t y r) B base (fun C => budget ⟨g,C⟩) (fun C => hcost ⟨g,C⟩)
      (live g) (∑ C∈live g, cost ⟨g,C⟩) hinactive (le_refl _)
      (by dsimp [BoundaryTailJointBudget6807.cellNormal,BoundaryTailAlgebra.normalFlag,RCN327.w]; omega) htangent
    exact stage_card_le_divisorBound S provider
  have hsum : (∑ g, ∑ C∈live g, cost ⟨g,C⟩)=∑ a∈active P SZ, cost a := by
    simp only [live,active,Finset.sum_filter]
    rw [Fintype.sum_sigma]
  calc
    P.seeds.card≤∑ g, (geometricSeeds K P.F P.selected P.seeds g).card := P.seeds_cover
    _≤∑ g, ∑ C∈live g, cost ⟨g,C⟩ := Finset.sum_le_sum (fun g _ => hsingle g)
    _=∑ a∈active P SZ, cost a := hsum
    _≤_ := hjoint

theorem pair_packet_count
    (P : Packet x t y r) (SZ SP SQ : Source P.F)
    (hFT : SZ.T<wt residualTotalWeights P.F) (hZd : SZ.k<2130706433)
    (hgates : Gates t y r (SZ.B-2*SZ.n0) (SZ.U-SZ.n0) (SZ.T-SZ.n0))
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0<delta) (hd3 : delta≤3)
    (hP : delta≤SP.d) (hQ : delta≤SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag≤6014)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag≤delta*28420) :
    P.seeds.card≤max (identityPrice t y r)
      (pairStageCost SZ SP SQ delta t y r ⟨t-y,y-r,r⟩+leadingPrice SZ t y r) := by
  by_cases hp : P.F∣numerator K P.F (w+1)
  · exact (packet_identity_count P hp).trans (le_max_left _ _)
  let good := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (SZ.leading (polynomialEmbedding K))≠0)
  let bad := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (SZ.leading (polynomialEmbedding K))=0)
  let PG := P.restrict good (Finset.filter_subset _ _)
  have hmain := regular_pair_packet_count PG hp SZ SP SQ hZd hcop delta hd hd3 hP hQ hz hu
    (fun gamma hg => (Finset.mem_filter.mp hg).2)
  have hbad : bad.card≤leadingPrice SZ t y r := packet_z_leading_count P SZ hFT hgates
  have hpartition : P.seeds.card=good.card+bad.card := by
    unfold good bad
    rw [Nat.add_comm]
    exact (Finset.card_filter_add_card_filter_not _).symm
  rw [hpartition]
  exact (Nat.add_le_add hmain hbad).trans (le_max_right _ _)

#print axioms regular_pair_packet_count
#print axioms pair_packet_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandPairCount6814
