import ProximityPrize.SubmissionLower.MovingSourceBandSharedCosts6815
namespace ProximityPrize.SubmissionLower.MovingSourceBandIdentity6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159 RCN174 RCN198
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN313 RCN327 RCN334
open RCN085 RCN087 RCN199 RCN206 RCN207 RCN271 RCN287 RCN312 RCN330 RCN332 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider MovingSourceBandGeometry6815
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}

def identityPrice (t y r : ℕ) : ℕ :=
  131073*80900*identityCurveDegree ⟨t-y,y-r,r⟩ (cellA t y) (cellB y r) (cellS r) w/50174

theorem packet_identity_count (P : Packet x t y r) (hidentity : P.F∣numerator K P.F (w+1)) :
    P.seeds.card ≤ identityPrice t y r := by
  have hrlo := P.rlow
  have hrhi := P.rhigh
  have hylo := P.ylow
  have hyhi := P.yhigh
  have hyt := P.yt
  have hthi := P.thigh
  let cost := fun g : GeometricFactor K P.F =>
    identityCurveDegree (geometricCumulativeFlag K g) (cellA t y) (cellB y r) (cellS r) w
  have hsingle (g : GeometricFactor K P.F) :
      (geometricSeeds K P.F P.selected P.seeds g).card*50174≤131073*80900*cost g := by
    let S := P.stage g
    have hflag := P.stage_flag g
    have hflagChar : (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all<2130706433 ∧
        (geometricCumulativeFlag K g).all<2130706433 ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all<2130706433 := by omega
    have hTailNumerator : S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1)) :=
      S.G_dvd_surface.trans (map_dvd (surfaceMap (polynomialEmbedding K)) hidentity)
    have hmixed := BoundaryTailGates.identity_gate (geometricCumulativeFlag K g) t y r
      (by omega) (by omega) (by omega) (by omega) (by omega) hflag.1 hflag.2.1
    have hnodes : S.nodes.card=262144 := P.nodeCount
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider S 181245
      hnodes (P.stage_agreement g) (by decide) hTailNumerator P.D t r (by decide)
      P.Dlow P.Dchar P.box hflagChar hmixed
    have hpositive : 1≤cost g := by
      apply Lower80788.FixedStage.identity_positive
      have hh := S.y_dependent
      have hd := degreeOf_le_flag_total S.G (geometricCumulativeFlag K g) S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181245 _ hprovider (P.stage_agreement g)
      (by decide) (by rw [hnodes]; decide) hpositive
    simpa only [cost,hnodes,RCN326.w,Nat.reduceSub,Nat.reduceAdd] using hinc
  have hb := geometricCumulativeFlag_budgets P.F P.irreducible.ne_zero
  have hc := originalCumulativeFlag_cumulative P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hz := sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K) ⟨t-y,y-r,r⟩
    (RCN203.paddedCut (cellA t y) (cellB y r) (cellS r) (w+1)) unitZFlag
    (hb.1.trans P.r_weight)
    ((hb.2.1.trans P.y_weight).trans_eq (by dsimp; omega))
    ((hb.2.2.trans P.total_weight).trans_eq (by dsimp; omega))
  have hu := sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K) ⟨t-y,y-r,r⟩
    (RCN203.paddedCut (cellA t y) (cellB y r) (cellS r) (w+1)) unitYZFlag
    (hb.1.trans P.r_weight)
    ((hb.2.1.trans P.y_weight).trans_eq (by dsimp; omega))
    ((hb.2.2.trans P.total_weight).trans_eq (by dsimp; omega))
  have hcost : (∑ g, cost g) ≤ identityCurveDegree ⟨t-y,y-r,r⟩ (cellA t y) (cellB y r) (cellS r) w := by
    simpa only [cost,identityCurveDegree,Finset.sum_add_distrib] using Nat.add_le_add hz hu
  have hsum := Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => hsingle g)
  simp only [←Finset.sum_mul,←Finset.mul_sum] at hsum
  have hfinal := (Nat.mul_le_mul_right 50174 P.seeds_cover).trans
    (hsum.trans (Nat.mul_le_mul_left (131073*80900) hcost))
  exact (Nat.le_div_iff_mul_le (by decide : 0<50174)).mpr hfinal

end
end ProximityPrize.SubmissionLower.MovingSourceBandIdentity6815
