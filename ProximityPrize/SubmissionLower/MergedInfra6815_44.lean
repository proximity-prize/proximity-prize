import ProximityPrize.SubmissionLower.MergedInfra6815_42
import ProximityPrize.SubmissionLower.MergedInfra6815_41
import ProximityPrize.SubmissionLower.MergedInfra6815_32
import ProximityPrize.SubmissionLower.MergedInfra6815_43
import ProximityPrize.SubmissionLower.RetainedSharedRemainder6815
import ProximityPrize.SubmissionLower.MergedInfra6815_39
import ProximityPrize.SubmissionLower.MergedInfra6815_40
import ProximityPrize.SubmissionLower.MergedInfra6815_37
import ProximityPrize.SubmissionLower.PortfolioSourceCatalogue6815
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingSourceBandLeading6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical
open RCN095 RCN135 RCN136 RCN156 RCN174 RCN234 RCN238 RCN243 RCN260 RCN319
open MovingSourceBandGeometry6815 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open SecondJetCoefficients SecondJetHelperWeights
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}

def pair (t y r b u l : ℕ) : UnequalParameters := ⟨262144,131071,181245,y,r,t,u,b,l⟩

def Gates (t y r b u l : ℕ) : Prop :=
  (pair t y r b u l).mixedCost.y<2130706433 ∧
  (pair t y r b u l).mixedCost.r<2130706433 ∧
  (pair t y r b u l).mixedCost.z<2130706433

theorem proper_cut_count (P : Packet x t y r) (Q : MvPolynomial (Fin 4) K)
    (b u l : ℕ) (hrel : IsRelPrime P.F Q)
    (hweights : wt residualSWeights Q≤b ∧ wt residualYSWeights Q≤u ∧ wt residualTotalWeights Q≤l)
    (hgates : Gates t y r b u l)
    (hzero : ∀ gamma∈P.seeds, specialization K (P.selected gamma) gamma Q=0) :
    P.seeds.card≤AsymmetricHelper.leftRegularCountCap (pair t y r b u l) := by
  have hrlo := P.rlow
  have hrhi := P.rhigh
  have hyhi := P.yhigh
  have hthi := P.thigh
  have hQ := SecondJetPairBounds.degree_caps_of_weights Q b u l hweights
  have hc := SecondJetProperCounting.regular_seed_bound_left (pair t y r b u l) P.F Q
    P.irreducible P.rdegree hrel 2130706433 P.coordinate_bounds.1 P.coordinate_bounds.2.1 P.coordinate_bounds.2.2
    hQ.1 hQ.2.1 hQ.2.2 (by dsimp [pair]; omega) (by dsimp [pair]; omega)
    (by dsimp [pair]; omega) (by dsimp [pair]; omega) hgates.1 hgates.2.1 hgates.2.2
    P.selected P.seeds P.nodes x P.u0 P.u1 P.injective P.nodeCount
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    P.degree P.agreement
    (by simpa only [pair,UnequalParameters.errors,Nat.reduceSub,RCN326.w] using P.noPencil)
    P.solution P.regular hzero
  exact SecondJetPairBounds.count_le_left_cap (pair t y r b u l) P.F P.coordinate_bounds.1
    P.coordinate_bounds.2.1 P.coordinate_bounds.2.2 P.seeds.card (by norm_num [pair,UnequalParameters.gap]) hc

theorem source_leading_weights (F : MvPolynomial (Fin 4) K) (S : Source F) :
    wt residualSWeights (asS S.P).leadingCoeff≤S.B-2*S.n0 ∧
    wt residualYSWeights (asS S.P).leadingCoeff≤S.U-S.n0 ∧
    wt residualTotalWeights (asS S.P).leadingCoeff≤S.T-S.n0 := by
  have hn := S.hn
  have hw := derivative_coefficient_weights S.P S.B S.U S.T 0 (asS S.P).natDegree S.hshape
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
  rw [Polynomial.leadingCoeff]
  omega

def leadingPrice {F : MvPolynomial (Fin 4) K} (S : Source F) (t y r : ℕ) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (pair t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0))

theorem packet_z_leading_count (P : Packet x t y r) (S : Source P.F)
    (hFT : S.T<wt residualTotalWeights P.F)
    (hgates : Gates t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0)) :
    (P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
      (S.leading (polynomialEmbedding K))=0)).card≤leadingPrice S t y r := by
  let bad := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (S.leading (polynomialEmbedding K))=0)
  let PB := P.restrict bad (Finset.filter_subset _ _)
  have hnot := SecondJetTotalAvoidance.leading_not_dvd S.P (source_nonzero P.F S) P.F S.T
    (fun e he => (S.hshape e he).2.2) hFT
  have hzero : ∀ gamma∈bad, specialization K (P.selected gamma) gamma (asS S.P).leadingCoeff=0 := by
    intro gamma hg
    have hh := (Finset.mem_filter.mp hg).2
    change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
      (surfaceMap (polynomialEmbedding K) (asS S.P).leadingCoeff)=0 at hh
    rw [RCN170.canonical_selectedPoint_surface_evaluation] at hh
    exact polynomialEmbedding_injective K (by simpa only [map_zero] using hh)
  exact proper_cut_count PB (asS S.P).leadingCoeff (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0)
    (P.irreducible.isRelPrime_iff_not_dvd.mpr hnot.2) (source_leading_weights P.F S) hgates hzero

end
end ProximityPrize.SubmissionLower.MovingSourceBandLeading6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingSourceBandSharedCosts6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN313 RCN327 RCN334 RCN338 RCN341
open RCN206 RCN209 RCN340 RCN344
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider CommonLinearChannels6807
open MovingFiberThreeSources6811 MovingFiberRetainedStage6811 HFreeDir6813
open MovingSourceBandGeometry6815 MovingSourceOuterStageFrames6814 MovingSourceSuppliedFrame6814
open MovingSourceOuterMovingBudget6814 MovingSourceCommonChannelBudget6814 MovingSourceExtendedPointCount6814
open MovingSourceMovingDegrees6814 MovingSourcePairRetainedStage6814 MovingSourcePairStageSupplier6814
open MovingSourceTwoProfiles6814 MovingSourceCoupledClearing6814
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)

abbrev Curve (P : Packet x t y r) := (g : GeometricFactor K P.F) × FirstTailComponent (P.stage g)

def active (P : Packet x t y r) (SZ : Source P.F) : Finset (Curve P) :=
  Finset.univ.filter (fun a => SZ.leading (polynomialEmbedding K)∉a.2.1)

def multiplicity (P : Packet x t y r) (hp : ¬P.F∣numerator K P.F (w+1)) (a : Curve P) : ℕ :=
  localMultiplicity (loosenStageGeneral (P.stage a.1))
    (canonicalLocalDVRFamily (loosenStageGeneral (P.stage a.1)) (P.stage_proper hp a.1)) a.2

def ordinary (P : Packet x t y r) (hp : ¬P.F∣numerator K P.F (w+1))
    (geometry : ∀ g, ReducedActiveGeometry (P.stage g)) (a : Curve P) (W : FlagDegree) : ℕ :=
  (suppliedBudget (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).weightedCost W a.2

private theorem mixed_swap (p q r : FlagDegree) : flagMixed p q r=flagMixed p r q := by
  unfold flagMixed
  ring

private theorem swap_weighted_sum {A : Type} [Fintype A]
    (scale : ℕ) (weight : Fin 3 → ℕ) (mu : A → ℕ) (degree : Fin 3 → A → ℕ) :
    (∑ j : Fin 3, weight j*(scale*∑ a, mu a*degree j a))=
      scale*(∑ a, mu a*(∑ j : Fin 3, weight j*degree j a)) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem sum_scaled_prices (W : FlagDegree) (scale coeff z u v : ℕ) (fixed : Fin 3 → ℕ) :
    (∑ j : Fin 3, weight W j*(scale*fixed j+coeff*price (MovingFiberThreeSources6811.direction j) z u v))=
      scale*(∑ j : Fin 3, weight W j*fixed j)+coeff*price W z u v := by
  simp only [Nat.mul_add,Finset.sum_add_distrib,Nat.mul_left_comm,←Finset.mul_sum]
  rw [sum_weight_price]

theorem exists_shared_packet_cost
    (P : Packet x t y r) (hp : ¬P.F∣numerator K P.F (w+1))
    (SZ SP SQ : Source P.F) (hZd : SZ.k<2130706433)
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0<delta) (hdchar : delta≤2130706433)
    (hP : delta≤SP.d) (hQ : delta≤SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433) :
    ∃ (geometry : ∀ g, ReducedActiveGeometry (P.stage g))
      (budget : ∀ a : Curve P, MovingPoleBudget a.2.1 (baseH P.F) (baseG P.F)),
      (∀ a, (budget a).zCost=(suppliedBudget (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).zCost a.2 ∧
        (budget a).yzCost=(suppliedBudget (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).yzCost a.2 ∧
        (budget a).allCost=(suppliedBudget (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).allCost a.2) ∧
      (∑ a∈active P SZ, (multiplicity P hp a*ordinary P hp geometry a (cellNormal t y r)+
        65539*(budget a).movingCost))≤pairStageCost SZ SP SQ delta t y r ⟨t-y,y-r,r⟩ := by
  have hrlo := P.rlow
  have hrhi := P.rhigh
  have hylo := P.ylow
  have hyhi := P.yhigh
  have hyt := P.yt
  have hthi := P.thigh
  have hflags (g : GeometricFactor K P.F) : (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all<2130706433 ∧
      (geometricCumulativeFlag K g).all<2130706433 ∧
      (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all<2130706433 := by
    have hh := P.stage_flag g
    omega
  have hmixed (g : GeometricFactor K P.F) := BoundaryTailGates.reduced_gate
    (geometricCumulativeFlag K g) t y r (by omega) (by omega) (by omega) (by omega) (by omega)
    (P.stage_flag g).1 (P.stage_flag g).2.1
  obtain ⟨lam,mu,hlam,hmu,geometry,heq⟩ := exists_common_stage_geometry
    (geometricSeeds K P.F P.selected P.seeds) x (geometricCumulativeFlag K) P.stage
    (P.stage_proper hp) hflags hmixed
  let unit := fun g => suppliedUnit (P.stage g) (P.stage_proper hp g) (geometry g)
  let scale := SZ.d*delta
  let zCap := delta*flagMixed ⟨t-y,y-r,r⟩ unitZFlag SZ.flag
  let uCap := SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag
  let vCap := SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag
  let live := active P SZ
  have hscale : 0<scale := Nat.mul_pos (by dsimp [Source.d]; omega) hd
  have hFchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by omega : r<2130706433)
  have hraw : ∀ Q A : MvPolynomial (Fin 3) Ω, (2 : MvPolynomial (Fin 3) Ω)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget (RingHom.id Ω) P.F SZ Q A scale zCap uCap vCap := by
    intro Q A hden hQf hAf
    exact extended_sources_point_budget (RingHom.id Ω) P.F P.irreducible.ne_zero P.rdegree hFchar
      SP SQ hcop delta hd hP hQ (by omega) SZ hZd ⟨t-y,y-r,r⟩ (P.parent_flag _ _) (by dsimp; omega)
      Q A hden hQf hAf (by omega) (by omega)
  obtain ⟨budget,hcost,hmoving⟩ := exists_outer_first_tail_pair_budget P.F SZ
    (fun a : Curve P => a.1.val) (fun a => (P.stage a.1).G_dvd_surface)
    (cellA t y) (cellB y r) (cellS r) w (by decide)
    P.support.coordinate_bounds.2.1 P.support.ys_weight P.support.total_weight
    (fun a : Curve P => suppliedBase (P.stage a.1) (geometry a.1))
    (fun a : Curve P => geometricCumulativeFlag K a.1) (cellFirstTail t y r)
    (fun a : Curve P => unit a.1) (fun a : Curve P => a.2) (P.prime_injective hp)
    live (fun a ha => (Finset.mem_filter.mp ha).2) scale zCap uCap vCap hraw
  refine ⟨geometry,budget,hcost,?_⟩
  let projection : (j : Fin 3) → (a : Curve P) → Coordinate Ω (CoordinateField Ω a.2.1) :=
    fun j a => ![(unit a.1).zProjection a.2,(unit a.1).yzProjection a.2,(unit a.1).allProjection a.2] j
  have hvalue (j : Fin 3) (a : Curve P) : coordinateValue Ω (CoordinateField Ω a.2.1) (projection j a)=
      coordinateEvaluation Ω a.2.1 (commonChannel lam mu j) := by
    fin_cases j
    · exact common_z_value (unit a.1) a.2
    · exact supplied_u_value (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1) lam (heq a.1).1 a.2
    · exact supplied_a_value (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1) lam mu (heq a.1).1 (heq a.1).2 a.2
  have hR : WeightBound residualSWeights P.F (r : ℤ) := Or.inr (by exact_mod_cast P.r_weight)
  have hYR : WeightBound residualYSWeights P.F ((r+(y-r) : ℕ) : ℤ) := Or.inr (by exact_mod_cast (show wt residualYSWeights P.F≤r+(y-r) by have := P.y_weight; omega))
  have hAll : MvPolynomial.weightedTotalDegree residualTotalWeights P.F≤r+(y-r)+(t-y) := by
    have hh : MvPolynomial.weightedTotalDegree residualTotalWeights P.F≤t := P.total_weight
    omega
  have hnormal (j : Fin 3) :
      3*scale*(∑ a : live, multiplicity P hp a.val*coordinateDegree Ω (CoordinateField Ω a.val.2.1) (projection j a.val))≤
        scale*flagMixed ⟨t-y,y-r,r⟩ (hfreeFirstDir t y r j) (MovingFiberThreeSources6811.direction j)+
          4*(w+1)*price (MovingFiberThreeSources6811.direction j) zCap uCap vCap := by
    have hh := outer_first_cut_from_sources (E:=Ext)
      (fun a : live => geometricSeeds K P.F P.selected P.seeds a.val.1)
      (fun a : live => geometricCumulativeFlag K a.val.1)
      (fun a : live => loosenStageGeneral (P.stage a.val.1))
      P.F P.irreducible.ne_zero (fun _ => rfl) ⟨t-y,y-r,r⟩ P.parent_flag
      (fun a => P.stage_proper hp a.val.1) (fun a : live => a.val.2)
      (fun a b hh => Subtype.ext (P.prime_injective hp hh))
      lam mu hlam hmu j (fun a => projection j a.val) (fun a => hvalue j a.val) (by dsimp; omega)
      SZ SP SQ (fun a => (Finset.mem_filter.mp a.property).2) r (y-r) (t-y) (by omega) (by omega)
      hR hYR hAll (by omega) P.rdegree hFchar hcop delta hd hP hQ (by omega) hZd (by omega) (by omega)
    simpa only [multiplicity,scale,zCap,uCap,vCap,price,hfreeFirstDir,mixed_swap] using hh
  let normal := cellNormal t y r
  have hordinary (a : Curve P) : ordinary P hp geometry a normal=
      ∑ j : Fin 3, weight normal j*coordinateDegree Ω (CoordinateField Ω a.2.1) (projection j a) := by
    simp only [Fin.sum_univ_three,projection,weight,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      ordinary,suppliedBudget,PrimeFlagBudgetFamily.weightedCost,unit,
      AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily,AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,
      AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget]
    rfl
  have hnormalSum : 3*scale*(∑ a∈live, multiplicity P hp a*ordinary P hp geometry a normal)≤
      scale*(∑ j : Fin 3, weight normal j*flagMixed ⟨t-y,y-r,r⟩
        (hfreeFirstDir t y r j) (MovingFiberThreeSources6811.direction j))+
          4*(w+1)*price normal zCap uCap vCap := by
    have hh := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) =>
      Nat.mul_le_mul_left (weight normal j) (hnormal j))
    rw [swap_weighted_sum,sum_scaled_prices] at hh
    rw [←Finset.sum_coe_sort live (fun a => multiplicity P hp a*ordinary P hp geometry a normal)]
    simpa only [hordinary] using hh
  have hmove : scale*(∑ a∈live, (budget a).movingCost)≤price (rawFirstFlag t y r) zCap uCap vCap := hmoving
  have hjoint : (3*scale)*(∑ a∈live, (multiplicity P hp a*ordinary P hp geometry a normal+
      65539*(budget a).movingCost))≤pairNumerator scale zCap uCap vCap t y r ⟨t-y,y-r,r⟩ := by
    have hh := Nat.add_le_add hnormalSum (Nat.mul_le_mul_left (3*65539) hmove)
    convert hh using 1
    · simp only [Finset.sum_add_distrib,←Finset.mul_sum]; ring
    · rfl
  apply (Nat.le_div_iff_mul_le (by omega : 0<3*scale)).mpr
  change (∑ a∈live, (multiplicity P hp a*ordinary P hp geometry a normal+
    65539*(budget a).movingCost))*(3*scale)≤pairNumerator scale zCap uCap vCap t y r ⟨t-y,y-r,r⟩
  exact (Nat.mul_comm _ _).trans_le hjoint

end
end ProximityPrize.SubmissionLower.MovingSourceBandSharedCosts6815
end MergedPart1
section MergedPart2
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
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingSourceBandPairCount6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN334 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider LocatorHybridTailProvider
open MovingFiberThreeSources6811 MovingSourceBandGeometry6815 MovingSourceBandSharedCosts6815
open MovingSourceSuppliedFrame6814 MovingSourceMovingDegrees6814 MovingSourcePairStageSupplier6814
open MovingSourceTwoProfiles6814 MovingSourceCoupledClearing6814
open MovingSourceBandIdentity6815 MovingSourceBandLeading6815
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K

theorem regular_pair_packet_count
    (P : Packet x t y r) (hp : ¬P.F∣numerator K P.F (w+1))
    (SZ SP SQ : Source P.F) (hZd : SZ.k<2130706433)
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0<delta) (hdchar : delta≤2130706433)
    (hP : delta≤SP.d) (hQ : delta≤SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433)
    (hgood : ∀ gamma∈P.seeds, MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
      (SZ.leading (polynomialEmbedding K))≠0) :
    P.seeds.card≤pairStageCost SZ SP SQ delta t y r ⟨t-y,y-r,r⟩ := by
  have hrlo := P.rlow
  have hylo := P.ylow
  have hyt := P.yt
  obtain ⟨geometry,budget,hcost,hjoint⟩ := exists_shared_packet_cost P hp SZ SP SQ hZd hcop delta hd hdchar hP hQ hz hu
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
          (selectedPoint (polynomialEmbedding K) S.selected) C).card≤(80899+1)*B.yzCost C := by
      intro C hall
      exact tangent_component_card_le S C (P.stage_proper hp g) (base C)
        181245 P.D t r P.nodeCount (P.stage_agreement g) (by decide) (by decide)
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
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0<delta) (hdchar : delta≤2130706433)
    (hP : delta≤SP.d) (hQ : delta≤SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433) :
    P.seeds.card≤max (identityPrice t y r)
      (pairStageCost SZ SP SQ delta t y r ⟨t-y,y-r,r⟩+leadingPrice SZ t y r) := by
  by_cases hp : P.F∣numerator K P.F (w+1)
  · exact (packet_identity_count P hp).trans (le_max_left _ _)
  let good := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (SZ.leading (polynomialEmbedding K))≠0)
  let bad := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (SZ.leading (polynomialEmbedding K))=0)
  let PG := P.restrict good (Finset.filter_subset _ _)
  have hmain := regular_pair_packet_count PG hp SZ SP SQ hZd hcop delta hd hdchar hP hQ hz hu
    (fun gamma hg => (Finset.mem_filter.mp hg).2)
  have hbad : bad.card≤leadingPrice SZ t y r := packet_z_leading_count P SZ hFT hgates
  have hpartition : P.seeds.card=good.card+bad.card := by
    unfold good bad
    rw [Nat.add_comm]
    exact (Finset.card_filter_add_card_filter_not _).symm
  rw [hpartition]
  exact (Nat.add_le_add hmain hbad).trans (le_max_right _ _)

end
end ProximityPrize.SubmissionLower.MovingSourceBandPairCount6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourceBandNativeCount6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN332 RCN334 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider MovingSourceBandGeometry6815
open MovingFiberThreeSources6811 HFreeDir6813
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K

def nativeNumerator {F : MvPolynomial (Fin 4) K} (source : Source F) (t y r : ℕ) (fl : FlagDegree) : ℕ :=
  numeratorDir (fun _ => source) (3*source.d) t y r fl

theorem native_regular_packet_count
    (P : Packet x t y r) (hp : ¬P.F∣numerator K P.F (w+1)) (source : Source P.F)
    (hk : source.k<2130706433)
    (hgood : ∀ gamma∈P.seeds, MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
      (source.leading (polynomialEmbedding K))≠0) :
    (3*source.d)*P.seeds.card≤nativeNumerator source t y r ⟨t-y,y-r,r⟩ := by
  have hrlo := P.rlow
  have hrhi := P.rhigh
  have hylo := P.ylow
  have hyhi := P.yhigh
  have hyt := P.yt
  have hthi := P.thigh
  have hd : 0<3*source.d := by dsimp [Source.d]; omega
  have hstage (g : GeometricFactor K P.F) :
      (3*source.d)*(geometricSeeds K P.F P.selected P.seeds g).card≤nativeNumerator source t y r (geometricCumulativeFlag K g) := by
    let S := P.stage g
    have hflag := P.stage_flag g
    have hc : (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all<2130706433 ∧
        (geometricCumulativeFlag K g).all<2130706433 ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all<2130706433 := by omega
    have hm := BoundaryTailGates.reduced_gate (geometricCumulativeFlag K g) t y r
      (by omega) (by omega) (by omega) (by omega) (by omega) hflag.1 hflag.2.1
    have hproper := P.stage_proper hp g
    let B := BoundaryTailReduced.reducedBudgetFamily S hproper hc hm
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1) →
        (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) (geometricSeeds K P.F P.selected P.seeds g)
          (selectedPoint (polynomialEmbedding K) S.selected) C).card≤80900*B.yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hproper (BoundaryTailReduced.reducedBaseOrd S hproper hc hm C)
        181245 P.D t r P.nodeCount (P.stage_agreement g) (by decide) (by decide)
        P.Dlow P.Dchar P.box B (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hproper hc hm C) hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hproper hc hm C)
    have hh := retained_stage_bound_dir t y r (3*source.d) (by omega) (by omega) (by omega)
      S (fun _ => source) hd (fun _ => dvd_rfl) (hfree_stage_dir_of_gaps S (by rw [P.support_caps.2.2]; omega)) hproper hc hm
      (by omega)
      (by
        have htotal := hflag.2.2.trans hthi
        calc
          _≤2*4100*4101 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 htotal) (by omega)
          _<2130706433 := by decide)
      (by decide) (by dsimp [cellNormal,BoundaryTailAlgebra.normalFlag,RCN327.w]; omega) htangent SecondJetOwnShape.two_ne
      (fun _ => SecondJetOwnShape.factorial_ne source.k hk)
      (fun gamma hgamma _ => hgood gamma (geometricSeeds_subset K P.F P.selected P.seeds g hgamma))
    exact (Nat.mul_comm _ _).trans_le ((Nat.le_div_iff_mul_le hd).mp hh)
  have hb := geometricCumulativeFlag_budgets P.F P.irreducible.ne_zero
  have hc := originalCumulativeFlag_cumulative P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hsum := sum_numeratorDir_le (fun _ => source) (3*source.d) t y r
    (geometricCumulativeFlag K) ⟨t-y,y-r,r⟩
    (hb.1.trans P.r_weight)
    ((hb.2.1.trans P.y_weight).trans_eq (by dsimp; omega))
    ((hb.2.2.trans P.total_weight).trans_eq (by dsimp; omega))
  calc
    _≤(3*source.d)*(∑ g, (geometricSeeds K P.F P.selected P.seeds g).card) := Nat.mul_le_mul_left _ P.seeds_cover
    _=∑ g, (3*source.d)*(geometricSeeds K P.F P.selected P.seeds g).card := Finset.mul_sum _ _ _
    _≤∑ g, nativeNumerator source t y r (geometricCumulativeFlag K g) := Finset.sum_le_sum (fun g _ => hstage g)
    _≤_ := hsum

open MovingSourceBandIdentity6815 MovingSourceBandLeading6815

theorem native_packet_count (P : Packet x t y r) (source : Source P.F)
    (hk : source.k<2130706433) (hFT : source.T<wt residualTotalWeights P.F)
    (hgates : Gates t y r (source.B-2*source.n0) (source.U-source.n0) (source.T-source.n0)) :
    P.seeds.card≤max (identityPrice t y r)
      (nativeNumerator source t y r ⟨t-y,y-r,r⟩/(3*source.d)+leadingPrice source t y r) := by
  by_cases hp : P.F∣numerator K P.F (w+1)
  · exact (packet_identity_count P hp).trans (le_max_left _ _)
  let good := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (source.leading (polynomialEmbedding K))≠0)
  let bad := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (source.leading (polynomialEmbedding K))=0)
  let PG := P.restrict good (Finset.filter_subset _ _)
  have hmain := native_regular_packet_count PG hp source hk (fun gamma hg => (Finset.mem_filter.mp hg).2)
  have hdiv : good.card≤nativeNumerator source t y r ⟨t-y,y-r,r⟩/(3*source.d) := by
    apply (Nat.le_div_iff_mul_le (by dsimp [Source.d]; omega : 0<3*source.d)).mpr
    exact (Nat.mul_comm good.card (3*source.d)).trans_le hmain
  have hbad : bad.card≤leadingPrice source t y r := packet_z_leading_count P source hFT hgates
  have hpartition : P.seeds.card=good.card+bad.card := by
    unfold good bad
    rw [Nat.add_comm]
    exact (Finset.card_filter_add_card_filter_not _).symm
  rw [hpartition]
  exact (Nat.add_le_add hdiv hbad).trans (le_max_right _ _)

end
end ProximityPrize.SubmissionLower.MovingSourceBandNativeCount6815
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.PortfolioOwners6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 25000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCarrierField6814
open MovingSourceOwnerSplit6814 MovingSourceCoupledClearing6814 MovingSourceNativeFactor6814
open MovingSourceNativeEnvelope6814 MovingSourceMixedOwnerRouting6814
open SecondJetCoefficients SecondJetClearedHelper SecondJetCarrierDichotomy RCN234 RCN156
variable {K : Type} [Field K] [CharP K 2130706433]

def multiplicity (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J : Poly (K:=K)) : ℕ :=
  ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)

theorem unique_owner_data
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (B U T s : ℕ) (hS : Profile S B U T s 2 3)
    (hT : T≤995) (hFT : 2985<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (hu : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J S.P) :
    0<multiplicity F J ∧ multiplicity F J≤order J ∧
    copies3 (multiplicity F J)*slope J≤B ∧
    copies3 (multiplicity F J)*middle J≤U ∧
    copies3 (multiplicity F J)*total J≤T ∧
    copies3 (multiplicity F J)*order J≤s ∧
    (3≤multiplicity F J → 5≤order J) ∧ (asS J).map (carrierMap F)≠0 := by
  have hp := canonical_source_power F S (by rw [hS.2.2.1]; omega) hpos hchar
    (by rw [hS.2.2.2.2.1]; decide)
  have hJne : rootPolynomialMap (carrierMap F) J≠0 := by
    intro hz
    have hd := map_dvd (rootPolynomialMap (carrierMap F)) hJS
    rw [hz,zero_dvd_iff] at hd
    exact hp.1 hd
  have hm : 0<multiplicity F J := (Polynomial.rootMultiplicity_pos hJne).mpr hroot
  have hms : multiplicity F J≤order J := by
    have hh := Polynomial.natDegree_le_of_dvd
      ((rootPolynomialMap (carrierMap F) J).pow_rootMultiplicity_dvd (ratio (carrierMap F) F)) hJne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq (asS_natDegree J))
  have hpower : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3∣rootPolynomialMap (carrierMap F) S.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3∣(asS S.P).map (carrierMap F)
    simpa only [Source.d,hS.2.2.2.2.1] using hp.2
  obtain ⟨e,he,heW,heS⟩ := unique_owner_charges (carrierMap F) (ratio (carrierMap F) F)
    S.P J (source_nonzero F S) hJ hu 3 (multiplicity F J) hJne rfl hpower
  have hqe := copies3_le (multiplicity F J) e hm he
  have hc := MovingSourceOwnerRouting6814.source_caps F S
  rw [hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.1] at hc
  have hb := (Nat.mul_le_mul_right (slope J) hqe).trans ((heW slopeWeights).trans hc.1)
  have hU := (Nat.mul_le_mul_right (middle J) hqe).trans ((heW middleWeights).trans hc.2.1)
  have ht := (Nat.mul_le_mul_right (total J) hqe).trans ((heW totalWeights).trans hc.2.2.1)
  have hs := (Nat.mul_le_mul_right (order J) hqe).trans (heS.trans hc.2.2.2)
  refine ⟨hm,hms,hb,hU,ht,hs,?_,hJne⟩
  intro hm3
  by_contra hn
  have hd : order J=3 ∨ order J=4 := by omega
  have hq := copies3_pos (multiplicity F J) hm
  have htJ : total J≤995 := by
    have hmul := Nat.mul_le_mul_right (total J) hq
    omega
  have hx := MovingSourceTripleOwnerExclusion6814.small_cubic_quartic_rootMultiplicity_lt_three
    F hFT J hJ htJ hd
  change multiplicity F J<3 at hx
  omega

theorem exact_owner_source (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (m s b u t : ℕ) (hm : 0<m) (hms : m≤s)
    (hs : J.degreeOf 1=s) (h2s : 2*s≤b) (hbu : b≤u) (hut : u≤t)
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤b ∧ e 1+e 2+e 3≤u ∧ e 1+e 2+e 3+e 4≤t)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m) :
    ∃ S : Source F, S.P=J ∧ Profile S b u t s (m-1) s := by
  have hS : ∀ e∈J.support, e 1≤s := MvPolynomial.degreeOf_le_iff.mp hs.le
  have hH := carrier_H_nonzero F hpos hchar
  let source : Source F := {
    P:=J, B:=b, U:=u, T:=t, s:=s, k:=m-1, n0:=s
    hS:=hS, hshape:=hshape, hBU:=hbu, hUT:=hut
    hdn:=by omega, hB:=by omega
    hn:=by rw [asS_natDegree,hs]
    hdiv:=by
      intro d hd
      apply (carrierMap_zero_iff F _).mp
      rw [mapped_helper J F (carrierMap F) s d hS hH]
      have hz : ((Polynomial.derivative)^[d] ((asS J).map (carrierMap F))).eval (ratio (carrierMap F) F)=0 :=
        Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot]; omega)
      rw [hz,mul_zero] }
  exact ⟨source,rfl,by repeat' constructor⟩

theorem root_source_profile (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (m s b u t k n0 : ℕ)
    (hkm : k+1≤m) (hkn : k+1≤n0) (hn : n0≤J.degreeOf 1) (hs : J.degreeOf 1≤s)
    (h2n : 2*n0≤b) (hbu : b≤u) (hut : u≤t)
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤b ∧ e 1+e 2+e 3≤u ∧ e 1+e 2+e 3+e 4≤t)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m) :
    ∃ S : Source F, S.P=J ∧ Profile S b u t s k n0 := by
  have hS : ∀ e∈J.support, e 1≤s := MvPolynomial.degreeOf_le_iff.mp hs
  have hH := carrier_H_nonzero F hpos hchar
  let source : Source F := {
    P:=J, B:=b, U:=u, T:=t, s:=s, k:=k, n0:=n0
    hS:=hS, hshape:=hshape, hBU:=hbu, hUT:=hut, hdn:=hkn, hB:=by omega
    hn:=by simpa only [asS_natDegree] using hn
    hdiv:=by
      intro d hd
      apply (carrierMap_zero_iff F _).mp
      rw [mapped_helper J F (carrierMap F) s d hS hH]
      have hz : ((Polynomial.derivative)^[d] ((asS J).map (carrierMap F))).eval (ratio (carrierMap F) F)=0 :=
        Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot]; omega)
      rw [hz,mul_zero] }
  exact ⟨source,rfl,by repeat' constructor⟩

end
end ProximityPrize.SubmissionLower.PortfolioOwners6815
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.PortfolioRootFactors6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 25000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCarrierField6814
open MovingSourceOwnerSplit6814 MovingSourceNativeFactor6814 MovingSourceCoupledClearing6814
open SecondJetCoefficients SecondJetCarrierDichotomy RCN234 RCN156
variable {K : Type} [Field K] [CharP K 2130706433]

theorem root_factor_data (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hFT : S.T<wt residualTotalWeights F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0) :
    (asS J).map (carrierMap F)≠0 ∧
    0<PortfolioOwners6815.multiplicity F J ∧ PortfolioOwners6815.multiplicity F J≤order J ∧
    slope J≤S.B ∧ middle J≤S.U ∧ total J≤S.T ∧ order J≤S.s := by
  have hP := source_nonzero F S
  have hne := carrier_polynomial_nonzero F S.P hP S.T (fun e he => (S.hshape e he).2.2) hFT
  have hJne : rootPolynomialMap (carrierMap F) J≠0 := by
    intro hz
    have hd := map_dvd (rootPolynomialMap (carrierMap F)) hJS
    rw [hz,zero_dvd_iff] at hd
    exact hne hd
  have hm : 0<PortfolioOwners6815.multiplicity F J := (Polynomial.rootMultiplicity_pos hJne).mpr hroot
  have hms : PortfolioOwners6815.multiplicity F J≤order J := by
    have hh := Polynomial.natDegree_le_of_dvd
      ((rootPolynomialMap (carrierMap F) J).pow_rootMultiplicity_dvd (ratio (carrierMap F) F)) hJne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq (asS_natDegree J))
  obtain ⟨Q,hEq⟩ := hJS
  have hQ : Q≠0 := by intro hz; exact hP (by rw [hEq,hz,mul_zero])
  obtain ⟨hb,hu,ht,hs⟩ := MovingSourceOwnerRouting6814.source_caps F S
  rw [hEq,weight_mul _ _ _ hJ.ne_zero hQ] at hb hu ht
  rw [hEq,degreeOf_mul_eq hJ.ne_zero hQ] at hs
  refine ⟨hJne,hm,hms,?_,?_,?_,?_⟩
  all_goals
    dsimp only [MovingSourceCoupledClearing6814.slope,middle,total,order]
    omega

theorem ramified_order_ge_three (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hT : S.T≤995) (hFT : 2985<wt residualTotalWeights F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (hm : 2≤PortfolioOwners6815.multiplicity F J) : 3≤order J := by
  obtain ⟨hne,_,hms,_,_,ht,_⟩ := root_factor_data F S (by omega) J hJ hJS hroot
  by_contra h
  have he : order J=2 := by omega
  have hx := QuadraticRamifiedOwner6815.quadratic_rootMultiplicity_lt_two F J hJ 995
    (ht.trans hT) (by omega) (by simpa only [asS_natDegree,order] using he)
  change PortfolioOwners6815.multiplicity F J<2 at hx
  omega

theorem third_root_cases {E : Type} [Field E]
    (psi : Poly (K:=K) →+* Polynomial E) (z : E)
    (P J D : Poly (K:=K)) (hP : psi P≠0) (hJ : Irreducible J) (hD : Irreducible D)
    (hcop : IsRelPrime J D) (hJP : J∣P) (hDP : D∣P)
    (hJroot : (psi J).rootMultiplicity z=1) (hDroot : (psi D).rootMultiplicity z=1)
    (hpow : (Polynomial.X-Polynomial.C z)^3∣psi P) :
    J^2*D∣P ∨ D^2*J∣P ∨ ∃ Q : Poly (K:=K), Irreducible Q ∧ (psi Q).eval z=0 ∧
      IsRelPrime J Q ∧ IsRelPrime D Q ∧ J*D*Q∣P := by
  obtain ⟨Q,hQ,hQroot,hdiv⟩ := RetainedSharedRemainder6815.third_root_divisor
    psi z P J D hP hcop hJP hDP hJroot hDroot hpow
  by_cases hqJ : Associated Q J
  · left
    have hm := mul_dvd_mul_left (J*D) hqJ.symm.dvd
    have h := hm.trans hdiv
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using h
  by_cases hqD : Associated Q D
  · right; left
    have hm := mul_dvd_mul_left (J*D) hqD.symm.dvd
    have h := hm.trans hdiv
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using h
  right; right
  refine ⟨Q,hQ,hQroot,?_,?_,hdiv⟩
  · apply hJ.isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hqJ (hJ.associated_of_dvd hQ hd).symm
  · apply hD.isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hqD (hD.associated_of_dvd hQ hd).symm

end
end ProximityPrize.SubmissionLower.PortfolioRootFactors6815
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.PortfolioLinearPacket6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN334
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 MovingSourceBandLeading6815
open MovingSourceLinearFlow6814 MovingSourceCarrierField6814 MovingSourceLinearSeedAssembly6814
open MovingSourcePairEnvelope6814 MovingSourceDenominatorSeeds6814
open PortfolioLinearRoute6815 PortfolioLinearProper6815 PortfolioLinearExceptions6815
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}

def linearPrice (first delay : FlagDegree) (t y r b u l : ℕ) : ℕ :=
  r*AsymmetricHelper.leftRegularCountCap (pair t y r b u l)+
    flagMixed ⟨t-y,y-r,r⟩ first delay+
    80901*flagMixed ⟨t-y,y-r,r⟩ first unitYZFlag+
    flagMixed ⟨t-y,y-r,r⟩ first unitAllFlag

theorem packet_count
    (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) (first delay : FlagDegree)
    (hroute : Route P.F J first delay) (b u l : ℕ)
    (hH : wt residualSWeights (linearH J)≤b ∧ wt residualYSWeights (linearH J)≤u ∧
      wt residualTotalWeights (linearH J)≤l)
    (hgates : Gates t y r b u l)
    (hsmall : flagMixed ⟨t-y,y-r,r⟩ first unitZFlag<2130706433) :
    P.seeds.card≤max (identityPrice t y r) (linearPrice first delay t y r b u l) := by
  by_cases hp : P.F∣numerator K P.F (RCN326.w+1)
  · exact (packet_identity_count P hp).trans (le_max_left _ _)
  let cap := AsymmetricHelper.leftRegularCountCap (pair t y r b u l)
  let bad := P.seeds.filter (fun gamma => MvPolynomial.eval
    (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (surfaceMap (polynomialEmbedding K) (linearH J))=0)
  let PB := P.restrict bad (Finset.filter_subset _ _)
  have hrel : IsRelPrime P.F (linearH J) := P.irreducible.isRelPrime_iff_not_dvd.mpr
    (fun hd => hroute.denominator ((carrierMap_zero_iff P.F _).mpr hd))
  have hbad : bad.card≤cap := by
    apply proper_cut_count PB (linearH J) b u l hrel hH hgates
    intro gamma hg
    have hh := (Finset.mem_filter.mp hg).2
    rw [RCN170.canonical_selectedPoint_surface_evaluation] at hh
    change RCN319.specialization K (P.selected gamma) gamma (linearH J)=0
    exact polynomialEmbedding_injective K (by simpa only [map_zero] using hh)
  have hb := geometricCumulativeFlag_budgets P.F P.irreducible.ne_zero
  have hc := originalCumulativeFlag_cumulative P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hry : r≤y := by have := P.ylow; omega
  have hyt := P.yt
  have hsum (W : FlagDegree) : (∑ g : GeometricFactor K P.F,
      flagMixed (geometricCumulativeFlag K g) first W)≤flagMixed ⟨t-y,y-r,r⟩ first W := by
    apply sum_flagMixed_le_of_cumulative
    · exact hb.1.trans P.r_weight
    · simpa only [Nat.sub_add_cancel hry] using hb.2.1.trans P.y_weight
    · have ht := hb.2.2.trans P.total_weight
      exact ht.trans_eq (by change t=(t-y)+(y-r)+r; omega)
  have hcard : Fintype.card (GeometricFactor K P.F)≤r := by
    have hone (g : GeometricFactor K P.F) : 1≤(geometricCumulativeFlag K g).all := by
      have hd := (P.stage g).y_dependent
      have hle : (P.stage g).G.degreeOf 1≤(geometricCumulativeFlag K g).all :=
        MvPolynomial.degreeOf_le_iff.mpr (fun e he => ((P.stage g).flag_support e he).1)
      omega
    have hh := (Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => hone g)).trans (hb.1.trans P.r_weight)
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hh
  let cost (fl : FlagDegree) := flagMixed fl first delay+
    (flagMixed fl first unitYZFlag+flagMixed fl first unitAllFlag)+80900*flagMixed fl first unitYZFlag
  have hsingle (g : GeometricFactor K P.F) :
      (geometricSeeds K P.F P.selected P.seeds g).card≤cap+cost (geometricCumulativeFlag K g) := by
    let S := P.stage g
    letI : Fact (Irreducible S.F) := ⟨P.irreducible⟩
    have hfirst := P.stage_proper hp g
    have hsmall' : flagMixed (geometricCumulativeFlag K g) first unitZFlag<2130706433 :=
      (mixed_mono_left _ ⟨t-y,y-r,r⟩ first unitZFlag (by
        have h := P.stage_flag g
        change _≤r ∧ _≤y-r+r ∧ _≤t-y+(y-r)+r
        omega)).trans_lt hsmall
    have hproper := denominator_proper S J hroute
    have hden : (denominatorSeeds S J).card≤cap := by
      apply (Finset.card_le_card (show denominatorSeeds S J⊆bad from ?_)).trans hbad
      intro gamma hg
      exact Finset.mem_filter.mpr
        ⟨geometricSeeds_subset K P.F P.selected P.seeds g (Finset.mem_filter.mp hg).1,
          (Finset.mem_filter.mp hg).2⟩
    have hd := wide_proper_seeds_sum_le S hfirst J hroute (geometricCumulativeFlag K g) S.flag_support hsmall'
    have hz := wide_constant_seed_sum_le S hfirst J hroute hproper (geometricCumulativeFlag K g) S.flag_support
    have ht := wide_persistent_seed_sum_le S hfirst J hroute hproper (geometricCumulativeFlag K g)
      S.flag_support hsmall' 181245 P.D t r P.nodeCount (P.stage_agreement g) (by decide) P.Dlow P.Dchar P.box
    have hh := (linear_seed_cover S hfirst J).trans (Nat.add_le_add hden (Nat.add_le_add hd (Nat.add_le_add hz ht)))
    exact hh.trans_eq (by dsimp only [cost]; ring)
  have hcost : (∑ g : GeometricFactor K P.F, cost (geometricCumulativeFlag K g))≤cost ⟨t-y,y-r,r⟩ := by
    unfold cost
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    exact Nat.add_le_add (Nat.add_le_add (hsum delay) (Nat.add_le_add (hsum unitYZFlag) (hsum unitAllFlag)))
      (Nat.mul_le_mul_left 80900 (hsum unitYZFlag))
  have htotal : P.seeds.card≤r*cap+cost ⟨t-y,y-r,r⟩ := by
    have hh := P.seeds_cover.trans (Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => hsingle g))
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
    exact hh.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hcard) hcost)
  apply (htotal.trans_eq ?_).trans (le_max_right _ _)
  dsimp [linearPrice,cap,cost]
  ring

end
end ProximityPrize.SubmissionLower.PortfolioLinearPacket6815
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.PortfolioLinearShape6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814
open MovingSourceReducedTailWeights6814 PortfolioLinearRoute6815 PortfolioLinearPacket6815
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingSourceCarrierField6814 SecondJetCoefficients SecondJetCarrierDichotomy
variable {K : Type} [Field K]

theorem tail_weights (J : Poly (K:=K)) (B U L : ℕ) (hB : 2≤B) (hBU : B≤U) (hUL : U≤L)
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤L)
    (n : ℕ) :
    wt residualSWeights (numerators (linearH J) (linearG J) n)≤(2*B-3)*n ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+(2*U-2)*n ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+(2*L-2)*n := by
  have hh := linear_coefficient_weights J B U L hshape
  have hR := numerator_weight residualSWeights (linearH J) (linearG J) (B-2) (B-1)
    hh.1.1 (by change _≤B-1+1; omega) (by change B-2≤B-1+0; omega)
    (by change 1+(B-2)≤B-1+0; omega) n
  have hY := numerator_weight residualYSWeights (linearH J) (linearG J) (U-1) (U-1)
    hh.1.2.1 (by change _≤U-1+1; omega) (by change U-1≤U-1+0; omega)
    (by change 1+(U-1)≤U-1+1; omega) n
  have hT := numerator_weight residualTotalWeights (linearH J) (linearG J) (L-1) (L-1)
    hh.1.2.2 (by change _≤L-1+1; omega) (by change L-1≤L-1+0; omega)
    (by change 1+(L-1)≤L-1+1; omega) n
  have hr : (B-2)+(B-1)=2*B-3 := by omega
  have hy : (U-1)+(U-1)=2*U-2 := by omega
  have ht : (L-1)+(L-1)=2*L-2 := by omega
  exact ⟨by simpa only [show residualSWeights 1=0 from rfl,zero_add,hr,Nat.mul_comm] using hR,
    by simpa only [show residualYSWeights 1=1 from rfl,hy,Nat.mul_comm] using hY,
    by simpa only [show residualTotalWeights 1=1 from rfl,ht,Nat.mul_comm] using hT⟩

variable [CharP K 2130706433] {I : Type} {x : I → K} {t y r : ℕ}

theorem packet_count_of_shape
    (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (hJ : J≠0) (hs : J.degreeOf 1=1)
    (B U L : ℕ) (hB : 2≤B) (hBU : B≤U) (hUL : U≤L)
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤L)
    (hFT : L<wt residualTotalWeights P.F)
    (hroot : ((asS J).map (carrierMap P.F)).eval (ratio (carrierMap P.F) P.F)=0)
    (hgates : Gates t y r (B-2) (U-1) (L-1))
    (hsmall : flagMixed ⟨t-y,y-r,r⟩ (firstFlag (2*B-3) (2*U-2) (2*L-2)) unitZFlag<2130706433) :
    P.seeds.card≤max (identityPrice t y r)
      (linearPrice (firstFlag (2*B-3) (2*U-2) (2*L-2))
        (delayFlag (2*B-3) (2*U-2) (2*L-2)) t y r (B-2) (U-1) (L-1)) := by
  have hchar := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega : r<2130706433)
  have route := route_of_weights P.F J hJ hs P.rdegree hchar L
    (fun e he => (hshape e he).2.2) hFT hroot (2*B-3) (2*U-2) (2*L-2)
    (by omega) (by omega) (tail_weights J B U L hB hBU hUL hshape)
  exact packet_count P J _ _ route (B-2) (U-1) (L-1)
    (linear_coefficient_weights J B U L hshape).1 hgates hsmall

end
end ProximityPrize.SubmissionLower.PortfolioLinearShape6815
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.PortfolioPacketHelpers6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815
open MovingSourcePairEnvelope6814 MovingSourceCoupledClearing6814
open PortfolioSource6815
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem helper_count {t y r : ℕ} (p : Parameters) (nodes : I ↪ K)
    (P : Packet (nodes : I → K) t y r) (Q : MvPolynomial (Fin 4) K)
    (hh : ProperHelper p P.F Q r y t nodes P.u0 P.u1)
    (hg : Gates t y r (p.B+p.s*(r-1)) (p.U+p.s*(y-1)) (p.L+p.s*(t-1))) :
    P.seeds.card≤AsymmetricHelper.leftRegularCountCap
      (pair t y r (p.B+p.s*(r-1)) (p.U+p.s*(y-1)) (p.L+p.s*(t-1))) := by
  classical
  apply proper_cut_count P Q _ _ _ hh.1 hh.2.1 hg
  intro gamma hgamma
  exact hh.2.2 (P.selected gamma) (P.degree gamma hgamma) gamma
    (P.nodes.filter (fun i => (P.selected gamma).eval (nodes i)=P.u0 i+gamma*P.u1 i))
    (P.agreement gamma hgamma)
    (fun i hi => by simpa only [mul_comm] using (Finset.mem_filter.mp hi).2)
    (P.solution gamma hgamma)

theorem pair_characteristic_gates (p q : FlagDegree)
    (hp : p.zOnly+p.yz+p.all≤8192) (hq : q.zOnly+q.yz+q.all≤8192) :
    flagMixed p q unitZFlag<2130706433 ∧ flagMixed p q unitYZFlag<2130706433 := by
  have hcP : CumulativeLe p ⟨0,0,8192⟩ := by
    change p.all≤8192 ∧ p.yz+p.all≤8192 ∧ p.zOnly+p.yz+p.all≤8192
    omega
  have hcQ : CumulativeLe q ⟨0,0,8192⟩ := by
    change q.all≤8192 ∧ q.yz+q.all≤8192 ∧ q.zOnly+q.yz+q.all≤8192
    omega
  exact ⟨(mixed_mono_pair _ _ _ _ unitZFlag hcP hcQ).trans_lt (by decide),
    (mixed_mono_pair _ _ _ _ unitYZFlag hcP hcQ).trans_lt (by decide)⟩

end
end ProximityPrize.SubmissionLower.PortfolioPacketHelpers6815
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.PortfolioCost6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped BigOperators
open RCN095 RCN135 RCN136 RCN156 RCN234
open MovingFiberThreeSources6811 MovingSourceCoupledClearing6814
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingSourceBandPairCount6815 MovingSourceBandNativeCount6815
open MovingSourcePairStageSupplier6814 MovingSourcePairRetainedStage6814
open MovingSourcePairEnvelope6814

structure Degrees where
  B : ℕ
  U : ℕ
  T : ℕ
  k : ℕ
  n0 : ℕ
  deriving DecidableEq

def Degrees.d (z : Degrees) := z.k+1
def Degrees.flag (z : Degrees) := SecondJetRelaxedFlag.budgetFlag z.B z.U z.T z.d z.n0
def parent (t y r : ℕ) : FlagDegree := ⟨t-y,y-r,r⟩
def leading (z : Degrees) (t y r : ℕ) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (pair t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
def pairCost (z : Degrees) (delta : ℕ) (p q : FlagDegree) (t y r : ℕ) : ℕ :=
  pairNumerator (z.d*delta) (delta*flagMixed (parent t y r) unitZFlag z.flag)
    (z.d*flagMixed p q unitYZFlag) (z.d*flagMixed p q unitAllFlag)
    t y r (parent t y r)/(3*(z.d*delta))

variable {K I : Type} [Field K] [CharP K 2130706433]
variable {F : MvPolynomial (Fin 4) K}

def Fits (S : Source F) (z : Degrees) : Prop :=
  S.B=z.B ∧ S.U=z.U ∧ S.T=z.T ∧ S.k=z.k ∧ S.n0=z.n0

theorem fits_degree (S : Source F) (z : Degrees) (h : Fits S z) : S.d=z.d := by
  simp only [Source.d,Degrees.d,h.2.2.2.1]
theorem fits_flag (S : Source F) (z : Degrees) (h : Fits S z) : S.flag=z.flag := by
  simp only [Source.flag,Degrees.flag,h.1,h.2.1,h.2.2.1,h.2.2.2.2,fits_degree S z h]
theorem fits_leading (S : Source F) (z : Degrees) (h : Fits S z) (t y r : ℕ) :
    leadingPrice S t y r=leading z t y r := by
  simp only [leadingPrice,leading,h.1,h.2.1,h.2.2.1,h.2.2.2.2]

theorem stageCost_le (SZ SP SQ : Source F) (z : Degrees) (hZ : Fits SZ z)
    (delta : ℕ) (p q : FlagDegree) (t y r : ℕ)
    (hp : CumulativeLe (ordinaryFlag SP.P) p) (hq : CumulativeLe (ordinaryFlag SQ.P) q) :
    pairStageCost SZ SP SQ delta t y r (parent t y r)≤pairCost z delta p q t y r := by
  unfold pairStageCost stageScale pairCost
  rw [fits_degree SZ z hZ,fits_flag SZ z hZ]
  apply Nat.div_le_div_right
  have hu := mixed_mono_pair _ _ _ _ unitYZFlag hp hq
  have hv := mixed_mono_pair _ _ _ _ unitAllFlag hp hq
  simp only [pairNumerator,price,parent]
  gcongr

variable {x : I → K} {t y r : ℕ}

theorem pair_count_of_bounds
    (P : Packet x t y r) (SZ SP SQ : Source P.F)
    (z : Degrees) (hZ : Fits SZ z) (hFT : z.T<wt residualTotalWeights P.F)
    (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0<delta) (hchar : delta≤2130706433)
    (hSP : delta≤SP.d) (hSQ : delta≤SQ.d)
    (p q : FlagDegree) (hp : CumulativeLe (ordinaryFlag SP.P) p)
    (hq : CumulativeLe (ordinaryFlag SQ.P) q)
    (hz : flagMixed p q unitZFlag<2130706433)
    (hu : flagMixed p q unitYZFlag<2130706433) :
    P.seeds.card≤max (identityPrice t y r) (pairCost z delta p q t y r+leading z t y r) := by
  have hg' : Gates t y r (SZ.B-2*SZ.n0) (SZ.U-SZ.n0) (SZ.T-SZ.n0) := by
    simpa only [hZ.1,hZ.2.1,hZ.2.2.1,hZ.2.2.2.2] using hg
  have hc := pair_packet_count P SZ SP SQ (by simpa only [hZ.2.2.1] using hFT)
    (by simpa only [hZ.2.2.2.1] using hk) hg' hcop delta hd hchar hSP hSQ
    ((mixed_mono_pair _ _ _ _ unitZFlag hp hq).trans_lt hz)
    ((mixed_mono_pair _ _ _ _ unitYZFlag hp hq).trans_lt hu)
  have hp' := stageCost_le SZ SP SQ z hZ delta p q t y r hp hq
  exact hc.trans (max_le_max le_rfl (Nat.add_le_add hp' (fits_leading SZ z hZ t y r).le))

def nativeScalar (z : Degrees) (t y r : ℕ) : ℕ :=
  z.d*MovingSourceBandPairArithmetic6814.fixedNumerator t y r (parent t y r)+
    ∑ j : Fin 3, MovingSourceBandPairArithmetic6814.coefficient t y r j*
      flagMixed (parent t y r) (direction j) z.flag

theorem native_scalar_eq (S : Source F) (z : Degrees) (h : Fits S z) (t y r : ℕ) :
    nativeNumerator S t y r (parent t y r)=nativeScalar z t y r := by
  have hd : 0<z.d := by dsimp [Degrees.d]; omega
  unfold nativeNumerator HFreeDir6813.numeratorDir nativeScalar
  simp only [fits_degree S z h,fits_flag S z h,Nat.mul_div_cancel_left z.d (by decide : 0<3),
    Nat.div_self (by omega : 0<3*z.d),Nat.mul_div_cancel 3 hd,mul_one,Finset.sum_add_distrib]
  refine congrArg₂ (fun a b : ℕ => a+b) ?_ ?_
  · unfold MovingSourceBandPairArithmetic6814.fixedNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    unfold MovingSourceBandPairArithmetic6814.coefficient
    simp only [RCN326.w,RCN327.w]
    ring

theorem native_count_of_degrees
    (P : Packet x t y r) (S : Source P.F) (z : Degrees) (h : Fits S z)
    (hFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0)) :
    P.seeds.card≤max (identityPrice t y r) (nativeScalar z t y r/(3*z.d)+leading z t y r) := by
  have hg' : Gates t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0) := by
    simpa only [h.1,h.2.1,h.2.2.1,h.2.2.2.2] using hg
  have hc := native_packet_count P S (by simpa only [h.2.2.2.1] using hk)
    (by simpa only [h.2.2.1] using hFT) hg'
  change P.seeds.card≤max (identityPrice t y r)
    (nativeNumerator S t y r (parent t y r)/(3*S.d)+leadingPrice S t y r) at hc
  simpa only [native_scalar_eq S z h t y r,fits_degree S z h,fits_leading S z h t y r] using hc

end
end ProximityPrize.SubmissionLower.PortfolioCost6815
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.PortfolioNativeOwner6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open PortfolioCost6815

def ownerDegrees (m s b u hi : ℕ) : Degrees := ⟨b,max b u,max b hi,m-1,s⟩

variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}

theorem packet_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (m s b u hi cap : ℕ) (hm : 0<m) (hms : m≤s)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J≤hi)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hFT : max b hi<wt residualTotalWeights P.F) (hk : m-1<2130706433)
    (hg : Gates t y r (b-2*s) (max b u-s) (max b hi-s))
    (hfit : nativeScalar (ownerDegrees m s b u hi) t y r/(3*(ownerDegrees m s b u hi).d)+
      leading (ownerDegrees m s b u hi) t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hn := source_nested J
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤b ∧ e 1+e 2+e 3≤max b u ∧
      e 1+e 2+e 3+e 4≤max b hi := by
    intro e he
    have hb' := le_weightedTotalDegree slopeWeights he
    have hu' := le_weightedTotalDegree middleWeights he
    have ht' := (le_weightedTotalDegree totalWeights he).trans ht
    change Finsupp.weight slopeWeights e≤slope J at hb'
    change Finsupp.weight middleWeights e≤middle J at hu'
    rw [hb] at hb'
    rw [hu] at hu'
    simp [weight_coords,slopeWeights,middleWeights,totalWeights] at hb' hu' ht'
    exact ⟨by omega,hu'.trans (le_max_right _ _),ht'.trans (le_max_right _ _)⟩
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨S,hSJ,hprofile⟩ := PortfolioOwners6815.exact_owner_source P.F P.rdegree hchar
    J m s b (max b u) (max b hi) hm hms hs (by rw [hs,hb] at hn; omega)
    (le_max_left _ _) (max_le_max le_rfl (by rw [hu] at hn; omega)) hshape hroot
  have hS : Fits S (ownerDegrees m s b u hi) :=
    ⟨hprofile.1,hprofile.2.1,hprofile.2.2.1,hprofile.2.2.2.2.1,hprofile.2.2.2.2.2⟩
  have hc := native_count_of_degrees P S _ hS hFT hk hg
  exact hc.trans (max_le_max le_rfl hfit)

theorem exists_owner_source (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (m s b u hi : ℕ) (hm : 0<m) (hms : m≤s)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J≤hi)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 : ∃ S : MovingFiberThreeSources6811.Source P.F, S.P=J ∧ Fits S (ownerDegrees m s b u hi) := by
  have hn := source_nested J
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤b ∧ e 1+e 2+e 3≤max b u ∧
      e 1+e 2+e 3+e 4≤max b hi := by
    intro e he
    have hb' := le_weightedTotalDegree slopeWeights he
    have hu' := le_weightedTotalDegree middleWeights he
    have ht' := (le_weightedTotalDegree totalWeights he).trans ht
    change Finsupp.weight slopeWeights e≤slope J at hb'
    change Finsupp.weight middleWeights e≤middle J at hu'
    rw [hb] at hb'
    rw [hu] at hu'
    simp [weight_coords,slopeWeights,middleWeights,totalWeights] at hb' hu' ht'
    exact ⟨by omega,hu'.trans (le_max_right _ _),ht'.trans (le_max_right _ _)⟩
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨S,hSJ,hprofile⟩ := PortfolioOwners6815.exact_owner_source P.F P.rdegree hchar
    J m s b (max b u) (max b hi) hm hms hs (by rw [hs,hb] at hn; omega)
    (le_max_left _ _) (max_le_max le_rfl (by rw [hu] at hn; omega)) hshape hroot
  have hS : Fits S (ownerDegrees m s b u hi) :=
    ⟨hprofile.1,hprofile.2.1,hprofile.2.2.1,hprofile.2.2.2.2.1,hprofile.2.2.2.2.2⟩
  exact ⟨S,hSJ,hS⟩

end
end ProximityPrize.SubmissionLower.PortfolioNativeOwner6815
end MergedPart11
section MergedPart12
namespace ProximityPrize.SubmissionLower.PortfolioHighOwner6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open PortfolioCost6815
variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}

def degrees (B U L : ℕ) : Degrees := ⟨B,U,L,6,7⟩

theorem packet_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (m B U L s cap : ℕ)
    (hm : 7≤m) (hord : m≤order J) (hs : order J≤s)
    (hb : slope J≤B) (hu : middle J≤U) (ht : total J≤L)
    (hB : 14≤B) (hBU : B≤U) (hUL : U≤L) (hFT : L<wt residualTotalWeights P.F)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hg : Gates t y r (B-14) (U-7) (L-7))
    (hfit : nativeScalar (degrees B U L) t y r/21+leading (degrees B U L) t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤L := by
    intro e he
    have h1 := (le_weightedTotalDegree slopeWeights he).trans hb
    have h2 := (le_weightedTotalDegree middleWeights he).trans hu
    have h3 := (le_weightedTotalDegree totalWeights he).trans ht
    constructor
    · simpa [weight_coords,slopeWeights,Nat.mul_comm] using h1
    constructor
    · simpa [weight_coords,middleWeights] using h2
    · simpa [weight_coords,totalWeights] using h3
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨S,hSJ,hprofile⟩ := PortfolioOwners6815.root_source_profile P.F P.rdegree hchar J
    m s B U L 6 7 hm (by decide) (by change 7≤order J; omega) hs hB hBU hUL hshape hroot
  have hS : Fits S (degrees B U L) :=
    ⟨hprofile.1,hprofile.2.1,hprofile.2.2.1,hprofile.2.2.2.2.1,hprofile.2.2.2.2.2⟩
  have hc := native_count_of_degrees P S _ hS hFT (by change 6<2130706433; decide) hg
  exact hc.trans (max_le_max le_rfl hfit)

end
end ProximityPrize.SubmissionLower.PortfolioHighOwner6815
end MergedPart12
section MergedPart13
namespace ProximityPrize.SubmissionLower.PortfolioUniformBudgets6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open RCN260 RCN294 RCN234 RCN156
open MovingSourceBandLeading6815 MovingSourceBandGeometry6815 PortfolioSource6815

theorem count_mono (t y r b u l capT capY capR capB capU capL : ℕ)
    (ht : t≤capT) (hy : y≤capY) (hr : r≤capR) (hb : b≤capB) (hu : u≤capU) (hl : l≤capL) :
    AsymmetricHelper.leftRegularCountCap (pair t y r b u l)≤
      AsymmetricHelper.leftRegularCountCap (pair capT capY capR capB capU capL) := by
  unfold AsymmetricHelper.leftRegularCountCap
  apply Nat.div_le_div_right
  simp only [AsymmetricHelper.leftRegularNumerator,pair,UnequalParameters.errors,
    UnequalParameters.gap,UnequalParameters.leftAgreement,UnequalParameters.mixedCost,dot]
  gcongr

theorem gates_mono (t y r b u l capT capY capR capB capU capL : ℕ)
    (ht : t≤capT) (hy : y≤capY) (hr : r≤capR) (hb : b≤capB) (hu : u≤capU) (hl : l≤capL)
    (h : Gates capT capY capR capB capU capL) : Gates t y r b u l := by
  rcases h with ⟨hY,hR,hZ⟩
  unfold Gates pair UnequalParameters.mixedCost at *
  constructor
  · apply lt_of_le_of_lt _ hY
    dsimp only
    gcongr
  constructor
  · apply lt_of_le_of_lt _ hR
    dsimp only
    gcongr
  · apply lt_of_le_of_lt _ hZ
    dsimp only
    gcongr

theorem maximum_helper : Gates 4100 59 13 1024 4224 266432 ∧
    AsymmetricHelper.leftRegularCountCap (pair 4100 59 13 1024 4224 266432)<1000000000000000 := by
  unfold Gates
  decide +kernel

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {x : I → K} {t y r : ℕ}

theorem helper_parameters (p : Parameters) (P : Packet x t y r)
    (hb : p.B≤256) (hu : p.U≤512) (hl : p.L≤4096) (hs : p.s≤64) :
    p.B+p.s*(r-1)≤1024 ∧ p.U+p.s*(y-1)≤4224 ∧ p.L+p.s*(t-1)≤266432 := by
  have hr := P.rhigh
  have hy := P.yhigh
  have ht := P.thigh
  have hrr : p.s*(r-1)≤64*12 := Nat.mul_le_mul hs (by omega)
  have hyy : p.s*(y-1)≤64*58 := Nat.mul_le_mul hs (by omega)
  have htt : p.s*(t-1)≤64*4099 := Nat.mul_le_mul hs (by omega)
  omega

theorem helper_count (p : Parameters) (nodes : I ↪ K) (P : Packet (nodes : I → K) t y r)
    (hb : p.B≤256) (hu : p.U≤512) (hl : p.L≤4096) (hs : p.s≤64)
    (Q : MvPolynomial (Fin 4) K) (hQ : ProperHelper p P.F Q r y t nodes P.u0 P.u1) :
    P.seeds.card<1000000000000000 := by
  obtain ⟨hr,hy,ht⟩ := helper_parameters p P hb hu hl hs
  have hg := gates_mono t y r _ _ _ 4100 59 13 1024 4224 266432
    P.thigh P.yhigh P.rhigh hr hy ht maximum_helper.1
  exact (PortfolioPacketHelpers6815.helper_count p nodes P Q hQ hg).trans_lt
    ((count_mono t y r _ _ _ 4100 59 13 1024 4224 266432
      P.thigh P.yhigh P.rhigh hr hy ht).trans_lt maximum_helper.2)

end
end ProximityPrize.SubmissionLower.PortfolioUniformBudgets6815
end MergedPart13
section MergedPart14
namespace ProximityPrize.SubmissionLower.PortfolioSourceCatalogue6815
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

theorem small (i : Fin 75) : (profile i).B≤256 ∧ (profile i).U≤512 ∧
    (profile i).L≤4096 ∧ (profile i).s≤64 ∧ (profile i).L+(profile i).s≤8192 := by
  fin_cases i <;> decide +kernel

end ProximityPrize.SubmissionLower.PortfolioSourceCatalogue6815
end MergedPart14
