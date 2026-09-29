import ProximityPrize.SubmissionLower.MovingSourceBandGeometry6814

/-! The proved shared outer count with variable cell caps and Z source.
This keeps actual normal and moving budgets; no price or count is assumed. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandSharedCosts6814
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
open MovingSourceBandGeometry6814 MovingSourceOuterStageFrames6814 MovingSourceSuppliedFrame6814
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
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0<delta) (hd3 : delta≤3)
    (hP : delta≤SP.d) (hQ : delta≤SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag≤6014)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag≤delta*28420) :
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

#print axioms exists_shared_packet_cost
end
end ProximityPrize.SubmissionLower.MovingSourceBandSharedCosts6814
