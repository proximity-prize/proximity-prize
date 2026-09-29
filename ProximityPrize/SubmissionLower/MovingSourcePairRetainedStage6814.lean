import ProximityPrize.SubmissionLower.MovingSourcePairFirstTailBudget6814

/-! The leading-regular retained Stage count with mixed source-pair prices.
Both the weighted normal count and the raw moving count are constructed;
the old local delay/tangent provider consumes their combined budget. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePairRetainedStage6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 35000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN084 RCN085 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTransportC2 LocatorHybridTailProvider
open BoundaryTailProvider CommonLinearChannels6807 MovingFiberThreeSources6811 MovingFiberRetainedStage6811 HFreeDir6813
open MovingSourcePairFirstChannel6814 MovingSourcePairFirstTailBudget6814
open MovingSourcePairMovingDegrees6814 MovingSourceExtendedPointCount6814
local notation "w" => RCN326.w

def price (W : FlagDegree) (z u v : ℕ) : ℕ := W.zOnly*z+W.yz*u+W.all*v
def pairNumerator (scale z u v t y r : ℕ) (flag : FlagDegree) : ℕ :=
  scale*(∑ j : Fin 3, weight (cellNormal t y r) j*flagMixed flag
    (hfreeFirstDir t y r j) (MovingFiberThreeSources6811.direction j))+
    4*(w+1)*price (cellNormal t y r) z u v+
    3*65539*price (rawFirstFlag t y r) z u v

private theorem mixed_swap_right (p q r : FlagDegree) : flagMixed p q r=flagMixed p r q := by
  simp only [flagMixed]
  ring

private theorem sum_two_scaled {A : Type} [Fintype A] (n x y : A → ℕ) (a b : ℕ) :
    (∑ i, n i*(a*x i+b*y i))=a*(∑ i, n i*x i)+b*(∑ i, n i*y i) := by
  simp only [Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_left_comm]

theorem sum_weight_price (W : FlagDegree) (z u v : ℕ) :
    (∑ j : Fin 3, weight W j*price (MovingFiberThreeSources6811.direction j) z u v)=price W z u v := by
  simp [Fin.sum_univ_three,weight,MovingFiberThreeSources6811.direction,price,unitZFlag,unitYZFlag,unitAllFlag]

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)

theorem retained_stage_pair_bound
    (t y r scale zCap uCap vCap : ℕ) (hr3 : 3≤r) (hb : r+2≤y) (hyt : y≤t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 errorCap flag w (cellSupport t y r))
    (SZ : Source S.F) (hscale : 0<scale)
    (hfree : HFreeStageDir S)
    (hproper : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all<2130706433 ∧ flag.all<2130706433 ∧ flag.zOnly+flag.yz+flag.all<2130706433)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag<2130706433)
    (hlinear : 2*(flag.zOnly+flag.yz+flag.all)<2130706433)
    (hgate : errorCap+1≤(cellNormal t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1) →
      (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card≤
        (errorCap+1)*(BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixedRed).yzCost C)
    (hgood : ∀ gamma∈Gamma, MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
      (SZ.leading (polynomialEmbedding K))≠0)
    (hraw : ∀ Q A : MvPolynomial (Fin 3) Ω, (2 : MvPolynomial (Fin 3) Ω)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ScaledPointBudget S.F SZ Q A scale zCap uCap vCap)
    (hfirst : ∀ Q A : MvPolynomial (Fin 3) Ext, (2 : MvPolynomial (Fin 3) Ext)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget (algebraMap Ω Ext) S.F SZ Q A scale zCap uCap vCap) :
    Gamma.card≤pairNumerator scale zCap uCap vCap t y r flag/(3*scale) := by
  classical
  let base := BoundaryTailReduced.reducedBaseOrd S hproper hflagChar hmixedRed
  let Uold := BoundaryTailReduced.reducedUnitFamily S hproper hflagChar hmixedRed
  let unit := unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S) Uold base
  let Bfam := BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixedRed
  let common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed
  let active : Finset (FirstTailComponent S) := Finset.univ.filter
    (fun C => SZ.leading (polynomialEmbedding K) ∉ C.1)
  have hlead (C : active) : SZ.leading (polynomialEmbedding K) ∉ C.val.1 :=
    (Finset.mem_filter.mp C.property).2
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = r+(y-r) := by dsimp [cellB,cellS]; omega
  have htot : cellA t y+cellB y r+cellS r+3 = r+(y-r)+(t-y) := by
    dsimp [cellA,cellB,cellS]; omega
  have hR : WeightBound residualSWeights S.F (r : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualSWeights S.F ≤ r by
      simpa only [cellSupport,RCN198.support,hs] using Hsupport.s_weight)
  have hYR : WeightBound residualYSWeights S.F ((r+(y-r) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualYSWeights S.F ≤ r+(y-r) by
      simpa only [cellSupport,RCN198.support,hys] using Hsupport.ys_weight)
  have hAll : WeightBound residualTotalWeights S.F ((r+(y-r)+(t-y) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualTotalWeights S.F ≤ r+(y-r)+(t-y) by
      simpa only [cellSupport,RCN198.support,htot] using Hsupport.total_weight)

  obtain ⟨budget,hcost,hmoving⟩ := exists_first_tail_pair_budget S.F SZ S.G S.G_dvd_surface
    (cellA t y) (cellB y r) (cellS r) w (by decide)
    Hsupport.coordinate_bounds.2.1 Hsupport.ys_weight Hsupport.total_weight
    base flag (cellFirstTail t y r) unit active (fun C hC => (Finset.mem_filter.mp hC).2)
    scale zCap uCap vCap hraw
  have hcost' (C : FirstTailComponent S) :
      (budget C).zCost = Bfam.zCost C ∧ (budget C).yzCost = Bfam.yzCost C ∧
        (budget C).allCost = Bfam.allCost C := by
    obtain ⟨hz,hy,ha⟩ := hcost C
    obtain ⟨ez,ey,ea⟩ :=
      unitFamilyOfCongruentCut_costs (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    exact ⟨hz.trans ez,hy.trans ey,ha.trans ea⟩
  have heq (f : FlagDegree) (C : FirstTailComponent S) :
      unit.toPrimeFlagBudgetFamily.weightedCost f C = Bfam.weightedCost f C := by
    obtain ⟨ez,ey,ea⟩ :=
      unitFamilyOfCongruentCut_costs (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    change unit.toPrimeFlagBudgetFamily.zCost C = Bfam.zCost C at ez
    change unit.toPrimeFlagBudgetFamily.yzCost C = Bfam.yzCost C at ey
    change unit.toPrimeFlagBudgetFamily.allCost C = Bfam.allCost C at ea
    unfold PrimeFlagBudgetFamily.weightedCost
    rw [ez,ey,ea]
  let mu := fun C : FirstTailComponent S => localMultiplicity (loosenStageGeneral S)
    (canonicalLocalDVRFamily (loosenStageGeneral S) hproper) C
  let first := hfreeFirstDir t y r
  let normal := cellNormal t y r
  let projection : (j : Fin 3) → (C : FirstTailComponent S) →
      Coordinate Ω (CoordinateField Ω C.1) :=
    ![unit.zProjection,unit.yzProjection,unit.allProjection]
  let ell := channel S hproper hflagChar hmixedRed
  have hell (j : Fin 3) : PolynomialInFlag (MovingFiberThreeSources6811.direction j) (ell j) := by
    fin_cases j
    · exact linearZ_in_flag
    · exact linearU_in_flag _
    · exact linearA_in_flag _ _
  have hvalue (j : Fin 3) (C : FirstTailComponent S) :
      coordinateValue Ω (CoordinateField Ω C.1) (projection j C) =
        coordinateEvaluation Ω C.1 (ell j) := by
    fin_cases j
    · exact common_z_value unit C
    · exact common_u_value unit common C
    · exact common_a_value unit common C

  have hnormal (j : Fin 3) :
      3*scale*(∑ C : active, mu C.val*
        coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val))≤
      scale*flagMixed flag (first j) (MovingFiberThreeSources6811.direction j)+4*(w+1)*price (MovingFiberThreeSources6811.direction j) zCap uCap vCap := by
    have hq : (MovingFiberThreeSources6811.direction j).zOnly+(MovingFiberThreeSources6811.direction j).yz+(MovingFiberThreeSources6811.direction j).all=1 := by fin_cases j <;> rfl
    have hh := first_cut_coordinate_channel (E:=Ext) (loosenStageGeneral S) hproper
      (fun C : active => C.val) Subtype.val_injective (ell j) (MovingFiberThreeSources6811.direction j) (hell j)
      (fun C => projection j C.val) (fun C => hvalue j C.val) hflagChar.2.2
      (by rw [hq,mul_one]; exact hlinear) SZ hlead j r (y-r) (t-y) hr3 (by omega) hR hYR hAll
      unitAllFlag (hfree hproper hflagChar hmixedRed j) scale zCap uCap vCap hfirst
    simpa only [mu,first,hfreeFirstDir,price,mixed_swap_right] using hh
  have hnormalSum : 3*scale*(∑ C∈active, mu C*Bfam.weightedCost normal C)≤
      scale*(∑ j : Fin 3, weight normal j*flagMixed flag (first j) (MovingFiberThreeSources6811.direction j))+
        4*(w+1)*price normal zCap uCap vCap := by
    have h := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) =>
      Nat.mul_le_mul_left (weight normal j) (hnormal j))
    have hsum : (∑ C ∈ active, mu C*Bfam.weightedCost normal C) =
        ∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val := by
      calc
        _ = ∑ C ∈ active, mu C*unit.toPrimeFlagBudgetFamily.weightedCost normal C := by
          apply Finset.sum_congr rfl
          intro C _
          rw [heq]
        _ = _ := (Finset.sum_coe_sort active
          (fun C => mu C*unit.toPrimeFlagBudgetFamily.weightedCost normal C)).symm
    rw [hsum]
    have hl : (3*scale)*(∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val) =
        ∑ j : Fin 3, weight normal j*((3*scale)*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) := by
      rw [Fin.sum_univ_three]
      change (3*scale)*(∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val) =
        normal.zOnly*((3*scale)*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.zProjection C.val)) +
        normal.yz*((3*scale)*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.yzProjection C.val)) +
        normal.all*((3*scale)*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.allProjection C.val))
      have hp (C : active) : mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val =
          normal.zOnly*(mu C.val*
            coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.zProjection C.val)) +
          normal.yz*(mu C.val*
            coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.yzProjection C.val)) +
          normal.all*(mu C.val*
            coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.allProjection C.val)) := by
        simp only [PrimeFlagBudgetFamily.weightedCost,
          AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily,
          AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,
          AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget]
        ring
      simp_rw [hp]
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    rw [hl]

    refine h.trans (le_of_eq ?_)
    rw [sum_two_scaled,sum_weight_price]
  have hmove : scale*(∑ C∈active, (budget C).movingCost)≤price (rawFirstFlag t y r) zCap uCap vCap := hmoving
  have hjointScaled : (3*scale)*(∑ C∈active,
      (mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost))≤pairNumerator scale zCap uCap vCap t y r flag := by
    have hh := Nat.add_le_add hnormalSum (Nat.mul_le_mul_left (3*65539) hmove)
    convert hh using 1
    · simp only [Finset.sum_add_distrib,←Finset.mul_sum]; ring
    · rfl
  have hjoint : (∑ C∈active, (mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost))≤
      pairNumerator scale zCap uCap vCap t y r flag/(3*scale) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0<3*scale)).mpr
    simpa only [Nat.mul_comm] using hjointScaled
  have hinactive : ∀ C : FirstTailComponent S, C∉active →
      (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card=0 := by
    intro C hC
    have hmem : SZ.leading (polynomialEmbedding K)∈C.1 := by
      simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hC
    exact SecondJetExceptionalComponents.component_empty_of_nonvanishing _ _ _ (SZ.leading (polynomialEmbedding K))
      Gamma _ C hmem hgood
  obtain ⟨provider⟩ := BoundaryTailJointBudget6807.exists_provider_of_joint_curve_budget
    t y r hr3 hb hyt (by decide) S hproper (cellFirstTail t y r) Bfam base budget hcost'
    active (pairNumerator scale zCap uCap vCap t y r flag/(3*scale)) hinactive hjoint hgate htangent
  exact stage_card_le_divisorBound S provider

#print axioms retained_stage_pair_bound
end
end ProximityPrize.SubmissionLower.MovingSourcePairRetainedStage6814
