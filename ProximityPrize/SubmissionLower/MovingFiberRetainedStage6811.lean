import ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811
import ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807
import ProximityPrize.SubmissionLower.HFreeFirstSlice6812

/-! Concrete retained Stage integration: the original multiplicity-weighted
normal cuts and the new unweighted moving budget use the same source triple.
-/
namespace ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
open scoped Classical BigOperators
open RCN002 RCN046 RCN057 RCN074 RCN084 RCN085 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTransportC2 LocatorHybridTailProvider
open BoundaryTailProvider CommonLinearChannels6807 MovingFiberThreeSources6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap : ℕ}
local notation "Ω" => GenericField K

def rawFirstFlag (t y r : ℕ) : FlagDegree :=
  RCN198.center (cellA t y) (cellB y r) (cellS r) +
    w • (⟨cellA t y,cellB y r+1,cellS r+2⟩ : FlagDegree)

/-- H-free first-cut flag of the cell: `2(w+1)•flag(H) + 3•unitAll`. -/
def hfreeFirst (t y r : ℕ) : FlagDegree :=
  HFreeFirstSlice6812.hfreeFlag r (y-r) (t-y) unitAllFlag

/-- Direction `j` is charged `(scale/3)·mix(f,X,e_j) + 4(w+1)(scale/3d_j)·mix(f,e_j,V_j)`
(the H-free first cut), plus the unchanged moving term. -/
def numerator {F : MvPolynomial (Fin 4) K} (source : Fin 3 → Source F)
    (scale t y r : ℕ) (flag : FlagDegree) : ℕ :=
  scale/3*flagMixed flag (hfreeFirst t y r) (cellNormal t y r) +
    ∑ j : Fin 3, (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(source j).d))+
      65539*weight (rawFirstFlag t y r) j*(scale/(source j).d))*
      flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag

theorem sum_numerator_le {J : Type*} [Fintype J] {F : MvPolynomial (Fin 4) K}
    (source : Fin 3 → Source F) (scale t y r : ℕ) (flags : J → FlagDegree) (total : FlagDegree)
    (hs : (∑ i, (flags i).all) ≤ total.all)
    (hm : (∑ i, ((flags i).yz+(flags i).all)) ≤ total.yz+total.all)
    (ht : (∑ i, ((flags i).zOnly+(flags i).yz+(flags i).all)) ≤ total.zOnly+total.yz+total.all) :
    (∑ i, numerator source scale t y r (flags i)) ≤ numerator source scale t y r total := by
  let first := hfreeFirst t y r
  let normal := cellNormal t y r
  let coeff := fun j : Fin 3 => 4*(w+1)*weight normal j*(scale/(3*(source j).d))+
    65539*weight (rawFirstFlag t y r) j*(scale/(source j).d)
  have hfirst := RCN084.sum_flagMixed_le_of_cumulative flags total first normal hs hm ht
  have hsource (j : Fin 3) := RCN084.sum_flagMixed_le_of_cumulative flags total
    (MovingFiberThreeSources6811.direction j) (source j).flag hs hm ht
  calc
    (∑ i, numerator source scale t y r (flags i)) =
        scale/3*(∑ i, flagMixed (flags i) first normal) +
          ∑ j : Fin 3, coeff j*(∑ i, flagMixed (flags i) (MovingFiberThreeSources6811.direction j) (source j).flag) := by
      simp only [numerator,Finset.sum_add_distrib,← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [coeff,first,normal,Finset.mul_sum]
    _ ≤ scale/3*flagMixed total first normal +
        ∑ j : Fin 3, coeff j*flagMixed total (MovingFiberThreeSources6811.direction j) (source j).flag :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hfirst)
        (Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hsource j)))
    _ = _ := rfl

/-- The three slice directions of the retained stage (`linearZ/U/A` at the common `λ, μ`). -/
def channel {t y r : ℕ}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r))
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag < p) :
    Fin 3 → MvPolynomial (Fin 3) Ω :=
  let common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed
  ![CommonLinearChannels6807.linearZ,CommonLinearChannels6807.linearU common.lam,
    CommonLinearChannels6807.linearA common.mu common.lam]

/-- The H-free hypothesis for a retained stage: `HFreeChannel` (with `C0 = unitAll`) in
each of its three slice directions, over `AlgebraicClosure (RatFunc Ω)`. -/
def HFreeStage {t y r : ℕ}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r)) : Prop :=
  ∀ hproper hflagChar hmixedRed (j : Fin 3),
    HFreeFirstSlice6812.HFreeChannel (E := AlgebraicClosure (RatFunc Ω)) S.F
      (channel S hproper hflagChar hmixedRed j) unitAllFlag

theorem retained_stage_bound
    (t y r scale : ℕ) (hr3 : 3 ≤ r) (hb : r+2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r))
    (source : Fin 3 → Source S.F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (hfree : HFreeStage S)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag < p)
    (hlinear : 2*(flag.zOnly+flag.yz+flag.all) < p)
    (hmovingGate : 2*(flag.zOnly+flag.yz+flag.all)*(t+1) < p)
    (hchar : 2*(w-1) < p)
    (hgate : errorCap+1 ≤ (cellNormal t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
      (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
        (errorCap+1)*(BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixedRed).yzCost C)
    (h2 : (2 : Ω) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : Ω) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0) :
    Gamma.card ≤ numerator source scale t y r flag / scale := by
  classical
  let Ext := AlgebraicClosure (RatFunc Ω)
  letI : CharP Ext p := charP_of_injective_algebraMap (algebraMap Ω Ext).injective p
  have h2E : (2 : Ext) ≠ 0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hfactE (j : Fin 3) : ((source j).k.factorial : Ext) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne (hfact j)
  let base := BoundaryTailReduced.reducedBaseOrd S hproper hflagChar hmixedRed
  let Uold := BoundaryTailReduced.reducedUnitFamily S hproper hflagChar hmixedRed
  let unit := unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S) Uold base
  let Bfam := BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixedRed
  let common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed
  let active : Finset (FirstTailComponent S) := Finset.univ.filter
    (fun C => ∀ j : Fin 3, (source j).leading (polynomialEmbedding K) ∉ C.1)
  have hlead (C : active) (j : Fin 3) : (source j).leading (polynomialEmbedding K) ∉ C.val.1 :=
    (Finset.mem_filter.mp C.property).2 j
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = r+(y-r) := by dsimp [cellB,cellS]; omega
  have htot : cellA t y+cellB y r+cellS r+3 = r+(y-r)+(t-y) := by dsimp [cellA,cellB,cellS]; omega
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
  have hgates : 2*(flag.zOnly+flag.yz+flag.all)*(cellA t y+(cellB y r+1)+(cellS r+3)) < p := by
    have he : cellA t y+(cellB y r+1)+(cellS r+3) = t+1 := by dsimp [cellA,cellB,cellS]; omega
    simpa only [he] using hmovingGate
  have hdiv1 (j : Fin 3) : (source j).d ∣ scale := (Dvd.intro_left 3 rfl).trans (hscaleDiv j)
  obtain ⟨budget,hcost,hmoving⟩ := MovingFiberDegreeSum6811.exists_first_tail_budget (E := Ext)
    (polynomialEmbedding K) S.F source scale hscale hdiv1 S.G flag (cellFirstTail t y r)
    S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
    (cellA t y) (cellB y r) (cellS r) w (by norm_num [w])
    Hsupport.coordinate_bounds.2.1 Hsupport.ys_weight Hsupport.total_weight p hlinear hgates h2E hfactE
    base unit active (fun C hC j => (Finset.mem_filter.mp hC).2 j)
  have hcost' (C : FirstTailComponent S) :
      (budget C).zCost = Bfam.zCost C ∧ (budget C).yzCost = Bfam.yzCost C ∧ (budget C).allCost = Bfam.allCost C := by
    obtain ⟨hz,hy,ha⟩ := hcost C
    obtain ⟨ez,ey,ea⟩ := unitFamilyOfCongruentCut_costs (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    exact ⟨hz.trans ez,hy.trans ey,ha.trans ea⟩
  have heq (f : FlagDegree) (C : FirstTailComponent S) :
      unit.toPrimeFlagBudgetFamily.weightedCost f C = Bfam.weightedCost f C := by
    obtain ⟨ez,ey,ea⟩ := unitFamilyOfCongruentCut_costs (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    change unit.toPrimeFlagBudgetFamily.zCost C = Bfam.zCost C at ez
    change unit.toPrimeFlagBudgetFamily.yzCost C = Bfam.yzCost C at ey
    change unit.toPrimeFlagBudgetFamily.allCost C = Bfam.allCost C at ea
    unfold PrimeFlagBudgetFamily.weightedCost
    rw [ez,ey,ea]
  let mu := fun C : FirstTailComponent S => localMultiplicity (loosenStageGeneral S)
    (canonicalLocalDVRFamily (loosenStageGeneral S) hproper) C
  let first := hfreeFirst t y r
  let normal := cellNormal t y r
  let projection : (j : Fin 3) → (C : FirstTailComponent S) → Coordinate Ω (CoordinateField Ω C.1) :=
    ![unit.zProjection,unit.yzProjection,unit.allProjection]
  let ell := channel S hproper hflagChar hmixedRed
  have hell (j : Fin 3) : PolynomialInFlag (MovingFiberThreeSources6811.direction j) (ell j) := by
    fin_cases j
    · exact linearZ_in_flag
    · exact linearU_in_flag _
    · exact linearA_in_flag _ _
  have hvalue (j : Fin 3) (C : FirstTailComponent S) :
      coordinateValue Ω (CoordinateField Ω C.1) (projection j C) = coordinateEvaluation Ω C.1 (ell j) := by
    fin_cases j
    · exact common_z_value unit C
    · exact common_u_value unit common C
    · exact common_a_value unit common C
  have hnormal (j : Fin 3) :
      scale*(∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) ≤
      scale/3*flagMixed flag first (MovingFiberThreeSources6811.direction j) +
        4*(w+1)*(scale/(3*(source j).d))*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag := by
    have hq : (MovingFiberThreeSources6811.direction j).zOnly+(MovingFiberThreeSources6811.direction j).yz+
        (MovingFiberThreeSources6811.direction j).all = 1 := by fin_cases j <;> rfl
    have h := ActualGenericChannel6807.first_cut_for_coordinate_channel (E := Ext)
      (loosenStageGeneral S) hproper (fun C : active => C.val) Subtype.val_injective
      (ell j) (MovingFiberThreeSources6811.direction j) (hell j)
      (fun C => projection j C.val) (fun C => hvalue j C.val)
      hflagChar.2.2 (by rw [hq,mul_one]; exact hlinear) _ (fun C => hlead C j)
      _ _ _ _ _ (HFreeFirstSlice6812.hfree_slice_charge (E := Ext) (loosenStageGeneral S) hproper
        (ell j) (source j).P (source j).B (source j).U (source j).T (source j).s (source j).k (source j).n0
        (source j).hS (source j).hshape (source j).hBU (source j).hUT (source j).hdn (source j).hB
        (source j).hn (source j).hdiv h2E (hfactE j) r (y-r) (t-y) hr3 (by omega) hR hYR hAll
        unitAllFlag (hfree hproper hflagChar hmixedRed j))
    have hexp : flagMixed flag (MovingFiberThreeSources6811.direction j)
        ((source j).d • first+(4*(w+1)) • (source j).flag) =
        (source j).d*flagMixed flag first (MovingFiberThreeSources6811.direction j) +
          4*(w+1)*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag := by
      simp only [flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
      ring
    change 3*(source j).d*(∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) ≤
      flagMixed flag (MovingFiberThreeSources6811.direction j) ((source j).d • first+(4*(w+1)) • (source j).flag) at h
    rw [hexp] at h
    obtain ⟨m,hm⟩ := hscaleDiv j
    have hd0 : 0 < 3*(source j).d := by simp only [Source.d]; omega
    have h3 : scale/3 = (source j).d*m := by
      rw [hm,Nat.mul_assoc,Nat.mul_div_cancel_left _ (by norm_num)]
    have h3d : scale/(3*(source j).d) = m := by rw [hm,Nat.mul_div_cancel_left _ hd0]
    rw [h3,h3d,hm]
    calc
      _ = m*(3*(source j).d*(∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val))) := by ring
      _ ≤ m*((source j).d*flagMixed flag first (MovingFiberThreeSources6811.direction j) +
          4*(w+1)*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag) :=
        Nat.mul_le_mul_left m h
      _ = _ := by ring
  have hnormalSum : scale*(∑ C ∈ active, mu C*Bfam.weightedCost normal C) ≤
      scale/3*flagMixed flag first normal +
        ∑ j : Fin 3, 4*(w+1)*weight normal j*(scale/(3*(source j).d))*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      Nat.mul_le_mul_left (weight normal j) (hnormal j))
    have hsum : (∑ C ∈ active, mu C*Bfam.weightedCost normal C) =
        ∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val := by
      calc
        _ = ∑ C ∈ active, mu C*unit.toPrimeFlagBudgetFamily.weightedCost normal C := by
          apply Finset.sum_congr rfl
          intro C _
          rw [heq]
        _ = _ := (Finset.sum_coe_sort active (fun C => mu C*unit.toPrimeFlagBudgetFamily.weightedCost normal C)).symm
    rw [hsum]
    have hl : scale*(∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val) =
        ∑ j : Fin 3, weight normal j*(scale*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) := by
      rw [Fin.sum_univ_three]
      change scale*(∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val) =
        normal.zOnly*(scale*∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.zProjection C.val)) +
        normal.yz*(scale*∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.yzProjection C.val)) +
        normal.all*(scale*∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.allProjection C.val))
      have hp (C : active) : mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val =
          normal.zOnly*(mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.zProjection C.val)) +
          normal.yz*(mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.yzProjection C.val)) +
          normal.all*(mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.allProjection C.val)) := by
        simp only [PrimeFlagBudgetFamily.weightedCost,AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily,
          AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget]
        ring
      simp_rw [hp]
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    have hmixed : (∑ j : Fin 3, weight normal j*flagMixed flag first (MovingFiberThreeSources6811.direction j)) =
        flagMixed flag first normal := by
      simp only [Fin.sum_univ_three,weight,MovingFiberThreeSources6811.direction,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
        flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
      ring
    have hr : scale/3*flagMixed flag first normal +
        (∑ j : Fin 3, 4*(w+1)*weight normal j*(scale/(3*(source j).d))*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag) =
        ∑ j : Fin 3, weight normal j*(scale/3*flagMixed flag first (MovingFiberThreeSources6811.direction j) +
          4*(w+1)*(scale/(3*(source j).d))*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag) := by
      rw [← hmixed,Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hl,hr]
    exact h
  let moveNum := ∑ j : Fin 3, weight (rawFirstFlag t y r) j*(scale/(source j).d)*
    flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag
  have hmovingScaled : scale*(∑ C ∈ active, (budget C).movingCost) ≤ moveNum := by
    exact (Nat.mul_le_mul_left scale hmoving).trans (by
      simpa only [moveNum,rawFirstFlag,Nat.mul_comm] using Nat.div_mul_le_self moveNum scale)
  have hjointScaled : scale*(∑ C ∈ active, (mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost)) ≤
      numerator source scale t y r flag := by
    have h := Nat.add_le_add hnormalSum (Nat.mul_le_mul_left 65539 hmovingScaled)
    convert h using 1
    · simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    · simp only [numerator,moveNum,first,normal,Nat.add_mul,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_assoc]
      ring
  have hjoint : (∑ C ∈ active, (mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost)) ≤
      numerator source scale t y r flag/scale := by
    apply (Nat.le_div_iff_mul_le hscale).mpr
    simpa only [Nat.mul_comm] using hjointScaled
  have hinactive : ∀ C : FirstTailComponent S, C ∉ active →
      (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card = 0 := by
    intro C hC
    have hex : ∃ j : Fin 3, (source j).leading (polynomialEmbedding K) ∈ C.1 := by
      simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_not] using hC
    obtain ⟨j,hj⟩ := hex
    exact SecondJetExceptionalComponents.component_empty_of_nonvanishing _ _ _
      ((source j).leading (polynomialEmbedding K)) Gamma _ C hj (fun gamma hgamma => hgood gamma hgamma j)
  obtain ⟨provider⟩ := BoundaryTailJointBudget6807.exists_provider_of_joint_curve_budget
    t y r hr3 hb hyt hchar S hproper (cellFirstTail t y r) Bfam base budget hcost'
    active (numerator source scale t y r flag/scale) hinactive hjoint hgate htangent
  exact stage_card_le_divisorBound S provider

#print axioms retained_stage_bound
end
end ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
