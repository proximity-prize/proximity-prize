import ProximityPrize.SubmissionLower.BoundaryTailRegularData

namespace ProximityPrize.SubmissionLower.BoundaryTailNumericGeometry
open RCN260 RCN095 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def properParameters (r v z B U L s : ℕ) : UnequalParameters :=
  ⟨262144,131071,181333,r+v,r,r+v+z,U+s*(r+v-1),B+s*(r-1),L+s*(r+v+z-1)⟩

def normal (r v z : ℕ) : ℕ :=
  flagMixed ⟨z,v,r⟩ ⟨262144*z,1+262144*v,262144*(r-1)⟩
    (⟨131074*z,131074*(v-1)+2,131074*(r-2)+3⟩ + 131071 • unitAllFlag)

def parameters (r y t R capY T : ℕ) : UnequalParameters :=
  ⟨262144,131071,181333,y,r,t,capY,R,T⟩

theorem count_mono {r y t R capY T r' y' t' R' capY' T' : ℕ}
    (hr : r ≤ r') (hy : y ≤ y') (ht : t ≤ t')
    (hR : R ≤ R') (hY : capY ≤ capY') (hT : T ≤ T') :
    (parameters r y t R capY T).regularCountCap ≤
      (parameters r' y' t' R' capY' T').regularCountCap := by
  norm_num only [parameters,UnequalParameters.regularCountCap,UnequalParameters.regularNumerator,UnequalParameters.agreement,
    UnequalParameters.leftAgreement,UnequalParameters.rightAgreement,UnequalParameters.mixedCost,
    UnequalParameters.errors,UnequalParameters.gap,RCN294.dot]
  apply Nat.div_le_div_right
  gcongr

theorem mixed_mono {r y t R capY T r' y' t' R' capY' T' : ℕ}
    (hr : r ≤ r') (hy : y ≤ y') (ht : t ≤ t')
    (hR : R ≤ R') (hY : capY ≤ capY') (hT : T ≤ T') :
    (parameters r y t R capY T).mixedCost.y ≤ (parameters r' y' t' R' capY' T').mixedCost.y ∧
    (parameters r y t R capY T).mixedCost.r ≤ (parameters r' y' t' R' capY' T').mixedCost.r ∧
    (parameters r y t R capY T).mixedCost.z ≤ (parameters r' y' t' R' capY' T').mixedCost.z := by
  dsimp [parameters,UnequalParameters.mixedCost]
  constructor
  · gcongr
  constructor <;> gcongr

theorem regularNumerator_right (P : UnequalParameters)
    (hy : P.leftY ≤ P.rightY) (hr : P.leftR ≤ P.rightR) (hz : P.leftZ ≤ P.rightZ) :
    P.regularNumerator = (P.n-P.w)*dot P.rightAgreement P.mixedCost+
      (P.errors+1)*P.gap*P.mixedCost.z := by
  have hy' : P.leftAgreement.y ≤ P.rightAgreement.y :=
    Nat.add_le_add_left (Nat.mul_le_mul_left (2*P.w) hy) 1
  have hr' : P.leftAgreement.r ≤ P.rightAgreement.r :=
    Nat.mul_le_mul_left P.w (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1)
  have hz' : P.leftAgreement.z ≤ P.rightAgreement.z :=
    Nat.add_le_add_right (Nat.mul_le_mul_left (2*P.w) hz) 1
  simp only [UnequalParameters.regularNumerator,UnequalParameters.agreement,
    max_eq_right hy',max_eq_right hr',max_eq_right hz']

end ProximityPrize.SubmissionLower.BoundaryTailNumericGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailOwnShape
open MvPolynomial RCN130 RCN234 RCN156 RCN095 RCN347 RCN135
open BoundaryTailRegularData BoundaryTailRegularData.Data LocatorHybridCells LocatorHybridCellsC1
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem zOnly_le_degree (F : MvPolynomial (Fin 4) K) :
    (originalCumulativeFlag F).zOnly ≤ F.degreeOf 3 := by
  have hw : wt residualTotalWeights F ≤ wt residualYSWeights F+F.degreeOf 3 := by
    apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
    intro e he
    have h1 := MvPolynomial.le_weightedTotalDegree residualYSWeights he
    have h2 := MvPolynomial.monomial_le_degreeOf (3:Fin 4) he
    simp [wt,RCN081.weight_fin4,residualYSWeights,residualTotalWeights] at h1 ⊢
    omega
  change wt residualTotalWeights F-wt residualYSWeights F ≤ F.degreeOf 3
  omega

def Own (S : Data nodes u0 u1) : Prop :=
  originalCumulativeFlag S.F = ⟨S.t-S.y,S.y-S.r,S.r⟩

theorem normal_eq (S : Data nodes u0 u1) (hown : Own S) :
    S.normal = BoundaryTailNumericGeometry.normal S.r (S.y-S.r) (S.t-S.y) := by
  have h1 : cellB S.y S.r = S.y-S.r-1 := rfl
  have h2 : cellS S.r = S.r-2 := rfl
  have h3 : 2*(S.y-S.r-1)+2 = 2*(S.y-S.r) := by have := S.ry; omega
  have h4 : 2*(S.r-2)+2 = 2*(S.r-1) := by have := S.rpos; omega
  unfold Data.normal BoundaryTailProvider.cellNormal
  rw [BoundaryTailAlgebra.normalFlag_eq_cell S.t S.y S.r S.rpos S.ry]
  rw [hown,SecondJetIdentity.cell_first_eq,SecondJetIdentity.cell_normal_eq]
  simp only [Lower80788.HybridIdentityC2.reducedABS,Lower80788.HybridIdentityC2.rationalABS,
    cellA,h1,h2,h3,h4,BoundaryTailNumericGeometry.normal]
  simp only [flagMixed, RCN327.w]
  ring

theorem avoidance (S : Data nodes u0 u1) (hown : Own S) (L : ℕ) (hL : L < S.t-S.y) :
    L < S.F.degreeOf 3 := by
  have h := zOnly_le_degree S.F
  rw [hown] at h
  exact hL.trans_le h

theorem factorial_ne (d : ℕ) (hd : d < 2130706433) : (d.factorial : K) ≠ 0 :=
  factorial_cast_ne_zero_below_characteristic 2130706433 d hd

theorem two_ne : (2 : K) ≠ 0 := by
  have h := factorial_ne (K := K) 2 (by decide)
  simpa only [show Nat.factorial 2 = 2 by decide,Nat.cast_ofNat] using h

theorem moving_eq (S : Data nodes u0 u1) (hown : Own S) (B U L k n0 : ℕ) :
    S.moving B U L k n0 = SecondJetAffineCeiling.moving S.r (S.y-S.r) (S.t-S.y)
      (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) := by
  have h3 : 2*(S.y-S.r-1)+2 = 2*(S.y-S.r) := by have := S.ry; omega
  have h4 : 2*(S.r-2)+2 = 2*(S.r-1) := by have := S.rpos; omega
  unfold Data.moving
  rw [hown,SecondJetIdentity.cell_first_eq]
  simp only [Lower80788.HybridIdentityC2.reducedABS,LocatorHybridCells.cellA,
    LocatorHybridCells.cellB,LocatorHybridCells.cellS,h3,h4,SecondJetAffineCeiling.moving,flagMixed]
  ring

theorem total_weight_eq (S : Data nodes u0 u1) (hown : Own S) :
    wt residualTotalWeights S.F = S.t := by
  have h := (originalCumulativeFlag_cumulative S.F).2.2
  rw [hown] at h
  dsimp only at h
  have := S.ry
  have := S.yt
  omega

theorem avoidance_total (S : Data nodes u0 u1) (hown : Own S) (L : ℕ) (hL : L < S.t) :
    L < wt residualTotalWeights S.F := by
  rwa [total_weight_eq S hown]

end
end ProximityPrize.SubmissionLower.BoundaryTailOwnShape
