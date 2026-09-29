import ProximityPrize.SubmissionLower.MovingSourceUniformPairBudget6814

/-! One checked Stage price covers both same-source pairs and every
power-avoidance cofactor pair, INCLUDING Z-leading-zero seeds. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCheckedPairStage6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN086 RCN095 RCN135 RCN136 RCN156 RCN159 RCN174 RCN234 RCN243 RCN244 RCN260 RCN264
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCoupledClearing6814
open MovingSourcePairRetainedStage6814 MovingSourcePairStageSupplier6814 MovingSourcePairStageArithmetic6814
open MovingSourcePairStageWithLeading6814 MovingSourcePairEnvelope6814 LocatorHybridCells

theorem price_mono (W : FlagDegree) {z u v z' u' v' : ℕ}
    (hz : z≤z') (hu : u≤u') (hv : v≤v') : price W z u v≤price W z' u' v' := by
  unfold price
  gcongr

theorem pairNumerator_mono (scale t y r : ℕ) (p p' : FlagDegree) (hp : CumulativeLe p p')
    {z u v z' u' v' : ℕ} (hz : z≤z') (hu : u≤u') (hv : v≤v') :
    pairNumerator scale z u v t y r p≤pairNumerator scale z' u' v' t y r p' := by
  have hfirst := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) =>
    Nat.mul_le_mul_left (weight (BoundaryTailJointBudget6807.cellNormal t y r) j)
      (mixed_mono_left p p' (HFreeDir6813.hfreeFirstDir t y r j) (MovingFiberThreeSources6811.direction j) hp))
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left scale hfirst)
    (Nat.mul_le_mul_left _ (price_mono _ hz hu hv))) (Nat.mul_le_mul_left _ (price_mono _ hz hu hv))

theorem pairNumerator_scale (n scale z u v t y r : ℕ) (p : FlagDegree) :
    pairNumerator (n*scale) (n*z) (n*u) (n*v) t y r p=n*pairNumerator scale z u v t y r p := by
  unfold pairNumerator price
  ring

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}
local notation "w" => RCN326.w

theorem pairStageCost_le_checked {F : MvPolynomial (Fin 4) K}
    (SZ SP SQ : Source F) (hSZ : Profile SZ 53 177 3429 24 6 8)
    (delta : ℕ) (hd : 0<delta) (p : FlagDegree) (hp : CumulativeLe p ⟨3504,45,12⟩)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag≤delta*28420)
    (hv : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag≤delta*98890) :
    pairStageCost SZ SP SQ delta 3561 57 12 p≤271825945823618136 := by
  have hZd : SZ.d=7 := by unfold Source.d; rw [hSZ.2.2.2.2.1]
  have hZflag : SZ.flag=⟨3252,132,51⟩ := by
    unfold Source.flag
    rw [hSZ.1,hSZ.2.1,hSZ.2.2.1,hZd,hSZ.2.2.2.2.2]
    rfl
  have hz : flagMixed ⟨3504,45,12⟩ unitZFlag SZ.flag=4491 := by rw [hZflag]; decide +kernel
  have hnum := pairNumerator_mono (7*delta) 3561 57 12 p ⟨3504,45,12⟩ hp
    (le_refl (delta*4491))
    (show 7*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag≤delta*(7*28420) by omega)
    (show 7*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag≤delta*(7*98890) by omega)
  have hscaled : pairNumerator (7*delta) (delta*4491) (delta*(7*28420)) (delta*(7*98890))
      3561 57 12 ⟨3504,45,12⟩=delta*5708344862295980862 := by
    rw [Nat.mul_comm 7 delta,pairNumerator_scale,checked_pair_numerator]
  rw [hscaled] at hnum
  change pairNumerator (SZ.d*delta) (delta*flagMixed ⟨3504,45,12⟩ unitZFlag SZ.flag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)
    3561 57 12 p/(3*(SZ.d*delta))≤_
  rw [hZd,hz]
  calc
    _≤(delta*5708344862295980862)/(3*(7*delta)) := Nat.div_le_div_right hnum
    _=5708344862295980862/21 := by
      rw [show 3*(7*delta)=delta*21 by ring]
      exact Nat.mul_div_mul_left _ _ hd
    _=271825945823618136 := by decide +kernel

theorem checked_pair_stage_card
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
    (delta : ℕ) (hd : 0<delta) (hd3 : delta≤3) (hP : delta≤SP.d) (hQ : delta≤SQ.d)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag≤6014)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag≤delta*28420)
    (hv : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag≤delta*98890) :
    Gamma.card≤271849050685725612 := by
  have hcount := checked_pair_stage_with_leading D hDlow hDchar S hFT hnodes hagreement hbox hflag hproper hpos
    SZ SP SQ hSZ hcop delta hd hP hQ (by omega) (by omega) (by omega)
  have hcost := pairStageCost_le_checked SZ SP SQ hSZ delta hd flag hflag hu hv
  omega

#print axioms checked_pair_stage_card
end
end ProximityPrize.SubmissionLower.MovingSourceCheckedPairStage6814
