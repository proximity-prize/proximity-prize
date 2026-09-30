import ProximityPrize.SubmissionLower.MovingSourceBandNativeCount6815
import ProximityPrize.SubmissionLower.MovingSourceBandPairArithmetic6814
import ProximityPrize.SubmissionLower.PortfolioPacketHelpers6815
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
