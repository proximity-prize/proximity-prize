import ProximityPrize.SubmissionLower.Part.G087


section Compact_SecondJetNumericGeometry
/-! Arithmetic interfaces for the three geometric profiles. -/
namespace ProximityPrize.SubmissionLower.SecondJetNumericGeometry
open RCN260 RCN095 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def properParameters (r v z B U L s : ℕ) : UnequalParameters :=
  ⟨262144,131071,181353,r+v,r,r+v+z,U+s*(r+v-1),B+s*(r-1),L+s*(r+v+z-1)⟩

def normal (r v z : ℕ) : ℕ :=
  flagMixed ⟨z,v,r⟩ ⟨262144*z,1+262144*v,262144*(r-1)⟩
    ⟨131074*z,131074*(v-1)+2,131074*(r-2)+3⟩

def parameters (r y t R capY T : ℕ) : UnequalParameters :=
  ⟨262144,131071,181353,y,r,t,capY,R,T⟩

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

end ProximityPrize.SubmissionLower.SecondJetNumericGeometry

end Compact_SecondJetNumericGeometry
