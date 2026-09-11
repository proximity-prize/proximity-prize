import ProximityPrize.SubmissionLower.BoundaryTailProfileCount
import ProximityPrize.SubmissionLower.BoundaryTailNormalArithmetic

namespace ProximityPrize.SubmissionLower.BoundaryTailRefinedCap
open RCN095 RCN260 RCN294 AsymmetricHelper BoundaryTailNumericGeometry
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def pairNumerator (r v z B U L s : ℕ) : ℕ :=
  leftRegularNumerator (properParameters r v z B U L s)

def pairSlope (r v B U s : ℕ) : ℕ :=
  131073*((1+262142*(r+v))*(r*s+B+s*(r-1))+
    131071*(2*r-1)*((r+v)*s+U+s*(r+v-1))+
    262142*((r+v)*(B+s*(r-1))+r*(U+s*(r+v-1))))

theorem pairNumerator_add (r v z h B U L s : ℕ) (hr : 1 ≤ r) :
    pairNumerator r v (z+h) B U L s =
      pairNumerator r v z B U L s + h*pairSlope r v B U s := by
  have hs : r+v+(z+h)-1 = (r+v+z-1)+h := by omega
  simp only [pairNumerator,pairSlope,properParameters,leftRegularNumerator,
    UnequalParameters.leftAgreement,UnequalParameters.mixedCost,
    UnequalParameters.errors,UnequalParameters.gap,dot]
  rw [hs]
  ring

def start (r v : ℕ) : ℕ := 2341-(r+v)

def properValue (r v : ℕ) : ℕ :=
  (pairNumerator r v (start r v) 47 157 2340 21+50261)/50262
def properSlope (r v : ℕ) : ℕ := (pairSlope r v 47 157 21+50261)/50262
def coefficientValue (r v : ℕ) : ℕ :=
  (pairNumerator r v (start r v) 47 157 2340 0+50261)/50262
def coefficientSlope (r v : ℕ) : ℕ := (pairSlope r v 47 157 0+50261)/50262

def retainedValue (r v : ℕ) : ℕ :=
  normal r v (start r v)+
    65539*((SecondJetAffineCeiling.moving r v (start r v)
      (SecondJetRelaxedFlag.budgetFlag 47 157 2340 6 7)+5)/6)+coefficientValue r v

def retainedSlope (r v : ℕ) : ℕ :=
  (normal r v 1-normal r v 0)+
    65539*((SecondJetAffineCeiling.movingSlope r v
      (SecondJetRelaxedFlag.budgetFlag 47 157 2340 6 7)+5)/6)+coefficientSlope r v

def properLine (r v z : ℕ) : ℕ := properValue r v+properSlope r v*(z-start r v)
def retainedLine (r v z : ℕ) : ℕ := retainedValue r v+retainedSlope r v*(z-start r v)
def profile (r v z : ℕ) : ℕ := max (properLine r v z) (retainedLine r v z)

theorem normal_add (r v z h : ℕ) :
    normal r v (z+h) = normal r v z + h*(normal r v 1-normal r v 0) := by
  have hid : normal r v (z+h)+h*normal r v 0 =
      normal r v z+h*normal r v 1 := by
    simp only [normal,flagMixed,add_zOnly,add_yz,add_all,
      nsmul_zOnly,nsmul_yz,nsmul_all,unitAllFlag]
    ring
  have hle : normal r v 0 ≤ normal r v 1 := by
    dsimp [normal,flagMixed]
    gcongr <;> norm_num
  have hs := Nat.sub_add_cancel hle
  nlinarith

theorem pairCount_le_line (r v z B U L s : ℕ) (hr : 1 ≤ r)
    (hz : start r v ≤ z) :
    leftRegularCountCap (properParameters r v z B U L s) ≤
      (pairNumerator r v (start r v) B U L s+50261)/50262+
      ((pairSlope r v B U s+50261)/50262)*(z-start r v) := by
  have he : z = start r v+(z-start r v) := by omega
  unfold leftRegularCountCap
  rw [show (properParameters r v z B U L s).gap = 50262 by
    norm_num [properParameters,UnequalParameters.gap]]
  change pairNumerator r v z B U L s / 50262 ≤ _
  have hp := pairNumerator_add r v (start r v) (z-start r v) B U L s hr
  rw [←he] at hp
  rw [hp]
  have h := SecondJetAffineCeiling.ceil_add_mul_le
    (pairNumerator r v (start r v) B U L s) (pairSlope r v B U s)
    (z-start r v) 50261
  have hl := Nat.div_le_div_right (c := 50262)
    (Nat.le_add_right (pairNumerator r v (start r v) B U L s+
      (z-start r v)*pairSlope r v B U s) 50261)
  simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.mul_comm] using hl.trans h

theorem numericBound_le_profile (r v z : ℕ) (hr : 1 ≤ r) (hz : start r v ≤ z) :
    BoundaryTailAsymmetric.numericBound r v z 47 157 2340 21 5 7 ≤ profile r v z := by
  apply max_le_max
  · exact pairCount_le_line r v z 47 157 2340 21 hr hz
  · have hc := pairCount_le_line r v z 47 157 2340 0 hr hz
    have he : z = start r v+(z-start r v) := by omega
    have hm := SecondJetAffineCeiling.moving_ceil_add_le r v (start r v)
      (z-start r v) 5 (SecondJetRelaxedFlag.budgetFlag 47 157 2340 6 7)
    rw [←he] at hm
    simp only [properParameters,Nat.zero_mul,Nat.add_zero] at hc
    change leftRegularCountCap (parameters r (r+v) (r+v+z) 47 157 2340) ≤
      coefficientValue r v+coefficientSlope r v*(z-start r v) at hc
    change normal r v z+65539*((SecondJetAffineCeiling.moving r v z
      (SecondJetRelaxedFlag.budgetFlag 47 157 2340 6 7)+5)/6)+
      leftRegularCountCap (parameters r (r+v) (r+v+z) 47 157 2340) ≤ retainedLine r v z
    have hn := normal_add r v (start r v) (z-start r v)
    rw [←he] at hn
    rw [hn]
    have h := Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 65539 hm)
      (normal r v (start r v)+(z-start r v)*(normal r v 1-normal r v 0))) hc
    apply h.trans_eq
    simp only [retainedLine,retainedValue,retainedSlope]
    ring

end ProximityPrize.SubmissionLower.BoundaryTailRefinedCap
