import ProximityPrize.SubmissionLower.Fast032
set_option Elab.async false

/- Arithmetic for the first-loss schedule, following P0_10R.Bridge in PR 631.
   The bounds on the common factor range over all its possible bidegrees. -/
namespace PriceReceipt6925
open K1_14 K1_14_2_2 K1_14_2_2_4
open private checkNumerator checked_bound numerator_bound from ProximityPrize.SubmissionLower.Fast032
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def freeZero : Shape := ⟨57,79,17,1160⟩
def movingZero : Shape := ⟨191,265,55,6963⟩
def freeFive : Shape := ⟨96,133,29,1557⟩
def movingFive : Shape := ⟨316,439,92,10562⟩
def full : Shape := ⟨3025,4200,890,84000⟩
def initial : Fin 4 → ℕ := ![7915,182171,857477,8077080]
def dual : Fin 4 → ℕ := ![455,9174,83530,606062]
def threshold : Fin 4 → ℕ := ![1,1,3,2]

private instance (s t : Shape) (d r M : ℕ) (k : Fin 4) :
    Decidable (checkNumerator s t d r M k) := by
  unfold checkNumerator
  split <;> infer_instance

private theorem bound {s t : Shape} {d r x z cap : ℕ} {k : Fin 4}
    (hu : s.U ≤ t.U) (hb : s.B ≤ t.B) (hx : x ≤ s.U) (hz : z ≤ s.B)
    (hc : checkNumerator s t d r (highScale r k*d*(cap+1)) k) :
    d*highCap x z k + highScale r k * pairCap (residualShape s x z) (residualShape t x z) k
      < highScale r k*d*(cap+1) :=
  (numerator_bound s t d r x z k).trans_lt (checked_bound s t d r _ x z k hu hb hx hz hc)

theorem initial_cap (k : Fin 4) (x z : ℕ) (hx : x ≤ freeZero.U) (hz : z ≤ freeZero.B) :
    highCap x z k + pairCap (residualShape freeZero x z) (residualShape movingZero x z) k
      ≤ initial k := by
  have hc : checkNumerator freeZero movingZero 1 1 (highScale 1 k*1*(initial k+1)) k := by
    fin_cases k <;> decide +kernel
  have hs : highScale 1 k = 1 := by fin_cases k <;> rfl
  simpa only [hs,one_mul,Nat.lt_succ_iff] using
    bound (by decide) (by decide) hx hz hc

theorem reserve_square (k : Fin 4) (x z : ℕ) (hx : x ≤ freeFive.U) (hz : z ≤ freeFive.B) :
    let r := threshold k
    let d := (8-r)^2
    d*highCap x z k + highScale r k * pairCap (residualShape freeFive x z) (residualShape movingFive x z) k
      < highScale r k*d*(dual k+1) := by
  dsimp only
  apply bound (by decide) (by decide) hx hz
  fin_cases k <;> decide +kernel

theorem linear_ordinate (x z : ℕ) (hx : x ≤ freeFive.U) (hz : z ≤ freeFive.B) :
    7*highCap x z 1 + highScale 1 1 * pairCap (residualShape freeFive x z) (residualShape movingFive x z) 1
      < highScale 1 1*7*(64220+1) := by
  apply bound (by decide) (by decide) hx hz
  decide +kernel

theorem linear_mixed (x z : ℕ) (hx : x ≤ freeFive.U) (hz : z ≤ freeFive.B) :
    6*highCap x z 2 + highScale 2 2 * pairCap (residualShape freeFive x z) (residualShape movingFive x z) 2
      < highScale 2 2*6*(348044+1) := by
  apply bound (by decide) (by decide) hx hz
  decide +kernel

end PriceReceipt6925

namespace LateReceipt6928
open K1_14 K1_14_2_2 K1_14_2_2_4
open private checkNumerator checked_bound numerator_bound from ProximityPrize.SubmissionLower.Fast032
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def freeZero : Shape := ⟨57,79,17,1160⟩
def movingZero : Shape := ⟨191,265,55,6963⟩
def freeFive : Shape := ⟨216,299,66,3130⟩
def movingFive : Shape := ⟨641,890,185,25837⟩
def full : Shape := ⟨3025,4200,890,84000⟩
def initial : Fin 4 → ℕ := ![7915,182171,857477,8077080]
def dual : Fin 4 → ℕ := ![176,3962,29245,202174]
def threshold : Fin 4 → ℕ := ![3,2,8,7]

private instance (s t : Shape) (d r M : ℕ) (k : Fin 4) :
    Decidable (checkNumerator s t d r M k) := by
  unfold checkNumerator
  split <;> infer_instance

private theorem bound {s t : Shape} {d r x z cap : ℕ} {k : Fin 4}
    (hu : s.U ≤ t.U) (hb : s.B ≤ t.B) (hx : x ≤ s.U) (hz : z ≤ s.B)
    (hc : checkNumerator s t d r (highScale r k*d*(cap+1)) k) :
    d*highCap x z k + highScale r k * pairCap (residualShape s x z) (residualShape t x z) k
      < highScale r k*d*(cap+1) :=
  (numerator_bound s t d r x z k).trans_lt (checked_bound s t d r _ x z k hu hb hx hz hc)

theorem initial_cap (k : Fin 4) (x z : ℕ) (hx : x ≤ freeZero.U) (hz : z ≤ freeZero.B) :
    highCap x z k + pairCap (residualShape freeZero x z) (residualShape movingZero x z) k
      ≤ initial k := by
  have hc : checkNumerator freeZero movingZero 1 1 (highScale 1 k*1*(initial k+1)) k := by
    fin_cases k <;> decide +kernel
  have hs : highScale 1 k = 1 := by fin_cases k <;> rfl
  simpa only [hs,one_mul,Nat.lt_succ_iff] using
    bound (by decide) (by decide) hx hz hc

theorem reserve_square (k : Fin 4) (x z : ℕ) (hx : x ≤ freeFive.U) (hz : z ≤ freeFive.B) :
    let r := threshold k
    let d := (27-r)^2
    d*highCap x z k + highScale r k * pairCap (residualShape freeFive x z) (residualShape movingFive x z) k
      < highScale r k*d*(dual k+1) := by
  dsimp only
  apply bound (by decide) (by decide) hx hz
  fin_cases k <;> decide +kernel

end LateReceipt6928
