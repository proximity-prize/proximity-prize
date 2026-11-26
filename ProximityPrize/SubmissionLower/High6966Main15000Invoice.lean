import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.High6966Main15000Books
import ProximityPrize.SubmissionLower.High6966Main13200
set_option Elab.async false



set_option Elab.async false
section Merged_R6960MainGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.High6966Main15000
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open Rescue6966 (RateOK beforeCuts lambda mu tau)
open Lower6960.Rescue6966 (heightBound height_spec)
open scoped Classical BigOperators

def degreeRates : List ℕ := [241715024, 240810775, 234510598, 237061080, 240851470, 180554299, 34489997, 34489997, 38845549, 38217945, 60369283, 61466906, 103291491, 73937253, 73997839, 126148452, 176265517]

def heightRates : List ℕ := [1517666, 1525107, 1576952, 1555964, 1524772, 2106872, 11841239, 11841239, 10490604, 10667349, 6682421, 6555966, 3819133, 5418009, 5413190, 3094385, 2158635]

def degreeRate (i : ℕ) : ℕ := degreeRates.getD i 0

def heightRate (i : ℕ) : ℕ := heightRates.getD i 0

private theorem checked_rates (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate i.val : ℚ) ∧
      min seedLimit (dotQ (cutWeight 0 i.val) (history i.val)) ≤ (degreeRate i.val : ℚ) ∧
      heightBound (degreeRate i.val) ≤ (heightRate i.val : ℚ) := by
  fin_cases i <;> decide +kernel

theorem rate_spec {i : ℕ} (hi : i<17) :
    RateOK (degreeRate i) (heightRate i) ∧
      min seedLimit (dotQ (cutWeight 0 i) (history i)) ≤ degreeRate i := by
  obtain ⟨base,degree,height⟩ := checked_rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB : ℕ := initialCap 2+2

def rankJ : ℕ := initialCap 1+1

def tau : ℚ := 1043/2500

def pivot : ℚ := 3468161/25

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 18 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_bound : mainFee ≤ 130933022881678518 := by decide +kernel

theorem credit_guard : (1729199597045:ℚ)≤P1_7_4.running (beforeCuts rankWeight lossWeight) 18 1 := by decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

#print axioms main_fee_bound
#print axioms rate_spec
end Lower6960.High6966Main15000

end
end Merged_R6960MainGeometryInvoice
