import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.High6966Main13200Books
import ProximityPrize.SubmissionLower.High6966Main13200
set_option Elab.async false



set_option Elab.async false
section Merged_R6960MainGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.High6966Main13200
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open Rescue6966 (RateOK beforeCuts lambda mu tau)
open Lower6960.Rescue6966 (heightBound height_spec)
open scoped Classical BigOperators

def degreeRates : List ℕ := [236015569, 234462842, 231641064, 229368020, 231403332, 174577109, 33853060, 33853060, 37521486, 36922011, 58351574, 59412511, 100317222, 71401690, 71506650, 119291198, 175686735]

def heightRates : List ℕ := [1564568, 1577345, 1600566, 1619271, 1602522, 2179013, 12066941, 12066941, 10867413, 11048624, 6915196, 6792648, 3944774, 5619709, 5611359, 3286244, 2165620]

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

def tau : ℚ := 207/500

def pivot : ℚ := 13746779/100

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 18 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_bound : mainFee ≤ 127815628075157321 := by decide +kernel

theorem credit_guard : (1729755992975:ℚ)≤P1_7_4.running (beforeCuts rankWeight lossWeight) 18 1 := by decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

#print axioms main_fee_bound
#print axioms rate_spec
end Lower6960.High6966Main13200

end
end Merged_R6960MainGeometryInvoice
