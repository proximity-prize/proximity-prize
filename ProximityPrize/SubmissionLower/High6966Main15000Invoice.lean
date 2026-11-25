import ProximityPrize.SubmissionLower.High6966Main15000Books
import ProximityPrize.SubmissionLower.High6966RescueCharge

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

def degreeRates : List ℕ := [280211443, 280211443, 280211443, 280211443, 280211443, 280211443, 280211443, 140105722, 72401517, 140105722, 170456467, 46751052, 76805308, 105940326, 105940326, 147811582, 196180823]

def heightRates : List ℕ := [1292414, 1292414, 1292414, 1292414, 1292414, 1292414, 1292414, 2769456, 5538912, 2769456, 2228239, 8683294, 5209977, 3721412, 3721412, 2604989, 1917832]

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

def pivot : ℚ := min (47843/5) (tau*rankB)

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 18 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_bound : mainFee ≤ 185233047747540462 := by decide +kernel

theorem credit_guard : (1838347228855:ℚ)≤P1_7_4.running (beforeCuts rankWeight lossWeight) 18 1 := by decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

#print axioms main_fee_bound
#print axioms rate_spec
end Lower6960.High6966Main15000

end
end Merged_R6960MainGeometryInvoice
