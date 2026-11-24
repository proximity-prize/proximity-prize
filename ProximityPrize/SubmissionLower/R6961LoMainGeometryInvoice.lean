import ProximityPrize.SubmissionLower.R6961LoMainGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6961.Lo.MainGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open RescueGeometry (RateOK beforeCuts lambda mu tau)
open Lower6961.Lo.RescueGeometry (heightBound height_spec)
open scoped Classical BigOperators

def degreeRates : List ℕ :=
  [205428085, 163258594, 100438946, 60842910, 37898191, 32689790, 26305018, 28247769, 26305018, 26343271, 33948150, 28235808, 27770200, 41057588, 58516306, 78021741, 261429975]

def heightRates : List ℕ :=
  [1814688, 2346473, 3936188, 6622060, 10747991, 12492989, 15571994, 14488270, 15571994, 15548783, 12021365, 14494498, 14739247, 9907168, 6889868, 5122595, 1387662]

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

theorem main_fee_bound : mainFee ≤ 144095433239244098 := by decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

#print axioms main_fee_bound
#print axioms rate_spec
end Lower6961.Lo.MainGeometry
