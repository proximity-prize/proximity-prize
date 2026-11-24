import ProximityPrize.SubmissionLower.R6961LoRescueGeometryRates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open scoped Classical BigOperators

def degreeRates : List (List ℕ) :=
  [
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 28725133, 26305018, 39562813, 53776714, 50435674, 62082867, 89228749, 121454682, 161980055, 83116262],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 28158783, 26305018, 38376143, 52211334, 49061254, 60616097, 87898559, 119360222, 158646925, 84557002],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 30756559, 42023510, 39828390, 50021921, 75344463, 101298542, 132705661, 89167370],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 27718268, 41196199, 65145499, 67260474, 101713403],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 32123792, 99437056],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 79515400],
    [52815968, 36041685, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26776298, 26305018, 34251751, 48274759, 54209741, 70630832, 128421884],
    [42584180, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 34099320, 40229143, 51682461, 115369918],
    [27071207, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 27879342, 35908590, 110074917],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 83672604]
  ]

def heightRates : List (List ℕ) :=
  [
    [15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 14243100, 15571994, 10288919, 7518801, 8027123, 6483408, 4454292, 3222892, 2367731, 4797011],
    [15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 14534607, 15571994, 10613509, 7747789, 8260001, 6648168, 4521370, 3281441, 2423149, 4711459],
    [15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 13290576, 9673152, 10219482, 8093957, 5307499, 3899908, 2929913, 4457387],
    [15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 14767741, 9873587, 6169489, 5972897, 3882398],
    [15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 12714810, 3978473],
    [15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 5019437],
    [7655720, 11312976, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15295089, 15571994, 11913200, 8395941, 7457089, 5676062, 3028127],
    [9544550, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 11965865, 10114702, 7830988, 3392988],
    [15124820, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 14680117, 11356018, 3575474],
    [15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 15571994, 4763975]
  ]

def degreeRate (rect : Fin 10) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0

def heightRate (rect : Fin 10) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem checked_rates (rect : Fin 10) (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem rate_spec (rect : Fin 10) {i : ℕ} (hi : i<17) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def lambda : ℚ := ((262144 : ℚ)/179818)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179818-endpointDegree : ℕ)

def rankB (rect : Fin 10) : ℕ := initialCap rect 2+2

def rankJ (rect : Fin 10) : ℕ := initialCap rect 1+1

def tau : ℚ := 49/100

def pivot (rect : Fin 10) : ℚ := min (47843/5) (tau*rankB rect)

def rankWeight (rect : Fin 10) : Mass :=
  ![0,4*lambda*rankB rect*tau+mu-4*lambda*pivot rect,
    4*lambda*rankJ rect*(1-tau)+rankB rect,0]

def rankRound (rect : Fin 10) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1

def lossWeight (rect : Fin 10) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k

def lossLimit (rect : Fin 10) : ℚ :=
  weightedBill 18 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect

def rescueFee (rect : Fin 10) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

theorem rescue_fee_bound (rect : Fin 10) : rescueFee rect ≤ 37710000000000000 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 10) : rescueFee rect < 37710000000000001 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 10) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms strict_rescue_fee

end Lower6961.Lo.RescueGeometry
