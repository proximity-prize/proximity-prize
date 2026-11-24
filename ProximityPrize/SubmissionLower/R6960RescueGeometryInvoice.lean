import ProximityPrize.SubmissionLower.R6960RescueGeometryRates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open scoped Classical BigOperators

def degreeRates : List (List ℕ) :=
  [
    [189498286, 161625854, 128361975, 146945198, 149575894, 141061697, 131659336, 87397241, 59815516, 101460080, 129133867, 110710035, 170456672, 165730530, 161431580, 206152089, 146221140],
    [182864463, 155886299, 123891264, 146945197, 144339646, 141052526, 131732962, 87455251, 57477071, 96497204, 129133830, 111315102, 170456739, 159577988, 155362509, 198602831, 145075247],
    [184261309, 156567153, 125143302, 143617747, 146945294, 137082771, 129134089, 94698251, 55928055, 94248026, 120547324, 101951261, 146945244, 153849613, 148570537, 192730934, 154962940],
    [136725248, 124852684, 114770775, 94698023, 92843819, 86967631, 75350342, 74500663, 51994873, 64599142, 77885168, 88455240, 100456628, 151424555, 147114701, 196276597, 271301566]
  ]

def heightRates : List (List ℕ) :=
  [
    [2463250, 2927544, 3736856, 3228595, 3174649, 3387695, 3641951, 5607687, 8313286, 4801607, 3710244, 4382677, 2746455, 2843371, 2931528, 2230834, 3248175],
    [2561915, 3045243, 3890998, 3228595, 3299054, 3387943, 3639960, 5604079, 8660052, 5059951, 3710245, 4356771, 2746454, 2969539, 3055985, 2327839, 3279162],
    [2541140, 3031281, 3847830, 3318575, 3228593, 3495292, 3710238, 5153596, 8905446, 5181596, 4006291, 4776039, 3228594, 3087009, 3195265, 2415171, 3064178],
    [3504960, 3857850, 4208812, 5153608, 5268932, 5634407, 6545591, 6621320, 9597863, 7678311, 6329671, 5541884, 4853842, 3136739, 3225119, 2362437, 1649209]
  ]

def degreeRate (rect : Fin 4) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0

def heightRate (rect : Fin 4) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

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

private theorem checked_rates (rect : Fin 4) (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem rate_spec (rect : Fin 4) {i : ℕ} (hi : i<17) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def lambda : ℚ := ((262144 : ℚ)/179808)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179808-endpointDegree : ℕ)

def rankB (rect : Fin 4) : ℕ := initialCap rect 2+2

def rankJ (rect : Fin 4) : ℕ := initialCap rect 1+1

def tau : ℚ := 49/100

def pivot (rect : Fin 4) : ℚ := min (47843/5) (tau*rankB rect)

def rankWeight (rect : Fin 4) : Mass :=
  ![0,4*lambda*rankB rect*tau+mu-4*lambda*pivot rect,
    4*lambda*rankJ rect*(1-tau)+rankB rect,0]

def rankRound (rect : Fin 4) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1

def lossWeight (rect : Fin 4) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k

def lossLimit (rect : Fin 4) : ℚ :=
  weightedBill 18 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect

def rescueFee (rect : Fin 4) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 117270526256058618 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 4) : rescueFee rect < 117270526256058619 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms strict_rescue_fee

end Lower6960.RescueGeometry
