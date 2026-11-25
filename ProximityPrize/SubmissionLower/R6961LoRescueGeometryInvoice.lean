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
    [26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 30544174, 26305019, 43246574, 58758795, 54760875, 66815348, 94483470, 129171563, 173471576, 101355830],
    [26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 29873664, 26305019, 41849024, 56908455, 53139095, 65077778, 92852560, 126635663, 169481166, 102796400],
    [26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 33174800, 45296231, 42669511, 53130002, 78795424, 106366863, 140253582, 107406224],
    [26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 28549128, 42036912, 67901595, 69623707, 122905672],
    [26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 32601825, 120000631],
    [26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 95547160],
    [53514770, 36189304, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 27179207, 26305019, 34454151, 48659301, 54700401, 71200887, 151891607],
    [42898729, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 34737713, 41110874, 52637138, 136754129],
    [27212974, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 28360116, 36430272, 130818999],
    [26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 26305019, 99707262]
  ]

def heightRates : List (List ℕ) :=
  [
    [15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 13385035, 15572861, 9396818, 6862339, 7378957, 6013571, 4189542, 3007566, 2190562, 3897708],
    [15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 13689904, 15572861, 9715966, 7094906, 7610095, 6176774, 4271790, 3078232, 2243139, 3836904],
    [15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 12306907, 8962218, 9525982, 7611391, 5069444, 3704405, 2764578, 3668322],
    [15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 14332144, 9670444, 5915126, 5759053, 3182508],
    [15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 12528161, 3263721],
    [15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 4142881],
    [7556553, 11265864, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15064349, 15572861, 11843930, 8329940, 7387576, 5631069, 2535609],
    [9474676, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 11745953, 9894810, 7681634, 2841308],
    [15045821, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 14430572, 11188101, 2971444],
    [15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 15572861, 3967291]
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

def lambda : ℚ := ((262144 : ℚ)/179808)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179808-endpointDegree : ℕ)

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

theorem rescue_fee_bound (rect : Fin 10) : rescueFee rect ≤ 41008681981222112 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 10) : rescueFee rect < 41008681981222113 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 10) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms strict_rescue_fee

end Lower6961.Lo.RescueGeometry
