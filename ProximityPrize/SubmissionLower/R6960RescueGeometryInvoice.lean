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
    [185818626, 129133477, 146943385, 146945197, 146944569, 129133830, 129133867, 129133651, 146945086, 146942720, 129133651, 129134052, 129133904, 159856720, 155401334, 198768067, 146945049],
    [179378044, 129133013, 129134052, 146944975, 129133867, 129133651, 129133719, 129133622, 146945012, 129133830, 129133622, 129133622, 129133651, 154005122, 149641067, 191596945, 146945123],
    [181733058, 115173753, 129133756, 146945086, 129133651, 129133793, 129133682, 129133682, 129133651, 129133651, 129133129, 129133622, 129133622, 149781012, 144393038, 187541244, 147843055],
    [136033029, 79972174, 74761669, 74761519, 69859172, 69859207, 69859207, 73833280, 69859190, 69859298, 75841228, 71158206, 98079156, 149905130, 145594273, 194227079, 257834722]
  ]

def heightRates : List (List ℕ) :=
  [
    [2517978, 3710256, 3228644, 3228595, 3228612, 3710245, 3710244, 3710250, 3228598, 3228662, 3710250, 3710239, 3710243, 2963823, 3055188, 2325381, 3228599],
    [2613768, 3710272, 3710239, 3228601, 3710244, 3710250, 3710248, 3710251, 3228600, 3710245, 3710251, 3710251, 3710250, 3083820, 3173312, 2432037, 3228597],
    [2578742, 4191562, 3710247, 3228598, 3710250, 3710246, 3710249, 3710249, 3710250, 3710250, 3710268, 3710251, 3710251, 3170442, 3297610, 2492357, 3210183],
    [3523679, 6151897, 6595735, 6595749, 7076308, 7076304, 7076304, 6686741, 7076306, 7076295, 6503777, 6948968, 4977602, 3167897, 3265127, 2392919, 1734182]
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

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 112382657497079418 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 4) : rescueFee rect < 112382657497079419 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms strict_rescue_fee

end Lower6960.RescueGeometry
