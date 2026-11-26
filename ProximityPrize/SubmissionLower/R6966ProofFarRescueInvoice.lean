import ProximityPrize.SubmissionLower.R6966ProofFarRescueRates
import ProximityPrize.SubmissionLower.R6960RescueGeometryInvoice

set_option Elab.async false


noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.FarRescueGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open scoped Classical BigOperators

def degreeRates : List (List ℕ) :=
  [[250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 107178122, 90561210, 111399090, 159856701, 155401324, 198768055, 150749576], [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 102814332, 87000554, 107157326, 154005122, 149641067, 191596945, 150749576], [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 97959228, 82217852, 103210618, 149781012, 144393038, 187541220, 150749576], [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 88312895, 79543745, 98079150, 149905130, 145594273, 194227079, 257834722]]

def heightRates : List (List ℕ) :=
  [[1780408, 1738050, 2203425, 2423996, 3140555, 3230824, 3712816, 4463137, 3603611, 4983716, 4537032, 5414639, 4356182, 2965871, 3057299, 2326988, 3152757], [1780408, 1738050, 2203425, 2423996, 3140555, 3230824, 3712816, 4463137, 3603611, 4983716, 4734379, 5636250, 4537923, 3085950, 3175504, 2433717, 3152757], [1780408, 1738050, 2203425, 2423996, 3140555, 3230824, 3712816, 4463137, 3603611, 4983716, 4987288, 5986403, 4713736, 3172632, 3299888, 2494079, 3152757], [1780408, 1738050, 2203425, 2423996, 3140555, 3230824, 3712816, 4463137, 3603611, 4983716, 5554572, 6192666, 4981041, 3170085, 3267382, 2394572, 1735380]]

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

def lambda : ℚ := ((262144 : ℚ)/179769)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179769-endpointDegree : ℕ)

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

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 119924194219759250 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 4) : rescueFee rect < 119924194219759251 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel


end Lower6960.FarRescueGeometry
