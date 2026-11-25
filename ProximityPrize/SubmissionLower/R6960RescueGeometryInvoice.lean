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
    [185043560, 109937049, 88848207, 80400640, 73162046, 70114100, 70615029, 79720288, 51946852, 82407157, 110174300, 92672929, 114221339, 163335932, 159134571, 203438581, 143300868],
    [178641878, 105961843, 85381999, 77154509, 70339295, 67525235, 68010692, 76697051, 49932063, 79071980, 105644121, 88998944, 109827321, 157305606, 153182906, 196027998, 142187977],
    [181190065, 104465706, 80299533, 70434417, 65913723, 65114349, 65641761, 73029214, 46650315, 73740953, 99957002, 83746967, 105058006, 152189520, 146978091, 190820550, 152240314],
    [135052727, 79467097, 61631379, 58289757, 63770849, 67236920, 68352757, 74190898, 45076042, 62264523, 76024565, 71516118, 98581029, 150945465, 146789647, 195859479, 266170054]
  ]

def heightRates : List (List ℕ) :=
  [
    [2529953, 4416555, 5518420, 6116483, 6753735, 7052567, 7003454, 6174447, 9608881, 5969464, 4406396, 5280496, 4233087, 2892989, 2979160, 2258751, 3327734],
    [2625182, 4586788, 5751554, 6393042, 7030488, 7338477, 7284207, 6432016, 10003742, 6229680, 4600394, 5509043, 4421254, 3016672, 3101230, 2366553, 3357833],
    [2587276, 4650858, 6125097, 7021162, 7518632, 7614527, 7549035, 6766759, 10728153, 6696977, 4880715, 5871321, 4625494, 3121605, 3228493, 2444017, 3120563],
    [3550817, 6196018, 8056916, 8532818, 7784402, 7370709, 7245967, 6652863, 11111021, 7974866, 6489309, 6915108, 4952354, 3147121, 3233374, 2369060, 1681886]
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

def lambda : ℚ := ((262144 : ℚ)/179798)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179798-endpointDegree : ℕ)

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

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 119400000000000000 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 4) : rescueFee rect < 119400000000000001 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms strict_rescue_fee

end Lower6960.RescueGeometry

end
