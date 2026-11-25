import ProximityPrize.SubmissionLower.R6961LoRescueGeometryRates

set_option Elab.async false

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
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 43264333, 26305018, 43264333, 58951914, 54927354, 67102547, 122503410, 144971839, 174572615, 92904309],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 33345784, 26305018, 41865663, 57090454, 53295894, 65348417, 120234804, 142246858, 170518925, 94344879],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 27084131, 26305018, 33185839, 45422390, 42778150, 53317761, 91906759, 116570970, 140974781, 98954703],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 28332378, 51919004, 67629849, 69223058, 112771068],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 27142756, 37788215, 51856792, 110472090],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 31813753, 55343020, 55343020, 36422330, 79893767],
    [26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 26305018, 34091301, 26305018, 28960949, 37711616, 30621441, 40584882, 43932089, 42192204, 42192204, 84115319],
    [52610031, 52610031, 52610031, 52610031, 50134265, 50134265, 44100766, 58375514, 44100766, 79523315, 58375514, 43710796, 60682684, 43932089, 52610031, 53386571, 129911338],
    [43747294, 43747294, 43747294, 43747294, 39095529, 39095529, 39095529, 39095529, 26305018, 33779288, 45821641, 26305018, 30155303, 41437082, 46203948, 60717286, 138696968],
    [61759601, 61759601, 66943090, 80876925, 80876925, 65560191, 80404006, 61759601, 34128381, 55343020, 61759601, 61759601, 65560191, 46850438, 74761620, 70872218, 128092601],
    [60035161, 60035161, 65560191, 65560191, 65560191, 58375514, 65560191, 60992961, 60992961, 80404006, 61759601, 61759601, 65024992, 47642770, 66070750, 90261369, 121299326],
    [45821641, 45821641, 45821641, 45821641, 45821641, 45821641, 45821641, 61759601, 27606032, 43768778, 58375514, 58375514, 65560191, 86967597, 69859220, 59285613, 84266988],
    [41579454, 41579454, 41579454, 41579454, 41579454, 41579454, 41579454, 45821641, 31337774, 45821641, 50134265, 41835658, 55343020, 85074685, 62332859, 62332859, 88523887]
  ]

def heightRates : List (List ℕ) :=
  [
    [15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 9389987, 15568128, 9389987, 6838029, 7352994, 5985722, 3192782, 2660314, 2176621, 4267882],
    [15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 12240201, 15568128, 9708983, 7069378, 7585441, 6147163, 3256184, 2720045, 2225492, 4195255],
    [15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15113605, 15568128, 12299101, 8933499, 9498777, 7582325, 4318173, 3358579, 2747929, 3997839],
    [15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 14440625, 7791841, 5937948, 5793601, 3481013],
    [15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15079765, 10776259, 7801626, 3560802],
    [15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 12838644, 7293771, 7293771, 11187098, 4992066],
    [15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 15568128, 11965664, 15568128, 14123218, 10797807, 13346881, 10019204, 9240568, 9629890, 9629890, 4736510],
    [7683161, 7683161, 7683161, 7683161, 8072534, 8072534, 9205813, 6904360, 9205813, 5017644, 6904360, 9290085, 6638855, 9240568, 7683161, 7572521, 2990436],
    [9281918, 9281918, 9281918, 9281918, 10408509, 10408509, 10408509, 10408509, 15568128, 12080563, 8851235, 15568128, 13554248, 9812790, 8778957, 6634873, 2797858],
    [6514925, 6514925, 6000169, 4928760, 4928760, 6125461, 4956835, 6514925, 11952856, 7293771, 6514925, 6514925, 6125461, 8656734, 5346425, 5655472, 3036577],
    [6713370, 6713370, 6125461, 6125461, 6125461, 6904360, 6125461, 6603148, 6603148, 4956835, 6514925, 6514925, 6180306, 8506938, 6079204, 4401126, 3226433],
    [8851235, 8851235, 8851235, 8851235, 8851235, 8851235, 8851235, 6514925, 14825640, 9277111, 6904360, 6904360, 6125461, 4567182, 5735964, 6799627, 4727506],
    [9778306, 9778306, 9778306, 9778306, 9778306, 9778306, 9778306, 8851235, 13036703, 8851235, 8072534, 9716250, 7293771, 4679557, 6456180, 6456180, 4488722]
  ]

def degreeRate (rect : Fin 13) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0

def heightRate (rect : Fin 13) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

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

private theorem checked_rates (rect : Fin 13) (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem rate_spec (rect : Fin 13) {i : ℕ} (hi : i<17) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def lambda : ℚ := ((262144 : ℚ)/179798)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179798-endpointDegree : ℕ)

def rankB (rect : Fin 13) : ℕ := initialCap rect 2+2

def rankJ (rect : Fin 13) : ℕ := initialCap rect 1+1

def tau : ℚ := 49/100

def pivot (rect : Fin 13) : ℚ := min (47843/5) (tau*rankB rect)

def rankWeight (rect : Fin 13) : Mass :=
  ![0,4*lambda*rankB rect*tau+mu-4*lambda*pivot rect,
    4*lambda*rankJ rect*(1-tau)+rankB rect,0]

def rankRound (rect : Fin 13) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1

def lossWeight (rect : Fin 13) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k

def lossLimit (rect : Fin 13) : ℚ :=
  weightedBill 18 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect

def rescueFee (rect : Fin 13) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

theorem rescue_fee_bound (rect : Fin 13) : rescueFee rect ≤ 34917696728717810 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 13) : rescueFee rect < 34917696728717811 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 13) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms strict_rescue_fee

end Lower6961.Lo.RescueGeometry
