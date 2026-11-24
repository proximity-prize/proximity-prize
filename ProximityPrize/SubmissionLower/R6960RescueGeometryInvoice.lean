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
    [185818626, 110433204, 89307106, 80981569, 73536324, 70050751, 70333505, 78862332, 51474031, 80824946, 107178122, 90561210, 111399090, 159856701, 155401324, 198768055, 138542104],
    [179378044, 106432694, 85817332, 77706467, 70695292, 67465905, 67744230, 75883229, 49483667, 77575308, 102814332, 87000554, 107157326, 154005122, 149641067, 191596945, 137489413],
    [181733058, 104811364, 80618367, 70841205, 66177076, 65013899, 65389313, 72436304, 46324207, 72672132, 97959228, 82217852, 103210618, 149781012, 144393038, 187541220, 147843055],
    [136033029, 79972168, 61971094, 58419873, 63658503, 67045494, 68100572, 73833280, 44860002, 62051252, 75841228, 71158176, 98079150, 149905130, 145594273, 194227079, 257834722]
  ]

def heightRates : List (List ℕ) :=
  [
    [2517532, 4393752, 5487930, 6071739, 6714662, 7056278, 7028566, 6245329, 9697201, 6083207, 4533097, 5409943, 4352404, 2963299, 3054648, 2324970, 3455218],
    [2613306, 4565008, 5717640, 6343770, 6993108, 7342509, 7311406, 6499049, 10095772, 6354940, 4730274, 5631363, 4533987, 3083274, 3172750, 2431607, 3483679],
    [2578286, 4634414, 6098334, 6978807, 7486539, 7624528, 7577076, 6822473, 10800400, 6799360, 4982963, 5981212, 4709649, 3169881, 3297026, 2491917, 3209615],
    [3523055, 6150809, 8009131, 8509917, 7795846, 7389491, 7271584, 6685557, 11161993, 7998999, 6502626, 6947741, 4976721, 3167336, 3264549, 2392496, 1733875]
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

def lambda : ℚ := ((262144 : ℚ)/179818)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179818-endpointDegree : ℕ)

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

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 118460744183568976 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 4) : rescueFee rect < 118687375614631597 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms strict_rescue_fee

end Lower6960.RescueGeometry
