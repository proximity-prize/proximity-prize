import ProximityPrize.SubmissionLower.MergedInfra6815_13
import ProximityPrize.SubmissionLower.Night6836FlowKernel
section BP0
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
namespace ProximityPrize.SubmissionLower.Night6836AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open Night6836FlowSources Night6836FlowStages Night6836FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
def menu : Fin 5 → List Stage
  | 0 => [.first]
  | 1 => [.second]
  | 2 => [.src394]
  | 3 => [.src481, .src485]
  | 4 => [.src700, .src701, .src702, .src703, .src704, .src705, .src706, .src707, .src708, .src709, .src710, .src711, .src712, .src713, .src714, .src715, .src716, .src717, .src718]
def capStage : Fin 5 → Stage
  | 0 => .first
  | 1 => .second
  | 2 => .src394
  | 3 => .src485
  | 4 => .src718
def fee : Fin 5 → ℕ
  | 0 => 8433335461657536
  | 1 => 2796436072784221
  | 2 => 1131584383633814
  | 3 => 1797872865458233
  | 4 => 10840806336973704
def sourceGroup : Stage → ℕ
  | .primary => 5
  | .first => 0
  | .second => 1
  | .src394 => 2
  | .src481 => 3
  | .src485 => 3
  | .src700 => 4
  | .src701 => 4
  | .src702 => 4
  | .src703 => 4
  | .src704 => 4
  | .src705 => 4
  | .src706 => 4
  | .src707 => 4
  | .src708 => 4
  | .src709 => 4
  | .src710 => 4
  | .src711 => 4
  | .src712 => 4
  | .src713 => 4
  | .src714 => 4
  | .src715 => 4
  | .src716 => 4
  | .src717 => 4
  | .src718 => 4
private theorem direction_cumulative (P : ResidualSupportParameters) :
    (reducedAgreementDirection P).all = 2 * P.s - 2 ∧
      middle (reducedAgreementDirection P) = 2 * P.ys - 2 ∧
      total (reducedAgreementDirection P) = 2 * P.total - 2 := by
  have hs := P.one_le_s
  have hy := P.s_le_ys
  have ht := P.ys_le_total
  simp only [reducedAgreementDirection, middle, total, true_and]
  omega

private theorem direction_mono {f g : FlagDegree} (hf : 0 < f.all) (hg : 0 < g.all)
    (hfg : Below f g) :
    Below (reducedAgreementDirection (stageSupport f hf))
      (reducedAgreementDirection (stageSupport g hg)) := by
  obtain ⟨hr, hy, ht⟩ := hfg
  obtain ⟨hrf, hyf, htf⟩ := direction_cumulative (stageSupport f hf)
  obtain ⟨hrg, hyg, htg⟩ := direction_cumulative (stageSupport g hg)
  unfold Below
  rw [hrf, hrg, hyf, hyg, htf, htg]
  have hy' := max_le_max_left 2 hy
  have ht' := max_le_max_left 2 ht
  change _ ∧ (2 * max 2 (middle f) - 2 ≤ 2 * max 2 (middle g) - 2) ∧
    (2 * max 2 (total f) - 2 ≤ 2 * max 2 (total g) - 2)
  exact ⟨by simpa only [stageSupport] using Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 2,
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hy') 2,
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 ht') 2⟩

private theorem below_scaled_add {f g : FlagDegree} (hfg : Below f g)
    (k : ℕ) (p q : FlagDegree) : Below (k • f + p + q) (k • g + p + q) := by
  obtain ⟨hr, hy, ht⟩ := hfg
  simp only [Below, middle, total, add_all, add_yz, add_zOnly, nsmul_all, nsmul_yz, nsmul_zOnly]
  have hS := Nat.mul_le_mul_left k hr
  have hY := Nat.mul_le_mul_left k hy
  have hT := Nat.mul_le_mul_left k ht
  simp only [middle, total, Nat.mul_add] at hY hT
  omega

theorem price_mono {f g : FlagDegree} (hf : 0 < f.all) (hg : 0 < g.all)
    (hfg : Below f g) (s : Stage) (gain : ℕ) :
    stagePrice f hf s gain ≤ stagePrice g hg s gain := by
  unfold stagePrice
  apply Nat.div_le_div_right
  apply (mixed_mono_first hfg _ _).trans
  apply mixed_mono_third
  unfold stageScaledCut scaledPairFlag
  exact below_scaled_add (direction_mono hf hg hfg) _ _ _


def raw (r y t : ℕ) : FlagDegree := ⟨t-y,y-r,r⟩

theorem raw_cumul {r y t : ℕ} (ry : r≤y) (yt : y≤t) :
    (raw r y t).all=r ∧ middle (raw r y t)=y ∧ total (raw r y t)=t := by
  exact ⟨rfl,by change y-r+r=y;omega,by change t-y+(y-r)+r=t;omega⟩

theorem raw_below {f : FlagDegree} {r y t : ℕ} (ry : r≤y) (yt : y≤t)
    (hr : r≤f.all) (hy : y≤middle f) (ht : t≤total f) : Below (raw r y t) f := by
  obtain ⟨er,ey,et⟩ := raw_cumul ry yt
  exact ⟨er.trans_le hr,ey.trans_le hy,et.trans_le ht⟩

theorem below_raw {f : FlagDegree} {r y t : ℕ} (ry : r≤y) (yt : y≤t)
    (hr : f.all≤r) (hy : middle f≤y) (ht : total f≤t) : Below f (raw r y t) := by
  obtain ⟨er,ey,et⟩ := raw_cumul ry yt
  exact ⟨hr.trans_eq er.symm,hy.trans_eq ey.symm,ht.trans_eq et.symm⟩

def priceAt (j : Fin 5) (r y t : ℕ) : ℕ :=
  if h : 0<r then stagePrice (raw r y t) h (capStage j) (capStage j).numbers.slopeCap else 0

def gateAt (s : Stage) (r y t : ℕ) : Bool := decide
  (evalPowerBandBudget weightGain t y r (s.numbers.totalCap-t) (s.numbers.middleCap-y)
    (s.numbers.slopeCap-r) (min (s.numbers.totalCap/t) (min (s.numbers.middleCap/y)
    (s.numbers.slopeCap/r))) < s.numbers.gap)

theorem gateOf {s : Stage} {r y t : ℕ} (ry : r≤y) (yt : y≤t) (h : gateAt s r y t = true) :
    adaptiveGate s.numbers (raw r y t) := by
  obtain ⟨er,ey,et⟩ := raw_cumul ry yt
  unfold adaptiveGate adaptiveBand LocatorPhase6800Oracle.SourceNumbers.fuel
  rw [er,ey,et]
  simpa only [gateAt,decide_eq_true_eq,evalPowerBandBudget_eq] using h

def Prior (j : ℕ) (f : FlagDegree) : Prop :=
  ∀ i : Fin 5, i.val < j → ∀ s ∈ menu i, ¬adaptiveGate s.numbers f

private theorem member_source (s : Stage) (h : sourceGroup s<5) :
    s∈menu ⟨sourceGroup s,h⟩ := by
  cases s <;> first | exact False.elim (Nat.lt_irrefl 5 h) | (repeat' first | exact List.Mem.head _ | apply List.Mem.tail)

theorem prior_contra {j : ℕ} {f : FlagDegree} (prev : Prior j f) (jle : j≤5)
    (s : Stage) {r y t : ℕ} (pos : 0<r) (ry : r≤y) (yt : y≤t)
    (hr : r≤f.all) (hy : y≤middle f) (ht : t≤total f)
    (check : (decide (sourceGroup s < j) && gateAt s r y t) = true) : False := by
  have ⟨a,b⟩ := Bool.and_eq_true_iff.mp check
  have z := of_decide_eq_true a
  exact prev ⟨sourceGroup s,z.trans_le jle⟩ z s (member_source s _) (adaptiveGate_mono _
    (raw_below ry yt hr hy ht) pos (gateOf ry yt b))

inductive Tile where
  | empty | full | excluded (s : Stage) | cut (t : ℕ) (s : Stage)
  | rank (m : ℕ) (l h : Tile) | middle (m : ℕ) (l h : Tile)

def checkTile (j : Fin 5) (rl rh yl yh : ℕ) : Tile → Bool
  | .empty => decide (yh<rl)
  | .full => decide (yh≤83491 ∧ priceAt j (min rh yh) yh 83491 ≤ fee j)
  | .excluded s => decide (sourceGroup s<j.val) && gateAt s rl (max yl rl) (max yl rl)
  | .cut t s => decide (yh≤t ∧ priceAt j (min rh yh) yh t ≤ fee j) &&
      (decide (sourceGroup s<j.val) && gateAt s rl (max yl rl) (max (max yl rl) (t+1)))
  | .rank m l h => checkTile j rl m yl yh l && checkTile j (m+1) rh yl yh h
  | .middle m l h => checkTile j rl rh yl m l && checkTile j rl rh (m+1) yh h

private theorem upperPrice {j : Fin 5} {f : FlagDegree} {rh yh : ℕ} (hp : 0<f.all)
    (hr1:f.all≤rh) (hy1:middle f≤yh) {t:ℕ} (yt:yh≤t) (ht:total f≤t) :
    stagePrice f hp (capStage j) (capStage j).numbers.slopeCap ≤ priceAt j (min rh yh) yh t := by
    have hry : f.all ≤ middle f := Nat.le_add_left _ _
    have hR := le_min hr1 (hry.trans hy1)
    rw [priceAt,dif_pos (hp.trans_le hR)]
    exact price_mono hp _ (below_raw (min_le_right _ _) yt hR hy1 ht) _ _

theorem cost_of_tile (j : Fin 5) (f : FlagDegree) (hp : 0<f.all)
    (hT : total f≤83491) (prev : Prior j.val f) (tree : Tile) (rl rh yl yh : ℕ)
    (check : checkTile j rl rh yl yh tree=true) (pos : 0<rl)
    (hr0:rl≤f.all) (hr1:f.all≤rh) (hy0:yl≤middle f) (hy1:middle f≤yh) :
    stagePrice f hp (capStage j) (capStage j).numbers.slopeCap ≤ fee j := by
  have hry : f.all ≤ middle f := Nat.le_add_left _ _
  have hyt : middle f ≤ total f := by simp only [middle,total]; omega
  induction tree generalizing rl rh yl yh with
  | empty => exact False.elim (by have hh := of_decide_eq_true check; omega)
  | full => have z := of_decide_eq_true check; exact (upperPrice hp hr1 hy1 z.1 hT).trans z.2
  | excluded s =>
    exact False.elim (prior_contra prev (by omega) s pos (le_max_right _ _) le_rfl hr0
      (max_le hy0 (hr0.trans hry)) ((max_le hy0 (hr0.trans hry)).trans hyt) check)
  | cut t s =>
    rcases Bool.and_eq_true_iff.mp check with ⟨a,b⟩
    have z := of_decide_eq_true a
    by_cases ht : total f≤t
    · exact (upperPrice hp hr1 hy1 z.1 ht).trans z.2
    · exact False.elim (prior_contra prev (by omega) s pos (le_max_right _ _) (le_max_left _ _)
        hr0 (max_le hy0 (hr0.trans hry)) (max_le ((max_le hy0 (hr0.trans hry)).trans hyt) (by omega)) b)
  | rank m l h il ih =>
    obtain ⟨c,d⟩ := Bool.and_eq_true_iff.mp check
    by_cases q : f.all≤m
    · exact il _ _ _ _ c pos hr0 q hy0 hy1
    · exact ih _ _ _ _ d (by omega) (by omega) hr1 hy0 hy1
  | middle m l h il ih =>
    obtain ⟨c,d⟩ := Bool.and_eq_true_iff.mp check
    by_cases q : middle f≤m
    · exact il _ _ _ _ c pos hr0 hr1 hy0 q
    · exact ih _ _ _ _ d pos hr0 hr1 (by omega) hy1

end ProximityPrize.SubmissionLower.Night6836AdaptiveCert

end BP0

section BP1
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
namespace ProximityPrize.SubmissionLower.Night6836AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open Night6836FlowSources Night6836FlowStages Night6836FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
def tree0 : Tile := .full
set_option maxHeartbeats 150000000 in
theorem checkedFee0 : checkTile 0 1 99 1 444 tree0=true := by decide +kernel
end ProximityPrize.SubmissionLower.Night6836AdaptiveCert

end BP1

section BP2
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
namespace ProximityPrize.SubmissionLower.Night6836AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open Night6836FlowSources Night6836FlowStages Night6836FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
def tree1 : Tile := (.middle 222 (.rank 50 (.middle 111 (.rank 25 (.middle 56 .full (.rank 13 .full (.cut 64978 .first))) (.middle 56 (.rank 38 (.cut 71496 .first) (.cut 58062 .first)) (.rank 38 (.middle 84 (.cut 59428 .first) (.rank 32 (.cut 56366 .first) (.middle 98 (.cut 54510 .first) (.cut 50457 .first)))) (.middle 84 (.rank 44 (.cut 53554 .first) (.cut 48715 .first)) (.rank 44 (.middle 98 (.cut 49194 .first) (.rank 41 (.cut 47899 .first) (.cut 45564 .first))) (.middle 98 (.cut 44773 .first) (.rank 47 (.cut 43426 .first) (.cut 41463 .first)))))))) (.rank 25 (.middle 167 (.rank 13 (.cut 61596 .first) (.middle 139 (.rank 19 (.cut 62722 .first) (.cut 55166 .first)) (.rank 19 (.cut 53893 .first) (.middle 153 (.cut 51129 .first) (.rank 22 (.cut 50570 .first) (.cut 47542 .first)))))) (.rank 13 (.middle 195 (.cut 53558 .first) (.cut 47420 .first)) (.middle 195 (.rank 19 (.middle 181 (.cut 50238 .first) (.cut 46979 .first)) (.middle 181 (.rank 22 (.cut 47156 .first) (.middle 174 (.cut 45895 .first) (.cut 44335 .first))) (.rank 22 (.cut 44099 .first) (.middle 188 (.cut 42856 .first) (.cut 41450 .first))))) (.rank 19 (.middle 209 (.cut 44056 .first) (.cut 41599 .first)) (.middle 209 (.rank 22 (.cut 41344 .first) (.cut 38841 .first)) (.cut 36633 .first)))))) (.middle 167 (.rank 38 (.middle 139 (.rank 32 (.middle 125 (.cut 51961 .first) (.rank 29 (.cut 50910 .first) (.middle 132 (.cut 49951 .first) (.cut 48055 .first)))) (.middle 125 (.rank 35 (.cut 49133 .first) (.middle 118 (.cut 48451 .first) (.cut 46556 .first))) (.rank 35 (.middle 132 (.cut 47239 .first) (.rank 34 (.cut 46292 .first) (.cut 45449 .first))) (.middle 132 (.rank 37 (.cut 45564 .first) (.cut 44762 .first)) (.rank 37 (.middle 136 (.cut 44565 .first) (.rank 36 (.cut 44630 .first) (.cut 43835 .first))) (.middle 136 (.cut 43780 .first) (.cut 43063 .first))))))) (.rank 32 (.middle 153 (.rank 29 (.middle 146 (.cut 49008 .first) (.rank 27 (.cut 49110 .first) (.cut 47211 .first))) (.middle 146 (.rank 31 (.cut 47151 .first) (.cut 46263 .first)) (.rank 31 (.middle 150 (.cut 46152 .first) (.cut 45423 .first)) (.middle 150 (.cut 45283 .first) (.cut 44568 .first))))) (.rank 29 (.middle 160 (.rank 27 (.cut 47342 .first) (.cut 45512 .first)) (.rank 27 (.cut 45670 .first) (.middle 164 (.cut 44582 .first) (.cut 43903 .first)))) (.middle 160 (.rank 31 (.middle 157 (.rank 30 (.cut 45340 .first) (.cut 44477 .first)) (.rank 30 (.cut 44637 .first) (.cut 43787 .first))) (.middle 157 (.cut 43639 .first) (.cut 42960 .first))) (.rank 31 (.middle 164 (.rank 30 (.cut 43724 .first) (.cut 42890 .first)) (.rank 30 (.cut 43057 .first) (.cut 42235 .first))) (.middle 164 (.middle 162 (.cut 42517 .first) (.cut 42079 .first)) (.middle 166 (.cut 41648 .first) (.cut 41435 .first))))))) (.middle 153 (.rank 35 (.middle 146 (.rank 34 (.middle 143 (.cut 45294 .first) (.cut 44565 .first)) (.middle 143 (.cut 44468 .first) (.cut 43753 .first))) (.rank 34 (.middle 150 (.rank 33 (.cut 44439 .first) (.cut 43620 .first)) (.rank 33 (.cut 43736 .first) (.cut 42929 .first))) (.middle 150 (.middle 148 (.cut 43284 .first) (.cut 42823 .first)) (.middle 152 (.cut 42369 .first) (.cut 42144 .first))))) (.middle 146 (.rank 37 (.middle 143 (.rank 36 (.cut 43667 .first) (.cut 42888 .first)) (.rank 36 (.cut 42963 .first) (.cut 42196 .first))) (.middle 143 (.middle 141 (.cut 42593 .first) (.cut 42131 .first)) (.middle 145 (.cut 41675 .first) (.cut 41449 .first)))) (.rank 37 (.middle 150 (.rank 36 (.middle 148 (.cut 42503 .first) (.cut 42049 .first)) (.middle 148 (.cut 41743 .first) (.cut 41296 .first))) (.rank 36 (.middle 152 (.middle 151 (.cut 41825 .first) (.cut 41602 .first)) (.cut 41381 .first)) (.middle 152 (.middle 151 (.cut 41075 .first) (.cut 40856 .first)) (.cut 40639 .first)))) (.middle 150 (.middle 148 (.cut 41004 .first) (.middle 149 (.cut 40783 .first) (.cut 40564 .first))) (.middle 152 (.middle 151 (.cut 40347 .first) (.cut 40131 .first)) (.cut 39916 .first)))))) (.rank 35 (.middle 160 (.rank 34 (.middle 157 (.rank 33 (.middle 155 (.cut 43277 .first) (.cut 42824 .first)) (.middle 155 (.cut 42477 .first) (.cut 42032 .first))) (.rank 33 (.middle 159 (.cut 42378 .first) (.cut 42157 .first)) (.middle 159 (.middle 158 (.cut 41812 .first) (.cut 41593 .first)) (.cut 41376 .first)))) (.middle 157 (.middle 155 (.middle 154 (.cut 41921 .first) (.cut 41700 .first)) (.middle 156 (.cut 41480 .first) (.cut 41262 .first))) (.middle 159 (.middle 158 (.cut 41045 .first) (.cut 40830 .first)) (.cut 40616 .first)))) (.rank 34 (.middle 164 (.rank 33 (.middle 162 (.cut 41721 .first) (.cut 41291 .first)) (.middle 162 (.middle 161 (.cut 41161 .first) (.cut 40947 .first)) (.middle 163 (.cut 40734 .first) (.cut 40524 .first)))) (.rank 33 (.middle 166 (.cut 40867 .first) (.cut 40657 .first)) (.middle 166 (.middle 165 (.cut 40314 .first) (.cut 40107 .first)) (.cut 39900 .first)))) (.middle 164 (.middle 162 (.middle 161 (.cut 40404 .first) (.cut 40194 .first)) (.middle 163 (.cut 39985 .first) (.cut 39777 .first))) (.middle 166 (.middle 165 (.cut 39571 .first) (.cut 39367 .first)) (.cut 39164 .first))))) (.middle 160 (.rank 37 (.middle 157 (.rank 36 (.middle 155 (.middle 154 (.cut 41161 .first) (.cut 40943 .first)) (.middle 156 (.cut 40727 .first) (.cut 40512 .first))) (.middle 155 (.middle 154 (.cut 40423 .first) (.cut 40208 .first)) (.middle 156 (.cut 39995 .first) (.cut 39783 .first)))) (.rank 36 (.middle 159 (.middle 158 (.cut 40299 .first) (.cut 40087 .first)) (.cut 39877 .first)) (.middle 159 (.middle 158 (.cut 39574 .first) (.cut 39365 .first)) (.cut 39158 .first)))) (.middle 157 (.middle 155 (.middle 154 (.cut 39704 .first) (.cut 39492 .first)) (.middle 156 (.cut 39283 .first) (.cut 39074 .first))) (.middle 159 (.middle 158 (.cut 38867 .first) (.cut 38662 .first)) (.cut 38458 .first)))) (.rank 37 (.middle 164 (.rank 36 (.middle 162 (.middle 161 (.cut 39669 .first) (.cut 39461 .first)) (.middle 163 (.cut 39255 .first) (.cut 39051 .first))) (.middle 162 (.middle 161 (.cut 38952 .first) (.cut 38748 .first)) (.middle 163 (.cut 38545 .first) (.cut 38344 .first)))) (.rank 36 (.middle 166 (.middle 165 (.cut 38848 .first) (.cut 38647 .first)) (.cut 38447 .first)) (.middle 166 (.middle 165 (.cut 38144 .first) (.cut 37945 .first)) (.cut 37748 .first)))) (.middle 164 (.middle 162 (.middle 161 (.cut 38255 .first) (.cut 38054 .first)) (.middle 163 (.cut 37854 .first) (.cut 37656 .first))) (.middle 166 (.middle 165 (.cut 37458 .first) (.cut 37263 .first)) (.cut 37068 .first))))))))) (.middle 139 (.rank 44 (.middle 125 (.rank 41 (.middle 118 (.cut 45999 .first) (.rank 40 (.cut 44962 .first) (.cut 44200 .first))) (.middle 118 (.cut 43756 .first) (.rank 43 (.cut 42739 .first) (.cut 42039 .first)))) (.rank 41 (.middle 132 (.rank 40 (.middle 129 (.cut 43960 .first) (.cut 43228 .first)) (.cut 42493 .first)) (.rank 40 (.middle 136 (.rank 39 (.cut 43018 .first) (.cut 42277 .first)) (.rank 39 (.cut 42312 .first) (.cut 41582 .first))) (.middle 136 (.cut 41557 .first) (.cut 40872 .first)))) (.middle 132 (.rank 43 (.middle 129 (.cut 41783 .first) (.cut 41084 .first)) (.cut 40408 .first)) (.rank 43 (.middle 136 (.rank 42 (.cut 40856 .first) (.cut 40175 .first)) (.rank 42 (.cut 40182 .first) (.cut 39510 .first))) (.cut 38857 .first))))) (.middle 125 (.rank 47 (.middle 118 (.cut 41697 .first) (.cut 40054 .first)) (.cut 38224 .first)) (.rank 47 (.middle 132 (.rank 46 (.cut 39111 .first) (.cut 38489 .first)) (.rank 46 (.cut 37601 .first) (.cut 36997 .first))) (.cut 35279 .first)))) (.rank 44 (.middle 153 (.rank 41 (.middle 146 (.rank 40 (.middle 143 (.rank 39 (.middle 141 (.cut 41850 .first) (.cut 41395 .first)) (.cut 40679 .first)) (.rank 39 (.middle 145 (.cut 40946 .first) (.cut 40724 .first)) (.cut 40018 .first))) (.middle 143 (.cut 39982 .first) (.cut 39331 .first))) (.rank 40 (.middle 150 (.rank 39 (.middle 148 (.cut 40285 .first) (.cut 39852 .first)) (.middle 148 (.cut 39585 .first) (.cut 39159 .first))) (.rank 39 (.middle 152 (.middle 151 (.cut 39638 .first) (.cut 39425 .first)) (.cut 39214 .first)) (.middle 152 (.cut 38738 .first) (.cut 38530 .first)))) (.middle 150 (.middle 148 (.cut 38905 .first) (.cut 38484 .first)) (.cut 37864 .first)))) (.middle 146 (.rank 43 (.middle 143 (.rank 42 (.cut 39305 .first) (.cut 38645 .first)) (.rank 42 (.cut 38663 .first) (.cut 38012 .first))) (.cut 37378 .first)) (.rank 43 (.middle 150 (.rank 42 (.cut 37827 .first) (.cut 37188 .first)) (.rank 42 (.cut 37216 .first) (.cut 36584 .first))) (.cut 35969 .first)))) (.rank 41 (.middle 160 (.rank 40 (.middle 157 (.rank 39 (.middle 155 (.middle 154 (.cut 39004 .first) (.cut 38796 .first)) (.middle 156 (.cut 38589 .first) (.cut 38384 .first))) (.middle 155 (.cut 38118 .first) (.cut 37711 .first))) (.rank 39 (.middle 159 (.middle 158 (.cut 38180 .first) (.cut 37977 .first)) (.cut 37776 .first)) (.middle 159 (.cut 37311 .first) (.cut 37112 .first)))) (.middle 157 (.middle 155 (.cut 37458 .first) (.cut 37057 .first)) (.cut 36465 .first))) (.rank 40 (.middle 164 (.rank 39 (.middle 162 (.cut 37378 .first) (.cut 36985 .first)) (.middle 162 (.cut 36719 .first) (.cut 36332 .first))) (.rank 39 (.middle 166 (.cut 36597 .first) (.cut 36406 .first)) (.cut 35760 .first))) (.middle 164 (.cut 35695 .first) (.cut 35131 .first)))) (.middle 160 (.rank 43 (.middle 157 (.rank 42 (.cut 36419 .first) (.cut 35797 .first)) (.rank 42 (.cut 35835 .first) (.cut 35221 .first))) (.cut 34623 .first)) (.rank 43 (.middle 164 (.rank 42 (.cut 35075 .first) (.cut 34470 .first)) (.cut 33919 .first)) (.cut 33336 .first))))) (.middle 153 (.rank 47 (.middle 146 (.rank 46 (.cut 36160 .first) (.cut 35574 .first)) (.rank 46 (.cut 34784 .first) (.cut 34215 .first))) (.cut 32588 .first)) (.rank 47 (.middle 160 (.cut 32915 .first) (.cut 31670 .first)) (.cut 30122 .first)))))) (.rank 38 (.middle 195 (.rank 32 (.middle 181 (.rank 29 (.middle 174 (.rank 27 (.cut 44086 .first) (.middle 171 (.rank 28 (.cut 43876 .first) (.cut 43022 .first)) (.cut 42377 .first))) (.rank 27 (.middle 178 (.cut 43218 .first) (.cut 42584 .first)) (.middle 178 (.rank 28 (.cut 42367 .first) (.cut 41540 .first)) (.cut 40928 .first)))) (.middle 174 (.rank 31 (.middle 171 (.rank 30 (.cut 42191 .first) (.middle 169 (.cut 41806 .first) (.cut 41384 .first))) (.rank 30 (.cut 41558 .first) (.cut 40761 .first))) (.middle 171 (.middle 169 (.cut 41013 .first) (.cut 40598 .first)) (.cut 39986 .first))) (.rank 31 (.middle 178 (.rank 30 (.cut 40735 .first) (.cut 39952 .first)) (.rank 30 (.cut 40133 .first) (.cut 39359 .first))) (.middle 178 (.middle 176 (.cut 39585 .first) (.cut 39189 .first)) (.cut 38606 .first))))) (.rank 29 (.middle 188 (.rank 27 (.cut 41158 .first) (.middle 185 (.cut 40132 .first) (.cut 39550 .first))) (.rank 27 (.cut 39801 .first) (.cut 38237 .first))) (.middle 188 (.rank 31 (.middle 185 (.rank 30 (.cut 39350 .first) (.cut 38589 .first)) (.cut 38025 .first)) (.middle 185 (.cut 37848 .first) (.cut 37292 .first))) (.rank 31 (.middle 192 (.cut 37291 .first) (.cut 36753 .first)) (.cut 36039 .first))))) (.middle 181 (.rank 35 (.middle 174 (.rank 34 (.middle 171 (.rank 33 (.middle 169 (.cut 40242 .first) (.cut 39833 .first)) (.middle 169 (.middle 168 (.cut 39695 .first) (.cut 39492 .first)) (.middle 170 (.cut 39290 .first) (.cut 39089 .first)))) (.rank 33 (.middle 173 (.cut 39430 .first) (.cut 39231 .first)) (.middle 173 (.cut 38692 .first) (.cut 38496 .first)))) (.middle 171 (.middle 169 (.middle 168 (.cut 38962 .first) (.cut 38762 .first)) (.middle 170 (.cut 38563 .first) (.cut 38365 .first))) (.middle 173 (.cut 37974 .first) (.cut 37780 .first)))) (.rank 34 (.middle 178 (.rank 33 (.middle 176 (.cut 38836 .first) (.cut 38447 .first)) (.middle 176 (.cut 38107 .first) (.cut 37724 .first))) (.rank 33 (.cut 37873 .first) (.cut 37158 .first))) (.middle 178 (.middle 176 (.cut 37397 .first) (.cut 37019 .first)) (.cut 36462 .first)))) (.middle 174 (.rank 37 (.middle 171 (.rank 36 (.middle 169 (.middle 168 (.cut 38248 .first) (.cut 38050 .first)) (.middle 170 (.cut 37854 .first) (.cut 37660 .first))) (.middle 169 (.middle 168 (.cut 37552 .first) (.cut 37358 .first)) (.cut 36973 .first))) (.rank 36 (.middle 173 (.cut 37274 .first) (.cut 37084 .first)) (.middle 173 (.cut 36593 .first) (.cut 36405 .first)))) (.middle 171 (.middle 169 (.cut 36683 .first) (.cut 36303 .first)) (.cut 35743 .first))) (.rank 37 (.middle 178 (.rank 36 (.middle 176 (.cut 36706 .first) (.cut 36333 .first)) (.cut 35665 .first)) (.rank 36 (.cut 35784 .first) (.cut 35122 .first))) (.middle 178 (.cut 35013 .first) (.cut 34477 .first))))) (.rank 35 (.middle 188 (.rank 34 (.middle 185 (.rank 33 (.cut 37126 .first) (.cut 36422 .first)) (.cut 35882 .first)) (.middle 185 (.cut 35736 .first) (.cut 35204 .first))) (.rank 34 (.middle 192 (.cut 35179 .first) (.cut 34664 .first)) (.cut 34002 .first))) (.middle 188 (.rank 37 (.middle 185 (.rank 36 (.cut 35067 .first) (.cut 34415 .first)) (.cut 33897 .first)) (.cut 33268 .first)) (.rank 37 (.cut 32726 .first) (.cut 32111 .first)))))) (.rank 32 (.middle 209 (.rank 29 (.middle 202 (.rank 27 (.cut 38509 .first) (.cut 36986 .first)) (.cut 35792 .first)) (.middle 202 (.cut 34842 .first) (.cut 33699 .first))) (.rank 29 (.cut 33714 .first) (.cut 31703 .first))) (.middle 209 (.rank 35 (.middle 202 (.cut 32853 .first) (.cut 31753 .first)) (.middle 202 (.cut 31003 .first) (.cut 29941 .first))) (.cut 28081 .first)))) (.middle 195 (.rank 44 (.middle 181 (.rank 41 (.middle 174 (.rank 40 (.middle 171 (.rank 39 (.middle 169 (.cut 36026 .first) (.cut 35651 .first)) (.cut 35015 .first)) (.rank 39 (.cut 35098 .first) (.cut 34469 .first))) (.cut 33856 .first)) (.rank 40 (.middle 178 (.rank 39 (.cut 34377 .first) (.cut 33757 .first)) (.cut 33235 .first)) (.cut 32637 .first))) (.middle 174 (.rank 43 (.middle 171 (.cut 33201 .first) (.cut 32674 .first)) (.cut 32105 .first)) (.cut 30927 .first))) (.rank 41 (.middle 188 (.rank 40 (.cut 32055 .first) (.cut 31470 .first)) (.cut 30352 .first)) (.middle 188 (.cut 29797 .first) (.cut 28713 .first)))) (.middle 181 (.rank 47 (.cut 29335 .first) (.cut 27852 .first)) (.cut 25756 .first))) (.rank 44 (.middle 209 (.rank 41 (.cut 28251 .first) (.cut 26673 .first)) (.cut 24916 .first)) (.cut 22137 .first))))))) (.middle 111 (.rank 75 (.middle 56 (.cut 53156 .first) (.rank 63 (.middle 84 (.rank 57 (.cut 44070 .first) (.cut 40758 .first)) (.rank 57 (.middle 98 (.cut 40492 .first) (.cut 37464 .first)) (.cut 34573 .first))) (.cut 29933 .first))) (.excluded .first)) (.rank 75 (.middle 167 (.rank 63 (.middle 139 (.rank 57 (.middle 125 (.cut 34477 .first) (.cut 31742 .first)) (.cut 29156 .first)) (.rank 57 (.middle 153 (.cut 29227 .first) (.cut 26907 .first)) (.cut 24532 .first))) (.cut 20619 .first)) (.rank 63 (.middle 195 (.cut 20540 .first) (.cut 17176 .first)) (.excluded .first))) (.excluded .first)))) (.rank 50 (.middle 333 (.rank 25 (.middle 278 (.rank 13 (.middle 250 (.cut 42253 .first) (.cut 37990 .first)) (.middle 250 (.rank 19 (.cut 37001 .first) (.cut 32461 .first)) (.cut 28935 .first))) (.cut 23394 .first)) (.middle 278 (.rank 38 (.middle 250 (.rank 32 (.cut 27899 .first) (.cut 24510 .first)) (.cut 21431 .first)) (.cut 16024 .first)) (.excluded .first))) (.excluded .first)) (.excluded .first)))
set_option maxHeartbeats 150000000 in
theorem checkedFee1 : checkTile 1 1 99 1 444 tree1=true := by decide +kernel
end ProximityPrize.SubmissionLower.Night6836AdaptiveCert

end BP2

section BP3
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
namespace ProximityPrize.SubmissionLower.Night6836AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open Night6836FlowSources Night6836FlowStages Night6836FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
def tree2 : Tile := (.middle 222 (.rank 50 (.middle 111 (.rank 25 (.middle 56 (.rank 13 (.middle 28 (.cut 23128 .second) (.rank 7 (.cut 20460 .second) (.middle 42 (.cut 18169 .second) (.cut 14620 .second)))) (.middle 28 (.rank 19 (.cut 17452 .second) (.cut 14053 .second)) (.rank 19 (.middle 42 (.rank 16 (.cut 15710 .second) (.cut 13782 .second)) (.rank 16 (.middle 49 (.cut 14049 .second) (.cut 12601 .second)) (.middle 49 (.cut 12291 .second) (.rank 18 (.middle 53 (.cut 12040 .second) (.cut 11480 .second)) (.cut 10975 .second))))) (.middle 42 (.rank 22 (.cut 12243 .second) (.cut 10996 .second)) (.rank 22 (.middle 49 (.rank 21 (.cut 11312 .second) (.cut 10871 .second)) (.rank 21 (.middle 53 (.cut 10580 .second) (.cut 10061 .second)) (.cut 9647 .second))) (.middle 49 (.cut 9709 .second) (.cut 8551 .second))))))) (.rank 13 (.middle 84 (.rank 7 (.middle 70 (.cut 16808 .second) (.cut 14123 .second)) (.middle 70 (.rank 10 (.cut 14111 .second) (.middle 63 (.cut 13198 .second) (.rank 12 (.cut 12622 .second) (.cut 11954 .second)))) (.rank 10 (.middle 77 (.cut 12876 .second) (.cut 11790 .second)) (.middle 77 (.rank 12 (.middle 74 (.cut 11955 .second) (.cut 11484 .second)) (.middle 74 (.cut 11310 .second) (.cut 10855 .second))) (.rank 12 (.middle 81 (.cut 10893 .second) (.cut 10476 .second)) (.middle 81 (.cut 10284 .second) (.cut 9879 .second))))))) (.rank 7 (.middle 98 (.rank 4 (.cut 14605 .second) (.cut 12067 .second)) (.cut 10546 .second)) (.middle 98 (.rank 10 (.middle 91 (.cut 10828 .second) (.cut 9970 .second)) (.middle 91 (.rank 12 (.middle 88 (.cut 9949 .second) (.cut 9576 .second)) (.middle 88 (.cut 9368 .second) (.cut 9005 .second))) (.rank 12 (.cut 8769 .second) (.cut 8218 .second)))) (.rank 10 (.cut 8599 .second) (.middle 105 (.cut 7506 .second) (.cut 6948 .second)))))) (.middle 84 (.rank 19 (.middle 70 (.rank 16 (.middle 63 (.rank 15 (.middle 60 (.cut 12452 .second) (.cut 11909 .second)) (.middle 60 (.cut 11855 .second) (.cut 11329 .second))) (.rank 15 (.middle 67 (.rank 14 (.cut 11826 .second) (.cut 11228 .second)) (.rank 14 (.cut 11330 .second) (.cut 10747 .second))) (.middle 67 (.middle 65 (.cut 10993 .second) (.cut 10668 .second)) (.middle 69 (.cut 10354 .second) (.cut 10201 .second))))) (.middle 63 (.rank 18 (.middle 60 (.rank 17 (.cut 11297 .second) (.cut 10777 .second)) (.rank 17 (.cut 10787 .second) (.cut 10280 .second))) (.middle 60 (.cut 10290 .second) (.cut 9805 .second))) (.rank 18 (.middle 67 (.rank 17 (.middle 65 (.cut 10460 .second) (.cut 10144 .second)) (.middle 65 (.cut 9962 .second) (.cut 9654 .second))) (.rank 17 (.middle 69 (.middle 68 (.cut 9990 .second) (.cut 9839 .second)) (.cut 9689 .second)) (.middle 69 (.middle 68 (.cut 9503 .second) (.cut 9355 .second)) (.cut 9209 .second)))) (.middle 67 (.middle 65 (.cut 9494 .second) (.cut 9193 .second)) (.middle 69 (.cut 8901 .second) (.cut 8758 .second)))))) (.rank 16 (.middle 77 (.rank 15 (.middle 74 (.rank 14 (.middle 72 (.cut 11013 .second) (.cut 10707 .second)) (.middle 72 (.cut 10440 .second) (.cut 10142 .second))) (.rank 14 (.cut 10267 .second) (.middle 76 (.middle 75 (.cut 9997 .second) (.cut 9855 .second)) (.cut 9714 .second)))) (.middle 74 (.middle 72 (.middle 71 (.cut 10050 .second) (.cut 9902 .second)) (.middle 73 (.cut 9756 .second) (.cut 9613 .second))) (.middle 76 (.middle 75 (.cut 9471 .second) (.cut 9332 .second)) (.cut 9195 .second)))) (.rank 15 (.middle 81 (.rank 14 (.middle 79 (.cut 9985 .second) (.cut 9712 .second)) (.middle 79 (.middle 78 (.cut 9576 .second) (.cut 9440 .second)) (.cut 9174 .second))) (.rank 14 (.cut 9318 .second) (.middle 83 (.cut 8916 .second) (.cut 8790 .second)))) (.middle 81 (.middle 79 (.middle 78 (.cut 9061 .second) (.cut 8928 .second)) (.middle 80 (.cut 8797 .second) (.cut 8668 .second))) (.middle 83 (.cut 8416 .second) (.cut 8293 .second))))) (.middle 77 (.rank 18 (.middle 74 (.rank 17 (.middle 72 (.middle 71 (.cut 9543 .second) (.cut 9398 .second)) (.middle 73 (.cut 9256 .second) (.cut 9116 .second))) (.middle 72 (.middle 71 (.cut 9066 .second) (.cut 8924 .second)) (.middle 73 (.cut 8785 .second) (.cut 8648 .second)))) (.rank 17 (.middle 76 (.middle 75 (.cut 8977 .second) (.cut 8842 .second)) (.cut 8708 .second)) (.middle 76 (.middle 75 (.cut 8513 .second) (.cut 8380 .second)) (.cut 8249 .second)))) (.middle 74 (.middle 72 (.cut 8479 .second) (.cut 8208 .second)) (.middle 76 (.cut 7945 .second) (.cut 7816 .second)))) (.rank 18 (.middle 81 (.rank 17 (.middle 79 (.middle 78 (.cut 8576 .second) (.cut 8446 .second)) (.middle 80 (.cut 8318 .second) (.cut 8192 .second))) (.middle 79 (.cut 7992 .second) (.cut 7743 .second))) (.rank 17 (.middle 83 (.cut 7945 .second) (.cut 7824 .second)) (.cut 7382 .second))) (.middle 81 (.middle 79 (.cut 7564 .second) (.cut 7319 .second)) (.cut 6964 .second)))))) (.middle 70 (.rank 22 (.middle 63 (.rank 21 (.middle 60 (.rank 20 (.cut 9834 .second) (.cut 9407 .second)) (.rank 20 (.cut 9360 .second) (.cut 8942 .second))) (.cut 8549 .second)) (.rank 21 (.middle 67 (.rank 20 (.cut 8760 .second) (.cut 8354 .second)) (.rank 20 (.cut 8334 .second) (.cut 7934 .second))) (.cut 7558 .second))) (.middle 63 (.cut 7504 .second) (.cut 6552 .second))) (.rank 22 (.middle 77 (.rank 21 (.middle 74 (.rank 20 (.cut 7794 .second) (.cut 7403 .second)) (.rank 20 (.cut 7408 .second) (.cut 7023 .second))) (.cut 6659 .second)) (.rank 21 (.middle 81 (.rank 20 (.cut 6919 .second) (.cut 6540 .second)) (.cut 6195 .second)) (.cut 5841 .second))) (.middle 77 (.cut 5683 .second) (.cut 4886 .second))))) (.rank 19 (.middle 98 (.rank 16 (.middle 91 (.rank 15 (.middle 88 (.rank 14 (.cut 8820 .second) (.middle 86 (.cut 8543 .second) (.cut 8304 .second))) (.rank 14 (.cut 8466 .second) (.cut 7958 .second))) (.middle 88 (.middle 86 (.cut 8052 .second) (.cut 7817 .second)) (.cut 7478 .second))) (.rank 15 (.middle 95 (.cut 7519 .second) (.cut 7205 .second)) (.cut 6739 .second))) (.middle 91 (.rank 18 (.middle 88 (.rank 17 (.cut 7358 .second) (.cut 6923 .second)) (.cut 6595 .second)) (.cut 6189 .second)) (.rank 18 (.cut 5879 .second) (.cut 5482 .second)))) (.rank 16 (.middle 105 (.cut 6066 .second) (.cut 5536 .second)) (.cut 4320 .second))) (.middle 98 (.rank 22 (.middle 91 (.rank 21 (.cut 5439 .second) (.cut 5092 .second)) (.cut 4405 .second)) (.cut 3478 .second)) (.cut 2352 .second)))))) (.middle 56 (.rank 38 (.middle 28 (.cut 12846 .second) (.rank 32 (.middle 42 (.cut 8884 .second) (.cut 6650 .second)) (.excluded .second))) (.excluded .second)) (.rank 38 (.middle 84 (.rank 32 (.middle 70 (.cut 4768 .second) (.cut 3160 .second)) (.excluded .second)) (.excluded .second)) (.excluded .second)))) (.rank 25 (.middle 167 (.rank 13 (.middle 139 (.rank 7 (.cut 8109 .second) (.cut 4833 .second)) (.excluded .second)) (.middle 139 (.rank 19 (.cut 2327 .second) (.excluded .second)) (.excluded .second))) (.excluded .second)) (.excluded .second))) (.excluded .second)) (.excluded .second))
set_option maxHeartbeats 150000000 in
theorem checkedFee2 : checkTile 2 1 99 1 444 tree2=true := by decide +kernel
end ProximityPrize.SubmissionLower.Night6836AdaptiveCert

end BP3

section BP4
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
namespace ProximityPrize.SubmissionLower.Night6836AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open Night6836FlowSources Night6836FlowStages Night6836FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
def tree3 : Tile := (.middle 222 (.rank 50 (.middle 111 (.rank 25 (.middle 56 (.rank 13 (.middle 28 (.rank 7 (.cut 19322 .second) (.cut 12431 .src394)) (.rank 7 (.middle 42 (.cut 13958 .src394) (.rank 4 (.cut 13935 .src394) (.cut 10523 .src394))) (.middle 42 (.rank 10 (.cut 10926 .src394) (.middle 35 (.cut 10410 .src394) (.rank 12 (.cut 9385 .src394) (.cut 8723 .src394)))) (.rank 10 (.middle 49 (.rank 9 (.cut 10154 .src394) (.cut 9333 .src394)) (.rank 9 (.cut 8758 .src394) (.middle 53 (.cut 8540 .src394) (.cut 7993 .src394)))) (.middle 49 (.rank 12 (.middle 46 (.cut 8513 .src394) (.rank 11 (.cut 8589 .src394) (.cut 7911 .src394))) (.middle 46 (.cut 7879 .src394) (.cut 7294 .src394))) (.rank 12 (.middle 53 (.rank 11 (.cut 7824 .src394) (.middle 51 (.cut 7533 .src394) (.cut 7170 .src394))) (.rank 11 (.middle 55 (.cut 7467 .src394) (.cut 7294 .src394)) (.middle 55 (.middle 54 (.cut 6995 .src394) (.cut 6823 .src394)) (.cut 6655 .src394)))) (.middle 53 (.middle 51 (.cut 6925 .src394) (.middle 52 (.cut 6747 .src394) (.cut 6572 .src394))) (.middle 55 (.middle 54 (.cut 6401 .src394) (.cut 6233 .src394)) (.cut 6068 .src394))))))))) (.middle 28 (.rank 19 (.middle 14 (.cut 16937 .second) (.rank 16 (.cut 10442 .src394) (.cut 8984 .src394))) (.cut 7069 .src394)) (.rank 19 (.middle 42 (.rank 16 (.middle 35 (.cut 8625 .src394) (.rank 15 (.middle 39 (.cut 8224 .src394) (.cut 7575 .src394)) (.cut 7076 .src394))) (.middle 35 (.cut 7290 .src394) (.rank 18 (.cut 6204 .src394) (.cut 5822 .src394)))) (.rank 16 (.middle 49 (.rank 15 (.middle 46 (.rank 14 (.cut 7301 .src394) (.cut 6773 .src394)) (.rank 14 (.cut 6730 .src394) (.cut 6214 .src394))) (.middle 46 (.cut 6290 .src394) (.cut 5740 .src394))) (.rank 15 (.middle 53 (.rank 14 (.middle 51 (.cut 6369 .src394) (.middle 52 (.cut 6195 .src394) (.cut 6023 .src394))) (.middle 51 (.cut 5860 .src394) (.cut 5520 .src394))) (.rank 14 (.middle 55 (.middle 54 (.cut 5855 .src394) (.cut 5691 .src394)) (.cut 5530 .src394)) (.middle 55 (.cut 5192 .src394) (.cut 5034 .src394)))) (.middle 53 (.cut 5056 .src394) (.cut 4576 .src394)))) (.middle 49 (.rank 18 (.middle 46 (.cut 5441 .src394) (.cut 4906 .src394)) (.cut 4538 .src394)) (.rank 18 (.middle 53 (.cut 4236 .src394) (.cut 3764 .src394)) (.cut 3404 .src394))))) (.middle 42 (.cut 4105 .src394) (.cut 1735 .src394))))) (.rank 13 (.middle 84 (.rank 7 (.middle 70 (.rank 4 (.cut 11073 .src394) (.middle 63 (.cut 9230 .src394) (.cut 8136 .src394))) (.rank 4 (.cut 9051 .src394) (.middle 77 (.cut 7196 .src394) (.cut 6381 .src394)))) (.middle 70 (.rank 10 (.middle 63 (.rank 9 (.middle 60 (.cut 8059 .src394) (.cut 7575 .src394)) (.middle 60 (.cut 7319 .src394) (.cut 6850 .src394))) (.rank 9 (.middle 67 (.cut 6977 .src394) (.cut 6560 .src394)) (.middle 67 (.cut 6270 .src394) (.cut 5864 .src394)))) (.middle 63 (.rank 12 (.middle 60 (.rank 11 (.middle 58 (.cut 6960 .src394) (.cut 6640 .src394)) (.middle 58 (.middle 57 (.cut 6490 .src394) (.cut 6329 .src394)) (.middle 59 (.cut 6172 .src394) (.cut 6017 .src394)))) (.rank 11 (.middle 62 (.cut 6333 .src394) (.cut 6184 .src394)) (.middle 62 (.middle 61 (.cut 5865 .src394) (.cut 5717 .src394)) (.cut 5571 .src394)))) (.middle 60 (.middle 58 (.middle 57 (.cut 5908 .src394) (.cut 5750 .src394)) (.middle 59 (.cut 5595 .src394) (.cut 5443 .src394))) (.middle 62 (.middle 61 (.cut 5295 .src394) (.cut 5149 .src394)) (.cut 5006 .src394)))) (.rank 12 (.middle 67 (.rank 11 (.middle 65 (.cut 5895 .src394) (.cut 5618 .src394)) (.middle 65 (.cut 5288 .src394) (.cut 5016 .src394))) (.rank 11 (.cut 5221 .src394) (.cut 4627 .src394))) (.middle 67 (.middle 65 (.cut 4727 .src394) (.cut 4459 .src394)) (.cut 4075 .src394))))) (.rank 10 (.middle 77 (.rank 9 (.cut 5680 .src394) (.cut 5005 .src394)) (.cut 4250 .src394)) (.middle 77 (.rank 12 (.middle 74 (.cut 4139 .src394) (.cut 3796 .src394)) (.cut 3254 .src394)) (.cut 2524 .src394))))) (.rank 7 (.cut 4045 .src394) (.middle 98 (.rank 10 (.cut 2983 .src394) (.excluded .src394)) (.excluded .src394)))) (.middle 84 (.rank 19 (.middle 70 (.rank 16 (.middle 63 (.rank 15 (.middle 60 (.rank 14 (.middle 58 (.middle 57 (.cut 5371 .src394) (.cut 5216 .src394)) (.middle 59 (.cut 5064 .src394) (.cut 4915 .src394))) (.middle 58 (.cut 4725 .src394) (.cut 4427 .src394))) (.rank 14 (.middle 62 (.cut 4625 .src394) (.cut 4483 .src394)) (.cut 4000 .src394))) (.middle 60 (.cut 3976 .src394) (.cut 3553 .src394))) (.rank 15 (.middle 67 (.rank 14 (.middle 65 (.cut 4209 .src394) (.cut 3944 .src394)) (.cut 3466 .src394)) (.cut 3089 .src394)) (.cut 2647 .src394))) (.middle 63 (.rank 18 (.cut 2754 .src394) (.cut 2396 .src394)) (.cut 1495 .src394))) (.rank 16 (.middle 77 (.rank 15 (.cut 2278 .src394) (.cut 1838 .src394)) (.cut 1113 .src394)) (.excluded .src394))) (.excluded .src394)) (.excluded .src394)))) (.excluded .src394)) (.excluded .src394)) (.excluded .second)) (.excluded .second))
set_option maxHeartbeats 150000000 in
theorem checkedFee3 : checkTile 3 1 99 1 444 tree3=true := by decide +kernel
end ProximityPrize.SubmissionLower.Night6836AdaptiveCert

end BP4

section BP5
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
namespace ProximityPrize.SubmissionLower.Night6836AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open Night6836FlowSources Night6836FlowStages Night6836FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
def tree4 : Tile := (.middle 222 (.rank 50 (.middle 111 (.rank 25 (.middle 56 (.rank 13 (.middle 28 (.rank 7 (.cut 15918 .src394) (.middle 14 (.cut 14975 .src394) (.cut 10025 .src481))) (.rank 7 (.middle 42 (.cut 11299 .src481) (.rank 4 (.cut 11419 .src394) (.middle 49 (.cut 9674 .src481) (.cut 8341 .src481)))) (.middle 42 (.rank 10 (.middle 35 (.cut 10325 .src481) (.cut 8638 .src481)) (.middle 35 (.rank 12 (.cut 8846 .src481) (.cut 8221 .src481)) (.rank 12 (.middle 39 (.cut 7923 .src481) (.rank 11 (.cut 7930 .src481) (.cut 7291 .src481))) (.middle 39 (.cut 7328 .src481) (.cut 6715 .src485))))) (.rank 10 (.middle 49 (.rank 9 (.middle 46 (.cut 8561 .src481) (.cut 7970 .src481)) (.middle 46 (.cut 7810 .src481) (.cut 7242 .src481))) (.rank 9 (.middle 53 (.rank 8 (.cut 8025 .src481) (.cut 7250 .src481)) (.rank 8 (.cut 7509 .src481) (.cut 6754 .src485))) (.middle 53 (.middle 51 (.cut 6886 .src481) (.middle 52 (.cut 6715 .src485) (.cut 6547 .src485))) (.cut 6068 .src485)))) (.middle 49 (.rank 12 (.middle 46 (.rank 11 (.middle 44 (.cut 7521 .src481) (.cut 7132 .src481)) (.middle 44 (.cut 6895 .src481) (.middle 45 (.cut 6704 .src485) (.cut 6518 .src485)))) (.rank 11 (.middle 48 (.middle 47 (.cut 6944 .src481) (.cut 6761 .src481)) (.cut 6583 .src485)) (.middle 48 (.cut 6158 .src485) (.cut 5984 .src485)))) (.middle 46 (.cut 5961 .src485) (.cut 5439 .src485))) (.rank 12 (.middle 53 (.rank 11 (.middle 51 (.middle 50 (.cut 6408 .src485) (.cut 6238 .src485)) (.cut 5908 .src485)) (.middle 51 (.cut 5648 .src485) (.cut 5326 .src485))) (.rank 11 (.cut 5441 .src485) (.cut 4869 .src485))) (.cut 4345 .src485))))))) (.middle 28 (.rank 19 (.middle 14 (.cut 14108 .src394) (.rank 16 (.cut 8344 .src481) (.cut 7123 .src485))) (.excluded .src485)) (.rank 19 (.middle 42 (.rank 16 (.middle 35 (.rank 15 (.middle 32 (.cut 7841 .src481) (.cut 7151 .src485)) (.cut 6694 .src485)) (.rank 15 (.middle 39 (.cut 6305 .src485) (.cut 5718 .src485)) (.cut 5287 .src485))) (.cut 4209 .src485)) (.rank 16 (.middle 49 (.rank 15 (.middle 46 (.cut 4994 .src485) (.cut 4489 .src485)) (.cut 4074 .src485)) (.cut 3017 .src485)) (.excluded .src485))) (.excluded .src485)))) (.rank 13 (.middle 84 (.rank 7 (.middle 70 (.rank 4 (.cut 8988 .src481) (.middle 63 (.rank 6 (.cut 8091 .src481) (.cut 7229 .src481)) (.cut 6286 .src485))) (.cut 4776 .src485)) (.middle 70 (.rank 10 (.middle 63 (.rank 9 (.middle 60 (.rank 8 (.cut 6878 .src485) (.cut 6146 .src485)) (.cut 5724 .src485)) (.cut 5066 .src485)) (.cut 4202 .src485)) (.middle 63 (.rank 12 (.middle 60 (.cut 4303 .src485) (.cut 3908 .src485)) (.cut 3397 .src485)) (.cut 2566 .src485))) (.cut 1182 .src485))) (.excluded .src485)) (.middle 84 (.rank 19 (.middle 70 (.rank 16 (.cut 1265 .src485) (.excluded .src485)) (.excluded .src485)) (.excluded .src394)) (.excluded .src394)))) (.excluded .src394)) (.excluded .src394)) (.excluded .second)) (.excluded .second))
set_option maxHeartbeats 150000000 in
theorem checkedFee4 : checkTile 4 1 99 1 444 tree4=true := by decide +kernel
end ProximityPrize.SubmissionLower.Night6836AdaptiveCert

end BP5

section BP6
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
namespace ProximityPrize.SubmissionLower.Night6836AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open Night6836FlowSources Night6836FlowStages Night6836FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
theorem fee_bound (j : Fin 5) (f : FlagDegree) (hpos : 0<f.all)
    (hcap : Below f primaryIncoming) (hprior : Prior j.val f) :
    stagePrice f hpos (capStage j) (capStage j).numbers.slopeCap ≤ fee j := by
  have r : f.all≤99 := hcap.1
  have y : middle f≤444 := hcap.2.1
  have t : total f≤83491 := hcap.2.2
  have p : 1≤middle f := hpos.trans_le (Nat.le_add_left _ _)
  fin_cases j
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee0 (by decide) hpos r p y
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee1 (by decide) hpos r p y
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee2 (by decide) hpos r p y
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee3 (by decide) hpos r p y
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee4 (by decide) hpos r p y
#print axioms fee_bound
end ProximityPrize.SubmissionLower.Night6836AdaptiveCert

end BP6
