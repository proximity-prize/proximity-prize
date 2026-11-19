/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
import ProximityPrize.SubmissionLower.Mid6833K6833FlowPaidCaps
import ProximityPrize.SubmissionLower.MergedInfra6815_13
namespace ProximityPrize.SubmissionLower.K6833AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open K6833FlowSources K6833FlowStages K6833FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
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
  | 0 => 6549797983858004
  | 1 => 1964970898496834
  | 2 => 953657939715696
  | 3 => 1527775511358948
  | 4 => 9367372783627535
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
  | .full => decide (yh≤65864 ∧ priceAt j (min rh yh) yh 65864 ≤ fee j)
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
    (hT : total f≤65864) (prev : Prior j.val f) (tree : Tile) (rl rh yl yh : ℕ)
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

end ProximityPrize.SubmissionLower.K6833AdaptiveCert
