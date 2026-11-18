import ProximityPrize.SubmissionLower.Koala6831ResidualLedger
import ProximityPrize.SubmissionLower.Koala6831MovingStages
import ProximityPrize.SubmissionLower.MergedInfra6815_13

namespace ProximityPrize.SubmissionLower.Koala6831Residual

open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (SourceNumbers)
open Koala6831MovingStages
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)

set_option Elab.async false
set_option maxRecDepth 20000

private def gateBand (s : SourceNumbers) (f : FlagDegree) : ℕ :=
  evalPowerBandBudget weightGain (total f) (middle f) f.all
    (s.totalCap - total f) (s.middleCap - middle f)
    (s.slopeCap - f.all) (s.fuel f)

private theorem gateBand_eq (s : SourceNumbers) (f : FlagDegree) :
    gateBand s f = adaptiveBand s f :=
  evalPowerBandBudget_eq _ _ _ _ _ _ _ _

private def someGate (r y t : ℕ) : Bool :=
  let f := (⟨r,y,t⟩ : Envelope).flag
  decide (gateBand adaptiveSource1 f < adaptiveSource1.gap) ||
  decide (gateBand adaptiveSource2 f < adaptiveSource2.gap) ||
  decide (gateBand adaptiveSource3 f < adaptiveSource3.gap)

private theorem someGate_sound {r y t : ℕ} (h : someGate r y t = true) :
    let f := (⟨r,y,t⟩ : Envelope).flag
    adaptiveGate adaptiveSource1 f ∨ adaptiveGate adaptiveSource2 f ∨ adaptiveGate adaptiveSource3 f := by
  simp only [someGate, Bool.or_eq_true, decide_eq_true_eq, gateBand_eq, adaptiveGate] at h ⊢
  tauto

private def cellsOfSlope (r : ℕ) : List Cell :=
  terminalCells.filter (fun c => decide (c.envelope.slope = r))

private def middleCell (cells : List Cell) (y : ℕ) : Option Cell :=
  cells.find? (fun c => decide (c.envelope.middle = y))

private def checkAt (r : ℕ) (cells : List Cell) (y : ℕ) : Bool :=
  if r ≤ y then
    match middleCell cells y with
    | none => someGate r y y
    | some c => decide (15351 ≤ c.envelope.total) ||
        someGate r y (c.envelope.total + 1)
  else true

private def checkedSlope (r : ℕ) : Bool :=
  let cells := cellsOfSlope r
  (List.range 138).all (fun i => checkAt r cells (i+1))

set_option maxHeartbeats 4000000 in
private theorem slope1_checked : checkedSlope 1 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope2_checked : checkedSlope 2 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope3_checked : checkedSlope 3 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope4_checked : checkedSlope 4 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope5_checked : checkedSlope 5 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope6_checked : checkedSlope 6 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope7_checked : checkedSlope 7 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope8_checked : checkedSlope 8 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope9_checked : checkedSlope 9 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope10_checked : checkedSlope 10 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope11_checked : checkedSlope 11 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope12_checked : checkedSlope 12 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope13_checked : checkedSlope 13 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope14_checked : checkedSlope 14 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope15_checked : checkedSlope 15 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope16_checked : checkedSlope 16 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope17_checked : checkedSlope 17 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope18_checked : checkedSlope 18 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope19_checked : checkedSlope 19 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope20_checked : checkedSlope 20 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope21_checked : checkedSlope 21 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope22_checked : checkedSlope 22 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope23_checked : checkedSlope 23 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope24_checked : checkedSlope 24 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope25_checked : checkedSlope 25 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope26_checked : checkedSlope 26 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope27_checked : checkedSlope 27 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope28_checked : checkedSlope 28 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope29_checked : checkedSlope 29 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem slope30_checked : checkedSlope 30 = true := by
  decide +kernel

private theorem checkedSlope_all (r : Fin 30) : checkedSlope (r.val+1) = true := by
  fin_cases r
  · exact slope1_checked
  · exact slope2_checked
  · exact slope3_checked
  · exact slope4_checked
  · exact slope5_checked
  · exact slope6_checked
  · exact slope7_checked
  · exact slope8_checked
  · exact slope9_checked
  · exact slope10_checked
  · exact slope11_checked
  · exact slope12_checked
  · exact slope13_checked
  · exact slope14_checked
  · exact slope15_checked
  · exact slope16_checked
  · exact slope17_checked
  · exact slope18_checked
  · exact slope19_checked
  · exact slope20_checked
  · exact slope21_checked
  · exact slope22_checked
  · exact slope23_checked
  · exact slope24_checked
  · exact slope25_checked
  · exact slope26_checked
  · exact slope27_checked
  · exact slope28_checked
  · exact slope29_checked
  · exact slope30_checked

private theorem below_padded_flag (f : FlagDegree) (t : ℕ) (hy : middle f ≤ t)
    (ht : t ≤ total f) : Below (⟨f.all,middle f,t⟩ : Envelope).flag f := by
  simp only [Envelope.flag, Below, middle, total] at *
  omega

private theorem no_checked_gate {f : FlagDegree}
    (h1 : ¬ adaptiveGate adaptiveSource1 f)
    (h2 : ¬ adaptiveGate adaptiveSource2 f)
    (h3 : ¬ adaptiveGate adaptiveSource3 f)
    (hr : 0 < f.all) (t : ℕ) (hy : middle f ≤ t) (ht : t ≤ total f) :
    someGate f.all (middle f) t ≠ true := by
  have hb := below_padded_flag f t hy ht
  intro hg
  rcases someGate_sound hg with hg | hg | hg
  · exact h1 (adaptiveGate_mono adaptiveSource1 hb hr hg)
  · exact h2 (adaptiveGate_mono adaptiveSource2 hb hr hg)
  · exact h3 (adaptiveGate_mono adaptiveSource3 hb hr hg)

theorem exists_terminalCell_of_failed_gates (f : FlagDegree)
    (hr : 0 < f.all) (hR : f.all ≤ 30) (hY : middle f ≤ 138) (hT : total f ≤ 15351)
    (h1 : ¬ adaptiveGate adaptiveSource1 f)
    (h2 : ¬ adaptiveGate adaptiveSource2 f)
    (h3 : ¬ adaptiveGate adaptiveSource3 f) :
    ∃ c ∈ terminalCells, c.envelope.slope = f.all ∧ c.envelope.middle = middle f ∧
      total f ≤ c.envelope.total := by
  have hRY : f.all ≤ middle f := by unfold middle; omega
  have hYT : middle f ≤ total f := by unfold middle total; omega
  let ri : Fin 30 := ⟨f.all-1, by omega⟩
  have hri : ri.val+1 = f.all := by dsimp [ri]; omega
  have hy : middle f - 1 ∈ List.range 138 := List.mem_range.mpr (by omega)
  have hyi : (middle f - 1)+1 = middle f := by omega
  have hc := checkedSlope_all ri
  rw [hri] at hc
  have hcheck := List.all_eq_true.mp hc (middle f - 1) hy
  change checkAt f.all (cellsOfSlope f.all) ((middle f - 1)+1) = true at hcheck
  rw [hyi, checkAt, ite_eq_left hRY] at hcheck
  cases hcell : middleCell (cellsOfSlope f.all) (middle f) with
  | none =>
    rw [hcell] at hcheck
    exact (no_checked_gate h1 h2 h3 hr (middle f) le_rfl hYT hcheck).elim
  | some c =>
    have hfound : (cellsOfSlope f.all).find? (fun d => decide (d.envelope.middle = middle f)) =
        some c := hcell
    have hcSide := List.mem_of_find?_eq_some hfound
    have hs : c.envelope.slope = f.all := of_decide_eq_true (List.mem_filter.mp hcSide).2
    have hmiddle := List.find?_some hfound
    have hm : c.envelope.middle = middle f := of_decide_eq_true hmiddle
    have hcTerm : c ∈ terminalCells := (List.mem_filter.mp hcSide).1
    use c, hcTerm, hs, hm
    by_contra hBelow
    have ht : c.envelope.total + 1 ≤ total f := by omega
    have hsmall : ¬ 15351 ≤ c.envelope.total := by omega
    have hy' : middle f ≤ c.envelope.total+1 := by
      have hmid := (terminalCell_shape_of_mem hcTerm).1
      omega
    rw [hcell] at hcheck
    simp only [hsmall, decide_false, Bool.false_or] at hcheck
    exact no_checked_gate h1 h2 h3 hr (c.envelope.total+1) hy' ht hcheck

end ProximityPrize.SubmissionLower.Koala6831Residual
