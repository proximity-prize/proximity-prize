/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
import ProximityPrize.SubmissionLower.Night6836FeeCert
import ProximityPrize.SubmissionLower.Night6836EndRank1
import ProximityPrize.SubmissionLower.Night6836EndRank2
import ProximityPrize.SubmissionLower.Night6836EndRank3
import ProximityPrize.SubmissionLower.Night6836EndRank4
import ProximityPrize.SubmissionLower.Night6836EndRank5
import ProximityPrize.SubmissionLower.Night6836EndRank6
import ProximityPrize.SubmissionLower.Night6836EndRank7
import ProximityPrize.SubmissionLower.Night6836EndRank8
import ProximityPrize.SubmissionLower.Night6836EndRank9
import ProximityPrize.SubmissionLower.Night6836EndRank10
import ProximityPrize.SubmissionLower.Night6836EndRank11
import ProximityPrize.SubmissionLower.Night6836EndRank12
import ProximityPrize.SubmissionLower.Night6836EndRank13
import ProximityPrize.SubmissionLower.Night6836EndRank14
import ProximityPrize.SubmissionLower.Night6836EndRank15
import ProximityPrize.SubmissionLower.Night6836EndRank16
import ProximityPrize.SubmissionLower.Night6836EndRank17
import ProximityPrize.SubmissionLower.Night6836EndRank18
import ProximityPrize.SubmissionLower.Night6836EndRank19
namespace ProximityPrize.SubmissionLower.Night6836AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open Night6836FlowSources Night6836FlowStages Night6836FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
def decode : Koala6836.FastEnd.Id → Stage
  | .primary => .primary
  | .first => .first
  | .second => .second
  | .src394 => .src394
  | .src481 => .src481
  | .src485 => .src485
  | .src700 => .src700
  | .src701 => .src701
  | .src702 => .src702
  | .src703 => .src703
  | .src704 => .src704
  | .src705 => .src705
  | .src706 => .src706
  | .src707 => .src707
  | .src708 => .src708
  | .src709 => .src709
  | .src710 => .src710
  | .src711 => .src711
  | .src712 => .src712
  | .src713 => .src713
  | .src714 => .src714
  | .src715 => .src715
  | .src716 => .src716
  | .src717 => .src717
  | .src718 => .src718
abbrev maxY := Koala6836.FastEnd.maxY
def endEntry (r y : Nat) : Nat × Stage :=
  let e:=Koala6836.FastEnd.endEntry r y
  (e.1,decode e.2)
def endCap (r y : Nat) := (endEntry r y).1
def checkEnd (r y : ℕ) : Bool :=
  let e := endEntry r y
  decide (r≤y ∧ y≤e.1+1 ∧ (y=maxY r+1 → e.1+1=y) ∧ sourceGroup e.2<5) &&
    gateAt e.2 r y (e.1+1)
def checkedRank (r : ℕ) : Bool :=
  (List.range (maxY r + 2-r)).all fun k => checkEnd r (k+r)

private theorem power_eq (g a b c t y s n : Nat) :
    Koala6836.FastEnd.power g a b c t y s n = evalPowerBandBudget g a b c t y s n := by
  induction n generalizing t y s with
  | zero => rfl
  | succ n ih => simp only [Koala6836.FastEnd.power, evalPowerBandBudget, ih]; rfl
private theorem gate_eq (i : Koala6836.FastEnd.Id) (r y t : Nat) :
    Koala6836.FastEnd.gate i r y t = gateAt (decode i) r y t := by
  cases i <;> simp only [Koala6836.FastEnd.gate, gateAt, power_eq] <;> rfl
private theorem group_eq (i : Koala6836.FastEnd.Id) : sourceGroup (decode i)=Koala6836.FastEnd.sourceGroup i := by
  cases i <;> rfl
private theorem check_eq (r y : Nat) : checkEnd r y = Koala6836.FastEnd.checkEnd r y := by
  simp only [checkEnd, endEntry, Koala6836.FastEnd.checkEnd, maxY, group_eq, gate_eq]
private theorem checked_eq (r : Nat) : checkedRank r = Koala6836.FastEnd.checkedRank r := by
  simp only [checkedRank, Koala6836.FastEnd.checkedRank, maxY, check_eq]

theorem portable_correct (r : Nat) : checkedRank r = Koala6836.FastEnd.checkedRank r := checked_eq r
#print axioms portable_correct

theorem getCheck {r y : ℕ} (h : checkedRank r=true) (ry:r≤y) (yup:y≤maxY r+1) :
    checkEnd r y = true := by
  have k : y-r ∈ List.range (maxY r+2-r) := List.mem_range.mpr (by omega)
  have h' := List.all_eq_true.mp h (y-r) k
  simpa [Nat.sub_add_cancel ry] using h'

set_option maxHeartbeats 1200000000 in
theorem checkedEnd1 : checkedRank 1=true := (checked_eq _).trans Koala6836.FastEnd.rank1
set_option maxHeartbeats 1200000000 in
theorem checkedEnd2 : checkedRank 2=true := (checked_eq _).trans Koala6836.FastEnd.rank2
set_option maxHeartbeats 1200000000 in
theorem checkedEnd3 : checkedRank 3=true := (checked_eq _).trans Koala6836.FastEnd.rank3
set_option maxHeartbeats 1200000000 in
theorem checkedEnd4 : checkedRank 4=true := (checked_eq _).trans Koala6836.FastEnd.rank4
set_option maxHeartbeats 1200000000 in
theorem checkedEnd5 : checkedRank 5=true := (checked_eq _).trans Koala6836.FastEnd.rank5
set_option maxHeartbeats 1200000000 in
theorem checkedEnd6 : checkedRank 6=true := (checked_eq _).trans Koala6836.FastEnd.rank6
set_option maxHeartbeats 1200000000 in
theorem checkedEnd7 : checkedRank 7=true := (checked_eq _).trans Koala6836.FastEnd.rank7
set_option maxHeartbeats 1200000000 in
theorem checkedEnd8 : checkedRank 8=true := (checked_eq _).trans Koala6836.FastEnd.rank8
set_option maxHeartbeats 1200000000 in
theorem checkedEnd9 : checkedRank 9=true := (checked_eq _).trans Koala6836.FastEnd.rank9
set_option maxHeartbeats 1200000000 in
theorem checkedEnd10 : checkedRank 10=true := (checked_eq _).trans Koala6836.FastEnd.rank10
set_option maxHeartbeats 1200000000 in
theorem checkedEnd11 : checkedRank 11=true := (checked_eq _).trans Koala6836.FastEnd.rank11
set_option maxHeartbeats 1200000000 in
theorem checkedEnd12 : checkedRank 12=true := (checked_eq _).trans Koala6836.FastEnd.rank12
set_option maxHeartbeats 1200000000 in
theorem checkedEnd13 : checkedRank 13=true := (checked_eq _).trans Koala6836.FastEnd.rank13
set_option maxHeartbeats 1200000000 in
theorem checkedEnd14 : checkedRank 14=true := (checked_eq _).trans Koala6836.FastEnd.rank14
set_option maxHeartbeats 1200000000 in
theorem checkedEnd15 : checkedRank 15=true := (checked_eq _).trans Koala6836.FastEnd.rank15
set_option maxHeartbeats 1200000000 in
theorem checkedEnd16 : checkedRank 16=true := (checked_eq _).trans Koala6836.FastEnd.rank16
set_option maxHeartbeats 1200000000 in
theorem checkedEnd17 : checkedRank 17=true := (checked_eq _).trans Koala6836.FastEnd.rank17
set_option maxHeartbeats 1200000000 in
theorem checkedEnd18 : checkedRank 18=true := (checked_eq _).trans Koala6836.FastEnd.rank18
set_option maxHeartbeats 1200000000 in
theorem checkedEnd19 : checkedRank 19=true := (checked_eq _).trans Koala6836.FastEnd.rank19
theorem checkedRanks (r : ℕ) (h : 1≤r) (h' : r≤19) : checkedRank r = true := by
  interval_cases r
  · exact checkedEnd1
  · exact checkedEnd2
  · exact checkedEnd3
  · exact checkedEnd4
  · exact checkedEnd5
  · exact checkedEnd6
  · exact checkedEnd7
  · exact checkedEnd8
  · exact checkedEnd9
  · exact checkedEnd10
  · exact checkedEnd11
  · exact checkedEnd12
  · exact checkedEnd13
  · exact checkedEnd14
  · exact checkedEnd15
  · exact checkedEnd16
  · exact checkedEnd17
  · exact checkedEnd18
  · exact checkedEnd19
private theorem cut_le {f : FlagDegree} (prev : Prior 5 f) {r y : ℕ}
    (rp:0<r) (ry:r≤y) (r16:r≤19) (yup:y≤maxY r+1) (hr:r≤f.all) (hy:y≤middle f) :
    total f≤endCap r y := by
  have c := getCheck (checkedRanks r rp r16) ry yup
  have ⟨a,b⟩ := Bool.and_eq_true_iff.mp c
  have aa := of_decide_eq_true a
  by_contra! nt
  exact prior_contra prev le_rfl (endEntry r y).2 rp ry aa.2.1 hr hy nt
    (Bool.and_eq_true_iff.mpr ⟨decide_eq_true aa.2.2.2,b⟩)

theorem inside {f : FlagDegree} (hp : 0<f.all) (prev : Prior 5 f) :
    1≤f.all ∧ f.all≤18 ∧ f.all≤middle f ∧ middle f≤maxY f.all := by
  have ry : f.all≤middle f := Nat.le_add_left _ _
  have yt : middle f≤total f := by unfold middle total; omega
  have r15 : f.all≤18 := by
    by_contra! z
    have h := cut_le (f:=f) prev (r:=19) (y:=19) (by decide) le_rfl le_rfl (by decide) z ((show 19≤f.all from z).trans ry)
    have e : endCap 19 19=18 := by decide +kernel
    omega
  refine ⟨hp,r15,ry,?_⟩
  by_contra! z
  have rbound : f.all≤maxY f.all+1 := by
    have all : ∀ r : Fin 19, r.val≤maxY r.val+1 := by decide +kernel
    exact all ⟨f.all,by omega⟩
  have h := cut_le (f:=f) prev hp rbound (by omega) le_rfl le_rfl z
  have ⟨a,_⟩ := Bool.and_eq_true_iff.mp (getCheck (r:=f.all) (y:=maxY f.all+1) (checkedRanks f.all hp (by omega)) rbound le_rfl)
  have eq := (of_decide_eq_true a).2.2.1 rfl
  unfold endCap at h
  omega

theorem end_bound (f : FlagDegree) (hpos : 0<f.all) (hprior : Prior 5 f) :
    total f ≤ endCap f.all (middle f) := by
  obtain ⟨_,rm,ry,ym⟩ := inside hpos hprior
  exact cut_le hprior hpos ry (by omega) (by omega) le_rfl le_rfl

#print axioms end_bound
end ProximityPrize.SubmissionLower.Night6836AdaptiveCert
