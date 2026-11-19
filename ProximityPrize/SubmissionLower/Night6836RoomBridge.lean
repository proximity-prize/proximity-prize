/- Apache-2.0. The two physical budget intervals shared by the packet and partition counts. -/
import ProximityPrize.SubmissionLower.Night6836Terminal
import ProximityPrize.SubmissionLower.Night6836Room
namespace ProximityPrize.SubmissionLower.Night6836Terminal
open ProximityPrize.Benchmark Genuine6969 RCN095 RCN156 RCN266 RCN319
open LocatorFactorAggregate Left6836Ready Night6836FlowSources Night6836AdaptiveCert
open Koala6831Moving Night6836FlowAdaptive Night6836FlowPaid
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def roomCheck (r y : ℕ) : Bool := decide
  (endCap r y = Koala6836.Room.maxTotal r (y-r) ∧ y ≤ 76 ∧ endCap r y ≤ 9352 ∧
   Koala6836.Room.lowBudget r (y-r) ≤ finalBudget-charged r y y ∧
   Koala6836.Room.highBudget r (y-r) ≤ finalBudget-charged r y (Koala6836.Room.split r (y-r)))
def roomRank (r : ℕ) : Bool :=
  (List.range (maxY r+1-r)).all fun e => roomCheck r (e+r)
private theorem roomRank1 : roomRank 1=true := by decide +kernel
private theorem roomRank2 : roomRank 2=true := by decide +kernel
private theorem roomRank3 : roomRank 3=true := by decide +kernel
private theorem roomRank4 : roomRank 4=true := by decide +kernel
private theorem roomRank5 : roomRank 5=true := by decide +kernel
private theorem roomRank6 : roomRank 6=true := by decide +kernel
private theorem roomRank7 : roomRank 7=true := by decide +kernel
private theorem roomRank8 : roomRank 8=true := by decide +kernel
private theorem roomRank9 : roomRank 9=true := by decide +kernel
private theorem roomRank10 : roomRank 10=true := by decide +kernel
private theorem roomRank11 : roomRank 11=true := by decide +kernel
private theorem roomRank12 : roomRank 12=true := by decide +kernel
private theorem roomRank13 : roomRank 13=true := by decide +kernel
private theorem roomRank14 : roomRank 14=true := by decide +kernel
private theorem roomRank15 : roomRank 15=true := by decide +kernel
private theorem roomRank16 : roomRank 16=true := by decide +kernel
private theorem roomRank17 : roomRank 17=true := by decide +kernel
private theorem roomRank18 : roomRank 18=true := by decide +kernel
theorem physical_room {r y t : ℕ} (rp : 0<r) (rh : r≤18) (ry : r≤y) (yh : y≤maxY r)
    (yt : y≤t) :
    endCap r y = Koala6836.Room.maxTotal r (y-r) ∧ y ≤ 76 ∧ endCap r y ≤ 9352 ∧
    Koala6836.Room.budget r (y-r) t ≤ finalBudget-charged r y t := by
  have hr : roomRank r = true := by
    interval_cases r
    · exact roomRank1
    · exact roomRank2
    · exact roomRank3
    · exact roomRank4
    · exact roomRank5
    · exact roomRank6
    · exact roomRank7
    · exact roomRank8
    · exact roomRank9
    · exact roomRank10
    · exact roomRank11
    · exact roomRank12
    · exact roomRank13
    · exact roomRank14
    · exact roomRank15
    · exact roomRank16
    · exact roomRank17
    · exact roomRank18
  have mem : y-r ∈ List.range (maxY r+1-r) := List.mem_range.mpr (by omega)
  have ck := List.all_eq_true.mp hr (y-r) mem
  rw [Nat.sub_add_cancel ry] at ck
  obtain ⟨same,ym,tm,low,high⟩ := of_decide_eq_true ck
  refine ⟨same,ym,tm,?_⟩
  unfold Koala6836.Room.budget
  split
  · exact low.trans (Nat.sub_le_sub_left (charged_antitone r y y t rp ry le_rfl yt) _)
  · rename_i h
    have splitLo : y≤Koala6836.Room.split r (y-r) := by unfold Koala6836.Room.split; omega
    exact high.trans (Nat.sub_le_sub_left (charged_antitone r y _ t rp ry splitLo (Nat.le_of_not_gt h)) _)

def SlabBudget : Prop :=
  ∀(original : Finset F) (R : Ready Dmn original) (H : P4 F), H≠0 →
    H∈LocatorLowQuotient.nestedCoefficientBox F Stage.primary.cutoff 131071 83491 444 99 →
    ∀(Γ : Finset F), Γ⊆R.seeds → ∀(A : Finset (RegularIndex H)), A.Nonempty →
    let f := aggregateFlag H A
    f.all≤18 → f.all+(middle f-f.all)≤76 →
    total f≤min 9352 (Koala6836.Room.maxTotal f.all (middle f-f.all)) →
    (A.biUnion (regularFiber H Γ R.selected)).card≤Koala6836.Room.budget f.all (middle f-f.all) (total f)

theorem rows_of_slabs (bounded : SlabBudget) : RowBudget := by
  intro original R H nz box Γ hg A ne _ rh yh th
  let f := aggregateFlag H A
  have pos := aggregateFlag_pos H ne
  have ry : f.all≤middle f := Nat.le_add_left _ _
  have yt : middle f≤total f := by unfold middle total; omega
  obtain ⟨same,ym,tm,room⟩ := physical_room pos rh ry yh yt
  have y76 : f.all+(middle f-f.all)≤76 := by omega
  exact (bounded original R H nz box Γ hg A ne rh y76 (le_min (th.trans tm) (th.trans_eq same))).trans room
theorem short_of_slabs (bounded : SlabBudget) : Intermediate.OpenAt 181039 274980640798883310 2133 9615 :=
  short_of_rows (rows_of_slabs bounded)
#print axioms physical_room
#print axioms short_of_slabs
end
end ProximityPrize.SubmissionLower.Night6836Terminal
