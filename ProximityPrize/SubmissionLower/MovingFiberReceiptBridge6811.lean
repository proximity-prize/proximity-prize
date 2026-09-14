import ProximityPrize.SubmissionLower.MovingFiberReceiptData6811
import ProximityPrize.SubmissionLower.MovingFiberPacking6811
import ProximityPrize.SubmissionLower.MovingFiberSingletonGeometry6811

namespace ProximityPrize.SubmissionLower.Lower80860.ReceiptBridge
open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open ReceiptData MovingFiberReceiptTypes6811 PhaseRows ThresholdFast
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def PrefixAt (r v : Nat) : Prop :=
  ∀ j ∈ List.range 10,
    (r+1≤35 → r+1+v≤159 → storedPrefix r v j ≤ storedPrefix (r+1) v j) ∧
    (r+(v+1)≤159 → storedPrefix r v j ≤ storedPrefix r (v+1) j)
def ThresholdAt (r v : Nat) : Prop :=
  ∀ j ∈ List.range 10, FastSourceThresholdSufficient (TenPhase.sound j).source r v
    (PhaseRows.thresholdAt (rowContext r v).threshold j)
def RunsAt (r v : Nat) : Prop :=
  RowRunsValid (rowContext r v) (lookup r v).phaseRuns

theorem prefix_at (h : Receipt) (r v : Nat) (hr : 1≤r) (hR : r≤35) (hY : r+v≤159) : PrefixAt r v := by
  intro j hj
  have hj10 : j<10 := List.mem_range.mp hj
  constructor
  · intro hR' hY'
    have hh := (h (r+1) v (by omega) hR' hY').prefixR ⟨j,hj10⟩
    simpa only [Nat.add_sub_cancel] using hh
  · intro hY'
    have hh := (h r (v+1) hr hR hY').prefixV (by omega) ⟨j,hj10⟩
    simpa only [Nat.add_sub_cancel] using hh

theorem threshold_at (h : Receipt) (r v : Nat) (hr : 1≤r) (hR : r≤35) (hY : r+v≤159) : ThresholdAt r v := by
  intro j hj
  have hh := (h r v hr hR hY).threshold ⟨j,List.mem_range.mp hj⟩
  exact threshold_valid_sound _ _ _ _ _ hh

theorem runs_at (h : Receipt) (r v : Nat) (hr : 1≤r) (hR : r≤35) (hY : r+v≤159) : RunsAt r v :=
  (h r v hr hR hY).phases

theorem sum_count_le_base {ι : Type} [DecidableEq ι]
    (h : Receipt) (s : Finset ι) (p : ι → FlagDegree) (count : ι → Nat)
    (hr : ∀ i ∈ s, 1≤(p i).all)
    (hR : (∑ i ∈ s, (p i).all)≤35)
    (hY : (∑ i ∈ s, (p i).all)+(∑ i ∈ s, (p i).yz)≤159)
    (hT : (∑ i ∈ s, (p i).all)+(∑ i ∈ s, (p i).yz)+(∑ i ∈ s, (p i).zOnly)≤9275)
    (hcount : ∀ i ∈ s, ∀ j : Fin 8, count i ≤ sheetSlope j.val*(p i).zOnly+
      sheetOwn j.val (p i).all (p i).yz) :
    (∑ i ∈ s, count i) ≤ baseCap (sumFlag s p) := by
  by_cases hs : s.Nonempty
  · obtain ⟨i,hi⟩ := hs
    have hpos : 1≤∑ i ∈ s, (p i).all := (hr i hi).trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le ((p j).all)) hi)
    have hb := (h _ _ hpos hR hY).base
    obtain ⟨j,hj,hbase⟩ := base_valid_sound _ _ _ _ _ _ hb
      (∑ i ∈ s, (p i).zOnly) (Nat.zero_le _) (by omega)
    have hc := AffineFactorAggregate6808.sum_count_le 35 159 (sheetSlope j)
      (sheetOwn j) (sheetPacked j) (MovingFiberPacking6811.sheet_bellman ⟨j,hj⟩)
      s (fun i => (p i).all) (fun i => (p i).yz) (fun i => (p i).zOnly) count
      hr hR hY (fun i hi => hcount i hi ⟨j,hj⟩)
    exact hc.trans hbase
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp only [Finset.sum_empty]
    exact Nat.zero_le _

#print axioms sum_count_le_base
end ProximityPrize.SubmissionLower.Lower80860.ReceiptBridge
