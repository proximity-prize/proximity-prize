import ProximityPrize.SubmissionLower.HighCore82258PrefixProcess

set_option Elab.async false

open FrontCore82258 (effectiveHeight)

namespace HighCore82258JointRank

open HighCore82268JointRank (splice bill_with_exit_terminal)

open Finset
open K1_14_2 (Ambient)
open P1_7_4 (Mass dotQ massQ running weightedBill)


section

open HighCore82258 (Band AnchorModel AnchoredFamily InBand Source)
open HighCore82258_3 (Process PairedMass laterCount stopIndex rankMass history)
open K1_14_2_2 (dual mass_mono)
open scoped Classical

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The rank exits and proper cuts in the ordinary high process share one mass bill. -/
theorem process_rank_bill_terminal {b : Band} {u del} {M : AnchorModel u del}
    {Γ} {F:AnchoredFamily M Γ} {rows} {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows}
    (R:Process pairs) (estimate:PairedMass) (src:Source b M F rows)
    (hw:InBand b (effectiveHeight M)) (rankWeight:Mass) (w:ℕ→Mass) :
    ((∑ i ∈ range (laterCount b+1), dotQ (w i) (massQ (R.lost i))) +
      dotQ rankWeight (massQ R.rankExit)) +
      dotQ (running (splice (stopIndex b) rankWeight w) (laterCount b+2)) (massQ R.final) ≤
    weightedBill (laterCount b+2) (splice (stopIndex b) rankWeight w)
      (splice (stopIndex b) (rankMass b) (history b)):=by
  have hcap (i : ℕ) (hi : i < laterCount b+1) (k : Fin 4) :
      massQ (R.live i) k≤history b i k:=by
    exact HighCore82258_3.Process.cap_live (b := b) (M := M) (F := F)
      (pairs:=pairs) R estimate src hw (i:=i) (Nat.le_of_lt_succ hi) k
  have hend:R.live (laterCount b+1)=R.final:=by simp [Process.live]
  rw [← hend]
  refine bill_with_exit_terminal (laterCount b+1) (stopIndex b) (R.sched.stop_le.trans (Nat.le_succ _))
    w (history b) rankWeight (rankMass b) R.live R.lost (R.tested (stopIndex b))
    R.rankExit (fun _ hi => R.next_sub (Nat.le_of_lt_succ hi))
    (fun _ hi => R.lost_diff (Nat.le_of_lt_succ hi)) hcap ?_ ?_ ?_ ?_ ?_
  · rw [Process.live, ite_eq_left R.sched.stop_le]
    exact R.kept_sub _
  · intro I hI
    obtain ⟨hI,hnot⟩:=mem_filter.mp hI
    refine mem_sdiff.mpr ⟨hI, ?_⟩
    rw [Process.live,ite_eq_left R.sched.stop_le]
    exact fun hkeep => hnot ((mem_filter.mp hkeep).2 le_rfl)
  · intro i hi
    change i+1=0 at hi
    omega
  · intro i hi
    change i+1=0 at hi
    omega
  · intro k
    change massQ (R.tested 0) k≤(HighCore82258_3.initialCap b k:ℚ)
    have h : (K1_14_2_2.mass R.parents k : ℚ) ≤ (HighCore82258_3.initialCap b k : ℚ) :=
      Nat.cast_le.mpr (R.init_mass k)
    exact (P1_7_4.massQ_mono (R.tested_sub 0) k).trans h

end

#print axioms process_rank_bill_terminal

end HighCore82258JointRank
