import ProximityPrize.SubmissionLower.Peer653High53FamilyCutoff

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
noncomputable section
open Finset Polynomial MvPolynomial
open Peer653High53 (agreement)
open K1_14 (Shape shapeSum Banks Equation FX Jet slots triangle SeedBound)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth seedDegree seedDegree_pow)
open P1_7_5 (kept)
open private position_sum from ProximityPrize.SubmissionLower.UpperBranch5
open private rank_joint_multiples_le gradeCapacity_eq from ProximityPrize.SubmissionLower.UpperBranch5
open private shapeSum_swap from ProximityPrize.SubmissionLower.Fast072
open private finrank_le_grades mem_filtered from ProximityPrize.SubmissionLower.Fast069
theorem cutoff_total (h : ℕ) (s : Shape) (E v : ℕ) (hh : 0 < 2*h) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range (s.m*agreement), cutoffCapacity h s E v W) + jointGain h s E v =
      triangle s.U * shapeSum s (fun q j => s.m*agreement+j-q*(131071-h)) := by
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range (s.m*agreement), shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range (s.m*agreement), F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [cutoffCapacity, jointGain]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact position_sum (s.m*agreement) (2*h) (q*(131071-h)) j s.U v ((q-j)/E)
    (hjq.trans hq) hh
private theorem trace_rank_le {h E v W : ℕ} {t : Bank}
    {rows : K1_14.Banks} {f : K1_14.Equation} (ht : TerminalTrace h t rows f)
    (hne : f ≠ 0) (hE : E ≤ f.natDegree) (hv : v ≤ K1_14_4.seedDegree f)
    (hk : 0 < 131071 - h) (he : 0 < E) (hW : W < t.shape.m * agreement) :
    Module.finrank FX (rows t.shape W) ≤ cutoffCapacity h t.shape E v W :=
  cutoff_finrank_le h t.shape E v W (rows t.shape W) (f := f) hne hE hv hk he
    (fun P hP => ht.shape W P hP)
    (fun P hP hn => ht.leading W P hP hn)
    (fun P hP hn => ht.divides W hW P hP hn)
theorem joint_loss {b : Peer653High53.Band} {h : ℕ} (hl : (start b) ≤ h) (hu : h ≤ (finish b))
    (x : Test b) {rows f} (hf : Reduced f) (ht : TerminalTrace h (tested b x) rows f)
    (hE : threshold b x ≤ f.natDegree) (hv : seedThreshold b x ≤ seedDegree f) :
    jointGain h (tested b x).shape (threshold b x) (seedThreshold b x) ≤ debit h (tested b x) := by
  obtain ⟨hlo, hhi, htop, _, hwidth⟩ := terminal_guards b
  obtain ⟨_, hm, hB, _, _⟩ := tested_spec b x
  have hh : 0 < 2*h := by omega
  have hk : 0 < 131071-h := by omega
  have he : 0 < threshold b x := by cases x <;> exact Nat.succ_pos _
  have hne : f ≠ 0 := by
    intro hz
    have hpos := hf.1
    simp [hz] at hpos
  let t := tested b x
  let top := t.shape.m*agreement
  have htopPos : 0 < top := by
    change 0 < (tested b x).shape.m*agreement
    rwa [hm]
  have hbWidth : t.shape.B*(131071-h) ≤ top := by
    change (tested b x).shape.B*(131071-h) ≤ (tested b x).shape.m*agreement
    rw [hm, hB]
    exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hl _)).trans hwidth
  have htopSub : top-1+1 = top := by omega
  have hraw : ∀ q ≤ t.shape.B, ∀ j ≤ min q t.shape.J,
      q*(131071-h) ≤ top-1+1+j := by
    intro q hq j _
    rw [htopSub]
    exact (Nat.mul_le_mul_right _ hq).trans (hbWidth.trans (by omega : top ≤ top+j))
  have hmin := ht.floor_bound (top-1) (show top-1 < top by omega) hraw
  change triangle t.shape.U * shapeSum t.shape (fun q j => top-1+1+j-q*(131071-h)) ≤
    debit h t + ∑ W ∈ range (top-1+1), Module.finrank FX (rows t.shape W) at hmin
  rw [htopSub] at hmin
  have hmax : (∑ W ∈ range top, Module.finrank FX (rows t.shape W)) ≤
      ∑ W ∈ range top, cutoffCapacity h t.shape (threshold b x) (seedThreshold b x) W := by
    apply sum_le_sum
    intro W hW
    exact trace_rank_le ht hne hE hv hk he (mem_range.mp hW)
  have htotal := cutoff_total h t.shape (threshold b x) (seedThreshold b x) hh hk
  change (∑ W ∈ range top, cutoffCapacity h t.shape (threshold b x) (seedThreshold b x) W) +
    jointGain h t.shape (threshold b x) (seedThreshold b x) =
    triangle t.shape.U * shapeSum t.shape (fun q j => top+j-q*(131071-h)) at htotal
  change jointGain h t.shape (threshold b x) (seedThreshold b x) ≤ debit h t
  omega
end
end Peer653High53
end
