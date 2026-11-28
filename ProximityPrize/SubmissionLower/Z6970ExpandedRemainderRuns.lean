import ProximityPrize.SubmissionLower.Z6970ExpandedRemainderPrefix
import ProximityPrize.SubmissionLower.Z6970ExpandedRemainderTable

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

namespace ExpandedTaper6970
open Finset
open scoped BigOperators

abbrev Run := ℕ × ℕ

def span : List Run → ℕ
  | [] => 0
  | (n,_)::tail => n + span tail

def valid : ℕ → List Run → Bool
  | _,[] => true
  | lo,(n,m)::tail =>
      (m != 0 || decide (lo+n ≤ 3000 ∨ 3000 ≤ lo)) && valid (lo+n) tail

def alternateFee (q a : ℕ) : ℕ :=
  let F := rowFlag q a
  (Wide50EulerPrimary.oldCountI F -
    Wide50EulerPrimary.kernelLowerI {F with degree := F.degree - valuePower q a}).toNat

theorem cell_le_alternate (q a : ℕ) : remainderCell q a ≤ alternateFee q a := by
  unfold remainderCell alternateFee
  dsimp only
  split
  · exact Nat.zero_le _
  · omega

def selectRun (q lo n m : ℕ) : ℤ :=
  if m = 0 then activeRun q lo n else
  if m = 2 then targetRun q lo n else
  24 * ((TaperBudget.sumRange (fun j => alternateFee q (lo+j)) n : ℕ) : ℤ)

def replay : ℕ → ℕ → List Run → ℤ
  | _,_,[] => 0
  | q,lo,(n,m)::tail => selectRun q lo n m + replay q (lo+n) tail

theorem selectRun_le (q lo n m : ℕ) (h : m=0 → lo+n ≤ 3000 ∨ 3000 ≤ lo) :
    24 * (∑ a ∈ range n, (remainderCell q (lo+a) : ℤ)) ≤ selectRun q lo n m := by
  unfold selectRun
  split
  · rename_i hm
    rw [← activeRun_eq q lo n (h hm)]
    exact mul_le_mul_of_nonneg_left
      (sum_le_sum fun a _ => cell_le_active q (lo+a)) (by decide)
  · split
    · rw [← targetRun_eq]
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum fun a _ => cell_le_target q (lo+a)) (by decide)
    · rw [TaperBudget.sumRange_eq, Nat.cast_sum]
      exact mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => by
        exact_mod_cast cell_le_alternate q (lo+a)) (by decide)

theorem replay_le (q lo : ℕ) (runs : List Run) (h : valid lo runs = true) :
    24 * (∑ a ∈ range (span runs), (remainderCell q (lo+a) : ℤ)) ≤ replay q lo runs := by
  induction runs generalizing lo with
  | nil => simp [span,replay]
  | cons entry tail ih =>
      obtain ⟨n,m⟩ := entry
      simp only [valid, Bool.and_eq_true] at h
      have hc : m=0 → lo+n ≤ 3000 ∨ 3000 ≤ lo := by
        intro hm
        subst m
        simpa using h.1
      simp only [span,sum_range_add,mul_add,replay,← Nat.add_assoc lo n]
      exact add_le_add (selectRun_le q lo n m hc) (ih (lo+n) h.2)

theorem certifyRow (q bill : ℕ) (runs : List Run)
    (hlen : span runs = 4679-q) (hv : valid 0 runs = true)
    (hpaid : replay q 0 runs ≤ 24 * (bill : ℤ)) : remainderRow q ≤ bill := by
  unfold remainderRow
  split
  · exact Nat.zero_le _
  · have h := replay_le q 0 runs hv
    rw [hlen] at h
    simp only [TaperBudget.sumRange_eq,← Nat.cast_sum,Nat.zero_add] at h ⊢
    omega

abbrev RunRow := ℕ × List Run

def batchCost : List RunRow → ℕ
  | [] => 0
  | (bill,_)::tail => bill+batchCost tail

def verifyBatch : ℕ → List RunRow → Bool
  | _,[] => true
  | q,(bill,runs)::tail =>
      ((decide (span runs = 4679-q) && valid 0 runs) &&
        decide (replay q 0 runs ≤ 24*(bill : ℤ))) && verifyBatch (q+1) tail

theorem batch_sound (lo : ℕ) (data : List RunRow) (h : verifyBatch lo data = true) :
    remainderChunk lo data.length ≤ batchCost data := by
  induction data generalizing lo with
  | nil => simp [remainderChunk,TaperBudget.sumRange,batchCost]
  | cons qs rest ih =>
      obtain ⟨bill,runs⟩ := qs
      simp only [verifyBatch,Bool.and_eq_true,decide_eq_true_eq] at h
      have he := certifyRow lo bill runs h.1.1.1 h.1.1.2 h.1.2
      have hr := ih (lo+1) h.2
      simp only [List.length_cons,batchCost]
      rw [Nat.add_comm rest.length 1, remainderChunk_add]
      have hs : remainderChunk lo 1 = remainderRow lo := by
        simp only [remainderChunk,TaperBudget.sumRange,Nat.add_zero,Nat.zero_add]
      rw [hs]
      change remainderRow lo + remainderChunk (lo+1) rest.length ≤ bill + batchCost rest
      omega

end ExpandedTaper6970
