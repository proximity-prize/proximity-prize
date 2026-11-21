import ProximityPrize.SubmissionLower.AnchorCuts82170Group0
import ProximityPrize.SubmissionLower.AnchorCuts82170Group1
import ProximityPrize.SubmissionLower.AnchorCuts82170Group2
import ProximityPrize.SubmissionLower.AnchorCuts82170Group3
import ProximityPrize.SubmissionLower.AnchorCuts82170Group4
import ProximityPrize.SubmissionLower.Fast070

set_option maxRecDepth 28000
set_option maxHeartbeats 3000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace AnchorCuts82170
open K1_13 K1_13_1_1 SoundnessAnchor AnchorSpace82170

open private rank_block_le_budget totalBudget_eq_sum from ProximityPrize.SubmissionLower.Fast070

private def cuts (s : ℕ) : List (Cut s) := match s with
  | 104 => cuts104
  | 105 => cuts105
  | 106 => cuts106
  | 107 => cuts107
  | 108 => cuts108
  | 109 => cuts109
  | 110 => cuts110
  | 111 => cuts111
  | 112 => cuts112
  | 113 => cuts113
  | 114 => cuts114
  | 115 => cuts115
  | 116 => cuts116
  | 117 => cuts117
  | 118 => cuts118
  | 119 => cuts119
  | 120 => cuts120
  | _ => []

private def lookup (s : ℕ) (g : ℤ) : Option (Cut s) :=
  (cuts s).find? (fun e => decide (offset e.index = g))

private def chooseDegree (s : ℕ) : Option (Cut s) → ℕ
  | some _ => min s (cap s)
  | none => residualDegree s

def degree (s : ℕ) (g : ℤ) : ℕ := chooseDegree s (lookup s g)

def extra (s r : ℕ) : ℕ := ((lookup s (offset r)).map Cut.gain).getD 0

theorem degree_le (s : ℕ) (g : ℤ) : degree s g ≤ s := by
  unfold degree
  cases lookup s g <;> apply min_le_left

private theorem old_cap {s : ℕ} (hs : s ≤ 120) : cap s ≤ 48 - (s - 113 + 1)/2 := by
  unfold cap
  split_ifs <;> omega

theorem degree_ge {s t : ℕ} (g : ℤ) (hs : s ≤ 120) (h₁ : t ≤ s) (h₂ : t ≤ cap s) :
    t ≤ degree s g := by
  unfold degree
  cases lookup s g with
  | none => exact le_min h₁ (h₂.trans (old_cap hs))
  | some => exact le_min h₁ h₂

private theorem extra_total : (∑ s : Fin 121, ∑ r : Fin 138, extra s r) = 8166 := by
  simp only [← sumRange_eq_fin]
  decide +kernel

theorem per_block (s : Fin 121) (r : Fin 138) :
    Module.finrank Geom (LinearMap.range (blockAt (degree s (offset r)) s (offset r))) +
      extra s r + improvement s r ≤ blockBudget s (offset r) := by
  unfold degree extra
  cases he : lookup s (offset r) with
  | none =>
    simp only [chooseDegree, Option.map_none, Option.getD_none, Nat.add_zero]
    exact rank_plus_gain s r (rank_block_le_budget K1_13_1_1_1.proof
      K1_13_1_1_2.proof K1_13_1_1_3.proof s (offset r) (Nat.le_of_lt_succ s.isLt)
      (by unfold offset; omega))
  | some e =>
    have h := List.find?_some he
    have hoff : offset e.index = offset r := of_decide_eq_true h
    have hr : e.index = r.val := by unfold offset at hoff; omega
    have hc := e.checked
    rw [hr] at hc
    exact (Nat.add_le_add_right (Nat.add_le_add_right
      (rank_at (min s (cap s)) s (offset r) e.powers) e.gain) (improvement s r)).trans hc

theorem total_rank :
    (∑ s : Fin 121, ∑ r : Fin 138, Module.finrank Geom
      (LinearMap.range (blockAt (degree s (offset r)) s (offset r)))) ≤ 9190403 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 121))) fun s _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 138))) fun r _ => per_block s r
  simp only [Finset.sum_add_distrib] at h
  rw [extra_total, gain_total, ← totalBudget_eq_sum, totalBudget_eq] at h
  omega

#print axioms total_rank

end AnchorCuts82170
