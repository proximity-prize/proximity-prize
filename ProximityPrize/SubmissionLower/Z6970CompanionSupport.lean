import ProximityPrize.SubmissionLower.Z6970H2307OrderLookup
import ProximityPrize.SubmissionLower.Z6970CompanionAnchors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

namespace Height2307Companion
open Height2307Orders (order lookup thresholds Threshold)

private theorem oneLookup (b j : ℕ) (rows : List Threshold) : 1 ≤ lookup b j rows := by
  induction rows with
  | nil => exact le_rfl
  | cons p rs ih => exact ih.trans (le_max_right _ _)

theorem monoLookup {a j b J : ℕ} (hab : a ≤ b) (hj : j ≤ J)
    (rows : List Threshold) : lookup a j rows ≤ lookup b J rows := by
  induction rows with
  | nil => exact le_rfl
  | cons p rs ih =>
    dsimp only [lookup]
    by_cases smaller : p.b ≤ a ∧ p.j ≤ j
    · have larger : p.b ≤ b ∧ p.j ≤ J := ⟨smaller.1.trans hab,smaller.2.trans hj⟩
      simp only [if_pos smaller,if_pos larger]
      exact max_le_max le_rfl ih
    · simp only [if_neg smaller]
      exact max_le ((oneLookup b J rs).trans (le_max_right _ _)) (ih.trans (le_max_right _ _))

private def bandOf (n : ℕ) : Fin 42 := ⟨n%42, Nat.mod_lt n (by decide)⟩

private theorem anchorPayments :
    anchors.all (fun p => decide (p.m ≤ order (bandOf p.k) p.b p.j)) = true := by
  decide +kernel

theorem supports_order (k : Fin 42) : Supports anchors k.val (order k) := by
  refine ⟨fun b j => oneLookup b j (thresholds k), ?_⟩
  intro p hp same
  have h := of_decide_eq_true ((List.all_eq_true.mp anchorPayments) p hp)
  have hk : bandOf p.k = k := by apply Fin.ext; change p.k%42=k.val; rw [same,Nat.mod_eq_of_lt k.isLt]
  rwa [hk] at h

end Height2307Companion
