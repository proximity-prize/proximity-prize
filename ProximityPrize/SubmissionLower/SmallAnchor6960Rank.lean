/-
The grade bounds and receipts are from public Proximity Prize peer submission
657, commit e07f14a81dfe2cf1bda985e67040ad4d31fe81ab.
-/
import ProximityPrize.SubmissionLower.SmallAnchor6960Blocks
import ProximityPrize.SubmissionLower.SmallAnchorBlockZero
import ProximityPrize.SubmissionLower.SmallAnchor6960RepricedFees

set_option Elab.async false
set_option autoImplicit false

namespace SmallAnchor6960Rank

open K1_13 (Geom)
open SmallAnchor6960Space (cap anchorLocal)
open scoped BigOperators

theorem origin_rank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 18553227 := by
  apply SmallAnchor6960Blocks.origin_le_blocks.trans
  rw [Fin.sum_univ_castSucc]
  have hlast : (∑ r : Fin 158, Module.finrank Geom
      (LinearMap.range (Final50RankCore.blockAt (cap (Fin.last 137)) (Fin.last 137)
        ((r:ℕ) - (56:ℤ)))))=0:=by
    change (∑ r : Fin 158, Module.finrank Geom
      (LinearMap.range (Final50RankCore.blockAt 34 137 ((r:ℕ) - (56:ℤ)))))=0
    simp only [SmallAnchorBlockZero.rank_eq_zero (d := 34) (s := 137) (by decide),
      Finset.sum_const_zero]
  rw [hlast,Nat.add_zero]
  change (∑ s : Fin 137, ∑ r : Fin 158, Module.finrank Geom
      (LinearMap.range (Final50RankCore.blockAt (cap s) s ((r:ℕ) - (56:ℤ)))))≤_
  calc
    _ ≤ ∑ s : Fin 137, Final50RankCore.gradeFee s (Final50RankReceipt.rows (cap s)) := by
      apply Finset.sum_le_sum
      intro s _
      let d:Fin 57:=⟨cap s,Nat.lt_succ_of_le (SmallAnchor6960Space.cap_le_index s)⟩
      exact Final50RankCore.grade_bound s d (Final50RankReceipt.rows d)
        (Final50RankReceipt.rows_good d) (Final50RankReceipt.rows_sorted d)
        (Final50RankReceipt.rows_cover d)
    _=_:=SmallAnchor6960RepricedFees.total_fees

#print axioms origin_rank
end SmallAnchor6960Rank
