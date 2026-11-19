/- P33Split: split a shared-cover tree check (`CP.check`) into independent per-subtree checks.
   The data modules (P33Slope*) decide `CP.check boxes N m tree (root m)` for trees of thousands of leaves; one `decide`
   over a whole tree exceeds the 12 GiB module budget. `cutList` cuts the tree into subtrees of at most `B` nodes (together
   with the boxes reaching them), `check_cut` says the tree check is the conjunction of the subtree checks, and
   each subtree is decided by its own small theorem. -/
import ProximityPrize.SubmissionLower.P33Base

set_option Elab.async false

namespace ProximityPrize
namespace SubmissionLower
namespace P33
set_option autoImplicit false
open CP PA
open DR (Box lower upper)

/-- node count -/
def treeSize : Tree → ℕ
  | .empty => 1
  | .leaf _ => 1
  | .node _ _ l r => treeSize l + treeSize r + 1

/-- Cut `tree` (with the box `a` reaching it) into subtrees of at most `B` nodes. -/
def cutList (m B : ℕ) : Tree → Box → List (Tree × Box)
  | .node ax pv l r, a =>
    if treeSize (.node ax pv l r) ≤ B then [(.node ax pv l r, a)]
    else
      let b := normalize m 8 a
      cutList m B l (lower b ax pv) ++ cutList m B r (upper b ax pv)
  | t, a => [(t, a)]

def subCheck (boxes : ℕ → Box) (N m : ℕ) (p : Tree × Box) : Bool := check boxes N m p.1 p.2

def noBox : Tree × Box := (.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩)

theorem check_cut (boxes : ℕ → Box) (N m B : ℕ) (t : Tree) (a : Box) :
    check boxes N m t a = (cutList m B t a).all (subCheck boxes N m) := by
  induction t generalizing a with
  | empty => simp [cutList, subCheck]
  | leaf i => simp [cutList, subCheck]
  | node ax pv l r ihl ihr =>
    by_cases h : treeSize (.node ax pv l r) ≤ B
    · simp [cutList, h, subCheck]
    · simp only [cutList, h, if_false, List.all_append]
      rw [← ihl, ← ihr]
      simp only [check]

theorem mem_getD {α : Type} (L : List α) (d p : α) (hp : p ∈ L) : ∃ i, i < L.length ∧ L.getD i d = p := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem hp
  exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi, h]⟩

/-- Recombination: if the list has at most `n` entries and each entry `getD i` (i < n) passes, all pass. -/
theorem all_of_getD {α : Type} (L : List α) (d : α) (f : α → Bool) (n : ℕ) (hn : L.length ≤ n)
    (h : ∀ i, i < n → f (L.getD i d) = true) : L.all f = true := by
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := mem_getD L d p hp
  exact h i (lt_of_lt_of_le hi hn)

end P33
end SubmissionLower
end ProximityPrize
