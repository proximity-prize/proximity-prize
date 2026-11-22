import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.Low48BentPolarization

set_option autoImplicit false
set_option Elab.async false

namespace Low48BentCycle

noncomputable section

open Low48BentLattice (Cap Chamber latticePoints)
open Low48Price (addBent ambientMix bentIntegral primaryBox tiltedSurface)
open K1_13 (Shape)
open K1_13_6_2_4_1 (positiveDiagonal)
open scoped BigOperators

def integral (a : Cap) : ℤ := bentIntegral a.1.b a.1.j a.1.t a.2

private def slots : List (Fin 5) := [0, 1, 2, 3, 4]

private theorem sublists_slots :
    (↑(slots.sublists.map List.toFinset) : Multiset (Finset (Fin 5))) =
      (Finset.univ : Finset (Fin 5)).powerset.val := by
  decide

private theorem fold_cap (B : Fin 5 → Cap) (l : List (Fin 5)) (hl : l.Nodup) (acc : Cap) :
    (l.map B).foldl addBent acc = Low48BentLattice.Add acc (Low48BentLattice.Sum l.toFinset B) := by
  induction l generalizing acc with
  | nil =>
    rcases acc with ⟨⟨b,j,t⟩, h⟩
    simp [Low48BentLattice.Add, Low48BentLattice.Sum, Shape.plus]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.foldl_cons, ih hl, List.toFinset_cons]
    simp [Low48BentLattice.Add, addBent, Low48BentLattice.Sum, Shape.plus,
      Finset.sum_insert (mt List.mem_toFinset.mp hi), Nat.add_assoc]

private theorem fold_charge {α : Type*} (f : α → ℤ) (l : List α) (a : ℤ) :
    l.foldl (fun s x => s + f x) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih => simp [ih, add_assoc]


set_option maxHeartbeats 1000000 in
private theorem ambient_list (B : Fin 5 → Cap) :
    ambientMix (slots.map B) =
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
        integral (Low48BentLattice.Sum J B)).toNat := by
  classical
  unfold ambientMix
  let charge := fun J : Finset (Fin 5) => (-1 : ℤ) ^ (5 - J.card) * integral (Low48BentLattice.Sum J B)
  congr 1
  rw [List.sublists_map, fold_charge, zero_add, List.map_map]
  calc
    _ = (slots.sublists.map (charge ∘ List.toFinset)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro l hl
      have hn := (List.mem_sublists.mp hl).nodup (show slots.Nodup by decide)
      simp only [Function.comp_apply, List.length_map, fold_cap B l hn]
      simp [charge, List.toFinset_card_of_nodup hn, integral, Low48BentLattice.Add, Shape.plus]
    _ = ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, charge J := by
      rw [← List.map_map]
      change (Multiset.map charge (↑(slots.sublists.map List.toFinset) :
        Multiset (Finset (Fin 5)))).sum = _
      rw [sublists_slots]
      rfl


end

end Low48BentCycle
