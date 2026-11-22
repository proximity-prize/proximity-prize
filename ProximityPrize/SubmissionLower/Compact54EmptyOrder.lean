import ProximityPrize.SubmissionLower.Final50PriceCaps

set_option Elab.async false
set_option maxRecDepth 4000

namespace Compact54EmptyOrder

open Final50PriceCaps (order order_pos thresholds)
open K1_13 (Shape)
open K1_13_8_2 (Threshold orderFor)

private instance : DecidableEq Threshold :=
  fun a b => match a, b with
    | ⟨x,y,z⟩, ⟨u,v,w⟩ =>
      decidable_of_iff (x = u ∧ y = v ∧ z = w) (by simp)

private def witnesses : List Threshold := [⟨100,49,47⟩, ⟨82,44,46⟩, ⟨117,46,47⟩, ⟨87,51,47⟩, ⟨101,41,46⟩, ⟨127,44,47⟩, ⟨106,48,47⟩, ⟨49,50,46⟩, ⟨80,52,47⟩, ⟨94,50,47⟩, ⟨122,45,47⟩, ⟨129,55,48⟩, ⟨112,47,47⟩, ⟨132,43,47⟩]

private theorem valid :
    witnesses.all (fun q => decide (q ∈ thresholds .empty)) = true := by decide +kernel

private theorem admits_order {q : Threshold} {b j : ℕ} {qs : List Threshold}
    (hq : q ∈ qs) (hb : q.b ≤ b) (hj : q.j ≤ j) : q.l ≤ orderFor b j qs := by
  induction qs with
  | nil => simp at hq
  | cons s rest ih =>
    rcases List.mem_cons.mp hq with he | ht
    · subst s
      rw [orderFor, if_pos ⟨hb,hj⟩]
      exact le_max_left _ _
    · exact (ih ht).trans (by rw [orderFor]; exact le_max_right _ _)

private def takes (x : Shape) (l : ℕ) (q : Threshold) : Bool :=
  decide (l ≤ q.l ∧ q.b ≤ x.b ∧ q.j ≤ x.j)

def Supported (x : Shape) (l : ℕ) : Prop :=
  l ≤ 1 ∨ witnesses.any (takes x l) = true

instance (x : Shape) (l : ℕ) : Decidable (Supported x l) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem le_order {x : Shape} {l : ℕ} (h : Supported x l) : l ≤ order .empty x := by
  rcases h with h | h
  · exact h.trans (order_pos .empty x)
  · obtain ⟨q,hq,ht⟩ := List.any_eq_true.mp h
    have hmem : q ∈ thresholds .empty :=
      of_decide_eq_true (List.all_eq_true.mp valid q hq)
    have hs : l ≤ q.l ∧ q.b ≤ x.b ∧ q.j ≤ x.j := of_decide_eq_true ht
    exact hs.1.trans (admits_order hmem hs.2.1 hs.2.2)

end Compact54EmptyOrder
