import ProximityPrize.SubmissionLower.Z6970H2307OrderShardCore

set_option autoImplicit false
set_option Elab.async false

namespace Height2307Orders
open K1_13 (Shape)

/-- Stop positions and cumulative values for a single retained stride. -/
def prefixChain (r : Shape) (w : Nat) : Nat → Nat → List (Nat × Nat) → Bool
  | _, _, [] => true
  | off, b, (stop,v) :: rest =>
    decide (off ≤ stop ∧ b + beforeSlice w r off (stop-off) = v) &&
      prefixChain r w stop v rest

theorem prefixGood_chain (r : Shape) (w off b : Nat) (xs : List (Nat × Nat))
    (hb : beforeSlice w r 0 off = b) (h : prefixChain r w off b xs = true) :
    prefixGood r (xs.map (fun (l,v) => (w,l,v))) = true := by
  induction xs generalizing off b with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨stop,v⟩ := hd
    simp only [prefixChain,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨hs,h₂⟩ := h
    have hv : beforeSlice w r 0 stop = v := by
      rw [← Nat.add_sub_of_le hs.1, beforeSlice_add, Nat.zero_add, hb]
      exact hs.2
    change (decide (beforeSlice w r 0 stop=v) && prefixGood r
      (rest.map (fun (l,v) => (w,l,v)))) = true
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hv,ih _ _ hv h₂⟩

end Height2307Orders
