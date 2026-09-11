import Mathlib.Tactic

namespace ConvexEndpoint
set_option autoImplicit false

private theorem bound_length (f : ℕ → ℕ) (n lo v : ℕ)
    (hl : lo ≤ v) (hh : v ≤ lo+n)
    (hc : ∀ i, lo ≤ i → i+2 ≤ lo+n → 2*f (i+1) ≤ f i+f (i+2)) :
    f v ≤ max (f lo) (f (lo+n)) := by
  induction n generalizing lo v with
  | zero =>
    have he : v = lo := by omega
    subst v
    simp
  | succ n ih =>
    have htail : ∀ w, lo+1 ≤ w → w ≤ lo+(n+1) →
        f w ≤ max (f (lo+1)) (f (lo+(n+1))) := by
      intro w hw hw'
      have ht := ih (lo+1) w hw (by omega)
        (fun i hi hi' => hc i (by omega) (by omega))
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ht
    have hm : f (lo+1) ≤ max (f lo) (f (lo+(n+1))) := by
      by_cases hn : n = 0
      · subst n; simp
      · have htwo := htail (lo+2) (by omega) (by omega)
        have hstep := hc lo (by omega) (by omega)
        omega
    by_cases hv : v = lo
    · subst v; exact le_max_left _ _
    · exact (htail v (by omega) hh).trans (max_le hm (le_max_right _ _))

theorem bound (f : ℕ → ℕ) (lo hi v : ℕ) (hl : lo ≤ v) (hh : v ≤ hi)
    (hc : ∀ i, lo ≤ i → i+2 ≤ hi → 2*f (i+1) ≤ f i+f (i+2)) :
    f v ≤ max (f lo) (f hi) := by
  have he : lo+(hi-lo) = hi := by omega
  have h := bound_length f (hi-lo) lo v hl (by omega)
    (fun i hi' hi'' => hc i hi' (by omega))
  simpa only [he] using h

end ConvexEndpoint
