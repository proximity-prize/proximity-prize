import ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex

/-! Packed from ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration. -/
section PackedLocator_LocatorOrdinaryConcentration

/-!
# Concentrating ordinary-factor excess total degree

Discrete convexity lets all raw `z` weight in a finite nonempty family be
moved to one carrier without decreasing the upper bound.  This reduces the
three-coordinate ordinary partition problem to a two-coordinate zero-`z`
knapsack plus one carrier line.
-/

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration

open scoped BigOperators
open LocatorOrdinaryZConvex

set_option autoImplicit false

theorem exists_z_carrier
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (r v z : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i) (hne : s.Nonempty) :
    ∃ c ∈ s,
      (∑ i ∈ s, rawCost (r i) (v i) (z i)) ≤
        rawCost (r c) (v c) (∑ i ∈ s, z i) +
          ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 := by
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert a s ha ih =>
      by_cases hs : s = ∅
      · subst s
        refine ⟨a, by simp, ?_⟩
        simp
      · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
        obtain ⟨c, hc, hbound⟩ := ih (fun i hi => hr i (by simp [hi])) hsne
        have hra : 1 ≤ r a := hr a (by simp)
        have hrc : 1 ≤ r c := hr c (by simp [hc])
        have hpair := two_discreteConvex_endpoint
          (rawCost (r a) (v a)) (rawCost (r c) (v c))
          (rawCost_mono_z (r a) (v a)) (rawCost_mono_z (r c) (v c))
          (fun n => rawCost_discreteConvex (r a) (v a) n hra)
          (fun n => rawCost_discreteConvex (r c) (v c) n hrc)
          (z a) (∑ i ∈ s, z i)
        have hpre :
            (∑ i ∈ insert a s, rawCost (r i) (v i) (z i)) ≤
              rawCost (r a) (v a) (z a) +
                (rawCost (r c) (v c) (∑ i ∈ s, z i) +
                  ∑ i ∈ s.erase c, rawCost (r i) (v i) 0) := by
          rw [Finset.sum_insert ha]
          exact Nat.add_le_add_left hbound _
        by_cases hend :
            rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                rawCost (r c) (v c) 0 ≤
              rawCost (r a) (v a) 0 +
                rawCost (r c) (v c) (z a + ∑ i ∈ s, z i)
        · refine ⟨c, by simp [hc], ?_⟩
          have htwo :
              rawCost (r a) (v a) (z a) +
                  rawCost (r c) (v c) (∑ i ∈ s, z i) ≤
                rawCost (r a) (v a) 0 +
                  rawCost (r c) (v c) (z a + ∑ i ∈ s, z i) := by
            exact hpair.trans (by simpa [max_eq_right hend])
          calc
            (∑ i ∈ insert a s, rawCost (r i) (v i) (z i)) ≤
                rawCost (r a) (v a) (z a) +
                  (rawCost (r c) (v c) (∑ i ∈ s, z i) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0) := hpre
            _ ≤ (rawCost (r a) (v a) 0 +
                  rawCost (r c) (v c) (z a + ∑ i ∈ s, z i)) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 := by omega
            _ = rawCost (r c) (v c) (∑ i ∈ insert a s, z i) +
                  ∑ i ∈ (insert a s).erase c,
                    rawCost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha]
              have hac : a ≠ c := fun h => ha (h ▸ hc)
              rw [Finset.erase_insert_of_ne hac, Finset.sum_insert]
              · ac_rfl
              · exact fun h => ha (Finset.mem_of_mem_erase h)
        · refine ⟨a, by simp, ?_⟩
          have hreverse :
              rawCost (r c) (v c) (z a + ∑ i ∈ s, z i) +
                  rawCost (r a) (v a) 0 ≤
                rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  rawCost (r c) (v c) 0 := by
            omega
          have htwo :
              rawCost (r a) (v a) (z a) +
                  rawCost (r c) (v c) (∑ i ∈ s, z i) ≤
                rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  rawCost (r c) (v c) 0 := by
            exact hpair.trans (by
              rw [max_eq_left]
              simpa [Nat.add_comm] using hreverse)
          have hzeros :
              rawCost (r c) (v c) 0 +
                  ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 =
                ∑ i ∈ s, rawCost (r i) (v i) 0 := by
            simpa only [Nat.add_comm] using
              (Finset.sum_erase_add s
                (fun i => rawCost (r i) (v i) 0) hc)
          calc
            (∑ i ∈ insert a s, rawCost (r i) (v i) (z i)) ≤
                rawCost (r a) (v a) (z a) +
                  (rawCost (r c) (v c) (∑ i ∈ s, z i) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0) := hpre
            _ ≤ (rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  rawCost (r c) (v c) 0) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 := by omega
            _ = rawCost (r a) (v a) (∑ i ∈ insert a s, z i) +
                  ∑ i ∈ (insert a s).erase a,
                    rawCost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha, Finset.erase_insert ha]
              rw [← hzeros]
              ac_rfl

end ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration
end PackedLocator_LocatorOrdinaryConcentration

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier16 : True := by trivial
end ProximityPrize.SubmissionLower

