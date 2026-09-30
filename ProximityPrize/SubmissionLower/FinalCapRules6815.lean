import ProximityPrize.SubmissionLower.TerminalCharge6815
namespace ProximityPrize.SubmissionLower.FinalCapRules6815
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem sum_le_of_rules {ι J : Type*} [DecidableEq ι]
    (ambient : Finset ι) (count : ι → ℕ) (cap : Finset ι → ℕ)
    (base : Finset ι → Prop) (routeable : J → Finset ι → Prop) (charge : J → ι → ℕ)
    (hbase : ∀ s, s⊆ambient → base s → (∑ i∈s,count i)≤cap s)
    (hroute : ∀ j s, s⊆ambient → routeable j s →
      ∃ U, U⊂s ∧ ∀ i∈s\U, count i≤charge j i)
    (hrules : ∀ s, s⊆ambient → base s ∨ ∃ j, routeable j s ∧
      ∀ U, U⊂s → ¬routeable j U → cap U+(∑ i∈s\U,charge j i)≤cap s) :
    (∑ i∈ambient,count i)≤cap ambient := by
  have aux : ∀ s : Finset ι, s⊆ambient → (∑ i∈s,count i)≤cap s := by
    intro s
    induction s using Finset.strongInduction with
    | H s ih =>
      intro hs
      rcases hrules s hs with hb | ⟨j,hj,hbudget⟩
      · exact hbase s hs hb
      obtain ⟨U,hU,hstop,hcharged⟩ := TerminalCharge6815.exists_terminal count (charge j) (routeable j) s
        (fun B hB hr => hroute j B (hB.trans hs) hr)
      have hproper : U⊂s := (Finset.ssubset_iff_subset_ne).mpr ⟨hU,by
        intro he
        subst U
        exact hstop hj⟩
      have hcount := ih U hproper (hU.trans hs)
      have hsum := Finset.sum_sdiff hU (f:=count)
      calc
        _=(∑ i∈U,count i)+(∑ i∈s\U,count i) := by omega
        _≤cap U+(∑ i∈s\U,charge j i) := Nat.add_le_add hcount (Finset.sum_le_sum hcharged)
        _≤cap s := hbudget U hproper hstop
  exact aux ambient (Finset.Subset.refl _)

theorem sum_weight_strict {ι : Type*} [DecidableEq ι]
    (s U : Finset ι) (r : ι → ℕ) (h : U⊂s) (hr : ∀ i∈s, 1≤r i) :
    (∑ i∈U,r i)<∑ i∈s,r i := by
  obtain ⟨i,his,hiU⟩ := Finset.exists_of_ssubset h
  have hsub : insert i U⊆s := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact his
    · exact h.subset hk
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le (r i))
  rw [Finset.sum_insert hiU] at hs
  have hp := hr i his
  omega

end ProximityPrize.SubmissionLower.FinalCapRules6815
