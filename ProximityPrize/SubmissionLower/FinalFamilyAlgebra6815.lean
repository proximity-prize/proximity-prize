import ProximityPrize.SubmissionLower.FinalBaseCount6815
import ProximityPrize.SubmissionLower.FinalRuleCheck6815
import ProximityPrize.SubmissionLower.FinalCapRules6815
namespace ProximityPrize.SubmissionLower.FinalFamilyAlgebra6815
open scoped BigOperators
open FinalRuleCheck6815 FinalPayment6815 FinalPrefixSound6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem family_count {ι : Type*} [DecidableEq ι]
    (ambient : Finset ι) (r v z count : ι → ℕ)
    (hr : ∀ i∈ambient, 1≤r i)
    (hR : (∑ i∈ambient,r i)≤39) (hy : (∑ i∈ambient,r i)+(∑ i∈ambient,v i)≤182)
    (ht : (∑ i∈ambient,r i)+(∑ i∈ambient,v i)+(∑ i∈ambient,z i)≤11192)
    (hsingle : ∀ i∈ambient, count i≤SingletonData6815.cap (r i) (v i) (z i))
    (hsplit : ∀ (j : Fin 7) (s : Finset ι), s⊆ambient →
      1≤(∑ i∈s,r i) → cut (∑ i∈s,r i) (∑ i∈s,v i) j.val≤(∑ i∈s,z i) →
      ∃ U, U⊂s ∧ ∀ i∈s\U, count i≤cost j.val (r i) (v i) (z i))
    (hrules : ∀ capR capV capZ, 1≤capR → capR≤39 → capR+capV≤182 → capR+capV+capZ≤11192 →
      RuleBound capR capV capZ (FinalLedgerData6815.cap capR capV capZ)) :
    (∑ i∈ambient,count i)≤FinalLedgerData6815.cap
      (∑ i∈ambient,r i) (∑ i∈ambient,v i) (∑ i∈ambient,z i) := by
  let cap := fun s : Finset ι => FinalLedgerData6815.cap (∑ i∈s,r i) (∑ i∈s,v i) (∑ i∈s,z i)
  let route := fun (j : Fin 7) (s : Finset ι) =>
    1≤(∑ i∈s,r i) ∧ cut (∑ i∈s,r i) (∑ i∈s,v i) j.val≤(∑ i∈s,z i)
  let base := fun s : Finset ι => s=∅ ∨ FinalBaseCheck6815.BaseBound
    (∑ i∈s,r i) (∑ i∈s,v i) (∑ i∈s,z i) (cap s)
  have narrow (s : Finset ι) (hs : s⊆ambient) :
      (∑ i∈s,r i)≤39 ∧ (∑ i∈s,r i)+(∑ i∈s,v i)≤182 ∧
      (∑ i∈s,r i)+(∑ i∈s,v i)+(∑ i∈s,z i)≤11192 := by
    have h1 : (∑ i∈s,r i)≤∑ i∈ambient,r i := Finset.sum_le_sum_of_subset hs
    have h2 : (∑ i∈s,v i)≤∑ i∈ambient,v i := Finset.sum_le_sum_of_subset hs
    have h3 : (∑ i∈s,z i)≤∑ i∈ambient,z i := Finset.sum_le_sum_of_subset hs
    omega
  have zero_empty (s : Finset ι) (hs : s⊆ambient) (hz : (∑ i∈s,r i)=0) : s=∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    have hiR := hr i (hs hi)
    have hiSum := Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) hi
    omega
  apply FinalCapRules6815.sum_le_of_rules ambient count cap base route
    (fun j i => cost j.val (r i) (v i) (z i))
  · intro s hs hb
    rcases hb with rfl | hb
    · simp
    · have hn := narrow s hs
      exact FinalBaseCount6815.count s r v z count (cap s)
        (fun i hi => hr i (hs hi)) hn.1 hn.2.1 hn.2.2 (fun i hi => hsingle i (hs hi)) hb
  · intro j s hs hroute
    exact hsplit j s hs hroute.1 hroute.2
  · intro s hs
    by_cases hempty : s=∅
    · exact Or.inl (Or.inl hempty)
    have hpos : 1≤∑ i∈s,r i := by
      by_contra hn
      exact hempty (zero_empty s hs (by omega))
    have hn := narrow s hs
    rcases hrules _ _ _ hpos hn.1 hn.2.1 hn.2.2 with hb | ⟨j,hj,hcut,hpay⟩
    · exact Or.inl (Or.inr hb)
    refine Or.inr ⟨⟨j,hj⟩,⟨hpos,hcut⟩,?_⟩
    intro U hU hstop
    have hq := FinalCapRules6815.sum_weight_strict s U r hU (fun i hi => hr i (hs hi))
    have hu : (∑ i∈U,v i)≤∑ i∈s,v i := Finset.sum_le_sum_of_subset hU.subset
    have hx : (∑ i∈U,z i)≤∑ i∈s,z i := Finset.sum_le_sum_of_subset hU.subset
    have hz0 : (∑ i∈U,r i)=0 → (∑ i∈U,v i)=0 ∧ (∑ i∈U,z i)=0 := by
      intro hzero
      rw [zero_empty U (hU.subset.trans hs) hzero]
      simp
    have hxcut : 1≤(∑ i∈U,r i) → (∑ i∈U,z i)<cut (∑ i∈U,r i) (∑ i∈U,v i) j := by
      intro hq1
      by_contra hz
      change ¬(1≤(∑ i∈U,r i) ∧ cut (∑ i∈U,r i) (∑ i∈U,v i) j≤(∑ i∈U,z i)) at hstop
      exact hstop ⟨hq1,by omega⟩
    have hb := hpay _ _ _ hq hu hx hz0 hxcut
    have hc := ExactInitialCharge6815.sum_cost_le (s\U) (src j).totalCap (src j).middleCap (src j).slopeCap
      r (fun i => r i+v i) (fun i => r i+v i+z i)
    have sr := Finset.sum_sdiff hU.subset (f:=r)
    have sv := Finset.sum_sdiff hU.subset (f:=v)
    have sz := Finset.sum_sdiff hU.subset (f:=z)
    have eR : (∑ i∈s\U,r i)=(∑ i∈s,r i)-(∑ i∈U,r i) := by omega
    have eV : (∑ i∈s\U,v i)=(∑ i∈s,v i)-(∑ i∈U,v i) := by omega
    have eZ : (∑ i∈s\U,z i)=(∑ i∈s,z i)-(∑ i∈U,z i) := by omega
    simp only [Finset.sum_add_distrib,eR,eV,eZ] at hc
    change (∑ i∈s\U,cost j (r i) (v i) (z i))≤
      cost j ((∑ i∈s,r i)-(∑ i∈U,r i)) ((∑ i∈s,v i)-(∑ i∈U,v i))
        ((∑ i∈s,z i)-(∑ i∈U,z i)) at hc
    exact (Nat.add_le_add_left hc (cap U)).trans hb

end ProximityPrize.SubmissionLower.FinalFamilyAlgebra6815
