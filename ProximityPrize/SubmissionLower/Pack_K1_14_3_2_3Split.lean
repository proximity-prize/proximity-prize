import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2Split
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Aux3
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Fast044
set_option Elab.async false

section PackSource_K1_14_3_2_3Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000

namespace K1_14_3_2_3

noncomputable section

open K1_14 K1_14_3 K1_14_3_2
open scoped BigOperators

/-- Extend by the generic line slopes, change coordinates, and localize
at the nonzero polynomials in the slopes and the two cut coordinates. -/
def c1 : Prop :=
  ∀ s : Slice, PrimeTransport s

/-- Use contraction and the fate of principal primes to preserve properness. -/
def c2 : Prop :=
  ∀ s : Slice, PrimeTransport s → ∀ P Q : Jet,
    ProperPair P Q → PlaneProper (planeMap s P) (planeMap s Q)

private theorem mass_le (s : Slice) (P Q : Jet) (qs : Finset Surface)
    (hq : ComponentsOn P Q qs)
    (hprime : PrimeTransport s)
    (hfin : Module.Finite SectionField (PlaneQuotient (planeMap s P) (planeMap s Q))) :
    mass qs s ≤ (Module.finrank SectionField (PlaneQuotient (planeMap s P) (planeMap s Q)) : ℚ) := by
  classical
  unfold mass
  simp_rw [sectionLength_eq s (sliceMap_surjective s) (sliceMap_ker s)]
  rw [← Nat.cast_sum, Nat.cast_le]
  apply sum_le_colength s _ _ qs _ (fun q _ => hprime q) hfin
  intro q h
  rw [Ideal.span_insert, sup_le_iff]
  exact ⟨(Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ (hq q h).2.1),
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ (hq q h).2.2)⟩

theorem of_children (h1 : c1) (h2 : c2) :
    K1_14_3_2.c3 := by
  intro P Q hp hc hl qs hq
  have hbound (s : Slice) (N : ℕ)
      (hB : Module.Finite SectionField (PlaneQuotient (planeMap s P) (planeMap s Q)) ∧
        Module.finrank SectionField (PlaneQuotient (planeMap s P) (planeMap s Q)) ≤ N) :
      mass qs s ≤ (N : ℚ) :=
    (mass_le s P Q qs hq (h1 s) hB.1).trans (Nat.cast_le.mpr hB.2)
  have hproper (s : Slice) := h2 s (h1 s) P Q hp
  refine ⟨hbound .seed 2828 ?_, hbound .ordinate 60186 ?_,
    hbound .mixed 278957 ?_, hbound .jets 2360484 ?_⟩
  · exact capped_bound _ _ 63 14 118 24 (by decide) (by decide)
      (hproper .seed) (planeMap_caps .seed P _ hc) (planeMap_caps .seed Q _ hl)
  · exact box_bound _ _ 812 14 2907 24 (by decide) (by decide) (hproper .ordinate)
      (planeMap_caps .ordinate P _ hc) (planeMap_caps .ordinate Q _ hl)
  · exact box_bound _ _ 812 63 2907 118 (by decide) (by decide) (hproper .mixed)
      (planeMap_caps .mixed P _ hc) (planeMap_caps .mixed Q _ hl)
  · exact total_bound _ _ 812 2907 (by decide) (hproper .jets)
      (planeMap_caps .jets P _ hc) (planeMap_caps .jets Q _ hl)

end
end K1_14_3_2_3
end PackSource_K1_14_3_2_3Split
