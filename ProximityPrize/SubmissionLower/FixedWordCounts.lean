/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.FixedWordAnchors
import ProximityPrize.SubmissionLower.NormalizedSeedCount

namespace ProximityPrize.SubmissionLower.FixedWordAnchors
open ProximityPrize.Benchmark Koala6844Normalization
open scoped Classical
noncomputable section
set_option autoImplicit false
variable {I : Type} [DecidableEq I] {x : I ↪ IRSProfile.Field} {nodes : Finset I}
variable {σ : IRSProfile.Field ≃+* IRSProfile.Field} {excess : ℕ}

/-- At 81,193 errors any family above the stated list bound admits two coprime
pole constraints and has positive overhead beyond the appropriate list profile. -/
theorem at_81193 (data : CenteredVirtualData x nodes σ 131071 180951 81193 excess)
    (points_fixed : ∀ i ∈ nodes, σ (x i) = x i) (nodeCap : nodes.card ≤ 262144) :
    data.seeds.card ≤ 53000000000000 ∨
      ∃ m : Model data,
        m.carrier.natDegree + affineDegree data.A0 + 120 < m.pole.natDegree ∧
        (nodes.card ≤ 256357 → m.carrier.natDegree + affineDegree data.A0 + 2500 < m.pole.natDegree) ∧
        (nodes.card ≤ 246652 → m.carrier.natDegree + affineDegree data.A0 + 6689 < m.pole.natDegree) := by
  classical
  by_cases hsmall : data.seeds.card ≤ 53000000000000
  · exact Or.inl hsmall
  obtain ⟨m⟩ := exists_model data points_fixed (by omega)
  have hn : 180951 ≤ nodes.card :=
    (data.normalized_agreements 0 data.zero_mem).trans (Finset.card_filter_le _ _)
  have force (d : ℕ) (fit : NormalizedLists.ListBound nodes.card (131071+d) 180951 53000000000000) :
      m.carrier.natDegree + affineDegree data.A0 + d < m.pole.natDegree := by
    by_contra! h
    apply hsmall
    apply NormalizedContent.count_words data m.words m.received m.injective _ m.agreements fit
    intro g hg
    have deg := m.degree g hg
    have bal := m.degree_balance
    omega
  exact Or.inr ⟨m,force 120 (NormalizedLists.dense _ hn nodeCap),
    fun cap => force 2500 (NormalizedLists.intermediate _ hn cap),
    fun cap => force 6689 (NormalizedLists.sparse _ hn cap)⟩

#print axioms at_81193
end
end ProximityPrize.SubmissionLower.FixedWordAnchors
