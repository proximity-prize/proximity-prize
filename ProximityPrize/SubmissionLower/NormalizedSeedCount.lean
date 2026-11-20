/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.NormalizedProfiles
import ProximityPrize.SubmissionLower.NormalizedContent

namespace ProximityPrize.SubmissionLower.NormalizedContent
open ProximityPrize.Benchmark ReedSolomon Koala6844Normalization
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
variable {I : Type} [DecidableEq I] {x : I ↪ IRSProfile.Field} {nodes : Finset I}
variable {σ : IRSProfile.Field ≃+* IRSProfile.Field} {w A errors excess : ℕ}

/-- Reindex an injective polynomial family on its actual evaluation domain. -/
theorem count_words (data : CenteredVirtualData x nodes σ w A errors excess)
    (words : IRSProfile.Field → Polynomial IRSProfile.Field) (received : I → IRSProfile.Field)
    (injective : Set.InjOn words (↑data.seeds : Set IRSProfile.Field)) {D limit : ℕ}
    (degree : ∀ g ∈ data.seeds, (words g).natDegree ≤ D)
    (agreement : ∀ g ∈ data.seeds, A ≤ (nodes.filter fun i => (words g).eval (x i) = received i).card)
    (bound : NormalizedLists.ListBound nodes.card D A limit) : data.seeds.card ≤ limit := by
  classical
  let e := nodes.equivFin
  let domain : Fin nodes.card ↪ IRSProfile.Field :=
    ⟨fun i => x (e.symm i).val, x.injective.comp (Subtype.val_injective.comp e.symm.injective)⟩
  let symbols (i : Fin nodes.card) := received (e.symm i)
  let S := data.seeds.image words
  have counted := bound domain symbols S (by
    intro P hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
    exact degree g hg) (by
    intro P hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
    let old := nodes.filter fun i => (words g).eval (x i) = received i
    let new := polynomialAgreementSet domain symbols (words g)
    let send (i : ↥old) : ↥new :=
      ⟨e ⟨i.val, (Finset.mem_filter.mp i.property).1⟩, by
        apply (mem_polynomialAgreementSet domain symbols (words g) _).mpr
        simpa only [domain, symbols, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply] using
          (Finset.mem_filter.mp i.property).2⟩
    have hs : Function.Injective send := by
      intro i j hij
      have h := congrArg Subtype.val hij
      exact Subtype.ext (congrArg (fun k : ↥nodes => (k : I)) (e.injective h))
    apply (agreement g hg).trans
    have inequality : old.card ≤ new.card := by
      simpa only [Fintype.card_coe] using (Fintype.card_le_of_injective send hs)
    convert inequality using 1
    congr 2)
  rwa [show S.card = data.seeds.card from Finset.card_image_of_injOn injective] at counted

theorem count_on_nodes (data : CenteredVirtualData x nodes σ w A errors excess) {D limit : ℕ}
    (hdegree : w + overlap data - affineDegree data.A0 ≤ D)
    (bound : NormalizedLists.ListBound nodes.card D A limit) : data.seeds.card ≤ limit := by
  classical
  obtain ⟨words, received, injective, degree, agreement⟩ := reduce data
  exact count_words data words received injective (fun g hg => (degree g hg).trans hdegree) agreement bound

/-- Each case gives a list bound below the active seed allowance at 81,193 errors. -/
theorem at_81193
    (data : CenteredVirtualData x nodes σ 131071 180951 81193 excess)
    (nodeCap : nodes.card ≤ 262144)
    (covered : overlap data ≤ affineDegree data.A0 + 120 ∨
      nodes.card ≤ 256357 ∧ overlap data ≤ affineDegree data.A0 + 2500 ∨
      nodes.card ≤ 246652 ∧ overlap data ≤ affineDegree data.A0 + 6689) :
    data.seeds.card ≤ 53000000000000 := by
  have hn : 180951 ≤ nodes.card :=
    (data.normalized_agreements 0 data.zero_mem).trans (Finset.card_filter_le _ _)
  rcases covered with small | ⟨mid, hmid⟩ | ⟨few, hlast⟩
  · exact count_on_nodes data (by omega) (NormalizedLists.dense _ hn nodeCap)
  · exact count_on_nodes data (by omega) (NormalizedLists.intermediate _ hn mid)
  · exact count_on_nodes data (by omega) (NormalizedLists.sparse _ hn few)

#print axioms at_81193
end
end ProximityPrize.SubmissionLower.NormalizedContent
