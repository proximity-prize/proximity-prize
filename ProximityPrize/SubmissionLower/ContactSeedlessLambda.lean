import ProximityPrize.SubmissionLower.ContactSeedlessListBound
import ProximityPrize.SubmissionLower.AlignmentInterleavedLambda

namespace ProximityPrize.SubmissionLower.ContactSeedlessLambda

open scoped Classical NNReal
open ProximityPrize.Benchmark
open ContactSeedlessInterpolation ContactSeedlessListBound
open AlignmentMomentCurveProjection AlignmentInterleavedLambda
open ContactTranslation

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

theorem squared_eight_lambda_le_of_interleaved_list
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (e B : ℕ)
    (hfinite : ∀ (received : ι → Fin 16 → F)
        (L : Finset (ι → Fin 16 → F)),
      (∀ v ∈ L, ∀ j : Fin 16, (fun i => v i j) ∈ C) →
      (∀ v ∈ L, Fintype.card ι - e ≤
        (Finset.univ.filter (fun i => v i = received i)).card) →
      L.card ≤ B)
    (delta : ℝ)
    (hcell : delta * (Fintype.card ι : ℝ) < ((e + 1 : ℕ) : ℝ)) :
    Code.Lambda
      (((C ^⋈ (Fin 8)) ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → Fin 8 → F)) :
        Set (ι → Fin 2 → Fin 8 → F)) delta ≤ (B : ℕ∞) := by
  classical
  letI : DecidableEq (ι → Fin 2 → Fin 8 → F) := Classical.decEq _
  letI : DecidableEq (ι → Fin 16 → F) := Classical.decEq _
  apply Code.Lambda_le_of_forall_finset_card_le
  intro received L hL
  let projected : Finset (ι → Fin 16 → F) := L.image flattenWord
  have hinj : Set.InjOn flattenWord (L : Set (ι → Fin 2 → Fin 8 → F)) :=
    fun _ _ _ _ hh => flattenWord_injective hh
  have hcard : projected.card = L.card := Finset.card_image_of_injOn hinj
  have hrows : ∀ v ∈ projected, ∀ j : Fin 16, (fun i => v i j) ∈ C := by
    intro v hv j
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    have hcode := (Code.mem_closeCodewordsRel_iff.mp (hL c hc)).1
    change (fun i => c i (sixteenIndexEquiv.symm j).1
      (sixteenIndexEquiv.symm j).2) ∈ C
    exact squared_eight_rows C c hcode _ _
  have hclose : ∀ v ∈ projected, Fintype.card ι - e ≤
      (Finset.univ.filter (fun i => v i = flattenWord received i)).card := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    rw [flattenWord_agreement_card]
    exact agreement_card_ge_of_closeCodewordsRel _ received c delta e hcell (hL c hc)
  have hbound := hfinite (flattenWord received) projected hrows hclose
  rwa [hcard] at hbound

end

end ProximityPrize.SubmissionLower.ContactSeedlessLambda
