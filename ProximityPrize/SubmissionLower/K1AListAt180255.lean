import ProximityPrize.SubmissionLower.Pack_K1DefsAt180255
import ProximityPrize.SubmissionLower.WeightedListAt180255
set_option Elab.async false

/-! `K1A.c0` at A = 180255: the official `K1.anchored_list_count` (Pack_K1Defs.lean:441)
re-run on the ported anchor definitions and the ported weighted list theorem
(`Astra7A.native_weighted_complete_list`, agreement 180255, cap 31924061854636696). UNBUILT. -/

section PackSource_K1AListAt180255
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K1A
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark

theorem anchored_list_count {u deleted} (M : AnchorModel u deleted) (Γ : Finset K)
    (F : AnchoredFamily M Γ) (hw : M.overhead ≤ 0) :
    Γ.card ≤ Astra7A.weightedListCap := by
  classical
  obtain ⟨hfinite, hprice⟩ := Astra7A.native_weighted_complete_list M.word
  have hsub : Γ.image F.scalar ⊆ hfinite.toFinset := by
    intro P hP
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hP
    have mark := F.mark γ hγ
    apply hfinite.mem_toFinset.mpr
    constructor
    · rcases mark.scalar_degree with hz | hd
      · rw [hz, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe (131073 : ℕ)
      · have hn : (F.scalar γ).natDegree < 131073 := by omega
        exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hn)
    · apply mark.bad.agreement.trans
      apply Finset.card_le_card
      intro i hi
      simp only [ReedSolomon.polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact mark.scalar_hits i hi
  calc
    Γ.card = (Γ.image F.scalar).card := (Finset.card_image_of_injOn F.distinct).symm
    _ ≤ hfinite.toFinset.card := Finset.card_le_card hsub
    _ = _ := (Set.ncard_eq_toFinset_card _ hfinite).symm
    _ ≤ Astra7A.weightedListCap := hprice

/-- The first child obligation of the ported K1 interface is discharged for every budget whose
list entry is at least the ported weighted list cap. -/
theorem c0_of_list (Bg : Budget) (h : Astra7A.weightedListCap ≤ Bg.list) : c0 Bg :=
  fun _ _ M Γ F hw => (anchored_list_count M Γ F hw).trans h

theorem weightedListCap_value : Astra7A.weightedListCap = 31924061854636696 := rfl

end
end K1A
end PackSource_K1AListAt180255
