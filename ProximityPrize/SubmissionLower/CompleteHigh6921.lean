import ProximityPrize.SubmissionLower.HighMassBridge6921
import ProximityPrize.SubmissionLower.HighPrice6921
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace CompleteHigh6921
noncomputable section
open K21 H21 HighMassBridge6921

theorem of_producers (source : H21.c1) (bridge : H21.c2) (paired : H21.c3) : K21.c14 := by
  classical
  intro u del M Γ F lo hi
  obtain ⟨H,chart⟩ := adjacent_chart M F
  obtain ⟨rows,hr⟩ := source u del M Γ F lo hi H chart
  have covered : PrefixCover M F rows := by
    by_cases hh : M.overhead ≤ 3554
    · exact bridge u del M Γ F lo hh H chart rows hr
    · exact paired u del M Γ F (by omega) hi H chart rows hr
  rcases covered with cheap | ⟨kept,hsub,paid,f,hf,hd,roots⟩
  · exact cheap.trans (Nat.le_add_right _ _)
  let b := HighMassBridge6921.choose M.overhead
  obtain ⟨hl,hu⟩ := bounds lo hi
  have low : (b.lower : ℤ) ≤ M.overhead := by dsimp [b]; omega
  have high : M.overhead ≤ (b.upper : ℤ) := by dsimp [b]; omega
  have word : HighPrice6921.FixedWord M.word kept F.scalar (131071+b.upper) := by
    refine ⟨F.distinct.mono hsub, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hsub hγ)).scalar_degree with hz | ht
      · simp [hz]
      · omega
    · intro γ hγ
      let mark := F.mark γ (hsub hγ)
      exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
  have label : Set.InjOn M.label (kept : Set K) := fun _ _ _ _ h => sub_left_inj.mp h
  have seedBound := seed hr lo hi f hf hd
  have he : f.natDegree ≤ b.ordinateCap := (cap_eq _).symm ▸ hf.2.1
  have price := HighPrice6921.retained_count b low high word label hf.1 hf.2.2.1 hf.2.2.2 he seedBound roots
  have partition := Finset.card_sdiff_add_card_eq_card hsub
  omega

end
end CompleteHigh6921
