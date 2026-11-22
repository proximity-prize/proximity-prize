import ProximityPrize.SubmissionLower.KoalaTwoCutMarks
import ProximityPrize.SubmissionLower.KoalaRectTaylorCutoff

set_option autoImplicit false

namespace SplitCut.TwoCut

open K1_14 (FX)
open P1 (K)
open HighCore82219Upper (Input ResidueLift Factors componentMarks mem_componentMarks)
open HighCore82219Upper_3 (JetRing)
open KoalaRectTaylor (cutoff_regularities mark_firstCut mark_secondCut)

theorem marked_cutoffs (J : Input) (B : ResidueLift J) (D : Factors J B) :
    MarkedCutoffs J B D := by
  obtain ⟨ht, hc⟩ := cutoff_regularities J B D
  refine ⟨ht, hc, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hm, hp⟩ := mem_componentMarks.mp hγ
    exact mark_firstCut J B D hm hp
  · intro γ hγ
    obtain ⟨hm, hp⟩ := mem_componentMarks.mp hγ
    exact mark_secondCut J B D hm hp

end SplitCut.TwoCut
