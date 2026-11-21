import ProximityPrize.SubmissionLower.KoalaTwoCutMarks
import ProximityPrize.SubmissionLower.KoalaRectTaylorCutoff

set_option autoImplicit false

namespace SplitCut.TwoCut

open K1_14 (FX)
open P1 (K)
open HighCore82229Upper (Input ResidueLift Factors componentMarks mem_componentMarks)
open HighCore82229Upper_3 (JetRing)
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

theorem marked_first_zeroLocus (J : Input) (B : ResidueLift J) (D : Factors J B)
    (v w : ℕ) {γ : K} (hγ : γ ∈ componentMarks J D.proper) :
    point J v w γ ∈ MvPolynomial.zeroLocus FX ((firstIdeal J B D).comap (projectJet J v w)) :=
  (mark_on_iff J v w γ _).mpr (proper_first_mark (marked_cutoffs J B D) hγ)

theorem marked_second_zeroLocus (J : Input) (B : ResidueLift J) (D : Factors J B)
    (v w : ℕ) {γ : K} (hγ : γ ∈ componentMarks J D.proper) {Q : Ideal JetRing}
    (hQ : point J v w γ ∈ MvPolynomial.zeroLocus FX (Q.comap (projectJet J v w))) :
    point J v w γ ∈ MvPolynomial.zeroLocus FX
      ((Q ⊔ Ideal.span {second J B}).comap (projectJet J v w)) := by
  apply (mark_on_iff J v w γ _).mpr
  refine sup_le ((mark_on_iff J v w γ Q).mp hQ) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  exact RingHom.mem_ker.mpr ((marked_cutoffs J B D).second_zero γ hγ)

end SplitCut.TwoCut

#print axioms SplitCut.TwoCut.marked_cutoffs
#print axioms SplitCut.TwoCut.marked_first_zeroLocus
#print axioms SplitCut.TwoCut.marked_second_zeroLocus
