import ProximityPrize.SubmissionLower.CurveListFacet30Aux82229Rank
import ProximityPrize.SubmissionLower.ScalarRootRows
import ProximityPrize.SubmissionLower.Scalar50LeadingPrice

set_option Elab.async false
namespace Scalar50Direct
open CJ0 CurveListFacet30AuxRank

private theorem surplus : Surplus 179915 support 136577 := by
  obtain ⟨hcount, hgrade, hindex⟩ := moments
  unfold Surplus
  rw [hcount, hgrade, hindex]
  decide +kernel

/-- Count close scalar polynomials by applying the three-jet equation to the actual
degree-131071 messages and their actual agreement sets. -/
theorem of_lower (lower : ∀ w Γ s, Scalar50LeadingPrice.Messages w Γ s →
    ∀ g, Scalar50LeadingPrice.LowerRow g →
    (∀ γ ∈ Γ, K1_13.atJet g (K1_13.extend (s γ)) = 0) → Γ.card ≤ 2493026848761586) :
    ScalarList 179915 2493026848761586 := by
  classical
  have tail : SilentTail support 73 := by
    intro j hj hcut
    have hq : j.q ≤ 72 := (shapeOK.support j hj).1
    omega
  have cert : RankCertificate 179915 support 136577 :=
    Or.inr ⟨73,le_rfl,tail,prefix_bound_82229⟩
  apply ScalarRootRows.list_of_indexed (by decide)
  · rw [Sol1.C64.native_field_card]
    decide
  intro w Γ s hinj hclose
  obtain ⟨P,hP,hB,hJ,hC,hweight,zero⟩ :=
    ScalarRootRows.exists_row_with_top support shapeOK (by decide) surplus cert w
  have msg : Scalar50LeadingPrice.Messages w Γ s := by
    exact ⟨hinj, fun γ hγ => (ScalarRootRows.close_data (hclose γ hγ)).1,
      fun γ hγ => (ScalarRootRows.close_data (hclose γ hγ)).2⟩
  apply lower w Γ s msg P ⟨hP,hB,hJ,hC,?_⟩ (fun γ hγ => zero _ (hclose γ hγ))
  intro m hm
  exact (hweight m hm).le.trans (by decide : support.m * 179915 ≤ Scalar50LeadingPrice.anchorCutoff)

#print axioms of_lower
end Scalar50Direct
