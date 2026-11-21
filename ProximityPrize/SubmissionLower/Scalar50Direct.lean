import ProximityPrize.SubmissionLower.CurveList179925Witness
import ProximityPrize.SubmissionLower.ScalarRootRows
import ProximityPrize.SubmissionLower.Scalar50LeadingPrice

set_option Elab.async false
namespace Scalar50Direct
open CJ0 CurveList179925Witness Polynomial
open private native_shape from ProximityPrize.SubmissionLower.CurveList179925Witness

/-- Count close scalar polynomials by applying the three-jet equation to the actual
degree-131071 messages and their actual agreement sets. -/
theorem of_lower (lower : ∀ w Γ s, Scalar50LeadingPrice.Messages w Γ s →
    ∀ g, Scalar50LeadingPrice.LowerRow g →
    (∀ γ ∈ Γ, K1_13.atJet g (K1_13.extend (s γ)) = 0) → Γ.card ≤ 2302614105857199) :
    ScalarList 179925 2302614105857199 := by
  classical
  have tail : SilentTail source 73 := by
    intro j hj hcut
    have hq : j.q ≤ 72 := (native_shape.support j hj).1
    omega
  have cert : RankCertificate 179925 source 130679 :=
    Or.inr ⟨73,le_rfl,tail,prefix_bound⟩
  apply ScalarRootRows.list_of_indexed (by decide)
  · rw [Sol1.C64.native_field_card]
    decide
  intro w Γ s hinj hclose
  obtain ⟨P,hP,hB,hJ,hweight,zero⟩ :=
    ScalarRootRows.exists_row source native_shape (by decide) surplus cert w
  have msg : Scalar50LeadingPrice.Messages w Γ s := by
    refine ⟨hinj,?_,?_⟩
    · intro γ hγ
      by_cases hz : s γ = 0
      · simp [hz]
      · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hz).mpr (hclose γ hγ).1)
    · intro γ hγ
      exact ⟨ReedSolomon.polynomialAgreementSet node w (s γ), (hclose γ hγ).2,
        fun _ hi => (Finset.mem_filter.mp hi).2⟩
  apply lower w Γ s msg P ⟨hP,hB,hJ,?_⟩ (fun γ hγ => zero _ (hclose γ hγ))
  intro m hm
  exact (hweight m hm).le.trans (by decide : source.m * 179925 ≤ Scalar50LeadingPrice.anchorCutoff)

#print axioms of_lower
end Scalar50Direct
