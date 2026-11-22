import ProximityPrize.SubmissionLower.CurveList179876
import ProximityPrize.SubmissionLower.ScalarRootRows
import ProximityPrize.SubmissionLower.Scalar55RefinedCount

set_option Elab.async false
namespace Scalar55RefinedList
open CJ0 CurveList179876 Polynomial
open private native_shape from ProximityPrize.SubmissionLower.CurveList179876

/-- Count all close native messages using the same interpolation equation on their
actual agreement sets. The highest jet keeps the bound from the native source. -/
theorem scalar_list : ScalarList 179876 2325506586623926 := by
  classical
  have tail : SilentTail source 76 := by
    intro j hj hcut
    have hq : j.q ≤ 75 := (native_shape.support j hj).1
    omega
  have cert : RankCertificate 179876 source 151799 := Or.inr ⟨76, le_rfl, tail, prefix_bound⟩
  apply ScalarRootRows.list_of_indexed (by decide)
  · rw [Sol1.C64.native_field_card]
    decide
  intro w Γ s hinj hclose
  obtain ⟨P,hP,hB,hJ,hTop,hweight,zero⟩ :=
    ScalarRootRows.exists_row_with_top source native_shape (by decide) surplus cert w
  have msg : Scalar55LeadingPrice.Messages w Γ s :=
    ⟨hinj, fun γ hγ => (ScalarRootRows.close_data (hclose γ hγ)).1,
      fun γ hγ => (ScalarRootRows.close_data (hclose γ hγ)).2⟩
  apply Scalar55RefinedCount.lower_count msg P ⟨hP,hB,hJ,hTop,?_⟩ (fun γ hγ => zero _ (hclose γ hγ))
  intro m hm
  exact (Nat.le_sub_one_of_lt (hweight m hm)).trans
    (by decide : source.m * 179876 - 1 ≤ Scalar55LeadingPrice.anchorCutoff)

#print axioms scalar_list
end Scalar55RefinedList
