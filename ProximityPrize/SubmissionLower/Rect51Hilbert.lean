import ProximityPrize.SubmissionLower.Rect51HilbertCore
import ProximityPrize.SubmissionLower.Rect51HilbertAmbient
import ProximityPrize.SubmissionLower.Rect51HilbertLift

set_option autoImplicit false
set_option Elab.async false

namespace Rect51Hilbert
noncomputable section

open HighCore82706Tangent_3 (JetRing)
open Rect51Tangent (Axes Section)

theorem cut_gap {Q R : Ideal JetRing} {h t : ℕ} {v : Axes}
    (S : Section Q h t v) (hQR : Q ≤ R) (hmem : S.affine ∈ R)
    (hreg : IsLeftRegular (Ideal.Quotient.mk Q S.affine))
    {p q : HilbertPoly} (hp : IsProfile Q p) (hq : IsProfile R q) :
    NonnegativeTop (difference p ![h,t,v 0,v 1] - q) := by
  obtain ⟨A, hA, eA⟩ := lift S.affine_bound S.affine_weight
  obtain ⟨B, hB, eB⟩ := lift S.inverse_bound S.inverse_weight
  have eq : nefDegree h t (v 0) (v 1) + S.order • (1,0,0,0) =
      (h+2*t+S.order,t,v 0,v 1) := by
    simp [nefDegree, Prod.mk_add_mk, Prod.smul_mk]
  let T : CoxSection Q (nefDegree h t (v 0) (v 1)) :=
    ⟨S.order, A, B, by rw [eq]; exact hA, by rw [eq]; exact hB, by rw [eA, eB]; exact S.glue⟩
  have he : T.affine = S.affine := eA
  exact cut_gap_cox T hQR (by rw [he]; exact hmem) (by rw [he]; exact hreg) hp hq

#print axioms cut_gap

end
end Rect51Hilbert
