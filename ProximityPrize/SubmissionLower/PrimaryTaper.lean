import ProximityPrize.SubmissionLower.PrimaryTaperFamily
import ProximityPrize.SubmissionLower.PrimaryTaperRankData

set_option Elab.async false

namespace PrimaryTaper

open K1_13 (Geom Row shape InBox Contact)
open P3 (I K)

theorem primary_family (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4012 ≤ 3000*A)
    (w : I → K) {n : ℕ} (hn : n ≤ sourceRank A D) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE D (e i) (3000*A-1) ∧
        JetsBounded (e i) ∧ Contact w (e i) :=
  primary_family_of_local TaperBudget.tapered_rank A D hA hD hBudget w hn

#print axioms primary_family
end PrimaryTaper
