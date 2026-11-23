-- Ported from public PR657, e07f14a81dfe2cf1bda985e67040ad4d31fe81ab, Pr657High6955.lean.
import ProximityPrize.SubmissionLower.FrontCore82258Model

set_option autoImplicit false

namespace Pr657High6955

def Count : Prop :=
  ∀ {u : P1.Words} {del : Finset P1.I} {Γ : Finset P1.K}
    (M : P1.ModelAt 34339 u del), P1.FamilyAt 179876 M Γ →
      (2431:ℤ)≤M.overhead→M.overhead≤2695 →
      Γ.card≤273002714226794744

end Pr657High6955
