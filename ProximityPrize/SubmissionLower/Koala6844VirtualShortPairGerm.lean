import ProximityPrize.SubmissionLower.Koala6844VirtualShortDirectGerm
import ProximityPrize.SubmissionLower.Koala6844VirtualShortResultant


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial Koala6844Normalization RCN156 RCN234
open scoped Classical

noncomputable section
set_option autoImplicit false

variable {K E I : Type} [Field K] [Field E] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

theorem coprime_pair_card_le_germ
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (germ : ActiveResultantGerm D embed)
    (p : ℕ) (σpow : ∀ g ∈ D.seeds, embed (σ g) = (embed g)^p)
    (F G : MvPolynomial (Fin 4) K) (irrF : Irreducible F) (hr : 0 < F.degreeOf 2)
    (proper : ¬ F ∣ G)
    (r y t s z h : ℕ) (fr : F.degreeOf 2 ≤ r) (gr : G.degreeOf 2 ≤ s)
    (fy : wt residualYSWeights F ≤ y) (gy : wt residualYSWeights G ≤ z)
    (ft : wt residualTotalWeights F ≤ t) (gt : wt residualTotalWeights G ≤ h)
    (ory : r ≤ y) (oyt : y ≤ t) (osz : s ≤ z) (ozh : z ≤ h)
    (digit : s*t+r*h-r*s < p)
    (S : Finset K) (hS : S ⊆ D.seeds)
    (hf : ∀ g ∈ S, RCN319.specialization K (D.selected g) g F = 0)
    (hg : ∀ g ∈ S, RCN319.specialization K (D.selected g) g G = 0) :
    S.card ≤ (s*t+r*h-r*s) + p*(s*y+r*z-r*s) := by
  obtain ⟨J,hJ,hJY,hJT,hJroot⟩ :=
    exists_weighted_R_resultant F G irrF hr proper y z t h fy gy ft gt
  exact direct_germ_card_le D embed germ p (s*y+r*z-r*s) (s*t+r*h-r*s) digit σpow
    J hJ (hJY.trans (resultant_cap_mono _ _ r s y z fr gr ory osz))
    (hJT.trans (resultant_cap_mono _ _ r s t h fr gr (ory.trans oyt) (osz.trans ozh)))
    S hS (fun g gS => hJroot (D.selected g) g (hf g gS) (hg g gS))

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
