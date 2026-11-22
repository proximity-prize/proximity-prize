import ProximityPrize.SubmissionLower.Final50FatBanks
import ProximityPrize.SubmissionLower.Final50FatFactors
import ProximityPrize.SubmissionLower.Final50FatContacts
import ProximityPrize.SubmissionLower.Final50FatEliminate

set_option Elab.async true

section
namespace Final50Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
open private eval_cleared order_cleared from ProximityPrize.SubmissionLower.GoldBranch6N4
set_option maxRecDepth 2400 in
/-- Equations for all pole families through height 2,390 at 179,895 agreements. -/
theorem fat_equations : Equations := by
  have h1 := Final50FatBanks.proof
  have h2 := Final50FatFactors.proof
  have h3 := Final50FatContacts.proof
  intro w Γ s _ hhits P hheight
  have hw : Messages w Γ s := ⟨hhits⟩
  obtain ⟨L⟩ := K1_13_4_1.proof Γ s P
  obtain ⟨⟨F, neF, hF⟩, rank2⟩ := h1 w Γ s P L hheight
  obtain ⟨vanishes1, vanishes2⟩ := h3 w Γ s hw P L hheight
  obtain ⟨G, hG, ⟨D⟩⟩ := h2 w Γ s P L F neF hF.1 rank2
  have hOrders : ∀ γ ∈ Γ, PairOrders (toGeneric F) (toGeneric G)
      (inclConst (P.z γ)) (trajectory (extend (s γ))) := fun γ hγ =>
    ⟨vanishes1 F hF γ hγ, vanishes2 G hG γ hγ⟩
  obtain ⟨book, Q, hcard, hQ, htQ, hiQ, hcover⟩ :=
    eliminate_common Γ P.z (fun γ => extend (s γ)) P.injective D hOrders
  obtain ⟨J⟩ := K1_13_4_6.proof D.left D.right D.left_ne D.right_ne D.proper D.left_caps D.right_caps
  let R := seedResultant (pad D.left J.a) (pad D.right J.b)
  obtain ⟨_, Q', _, suppQ, mapQ⟩ := clear_denominators Q
  obtain ⟨_, R', _, suppR, mapR⟩ := clear_denominators R
  have neQ : Q' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppQ
    exact hQ suppQ
  have neR : R' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppR
    exact J.nonzero suppR
  have totalQ : Q'.totalDegree ≤ 6245 := by
    simpa only [MvPolynomial.totalDegree, suppQ] using htQ
  have indexQ : indexDegree Q' ≤ 2022 := by
    simpa only [K1_13.indexDegree, lowerIndex, suppQ] using hiQ
  have totalR : R'.totalDegree ≤ 0x38c7faf0 := by
    have htR : R.totalDegree ≤ 0x38c7faf0 := J.total
    simpa only [MvPolynomial.totalDegree, suppR] using htR
  have indexR : indexDegree R' ≤ 0x13315480 := by
    have hiR : lowerIndex R ≤ 0x13315480 := J.index
    simpa only [K1_13.indexDegree, lowerIndex, suppR] using hiR
  refine ⟨book, ⟨Q', R', neQ, neR, totalQ, indexQ, totalR, indexR⟩, hcard, ?_⟩
  intro γ hγ hb
  rcases hcover γ hγ hb with he | ho
  · exact Or.inl (eval_cleared mapQ _ he)
  · refine Or.inr (order_cleared mapR _ ?_)
    have hres : LowerOrder R (trajectory (extend (s γ))) 51281 :=
      resultant_order (pad D.left J.a) (pad D.right J.b) (inclConst (P.z γ)) _
        J.degree_left.le J.degree_right.le ⟨mixedOrder_pad J.a ho.1, mixedOrder_pad J.b ho.2⟩
    exact hres
end
end Final50Fat
end
