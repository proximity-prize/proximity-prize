import ProximityPrize.SubmissionLower.H2429AffineResidue
import ProximityPrize.SubmissionLower.H2429NormalCount

set_option Elab.async false
set_option autoImplicit false

namespace H2429Minimum

theorem count {u del Γ}
    (M : Front82706.AnchorModel u del) (F : P1.FamilyAt 179876 M Γ)
    (h : M.overhead = 2429) (hE : M.E.natDegree = 2429) :
    Γ.card ≤ Front6955On6960.coreBudget := by
  classical
  obtain ⟨labels,v,N,G,hinj,shift,eqE,_,factor,first,second,_,hN,_⟩ :=
    H2429AffineResidue.normalize M F h hE
  let U := Γ.image labels
  let T := U.erase N.shift
  have hsub : T ⊆ U := Finset.erase_subset _ _
  let G' : P1.FamilyAt 179876 N T :=
    ⟨G.scalar,fun γ hγ => G.mark γ (hsub hγ),G.distinct.mono hsub⟩
  have pole : N.E.natDegree = 2429 := by rw [eqE,hE]
  obtain ⟨D,R,_,_,hoff,hdeg,_,hmem⟩ := MinimumPoleTwoBlockFrame.two_blocks N G' pole hN
    (by decide) (by decide) shift factor first second
  have height : FrontCore82258.effectiveHeight N = 2429 := by
    rw [FrontCore82258.effectiveHeight,hN,pole] <;> decide
  have hc := H2429NormalCount.count N G' height (Finset.notMem_erase _ _) ⟨D,R,hoff,hdeg,hmem⟩
  have hcard : U.card = Γ.card := Finset.card_image_of_injOn hinj
  have hm : U.card - 1 ≤ T.card := Finset.pred_card_le_card_erase
  change T.card+1 ≤ Front6955On6960.coreBudget at hc
  omega

end H2429Minimum
