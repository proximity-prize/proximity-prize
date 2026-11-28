import ProximityPrize.SubmissionLower.Z6970ExpandedMomentData

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace ExpandedColumns6970
open K1_13 (Geom)

private theorem evaluateExact (A D C : ℕ) (x y z : ℤ)
    (hm : (x,y,z) = (427286700047,1015009542543574,12678308899820400))
    (h : 24*(C : ℤ) = 24*(3000*(A : ℤ))*x - (24*(D : ℤ))*y + z) :
    C = 3000*A*427286700047 + 528262870825850 - D*1015009542543574 := by
  obtain ⟨hx,hyz⟩ := Prod.mk.inj hm
  obtain ⟨hy,hz⟩ := Prod.mk.inj hyz
  rw [hx,hy,hz] at h
  omega

theorem exact_finrank (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4024 ≤ 3000*A) :
    Module.finrank Geom (Source A D) =
      3000*A*427286700047 + 528262870825850 - D*1015009542543574 := by
  rw [finrank_source A D hD]
  exact evaluateExact A D (columns A D hD).card sourceCount sourceDegree sourceIndex24
    exact_moments (scaled_columns A D hA hD hBudget)

end ExpandedColumns6970
