import ProximityPrize.SubmissionLower.MovingSourceIdentityFirstCharge6814
namespace ProximityPrize.SubmissionLower.MovingSourceUniformTail6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 20000
open RCN074 RCN086 RCN095 RCN135 RCN136 RCN244 RCN313
open MovingSourceDenominatorSeeds6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p errorCap : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {stageSupport : RCN275.ResidualSupportParameters}

theorem geometric_tail_dvd_iff_original
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hF : Irreducible S.F) (n : ℕ) :
    S.G∣globalTailCut (polynomialEmbedding K) S.F n ↔ S.F∣numerator K S.F n := by
  rw [globalTailCut_dvd_iff (polynomialEmbedding K) (polynomialEmbedding_injective K)]
  constructor
  · intro hG
    by_contra hnot
    have hrel := surfaceMap_relPrime S.F (numerator K S.F n) hF.ne_zero
      (hF.isRelPrime_iff_not_dvd.mpr hnot)
    exact S.irreducible_G.not_isUnit (hrel S.G_dvd_surface hG)
  · intro hdiv
    exact S.G_dvd_surface.trans (map_dvd (surfaceMap (polynomialEmbedding K)) hdiv)

end
end ProximityPrize.SubmissionLower.MovingSourceUniformTail6814
