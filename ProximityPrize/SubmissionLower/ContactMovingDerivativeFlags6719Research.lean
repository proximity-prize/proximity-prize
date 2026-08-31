import ProximityPrize.SubmissionLower.ContactMovingAgreementCertificate6719Research
namespace ProximityPrize.SubmissionLower.ContactMovingDerivativeFlags6719Research
open scoped Classical
open ContactMovingAgreementCertificate6719Research
open ContactGenericSurface ContactTaylorNumerators ContactFlagBezout6543Research
open ContactPost6464MinkowskiRecurrenceResearch ContactIdentityResidualGlobalFlagResearch
open ContactBaseIdealWeights6676Research ContactBaseIdealAlgebra6676Research
noncomputable section
set_option maxHeartbeats 3000000
variable {K Ω:Type} [Field K] [Field Ω]
private theorem mapped_flag (φ:Polynomial K →+*Ω)
    (Q:MvPolynomial (Fin 4) K) (a b s:ℕ)
    (hR:wt residualSWeights Q ≤ s)
    (hM:wt residualYSWeights Q ≤ b+s)
    (hT:wt residualTotalWeights Q ≤ a+b+s):
    PolynomialInFlag ⟨a,b,s⟩ (surfaceMap φ Q):=by
  intro e he
  obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
  have hr:=(MvPolynomial.le_weightedTotalDegree residualSWeights hq).trans hR
  have hm:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hM
  have ht:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hT
  simp [ContactFactorCaps.weight_fin4,residualSWeights] at hr
  simp [ContactFactorCaps.weight_fin4,residualYSWeights] at hm
  simp [ContactFactorCaps.weight_fin4,residualTotalWeights] at ht
  exact ⟨hr,hm,ht⟩
private theorem G_weight (w:Fin 4 → ℕ) (t:ℕ)
    (h0:w 0=0) (h1:w 1=t) (h2:w 2=1) (ht:t≤1)
    (F:MvPolynomial (Fin 4) K) (C:ℕ)
    (hC:1≤C) (hF:wt w F≤C):wt w (polyG K F)≤C+1-t:=by
  have hf:WeightBound w F (C:ℤ):=Or.inr (by exact_mod_cast hF)
  have hg:WeightBound w (polyG K F) ((C:ℤ)+1-t):=by
    simpa only [polyG,horizontalDerivation,Derivation.add_apply,
      Derivation.smul_apply,smul_eq_mul] using (hf.horizontal t h0 h1 h2 ht).neg
  rcases hg with hz | hb
  · simp [hz,wt,MvPolynomial.weightedTotalDegree]
  · have htc:t≤C+1:=by omega
    have hb':(wt w (polyG K F):ℤ) ≤ ((C+1-t:ℕ):ℤ):=by
      rw [Nat.cast_sub htc]
      push_cast
      exact hb
    exact_mod_cast hb'
theorem surfaceMap_HG_flags (φ:Polynomial K →+*Ω)
    (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
    (hR:F.degreeOf 2 ≤ s+2)
    (hYR:wt ![0,1,1,0] F ≤ b+s+3)
    (hAll:wt ![0,1,1,1] F ≤ a+b+s+3):
    PolynomialInFlag ⟨a,b+1,s+1⟩ (surfaceMap φ (polyH K F))∧
    PolynomialInFlag ⟨a,b,s+3⟩ (surfaceMap φ (polyG K F)):=by
  have hS:=support_data a b s F hR hYR hAll
  have hr:=hS.s_weight
  have hm:=hS.ys_weight
  have ha:=hS.total_weight
  change wt residualSWeights F≤s+2 at hr
  change wt residualYSWeights F≤b+s+3 at hm
  change wt residualTotalWeights F≤a+b+s+3 at ha
  constructor
  · apply mapped_flag φ (polyH K F) a (b+1) (s+1)
    · simpa [residualSWeights] using wt_polyH_le residualSWeights F (s+2) hr
    · have h:=wt_polyH_le residualYSWeights F (b+s+3) hm
      change wt residualYSWeights (polyH K F) ≤ b+s+3-1 at h
      omega
    · have h:=wt_polyH_le residualTotalWeights F (a+b+s+3) ha
      change wt residualTotalWeights (polyH K F) ≤ a+b+s+3-1 at h
      omega
  · apply mapped_flag φ (polyG K F) a b (s+3)
    · simpa using G_weight residualSWeights 0 rfl rfl rfl (by omega) F
        (s+2) (by omega) hr
    · simpa [Nat.add_assoc] using G_weight residualYSWeights 1 rfl rfl rfl (by omega) F
        (b+s+3) (by omega) hm
    · have h:=G_weight residualTotalWeights 1 rfl rfl rfl (by omega) F
        (a+b+s+3) (by omega) ha
      omega
end
end ProximityPrize.SubmissionLower.ContactMovingDerivativeFlags6719Research
