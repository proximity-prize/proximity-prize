import ProximityPrize.SubmissionLower.MovingSourceFrameZeroCount6814

/-! Actual seed vanishing and proper-delay transport. Seed vanishing does
not require Hnew nonzero at the seed. A component lying in Hnew=0 is a
separate exception; no point on the other components is discarded. -/
namespace ProximityPrize.SubmissionLower.MovingSourceReducedSeedTails6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open RCN002 RCN135 RCN136 RCN074 RCN086 RCN095 RCN238 RCN243 RCN244 RCN264 RCN313 RCN330
open MovingSourceFlowNumerator6814 MovingSourceLinearTailTransport6814
open MovingSourceReducedGamma6814 MovingSourceLinearFlow6814 MovingSourceReducedRoutes6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem reduced_selected_tail_zero
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (H G : MvPolynomial (Fin 4) K) (n : ℕ) (hn : RCN326.w<n)
    (hcross : S.F∣H^(2*n)*numerator K S.F n-(polyH K S.F)^(2*n)*numerators H G n)
    (gamma : K) (hgamma : gamma∈Gamma) :
    MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) S.selected gamma)
      (surfaceMap (polynomialEmbedding K) (numerators H G n))=0 := by
  let f : MvPolynomial (Fin 3) (GenericField K) →+* GenericField K :=
    (MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) S.selected gamma)).toRingHom
  let ev := f.comp (surfaceMap (polynomialEmbedding K))
  have hF : ev S.F=0 := by
    have hh := map_dvd f S.G_dvd_surface
    have hG : f S.G=0 := S.on_component gamma hgamma
    rw [hG,zero_dvd_iff] at hh
    exact hh
  have holdGlobal : globalTailCut (polynomialEmbedding K) S.F n∈RingHom.ker f :=
    selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F S.selected gamma RCN326.w n
      (S.degree_le gamma hgamma) (S.solution gamma hgamma) hn
  have hold : ev (numerator K S.F n)=0 :=
    (globalTailCut_mem_iff (polynomialEmbedding K) (polynomialEmbedding_injective K)
      S.F n (RingHom.ker f)).mp holdGlobal
  have hOld : ev (polyH K S.F)≠0 := by
    change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
      (surfaceMap (polynomialEmbedding K) (MvPolynomial.pderiv (2 : Fin 4) S.F))≠0
    rw [selectedPoint_evaluation]
    exact S.regular gamma hgamma
  have he := map_dvd ev hcross
  rw [hF,zero_dvd_iff,map_sub,map_mul,map_mul,map_pow,map_pow,hold,mul_zero,
    zero_sub,neg_eq_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hOld)

theorem reduced_tail_proper_on_component
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (H G : MvPolynomial (Fin 4) K) (n : ℕ)
    (hcross : S.F∣H^(2*n)*numerator K S.F n-(polyH K S.F)^(2*n)*numerators H G n)
    (hH : surfaceMap (polynomialEmbedding K) H∉C.1)
    (hproper : globalTailCut (polynomialEmbedding K) S.F n∉C.1) :
    surfaceMap (polynomialEmbedding K) (numerators H G n)∉C.1 := by
  let ev := (coordinateEvaluation (GenericField K) C.1).toRingHom
  have he (N : MvPolynomial (Fin 3) (GenericField K)) : ev N=0 ↔ N∈C.1 := by
    change N∈RingHom.ker (coordinateEvaluation (GenericField K) C.1).toRingHom ↔ N∈C.1
    rw [coordinateEvaluation_ker]
  have hF := (he _).mpr (RCN312.firstTailComponent_surface_mem S C)
  have hold : IsUnit (ev (surfaceMap (polynomialEmbedding K) (polyH K S.F))) :=
    isUnit_iff_ne_zero.mpr ((he _).not.mpr (RCN312.firstTailComponent_regularity_not_mem S C))
  have hnew : IsUnit (ev (surfaceMap (polynomialEmbedding K) H)) :=
    isUnit_iff_ne_zero.mpr ((he _).not.mpr hH)
  have hassoc := global_tails_associated (polynomialEmbedding K) (polynomialEmbedding_injective K)
    ev S.F H G n hF hold hnew hcross
  intro hmem
  have hh := hassoc.symm.dvd
  rw [(he _).mpr hmem,zero_dvd_iff] at hh
  exact hproper ((he _).mp hh)

def reducedDelayFlag : FlagDegree := ⟨80216676,4849702,1441803⟩

theorem reduced_delay_flag_of_route
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute F J)
    (mu delay : ℕ) (hmu : 1≤mu) (hdelay : delay≤mu) :
    RCN095.PolynomialInFlag (mu • reducedDelayFlag)
      (surfaceMap (polynomialEmbedding K)
        (numerators (linearH J) (linearG J) (RCN326.w+1+delay))) := by
  have hw := (hroute.2.2.2.2 (RCN326.w+1+delay)).2
  have hr : RCN234.wt RCN156.residualSWeights
      (numerators (linearH J) (linearG J) (RCN326.w+1+delay))≤1441803*mu := by
    dsimp only [RCN326.w] at hw ⊢
    nlinarith [hw.1]
  have hy : RCN234.wt RCN156.residualYSWeights
      (numerators (linearH J) (linearG J) (RCN326.w+1+delay))≤6291505*mu := by
    dsimp only [RCN326.w] at hw ⊢
    nlinarith [hw.2.1]
  have ht : RCN234.wt RCN156.residualTotalWeights
      (numerators (linearH J) (linearG J) (RCN326.w+1+delay))≤86508181*mu := by
    dsimp only [RCN326.w] at hw ⊢
    nlinarith [hw.2.2]
  have hh := surface_flag_of_caps (polynomialEmbedding K) _ (1441803*mu) (6291505*mu) (86508181*mu)
    (by omega) (by omega) hr hy ht
  have he : (⟨86508181*mu-6291505*mu,6291505*mu-1441803*mu,1441803*mu⟩ : FlagDegree)=
      mu • reducedDelayFlag := by
    change (⟨86508181*mu-6291505*mu,6291505*mu-1441803*mu,1441803*mu⟩ : FlagDegree)=
      ⟨mu*80216676,mu*4849702,mu*1441803⟩
    congr 1 <;> omega
  rw [←he]
  exact hh

#print axioms reduced_selected_tail_zero
#print axioms reduced_tail_proper_on_component
#print axioms reduced_delay_flag_of_route
end
end ProximityPrize.SubmissionLower.MovingSourceReducedSeedTails6814
