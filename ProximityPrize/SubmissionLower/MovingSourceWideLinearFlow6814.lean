import ProximityPrize.SubmissionLower.WholeSpaceUniqueOwnerAlternative6814
import ProximityPrize.SubmissionLower.MovingSourceLinearSeedAssembly6814

/-! The small-source-only linear owner has envelope (10,32,331).
Reuse the proved flow and denominator-change algebra; only the support
bounds grow. No ownership of the separate Z source is required. -/
namespace ProximityPrize.SubmissionLower.MovingSourceWideLinearFlow6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open MvPolynomial RCN234 RCN156 RCN095 RCN135 RCN136
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814
open MovingSourceDenominatorChange6814 MovingSourceReducedTailWeights6814
open MovingSourceReducedGamma6814 MovingSourceReducedCycle6814
open MovingSourceCarrierField6814 MovingSourceOwnerSplit6814
open MovingSourceCoupledClearing6814 WholeSpaceUniqueOwnerAlternative6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open WholeSpaceCube6814 WholeSpaceCubeUniform6814

variable {K : Type} [Field K]

def WideLinearRoute (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : Poly (K:=K)) : Prop :=
  J.degreeOf 1=1 ∧ carrierMap F (linearH J)≠0 ∧
  (wt residualSWeights (linearH J)≤8 ∧ wt residualYSWeights (linearH J)≤31 ∧
    wt residualTotalWeights (linearH J)≤330) ∧
  (wt residualSWeights (linearG J)≤10 ∧ wt residualYSWeights (linearG J)≤32 ∧
    wt residualTotalWeights (linearG J)≤331) ∧
  ∀ n, (F∣(linearH J)^(2*n)*RCN313.numerator K F n-
    (RCN313.polyH K F)^(2*n)*numerators (linearH J) (linearG J) n) ∧
    wt residualSWeights (numerators (linearH J) (linearG J) n)≤17*n ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+62*n ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+660*n

theorem unique_linear_shape [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (hFT : 2985<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P) (hs : J.degreeOf 1=1)
    (hroot : rootEvaluation (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F)) J S.P) :
    ∀ e∈J.support, 2*e 1+e 3≤10 ∧ e 1+e 2+e 3≤32 ∧ e 1+e 2+e 3+e 4≤331 := by
  obtain ⟨hm,hms,hB,hU,hT,-,-⟩ := unique_owner_data F S hS hFT hpos hsmall J hJ hJS hroot hunique
  have hm1 : multiplicity F J=1 := by change multiplicity F J≤J.degreeOf 1 at hms; omega
  rw [hm1] at hB hU hT
  norm_num [MovingSourceNativeEnvelope6814.copies3] at hB hU hT
  intro e he
  have hb := MvPolynomial.le_weightedTotalDegree slopeWeights he
  have hu := MvPolynomial.le_weightedTotalDegree middleWeights he
  have ht := MvPolynomial.le_weightedTotalDegree totalWeights he
  change 3*weightedTotalDegree slopeWeights J≤31 at hB
  change 3*weightedTotalDegree middleWeights J≤98 at hU
  change 3*weightedTotalDegree totalWeights J≤995 at hT
  simp only [weight_coords,slopeWeights,middleWeights,totalWeights] at hb hu ht
  simp at hb hu ht
  dsimp only [slopeWeights,middleWeights,totalWeights] at hB hU hT
  omega

theorem linear_tail_weights
    (J : Poly (K:=K))
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤10 ∧ e 1+e 2+e 3≤32 ∧ e 1+e 2+e 3+e 4≤331)
    (n : ℕ) :
    wt residualSWeights (numerators (linearH J) (linearG J) n)≤17*n ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+62*n ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+660*n := by
  have hh := linear_coefficient_weights J 10 32 331 hshape
  have hR := numerator_weight residualSWeights (linearH J) (linearG J) 8 9 hh.1.1 hh.2.1 (by decide) (by decide) n
  have hY := numerator_weight residualYSWeights (linearH J) (linearG J) 31 31 hh.1.2.1 hh.2.2.1 (by decide) (by decide) n
  have hT := numerator_weight residualTotalWeights (linearH J) (linearG J) 330 330 hh.1.2.2 hh.2.2.2 (by decide) (by decide) n
  refine ⟨?_,?_,?_⟩
  · simpa only [show residualSWeights 1=0 from rfl,zero_add,Nat.reduceAdd,Nat.mul_comm] using hR
  · simpa only [show residualYSWeights 1=1 from rfl,Nat.reduceAdd,Nat.mul_comm] using hY
  · simpa only [show residualTotalWeights 1=1 from rfl,Nat.reduceAdd,Nat.mul_comm] using hT

theorem wide_linear_route [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (hFT : 2985<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P) (hs : J.degreeOf 1=1)
    (hroot : rootEvaluation (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap F) (SecondJetCarrierDichotomy.ratio (carrierMap F) F)) J S.P) :
    WideLinearRoute F J := by
  have hshape := unique_linear_shape F S hS hFT hpos hsmall J hJ hJS hs hroot hunique
  have hcoeff := linear_coefficient_weights J 10 32 331 hshape
  refine ⟨hs,linearH_nonzero_on_carrier J hJ.ne_zero hs F 331
    (fun e he => (hshape e he).2.2) (by omega),hcoeff.1,hcoeff.2,?_⟩
  intro n
  exact ⟨linear_denominator_change J hJ.ne_zero hs F hpos hsmall 331
    (fun e he => (hshape e he).2.2) (by omega) hroot n,linear_tail_weights J hshape n⟩

def wideFirstFlag : FlagDegree := ⟨78381056,5898241,2228224⟩
def wideDelayFlag : FlagDegree := ⟨78381654,5898286,2228241⟩

theorem wide_first_flag (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : Poly (K:=K)) (hroute : WideLinearRoute F J) :
    PolynomialInFlag wideFirstFlag (reducedTailSurface (linearH J) (linearG J)) := by
  have hw := (hroute.2.2.2.2 (RCN326.w+1)).2
  exact surface_flag_of_caps (polynomialEmbedding K) _ 2228224 8126465 86507521
    (by decide) (by decide) hw.1 hw.2.1 hw.2.2

theorem wide_delay_flag (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : Poly (K:=K)) (hroute : WideLinearRoute F J)
    (mu delay : ℕ) (hmu : 1≤mu) (hdelay : delay≤mu) :
    PolynomialInFlag (mu • wideDelayFlag)
      (surfaceMap (polynomialEmbedding K)
        (numerators (linearH J) (linearG J) (RCN326.w+1+delay))) := by
  have hw := (hroute.2.2.2.2 (RCN326.w+1+delay)).2
  have hr : wt residualSWeights (numerators (linearH J) (linearG J) (RCN326.w+1+delay))≤2228241*mu := by
    dsimp only [RCN326.w] at hw ⊢; nlinarith [hw.1]
  have hy : wt residualYSWeights (numerators (linearH J) (linearG J) (RCN326.w+1+delay))≤8126527*mu := by
    dsimp only [RCN326.w] at hw ⊢; nlinarith [hw.2.1]
  have ht : wt residualTotalWeights (numerators (linearH J) (linearG J) (RCN326.w+1+delay))≤86508181*mu := by
    dsimp only [RCN326.w] at hw ⊢; nlinarith [hw.2.2]
  have hh := surface_flag_of_caps (polynomialEmbedding K) _ (2228241*mu) (8126527*mu) (86508181*mu)
    (by omega) (by omega) hr hy ht
  have he : (⟨86508181*mu-8126527*mu,8126527*mu-2228241*mu,2228241*mu⟩ : FlagDegree)=mu • wideDelayFlag := by
    change (⟨86508181*mu-8126527*mu,8126527*mu-2228241*mu,2228241*mu⟩ : FlagDegree)=
      ⟨mu*78381654,mu*5898286,mu*2228241⟩
    congr 1 <;> omega
  rw [←he]
  exact hh

theorem wide_gamma_budget : flagMixed ⟨3504,45,12⟩ wideFirstFlag unitZFlag=197787660 ∧
    flagMixed ⟨3504,45,12⟩ wideFirstFlag unitZFlag<2130706433 := by decide +kernel

variable {I : Type} {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}

theorem wide_denominator_proper
    (S : RCN244.Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (J : Poly (K:=K)) (hroute : WideLinearRoute S.F J) :
    ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J) := by
  have hF : Irreducible S.F := Fact.out
  have hnot : ¬S.F∣linearH J := fun hd => hroute.2.1 ((carrierMap_zero_iff S.F _).mpr hd)
  have hrel := MovingSourceDenominatorSeeds6814.surfaceMap_relPrime S.F (linearH J) hF.ne_zero
    (hF.isRelPrime_iff_not_dvd.mpr hnot)
  intro hd
  exact S.irreducible_G.not_isUnit (hrel S.G_dvd_surface hd)

#print axioms wide_linear_route
#print axioms wide_delay_flag
#print axioms wide_denominator_proper
end
end ProximityPrize.SubmissionLower.MovingSourceWideLinearFlow6814
