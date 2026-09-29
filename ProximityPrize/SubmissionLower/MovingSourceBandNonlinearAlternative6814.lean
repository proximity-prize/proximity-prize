import ProximityPrize.SubmissionLower.MovingSourceBandNativeCover6814
import ProximityPrize.SubmissionLower.MovingSourceBandNativeExit6814
import ProximityPrize.SubmissionLower.WholeSpaceTrimmedSupplier6814

/-! Exhaustive nonlinear-owner routing at the new 270e15 threshold.
Both ordinary and trimmed boxes produce actual received-word sources.
The cofactor branch retains the native-failure fact needed for pricing. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandNonlinearAlternative6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 25000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpaceUniqueOwnerAlternative6814 WholeSpaceSourceAlternative6814
open MovingSourceNativeEnvelope6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceOwnerSplit6814 MovingSourceMixedOwnerRouting6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandNativeArithmetic6814 MovingSourceBandNativeForms6814 MovingSourceBandNativeExit6814
open SecondJetCoefficients SecondJetCarrierDichotomy RCN234 RCN156
variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]

def ownerCost (i : Fin 11) (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : Poly (K:=K)) : ℕ :=
  scalar i (multiplicity F J) (order J) (slope J) (max (slope J) (middle J)) (max (slope J) (total J))

theorem unique_nonlinear_alternative (i : Fin 11)
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (hFT : 2985<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J S.P)
    (hs : 2≤order J)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    ownerCost i F J<3*269880000000000000*multiplicity F J ∨
      (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      (WeightedPair F J ∧ Failure i (multiplicity F J) (order J) (slope J) (middle J) (total J)) := by
  obtain ⟨hm,hms,hB,hU,hT,hex,hJne⟩ := unique_owner_data F S hS hFT hpos hsmall J hJ hJS hroot hunique
  have hn := source_nested J
  by_cases hfit : ownerCost i F J<3*269880000000000000*multiplicity F J
  · exact Or.inl hfit
  by_cases hbu : slope J≤middle J
  · right
    have hbt : slope J≤total J := hbu.trans hn.1
    have hcost : ownerCost i F J=scalar i (multiplicity F J) (order J) (slope J) (middle J) (total J) := by
      simp only [ownerCost,max_eq_right hbu,max_eq_right hbt]
    have hfail : Failure i (multiplicity F J) (order J) (slope J) (middle J) (total J) :=
      (failure_iff i _ _ _ _ _ hms hn.2.2.1 hbu hn.1).mpr (by omega)
    obtain ⟨a,haq,ha,hgood⟩ := MovingSourceBandNativeCover6814.failure_has_box i
      (multiplicity F J) (order J) (slope J) (middle J) (total J)
      hm hs hms hn.2.2.1 hbu hn.1 hB hU hT hex hfail
    have hout : (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨ WeightedPair F J := by
      rcases hgood with hordinary | htrimmed
      · exact MovingSourceReservedOwnerAlternative6814.helper_or_weighted_pair_of_box
          nodes u0 u1 hN J hJ (multiplicity F J) hm a haq ha hordinary
          F (Fact.out : Irreducible F) (by omega) r y t hr hy ht hF
          (carrierMap F) (carrierMap_self F) (carrier_H_nonzero F hpos hsmall) hJne rfl
      · exact WholeSpaceTrimmedSupplier6814.helper_or_weighted_pair_of_trimmed_box
          nodes u0 u1 hN J hJ (multiplicity F J) hm a haq ha htrimmed
          F (Fact.out : Irreducible F) (by omega) r y t hr hy ht hF
          (carrierMap F) (carrierMap_self F) (carrier_H_nonzero F hpos hsmall) hJne rfl
    exact hout.elim Or.inl (fun hp => Or.inr ⟨hp,hfail⟩)
  · have hub : middle J≤slope J := by omega
    have hq := copies3_pos (multiplicity F J) hm
    have hmax : copies3 (multiplicity F J)*max (slope J) (total J)≤995 := by
      rcases le_total (slope J) (total J) with h | h
      · rw [max_eq_right h]; exact hT
      · rw [max_eq_left h]; omega
    have hh := padded_scalar_fits i (multiplicity F J) (order J) (slope J) (max (slope J) (total J))
      hm hs hms hn.2.2.1 (le_max_left _ _) hB hmax hex
    exact False.elim (hfit (by simpa only [ownerCost,max_eq_left hub] using hh))

#print axioms unique_nonlinear_alternative
end
end ProximityPrize.SubmissionLower.MovingSourceBandNonlinearAlternative6814
