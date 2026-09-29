import ProximityPrize.SubmissionLower.WholeSpacePowerAlternative6814

/-! Connect power avoidance to the actual unique owner of the small
contact source. Degree caps and the excluded band are proved here. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceUniqueOwnerAlternative6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceCarrierField6814 MovingSourceOwnerSplit6814
open MovingSourceCoupledClearing6814 MovingSourceNativeEnvelope6814
open MovingSourceMixedOwnerRouting6814 MovingSourceNativeFactor6814
open WholeSpacePowerCover6814 WholeSpaceSourceAlternative6814
open WholeSpacePowerAlternative6814 SecondJetCoefficients SecondJetCarrierDichotomy
open RCN234 RCN156

variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]

def multiplicity (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J : Poly (K := K)) : ℕ :=
  ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)

def nativeCost (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J : Poly (K := K)) : ℕ :=
  native (multiplicity F J) (order J) (slope J) (max (slope J) (middle J)) (max (slope J) (total J))

def WeightedPair (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J : Poly (K := K)) : Prop :=
  ∃ e<copies3 (multiplicity F J), ∃ Q : Poly (K := K), Q≠0 ∧ IsRelPrime J Q ∧
    0<3-e*multiplicity F J ∧
    (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^(3-e*multiplicity F J)∣(asS Q).map (carrierMap F) ∧
    e*total J+total Q≤1700 ∧ e*middle J+middle Q≤98 ∧
    e*slope J+slope Q≤31 ∧ e*order J+order Q≤14

theorem unique_owner_data
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (hFT : 2985<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : Poly (K := K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J S.P) :
    0<multiplicity F J ∧ multiplicity F J≤order J ∧
    copies3 (multiplicity F J)*slope J≤31 ∧
    copies3 (multiplicity F J)*middle J≤98 ∧
    copies3 (multiplicity F J)*total J≤995 ∧
    (3≤multiplicity F J → 5≤order J) ∧ (asS J).map (carrierMap F)≠0 := by
  have hp := canonical_source_power F S (by rw [hS.2.2.1]; omega) hpos hsmall
    (by rw [hS.2.2.2.2.1]; omega)
  have hJne : rootPolynomialMap (carrierMap F) J≠0 := by
    intro hz
    have hd := map_dvd (rootPolynomialMap (carrierMap F)) hJS
    rw [hz,zero_dvd_iff] at hd
    exact hp.1 hd
  have hm : 0<multiplicity F J := (Polynomial.rootMultiplicity_pos hJne).mpr hroot
  have hms : multiplicity F J≤order J := by
    have hh := Polynomial.natDegree_le_of_dvd
      ((rootPolynomialMap (carrierMap F) J).pow_rootMultiplicity_dvd (ratio (carrierMap F) F)) hJne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq (asS_natDegree J))
  have hpower : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3∣
      rootPolynomialMap (carrierMap F) S.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3∣(asS S.P).map (carrierMap F)
    simpa only [Source.d,hS.2.2.2.2.1] using hp.2
  obtain ⟨e,he,heW,_⟩ := unique_owner_charges (carrierMap F) (ratio (carrierMap F) F)
    S.P J (source_nonzero F S) hJ hunique 3 (multiplicity F J) hJne rfl hpower
  have hqe := copies3_le (multiplicity F J) e hm he
  have hc := MovingSourceOwnerRouting6814.source_caps F S
  rw [hS.1,hS.2.1,hS.2.2.1] at hc
  have hb := (Nat.mul_le_mul_right (slope J) hqe).trans ((heW slopeWeights).trans hc.1)
  have hu := (Nat.mul_le_mul_right (middle J) hqe).trans ((heW middleWeights).trans hc.2.1)
  have ht := (Nat.mul_le_mul_right (total J) hqe).trans ((heW totalWeights).trans hc.2.2.1)
  refine ⟨hm,hms,hb,hu,ht,?_,hJne⟩
  intro hm3
  by_contra hn
  have hs : order J=3 ∨ order J=4 := by omega
  have hx := small_source_factor_triple_excluded F hFT S hS J hJ hJS hs
  change multiplicity F J<3 at hx
  omega

/-- No avoidance, degree-charge, or excluded-band premise. Starting with
the actual unique nonlinear owner, either the native price fits, a proper
helper exists, or the multiplicity-preserving coprime pair exists. -/
theorem unique_nonlinear_alternative
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (hFT : 2985<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : Poly (K := K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J S.P)
    (hs : 2≤order J)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    nativeCost F J<3*272069082261391681*multiplicity F J ∨
      (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨ WeightedPair F J := by
  obtain ⟨hm,hms,hB,hU,hT,hex,hJne⟩ := unique_owner_data F S hS hFT hpos hsmall J hJ hJS hroot hunique
  have hn := source_nested J
  by_cases hbu : slope J≤middle J
  · have hbt : slope J≤total J := hbu.trans hn.1
    have hcost : nativeCost F J=native (multiplicity F J) (order J) (slope J) (middle J) (total J) := by
      simp only [nativeCost,max_eq_right hbu,max_eq_right hbt]
    by_cases hfit : nativeCost F J<3*272069082261391681*multiplicity F J
    · exact Or.inl hfit
    right
    have hfail : 3*272069082261391681*multiplicity F J≤
        native (multiplicity F J) (order J) (slope J) (middle J) (total J) := by omega
    exact exists_helper_or_weighted_pair nodes u0 u1 hN J hJ (multiplicity F J) hm hs hms hn.2.2.1
      hbu hn.1 hB hU hT hex hfail F (Fact.out : Irreducible F) (by omega)
      r y t hr hy ht hF (carrierMap F) (carrierMap_self F) (carrier_H_nonzero F hpos hsmall) hJne rfl
  · left
    have hub : middle J≤slope J := by omega
    have hmax : copies3 (multiplicity F J)*max (slope J) (total J)≤995 := by
      rcases le_total (slope J) (total J) with h | h
      · rw [max_eq_right h]; exact hT
      · rw [max_eq_left h]; omega
    have hh := padded_native_fits (multiplicity F J) (order J) (slope J) (max (slope J) (total J))
      hm hs hms hn.2.2.1 (le_max_left _ _) hB hmax
    simpa only [nativeCost,max_eq_left hub] using hh

#print axioms unique_owner_data
#print axioms unique_nonlinear_alternative
end
end ProximityPrize.SubmissionLower.WholeSpaceUniqueOwnerAlternative6814
