import ProximityPrize.SubmissionLower.WholeSpaceUniqueOwnerAlternative6814

/-! Turn the actual avoidance cofactor into the Source records consumed by
the cross-source geometric counter. No root or helper identity is assumed
for the new record beyond the already-proved weighted-pair conclusion. -/
namespace ProximityPrize.SubmissionLower.WholeSpacePowerSourcePair6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingFiberThreeSources6811 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814
open WholeSpaceUniqueOwnerAlternative6814 MovingSourceNativeEnvelope6814
open SecondJetCoefficients SecondJetCarrierDichotomy RCN234 RCN156

variable {K : Type} [Field K] [CharP K 2130706433]

theorem source_of_small_power
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 1700<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (P : Poly (K := K)) (hP : P≠0) (hT : total P≤1700)
    (d : ℕ) (hd : 0<d)
    (hpower : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^d∣(asS P).map (carrierMap F)) :
    ∃ S : Source F, S.P=P ∧ d≤S.d := by
  have hshapeT : ∀ e∈P.support, e 1+e 2+e 3+e 4≤1700 := by
    intro e he
    have hh := (Finset.le_sup (f := Finsupp.weight totalWeights) he).trans hT
    simpa [weight_coords,totalWeights] using hh
  have hne := carrier_polynomial_nonzero F P hP 1700 hshapeT hFT
  let m := ((asS P).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)
  have hdm : d≤m := (Polynomial.le_rootMultiplicity_iff hne).mpr hpower
  have hn := source_nested P
  have hshape : ∀ e∈P.support, 2*e 1+e 3≤slope P ∧
      e 1+e 2+e 3≤max (slope P) (middle P) ∧
      e 1+e 2+e 3+e 4≤max (slope P) (total P) := by
    intro e he
    have hb : Finsupp.weight slopeWeights e≤slope P := Finset.le_sup he
    have hu : Finsupp.weight middleWeights e≤middle P := Finset.le_sup he
    have ht : Finsupp.weight totalWeights e≤total P := Finset.le_sup he
    refine ⟨?_,?_,?_⟩
    · simpa [weight_coords,slopeWeights,Nat.mul_comm] using hb
    · have hu' : e 1+e 2+e 3≤middle P := by simpa [weight_coords,middleWeights] using hu
      exact hu'.trans (le_max_right _ _)
    · have ht' : e 1+e 2+e 3+e 4≤total P := by simpa [weight_coords,totalWeights] using ht
      exact ht'.trans (le_max_right _ _)
  obtain ⟨S,hSP,hSd,_⟩ := canonical_source_of_root P F hpos hsmall m (order P)
    (slope P) (max (slope P) (middle P)) (max (slope P) (total P))
    (by omega) rfl hn.2.2.1 (le_max_left _ _) (max_le_max (le_refl _) hn.1) hshape rfl
  exact ⟨S,hSP,by omega⟩

/-- Concrete bridge to source_pair_weighted_point_count: the new cofactor
and original owner are actual coprime Source records, and their common
order is min(m,3-e*m), with all coupled degree charges preserved. -/
theorem source_pair_of_weighted_pair
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 1700<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : Poly (K := K)) (hJ : J≠0) (hT : total J≤1700)
    (hm : 0<multiplicity F J) (hpair : WeightedPair F J) :
    ∃ e<copies3 (multiplicity F J), ∃ S T : Source F,
      S.P=J ∧ IsRelPrime S.P T.P ∧
      0<min (multiplicity F J) (3-e*multiplicity F J) ∧
      min (multiplicity F J) (3-e*multiplicity F J)≤S.d ∧
      min (multiplicity F J) (3-e*multiplicity F J)≤T.d ∧
      min (multiplicity F J) (3-e*multiplicity F J)≤2130706433 ∧
      e*total J+total T.P≤1700 ∧ e*middle J+middle T.P≤98 ∧
      e*slope J+slope T.P≤31 ∧ e*order J+order T.P≤14 := by
  obtain ⟨e,he,Q,hQ,hcop,hposQ,hpowQ,hTQ,hUQ,hBQ,hSQ⟩ := hpair
  have hpowJ : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^(multiplicity F J)∣
      (asS J).map (carrierMap F) := Polynomial.pow_rootMultiplicity_dvd _ _
  obtain ⟨S,hSJ,hSm⟩ := source_of_small_power F hFT hpos hsmall J hJ hT (multiplicity F J) hm hpowJ
  obtain ⟨T,hTQeq,hTd⟩ := source_of_small_power F hFT hpos hsmall Q hQ (by omega)
    (3-e*multiplicity F J) hposQ hpowQ
  refine ⟨e,he,S,T,hSJ,?_,by omega,by omega,by omega,by omega,?_,?_,?_,?_⟩
  · rwa [hSJ,hTQeq]
  · rwa [hTQeq]
  · rwa [hTQeq]
  · rwa [hTQeq]
  · rwa [hTQeq]

#print axioms source_of_small_power
#print axioms source_pair_of_weighted_pair
end
end ProximityPrize.SubmissionLower.WholeSpacePowerSourcePair6814
