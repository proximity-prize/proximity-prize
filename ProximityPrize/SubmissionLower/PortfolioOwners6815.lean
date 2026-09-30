import ProximityPrize.SubmissionLower.PortfolioAvoidanceSource6815
import ProximityPrize.SubmissionLower.MovingSourceBandNativeCount6815
import ProximityPrize.SubmissionLower.MovingSourceMixedOwnerRouting6814
import ProximityPrize.SubmissionLower.QuadraticRamifiedOwner6815
namespace ProximityPrize.SubmissionLower.PortfolioOwners6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 25000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCarrierField6814
open MovingSourceOwnerSplit6814 MovingSourceCoupledClearing6814 MovingSourceNativeFactor6814
open MovingSourceNativeEnvelope6814 MovingSourceMixedOwnerRouting6814
open SecondJetCoefficients SecondJetClearedHelper SecondJetCarrierDichotomy RCN234 RCN156
variable {K : Type} [Field K] [CharP K 2130706433]

def multiplicity (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J : Poly (K:=K)) : ℕ :=
  ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)

theorem unique_owner_data
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (B U T s : ℕ) (hS : Profile S B U T s 2 3)
    (hT : T≤995) (hFT : 2985<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (hu : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J S.P) :
    0<multiplicity F J ∧ multiplicity F J≤order J ∧
    copies3 (multiplicity F J)*slope J≤B ∧
    copies3 (multiplicity F J)*middle J≤U ∧
    copies3 (multiplicity F J)*total J≤T ∧
    copies3 (multiplicity F J)*order J≤s ∧
    (3≤multiplicity F J → 5≤order J) ∧ (asS J).map (carrierMap F)≠0 := by
  have hp := canonical_source_power F S (by rw [hS.2.2.1]; omega) hpos hchar
    (by rw [hS.2.2.2.2.1]; decide)
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
  have hpower : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3∣rootPolynomialMap (carrierMap F) S.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3∣(asS S.P).map (carrierMap F)
    simpa only [Source.d,hS.2.2.2.2.1] using hp.2
  obtain ⟨e,he,heW,heS⟩ := unique_owner_charges (carrierMap F) (ratio (carrierMap F) F)
    S.P J (source_nonzero F S) hJ hu 3 (multiplicity F J) hJne rfl hpower
  have hqe := copies3_le (multiplicity F J) e hm he
  have hc := MovingSourceOwnerRouting6814.source_caps F S
  rw [hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.1] at hc
  have hb := (Nat.mul_le_mul_right (slope J) hqe).trans ((heW slopeWeights).trans hc.1)
  have hU := (Nat.mul_le_mul_right (middle J) hqe).trans ((heW middleWeights).trans hc.2.1)
  have ht := (Nat.mul_le_mul_right (total J) hqe).trans ((heW totalWeights).trans hc.2.2.1)
  have hs := (Nat.mul_le_mul_right (order J) hqe).trans (heS.trans hc.2.2.2)
  refine ⟨hm,hms,hb,hU,ht,hs,?_,hJne⟩
  intro hm3
  by_contra hn
  have hd : order J=3 ∨ order J=4 := by omega
  have hq := copies3_pos (multiplicity F J) hm
  have htJ : total J≤995 := by
    have hmul := Nat.mul_le_mul_right (total J) hq
    omega
  have hx := MovingSourceTripleOwnerExclusion6814.small_cubic_quartic_rootMultiplicity_lt_three
    F hFT J hJ htJ hd
  change multiplicity F J<3 at hx
  omega

theorem exact_owner_source (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (m s b u t : ℕ) (hm : 0<m) (hms : m≤s)
    (hs : J.degreeOf 1=s) (h2s : 2*s≤b) (hbu : b≤u) (hut : u≤t)
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤b ∧ e 1+e 2+e 3≤u ∧ e 1+e 2+e 3+e 4≤t)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m) :
    ∃ S : Source F, S.P=J ∧ Profile S b u t s (m-1) s := by
  have hS : ∀ e∈J.support, e 1≤s := MvPolynomial.degreeOf_le_iff.mp hs.le
  have hH := carrier_H_nonzero F hpos hchar
  let source : Source F := {
    P:=J, B:=b, U:=u, T:=t, s:=s, k:=m-1, n0:=s
    hS:=hS, hshape:=hshape, hBU:=hbu, hUT:=hut
    hdn:=by omega, hB:=by omega
    hn:=by rw [asS_natDegree,hs]
    hdiv:=by
      intro d hd
      apply (carrierMap_zero_iff F _).mp
      rw [mapped_helper J F (carrierMap F) s d hS hH]
      have hz : ((Polynomial.derivative)^[d] ((asS J).map (carrierMap F))).eval (ratio (carrierMap F) F)=0 :=
        Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot]; omega)
      rw [hz,mul_zero] }
  exact ⟨source,rfl,by repeat' constructor⟩

theorem root_source_profile (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (m s b u t k n0 : ℕ)
    (hkm : k+1≤m) (hkn : k+1≤n0) (hn : n0≤J.degreeOf 1) (hs : J.degreeOf 1≤s)
    (h2n : 2*n0≤b) (hbu : b≤u) (hut : u≤t)
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤b ∧ e 1+e 2+e 3≤u ∧ e 1+e 2+e 3+e 4≤t)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m) :
    ∃ S : Source F, S.P=J ∧ Profile S b u t s k n0 := by
  have hS : ∀ e∈J.support, e 1≤s := MvPolynomial.degreeOf_le_iff.mp hs
  have hH := carrier_H_nonzero F hpos hchar
  let source : Source F := {
    P:=J, B:=b, U:=u, T:=t, s:=s, k:=k, n0:=n0
    hS:=hS, hshape:=hshape, hBU:=hbu, hUT:=hut, hdn:=hkn, hB:=by omega
    hn:=by simpa only [asS_natDegree] using hn
    hdiv:=by
      intro d hd
      apply (carrierMap_zero_iff F _).mp
      rw [mapped_helper J F (carrierMap F) s d hS hH]
      have hz : ((Polynomial.derivative)^[d] ((asS J).map (carrierMap F))).eval (ratio (carrierMap F) F)=0 :=
        Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot]; omega)
      rw [hz,mul_zero] }
  exact ⟨source,rfl,by repeat' constructor⟩

end
end ProximityPrize.SubmissionLower.PortfolioOwners6815
