import ProximityPrize.SubmissionLower.PortfolioOwners6815
import ProximityPrize.SubmissionLower.RetainedSharedRemainder6815
namespace ProximityPrize.SubmissionLower.PortfolioRootFactors6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 25000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCarrierField6814
open MovingSourceOwnerSplit6814 MovingSourceNativeFactor6814 MovingSourceCoupledClearing6814
open SecondJetCoefficients SecondJetCarrierDichotomy RCN234 RCN156
variable {K : Type} [Field K] [CharP K 2130706433]

theorem root_factor_data (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hFT : S.T<wt residualTotalWeights F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0) :
    (asS J).map (carrierMap F)≠0 ∧
    0<PortfolioOwners6815.multiplicity F J ∧ PortfolioOwners6815.multiplicity F J≤order J ∧
    slope J≤S.B ∧ middle J≤S.U ∧ total J≤S.T ∧ order J≤S.s := by
  have hP := source_nonzero F S
  have hne := carrier_polynomial_nonzero F S.P hP S.T (fun e he => (S.hshape e he).2.2) hFT
  have hJne : rootPolynomialMap (carrierMap F) J≠0 := by
    intro hz
    have hd := map_dvd (rootPolynomialMap (carrierMap F)) hJS
    rw [hz,zero_dvd_iff] at hd
    exact hne hd
  have hm : 0<PortfolioOwners6815.multiplicity F J := (Polynomial.rootMultiplicity_pos hJne).mpr hroot
  have hms : PortfolioOwners6815.multiplicity F J≤order J := by
    have hh := Polynomial.natDegree_le_of_dvd
      ((rootPolynomialMap (carrierMap F) J).pow_rootMultiplicity_dvd (ratio (carrierMap F) F)) hJne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq (asS_natDegree J))
  obtain ⟨Q,hEq⟩ := hJS
  have hQ : Q≠0 := by intro hz; exact hP (by rw [hEq,hz,mul_zero])
  obtain ⟨hb,hu,ht,hs⟩ := MovingSourceOwnerRouting6814.source_caps F S
  rw [hEq,weight_mul _ _ _ hJ.ne_zero hQ] at hb hu ht
  rw [hEq,degreeOf_mul_eq hJ.ne_zero hQ] at hs
  refine ⟨hJne,hm,hms,?_,?_,?_,?_⟩
  all_goals
    dsimp only [slope,middle,total,order]
    omega

theorem ramified_order_ge_three (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hT : S.T≤995) (hFT : 2985<wt residualTotalWeights F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (hm : 2≤PortfolioOwners6815.multiplicity F J) : 3≤order J := by
  obtain ⟨hne,_,hms,_,_,ht,_⟩ := root_factor_data F S (by omega) J hJ hJS hroot
  by_contra h
  have he : order J=2 := by omega
  have hx := QuadraticRamifiedOwner6815.quadratic_rootMultiplicity_lt_two F J hJ 995
    (ht.trans hT) (by omega) (by simpa only [asS_natDegree,order] using he)
  change PortfolioOwners6815.multiplicity F J<2 at hx
  omega

theorem third_root_cases {E : Type} [Field E]
    (psi : Poly (K:=K) →+* Polynomial E) (z : E)
    (P J D : Poly (K:=K)) (hP : psi P≠0) (hJ : Irreducible J) (hD : Irreducible D)
    (hcop : IsRelPrime J D) (hJP : J∣P) (hDP : D∣P)
    (hJroot : (psi J).rootMultiplicity z=1) (hDroot : (psi D).rootMultiplicity z=1)
    (hpow : (Polynomial.X-Polynomial.C z)^3∣psi P) :
    J^2*D∣P ∨ D^2*J∣P ∨ ∃ Q : Poly (K:=K), Irreducible Q ∧ (psi Q).eval z=0 ∧
      IsRelPrime J Q ∧ IsRelPrime D Q ∧ J*D*Q∣P := by
  obtain ⟨Q,hQ,hQroot,hdiv⟩ := RetainedSharedRemainder6815.third_root_divisor
    psi z P J D hP hcop hJP hDP hJroot hDroot hpow
  by_cases hqJ : Associated Q J
  · left
    have hm := mul_dvd_mul_left (J*D) hqJ.symm.dvd
    have h := hm.trans hdiv
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using h
  by_cases hqD : Associated Q D
  · right; left
    have hm := mul_dvd_mul_left (J*D) hqD.symm.dvd
    have h := hm.trans hdiv
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using h
  right; right
  refine ⟨Q,hQ,hQroot,?_,?_,hdiv⟩
  · apply hJ.isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hqJ (hJ.associated_of_dvd hQ hd).symm
  · apply hD.isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hqD (hD.associated_of_dvd hQ hd).symm

end
end ProximityPrize.SubmissionLower.PortfolioRootFactors6815
