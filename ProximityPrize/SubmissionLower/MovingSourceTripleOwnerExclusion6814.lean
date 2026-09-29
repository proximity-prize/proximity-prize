import ProximityPrize.SubmissionLower.MovingSourceTripleRootPolynomial6814
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! A cubic/quartic factor of total residual weight <=995 cannot have a
triple curvature root modulo the large carrier F. The degree-two/three
invariants vanish modulo F, hence globally; Gauss's lemma then contradicts
irreducibility. No discriminant determinant or multiplicity discount is
assumed. -/
namespace ProximityPrize.SubmissionLower.MovingSourceTripleOwnerExclusion6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open MvPolynomial RCN234 RCN156
open MovingSourceTripleRootInvariants6814 MovingSourceTripleRootPolynomial6814
open MovingSourceCarrierField6814 MovingSourceCoupledClearing6814
open WholeSpaceCube6814 WholeSpaceCubeUniform6814

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local notation "Poly4" => MvPolynomial (Fin 4) K

theorem invariant_weights (w : Fin 4 → ℕ) (a b c d e : Poly4) (T : ℕ)
    (ha : wt w a≤T) (hb : wt w b≤T) (hc : wt w c≤T) (hd : wt w d≤T) (he : wt w e≤T) :
    wt w (inv2 a b c d e)≤2*T ∧ wt w (inv3 a b c d e)≤3*T := by
  have hscale (n : ℕ) (P : Poly4) : wt w ((n : Poly4)*P)≤wt w P := by
    have hh := wt_mul_le w (n : Poly4) P
    rw [wt_natCast,zero_add] at hh
    exact hh
  have htwo (n : ℕ) (P Q : Poly4) (hp : wt w P≤T) (hq : wt w Q≤T) :
      wt w ((n : Poly4)*P*Q)≤2*T := by
    have hm := wt_mul_le w ((n : Poly4)*P) Q
    have hh := hscale n P
    omega
  have hthree (n : ℕ) (P Q R : Poly4) (hp : wt w P≤T) (hq : wt w Q≤T) (hr : wt w R≤T) :
      wt w ((n : Poly4)*P*Q*R)≤3*T := by
    have hm := wt_mul_le w ((n : Poly4)*P*Q) R
    have hh := htwo n P Q hp hq
    omega
  have hcc := (wt_pow_le w c 2).trans (Nat.mul_le_mul_left _ hc)
  have hi := (wt_add_le w (12*a*e-3*b*d) (c^2)).trans
    (max_le ((wt_sub_le w _ _).trans (max_le (htwo 12 a e ha he) (htwo 3 b d hb hd))) hcc)
  have h1 := hthree 72 a c e ha hc he
  have h2 := hthree 9 b c d hb hc hd
  have h3 : wt w (27*a*d^2)≤3*T := by
    rw [show (27 : Poly4)*a*d^2=27*a*d*d by ring]
    exact hthree 27 a d d ha hd hd
  have h4 : wt w (27*b^2*e)≤3*T := by
    rw [show (27 : Poly4)*b^2*e=27*b*b*e by ring]
    exact hthree 27 b b e hb hb he
  have h5 : wt w (2*c^3)≤3*T := by
    rw [show (2 : Poly4)*c^3=2*c*c*c by ring]
    exact hthree 2 c c c hc hc hc
  refine ⟨hi,?_⟩
  exact (wt_sub_le w _ _).trans (max_le
    ((wt_sub_le w _ _).trans (max_le
      ((wt_sub_le w _ _).trans (max_le ((wt_add_le w _ _).trans (max_le h1 h2)) h3)) h4)) h5)

theorem source_coefficient_total_cap (J : MvPolynomial (Fin 5) K) (T : ℕ)
    (hT : total J≤T) (j : ℕ) : wt residualTotalWeights ((SecondJetCoefficients.asS J).coeff j)≤T := by
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤slope J ∧ e 1+e 2+e 3≤middle J ∧
      e 1+e 2+e 3+e 4≤T := by
    intro e he
    refine ⟨?_,?_,?_⟩
    · simpa [slope,weight_coords,slopeWeights,Nat.mul_comm] using le_weightedTotalDegree slopeWeights he
    · simpa [middle,weight_coords,middleWeights] using le_weightedTotalDegree middleWeights he
    · have hh := (le_weightedTotalDegree totalWeights he).trans hT
      simpa [weight_coords,totalWeights] using hh
  have hh := SecondJetHelperWeights.derivative_coefficient_weights J (slope J) (middle J) T 0 j hshape
  simpa only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] using hh.2.2.trans (Nat.sub_le T j)

private theorem small_divisor_zero
    (F N : Poly4) (T : ℕ) (hF : T<wt residualTotalWeights F)
    (hN : wt residualTotalWeights N≤T) (hdiv : F∣N) : N=0 := by
  by_contra hn
  have hh := RCN081.weightedTotalDegree_le_of_dvd residualTotalWeights F N hdiv hn
  change wt residualTotalWeights F≤wt residualTotalWeights N at hh
  omega

theorem triple_owner_impossible [CharP K 2130706433]
    (F : Poly4) [Fact (Irreducible F)] (hFT : 2985<wt residualTotalWeights F)
    (J : MvPolynomial (Fin 5) K) (hJ : Irreducible J)
    (hT : total J≤995) (hs : order J=3 ∨ order J=4)
    (hroot : (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^3∣
      (SecondJetCoefficients.asS J).map (carrierMap F)) : False := by
  let P := SecondJetCoefficients.asS J
  have hdegree : P.natDegree=3 ∨ P.natDegree=4 := by
    simpa only [P,MovingSourceNativeFactor6814.asS_natDegree,order] using hs
  have hshape : ∀ e∈J.support, e 1+e 2+e 3+e 4≤995 := by
    intro e he
    have hh := (le_weightedTotalDegree totalWeights he).trans hT
    simpa [weight_coords,totalWeights] using hh
  have hn := carrier_polynomial_nonzero F J hJ.ne_zero 995 hshape (by omega)
  have hvals := invariants_of_triple_root (P.map (carrierMap F)) hn
    (Polynomial.natDegree_map_le.trans (show P.natDegree≤4 by omega)) _ hroot
  have hweights := invariant_weights residualTotalWeights (P.coeff 4) (P.coeff 3) (P.coeff 2) (P.coeff 1) (P.coeff 0)
    995 (source_coefficient_total_cap J 995 hT 4) (source_coefficient_total_cap J 995 hT 3)
    (source_coefficient_total_cap J 995 hT 2) (source_coefficient_total_cap J 995 hT 1)
    (source_coefficient_total_cap J 995 hT 0)
  have hi : polynomialInv2 P=0 := small_divisor_zero F _ 1990 (by omega) hweights.1
    ((carrierMap_zero_iff F _).mp (by rw [map_inv2]; exact hvals.1))
  have hj : polynomialInv3 P=0 := small_divisor_zero F _ 2985 hFT hweights.2
    ((carrierMap_zero_iff F _).mp (by rw [map_inv3]; exact hvals.2))
  let A := Poly4
  let E := FractionRing A
  letI : StrongNormalizationMonoid A := UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid A := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  let psi : A →+* E := algebraMap A E
  have hPi : Irreducible P := (MulEquiv.irreducible_iff
    (f := (SecondJetCoefficients.asS (K:=K)).toMulEquiv)).mpr hJ
  have hprim := hPi.isPrimitive (show P.natDegree≠0 by omega)
  have hirr : Irreducible (P.map psi) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K:=E)).mp hPi
  have hnd : (P.map psi).natDegree=P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective A E) P
  have h2 : (2 : E)≠0 := by
    have hh := ((psi.comp MvPolynomial.C) : K →+* E).injective.ne
      ((CharP.cast_eq_zero_iff K 2130706433 2).not.mpr (by decide))
    simpa only [map_ofNat,map_natCast,map_zero,Nat.cast_ofNat] using hh
  have h3 : (3 : E)≠0 := by
    have hh := ((psi.comp MvPolynomial.C) : K →+* E).injective.ne
      ((CharP.cast_eq_zero_iff K 2130706433 3).not.mpr (by decide))
    simpa only [map_ofNat,map_natCast,map_zero,Nat.cast_ofNat] using hh
  apply irreducible_small_invariants_not_both_zero h2 h3 (P.map psi) hirr (by rw [hnd]; exact hdegree)
  constructor
  · rw [←map_inv2,hi,map_zero]
  · rw [←map_inv3,hj,map_zero]

theorem small_cubic_quartic_rootMultiplicity_lt_three [CharP K 2130706433]
    (F : Poly4) [Fact (Irreducible F)] (hFT : 2985<wt residualTotalWeights F)
    (J : MvPolynomial (Fin 5) K) (hJ : Irreducible J)
    (hT : total J≤995) (hs : order J=3 ∨ order J=4) :
    ((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)<3 := by
  by_contra hn
  have hm : 3≤((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F) := by omega
  have hp := (pow_dvd_pow _ hm).trans (Polynomial.pow_rootMultiplicity_dvd _ _)
  exact triple_owner_impossible F hFT J hJ hT hs hp

#print axioms small_cubic_quartic_rootMultiplicity_lt_three
end
end ProximityPrize.SubmissionLower.MovingSourceTripleOwnerExclusion6814
