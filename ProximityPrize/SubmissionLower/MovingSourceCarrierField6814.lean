import ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814
import ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814

/-! The faithful field of the original four-variable carrier. Its kernel
is proved to be exactly (F), so the source alternative produces global
helper divisibility, not a root identity at a special closed point. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceCarrierZeros6814 RCN234 RCN156

variable {K : Type} [Field K]

instance carrierSpanPrime (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] :
    (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (Fact.out : Irreducible F).prime

abbrev CarrierRing (F : MvPolynomial (Fin 4) K) :=
  MvPolynomial (Fin 4) K ⧸ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))

abbrev CarrierField (F : MvPolynomial (Fin 4) K) := FractionRing (CarrierRing F)

def carrierMap (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] :
    MvPolynomial (Fin 4) K →+* CarrierField F :=
  (algebraMap (CarrierRing F) (CarrierField F)).comp (Ideal.Quotient.mk _)

theorem carrierMap_zero_iff (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (P : MvPolynomial (Fin 4) K) : carrierMap F P=0 ↔ F∣P := by
  change algebraMap (CarrierRing F) (CarrierField F) (Ideal.Quotient.mk _ P)=0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (CarrierRing F) (CarrierField F)),
    Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]

theorem carrierMap_self (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] :
    carrierMap F F=0 := (carrierMap_zero_iff F F).mpr (dvd_refl F)

instance carrierField_charP (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (p : ℕ) [CharP K p] : CharP (CarrierField F) p :=
  charP_of_injective_ringHom ((carrierMap F).comp MvPolynomial.C).injective p

theorem carrier_H_nonzero (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    [CharP K 2130706433] (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433) :
    carrierMap F (2*RCN313.polyH K F)≠0 := by
  have hh : carrierMap F (RCN313.polyH K F)≠0 := by
    intro hz
    exact RCN267.equation_not_dvd_R_derivative F 2130706433 hpos hsmall
      ((carrierMap_zero_iff F _).mp hz)
  rw [map_mul,map_ofNat]
  apply mul_ne_zero _ hh
  exact (CharP.cast_eq_zero_iff (CarrierField F) 2130706433 2).not.mpr (by decide)

theorem carrier_polynomial_nonzero
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (P : WholeSpaceCube6814.Poly (K := K)) (hP : P≠0) (cap : ℕ)
    (hshape : ∀ e ∈ P.support, e 1+e 2+e 3+e 4≤cap)
    (hF : cap<wt residualTotalWeights F) : (asS P).map (carrierMap F)≠0 := by
  have hh := SecondJetTotalAvoidance.leading_not_dvd P hP F cap hshape hF
  have hl : carrierMap F (asS P).leadingCoeff≠0 := by
    exact fun hz => hh.2 ((carrierMap_zero_iff F _).mp hz)
  exact (SecondJetCoefficientAvoidance.map_degree_preserved (asS P) (carrierMap F) hl).1

/-- Received-word data and the actual simple-quadratic branch yield both
global carrier identities. Neither a faithful-map assumption nor either
helper-divisibility conclusion is a premise. -/
theorem exists_helper_or_global_pair
    {N : Type} [Fintype N] [CharP K 2130706433]
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K := K)) (hJi : Irreducible J)
    (hmid : 25≤weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9)
    (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hJbounds : ∀ e ∈ J.support,
      2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (hT : T≤1700)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
    ∃ Q : WholeSpaceCube6814.Poly (K := K), Q≠0 ∧ IsRelPrime J Q ∧
      F∣helper J F 2 0 ∧ F∣helper Q F 14 0 ∧
      (∀ e ∈ Q.support, 2*e 1+e 3≤31 ∧ e 1+e 2+e 3≤98 ∧ e 1+e 2+e 3+e 4≤1700) ∧
      Q.degreeOf 1≤14 := by
  have hH := carrier_H_nonzero F hpos hsmall
  have hJne := carrier_polynomial_nonzero F J hJi.ne_zero T
    (fun e he => (hJbounds e he).2.2) (hT.trans_lt hFT)
  rcases exists_helper_or_curvature_pair nodes u0 u1 hN J hJi hmid hB F Fact.out
    hFT r y t hr hy ht hF (carrierMap F) (carrierMap_self F) hH hJne hroot with hhelp | hp
  · exact Or.inl hhelp
  obtain ⟨Q,hQ,hcop,hzero,hTotal,hMid,hSlope,hDegree⟩ := hp
  right
  refine ⟨Q,hQ,hcop,?_,?_,?_,hDegree⟩
  · exact helper_dvd_of_generic_root J F (carrierMap F) (carrierMap_zero_iff F) 2
      (MvPolynomial.degreeOf_le_iff.mp hJdegree) hH (simple_root_vanishes _ _ hroot)
  · exact helper_dvd_of_generic_root Q F (carrierMap F) (carrierMap_zero_iff F) 14
      (MvPolynomial.degreeOf_le_iff.mp hDegree) hH hzero
  · intro e he
    have hs := (MvPolynomial.le_weightedTotalDegree slopeWeights he).trans hSlope
    have hm := (MvPolynomial.le_weightedTotalDegree middleWeights he).trans hMid
    have ht := (MvPolynomial.le_weightedTotalDegree totalWeights he).trans hTotal
    exact ⟨by simpa [weight_coords,slopeWeights,Nat.mul_comm] using hs,
      by simpa [weight_coords,middleWeights] using hm,
      by simpa [weight_coords,totalWeights] using ht⟩

#print axioms carrierMap_zero_iff
#print axioms exists_helper_or_global_pair
end
end ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
