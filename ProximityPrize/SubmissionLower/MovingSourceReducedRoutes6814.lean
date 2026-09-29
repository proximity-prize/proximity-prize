import ProximityPrize.SubmissionLower.MovingSourceLinearBudgetTarget6814

/-! Preserve the proved reduced-flow data in the actual exhaustive source
split. This avoids dropping unique-ownership information before supplying
the linear branch. LinearRoute is flow data, NOT a completed count. -/
namespace ProximityPrize.SubmissionLower.MovingSourceReducedRoutes6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial SecondJetCoefficients SecondJetCarrierDichotomy
open MovingFiberThreeSources6811 MovingSourceCarrierField6814 MovingSourceTwoProfiles6814
open MovingSourceOwnerSplit6814 MovingSourceOwnerRouting6814 MovingSourceNativeFactor6814
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814 MovingSourceLinearOwnerData6814
open RCN234 RCN156

variable {K : Type} [Field K]

def LinearRoute (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) : Prop :=
  J.degreeOf 1=1 ∧ carrierMap F (linearH J)≠0 ∧
  (wt residualSWeights (linearH J)≤5 ∧ wt residualYSWeights (linearH J)≤24 ∧
    wt residualTotalWeights (linearH J)≤330) ∧
  (wt residualSWeights (linearG J)≤7 ∧ wt residualYSWeights (linearG J)≤25 ∧
    wt residualTotalWeights (linearG J)≤331) ∧
  ∀ n, (F∣(linearH J)^(2*n)*RCN313.numerator K F n-
    (RCN313.polyH K F)^(2*n)*numerators (linearH J) (linearG J) n) ∧
    wt residualSWeights (numerators (linearH J) (linearG J) n)≤11*n ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+48*n ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+660*n

theorem retained_reduced_routes [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S Sz : Source F) (hS : Profile S 31 98 995 14 2 3) (hZ : Profile Sz 53 177 3429 24 6 8)
    (hFT : 3429<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433) :
    ∃ J, Irreducible J ∧ J∣S.P ∧ rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0 ∧
      (LinearRoute F J ∨ NativeRoute F J ∨
        ∃ D, Irreducible D ∧ (D∣S.P ∨ D∣Sz.P) ∧
          rootEvaluation (carrierMap F) (ratio (carrierMap F) F) D=0 ∧ IsRelPrime J D) := by
  have hPs := canonical_source_power F S (by rw [hS.2.2.1]; omega) hpos hsmall
    (by rw [hS.2.2.2.2.1]; omega)
  have hp3 : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3 ∣
      rootPolynomialMap (carrierMap F) S.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3 ∣ (asS S.P).map (carrierMap F)
    simpa only [Source.d,hS.2.2.2.2.1] using hPs.2
  have heval : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) S.P=0 :=
    Polynomial.dvd_iff_isRoot.mp ((dvd_pow_self _ (by decide : 3≠0)).trans hp3)
  obtain ⟨J,hJ,hJS,hJroot,hsplit⟩ := two_source_owner_split
    (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) S.P Sz.P
    (source_nonzero F S) (source_nonzero F Sz) heval
  refine ⟨J,hJ,hJS,hJroot,?_⟩
  rcases hsplit with huniq | hmixed
  · have hJne : rootPolynomialMap (carrierMap F) J≠0 := by
      intro hz
      have hd := map_dvd (rootPolynomialMap (carrierMap F)) hJS
      rw [hz,zero_dvd_iff] at hd
      exact hPs.1 hd
    have hdegree : 0<J.degreeOf 1 := by
      have hm := (Polynomial.rootMultiplicity_pos hJne).mpr hJroot
      have hh := Polynomial.natDegree_le_of_dvd
        ((rootPolynomialMap (carrierMap F) J).pow_rootMultiplicity_dvd (ratio (carrierMap F) F)) hJne
      simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
      have he : (rootPolynomialMap (carrierMap F) J).natDegree≤J.degreeOf 1 :=
        Polynomial.natDegree_map_le.trans_eq (asS_natDegree J)
      omega
    by_cases hl : J.degreeOf 1=1
    · exact Or.inl ⟨hl,linear_owner_reduced_tails F S Sz hS hZ hFT hpos hsmall
        J hJ hJS hl hJroot huniq.1 huniq.2.1⟩
    · exact Or.inr (Or.inl (unique_nonlinear_route F S Sz hS hZ hFT hpos hsmall
        J hJ hJS hJroot huniq.1 huniq.2.1 (by omega)))
  · exact Or.inr (Or.inr hmixed)

theorem helpers_or_reduced_routes [CharP K 2130706433]
    {N : Type} [Fintype N] (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 3429<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    (∃ Q, WholeSpaceSourceAlternative6814.ProperHelper F Q r y t nodes u0 u1) ∨
    (∃ Q, MovingSourceZSupplier6814.ProperHelper F Q r y t nodes u0 u1) ∨
    ∃ S : Source F, ∃ Sz : Source F,
      Profile S 31 98 995 14 2 3 ∧ Profile Sz 53 177 3429 24 6 8 ∧
      ∃ J, Irreducible J ∧ J∣S.P ∧ rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0 ∧
        (LinearRoute F J ∨ NativeRoute F J ∨
          ∃ D, Irreducible D ∧ (D∣S.P ∨ D∣Sz.P) ∧
            rootEvaluation (carrierMap F) (ratio (carrierMap F) F) D=0 ∧ IsRelPrime J D) := by
  rcases helpers_or_two_profiles nodes u0 u1 hN F Fact.out hFT r y t hr hy ht hF with
    hhelp | hhelp | ⟨S,Sz,hS,hZ⟩
  · exact Or.inl hhelp
  · exact Or.inr (Or.inl hhelp)
  · exact Or.inr (Or.inr ⟨S,Sz,hS,hZ,retained_reduced_routes F S Sz hS hZ hFT hpos hsmall⟩)

theorem linear_reduced_proper
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hdata : LinearRoute F J) (n : ℕ)
    (hproper : ¬F∣RCN313.numerator K F n) :
    ¬F∣numerators (linearH J) (linearG J) n := by
  intro hnew
  have hn := (carrierMap_zero_iff F _).mpr hnew
  have hc := (carrierMap_zero_iff F _).mpr ((hdata.2.2.2.2 n).1)
  simp only [map_sub,map_mul,map_pow,hn,mul_zero,sub_zero] at hc
  have hz := (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ hdata.2.1)
  exact hproper ((carrierMap_zero_iff F _).mp hz)

#print axioms retained_reduced_routes
#print axioms helpers_or_reduced_routes
#print axioms linear_reduced_proper
end
end ProximityPrize.SubmissionLower.MovingSourceReducedRoutes6814
