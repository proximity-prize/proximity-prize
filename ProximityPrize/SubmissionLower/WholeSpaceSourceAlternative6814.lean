import ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814

/-! Concrete 181255-agreement source alternative. The source is chosen
outside J^3 before taking the helper/retention alternative. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceKernel6814
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetClearedHelper
open SecondJetHelperWeights RCN234 RCN156

variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]

def ProperHelper (F Q : MvPolynomial (Fin 4) K) (r y t : ℕ)
    (nodes : N ↪ K) (u0 u1 : N → K) : Prop :=
  IsRelPrime F Q ∧
  (wt residualSWeights Q ≤ 31+14*(r-1) ∧
    wt residualYSWeights Q ≤ 98+14*(y-1) ∧
    wt residualTotalWeights Q ≤ 1700+14*(t-1)) ∧
  ∀ f : Polynomial K, f.natDegree ≤ 131071 → ∀ z : K, ∀ S : Finset N,
    181255 ≤ S.card → (∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z) →
    RCN319.specialization K f z F=0 → RCN319.specialization K f z Q=0

theorem helper_or_retained
    (nodes : N ↪ K) (u0 u1 : N → K)
    (P : WholeSpaceCube6814.Poly (K := K)) (hP : P≠0) (hb : Bounds P)
    (hc : ∀ i, MvPolynomial.X 0^72 ∣ SecondJetDifferentiation.substitute (K := K)
      (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) P))
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F)
    (hFT : 1700 < wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1 ≤ r) (hy : 1 ≤ y) (ht : 1 ≤ t)
    (hF : wt residualSWeights F ≤ r ∧ wt residualYSWeights F ≤ y ∧ wt residualTotalWeights F ≤ t) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      (3 ≤ (asS P).natDegree ∧ ∀ d ≤ 2, F ∣ helper P F (14-d) d) := by
  classical
  have hflags : ∀ e ∈ P.support, 2*e 1+e 3 ≤ 31 ∧
      e 1+e 2+e 3 ≤ 98 ∧ e 1+e 2+e 3+e 4 ≤ 1700 :=
    fun e he => ⟨(hb e he).1,(hb e he).2.2.1,(hb e he).2.2.2.1⟩
  have hS : ∀ e ∈ P.support, e 1 ≤ 14 := fun e he => (hb e he).2.1
  have hdegree : (asS P).natDegree ≤ 14 := by
    simpa using asS_derivative_degree P 14 0 hS
  have hfact : ∀ d ≤ 14, (d.factorial : K) ≠ 0 := by
    intro d hd
    exact SecondJetOwnShape.factorial_ne (K := K) d (by omega)
  by_cases hn : (asS P).natDegree < 3
  · left
    let n := (asS P).natDegree
    let Q := (asS P).leadingCoeff
    have hQ := SecondJetTotalAvoidance.leading_not_dvd P hP F 1700
      (fun e he => (hflags e he).2.2) hFT
    refine ⟨Q,hFi.isRelPrime_iff_not_dvd.mpr hQ.2,?_,?_⟩
    · have hw := derivative_coefficient_weights P 31 98 1700 0 n hflags
      simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
      change wt residualSWeights ((asS P).coeff n) ≤ 31+14*(r-1) ∧
        wt residualYSWeights ((asS P).coeff n) ≤ 98+14*(y-1) ∧
        wt residualTotalWeights ((asS P).coeff n) ≤ 1700+14*(t-1)
      omega
    · intro f hf z S hSc hvalues _
      have hv := source_derivative_vanish nodes u0 u1 P hb hc n (by dsimp [n]; omega)
        f hf z S hSc hvalues
      have htop := MovingFiberLeadingCoefficient6811.specialize_top P f z n
        (by intro j hj; rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero])
      rw [htop,nsmul_eq_mul] at hv
      change coefficientSpecialize f z ((asS P).coeff n)=0
      apply (mul_eq_zero.mp hv).resolve_left
      simpa only [map_natCast] using (Polynomial.C_ne_zero.mpr (hfact n hdegree))
  · by_cases hdiv : ∀ d ≤ 2, F ∣ helper P F (14-d) d
    · exact Or.inr ⟨by omega,hdiv⟩
    · left
      push_neg at hdiv
      obtain ⟨d,hd,hproper⟩ := hdiv
      refine ⟨helper P F (14-d) d,hFi.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hw := helper_weights P F 31 98 1700 14 d t y r
          (by omega) (by omega) (by omega) (by omega) hr hy ht hflags hF
        have hrr := Nat.mul_le_mul_right (r-1) (Nat.sub_le 14 d)
        have hyy := Nat.mul_le_mul_right (y-1) (Nat.sub_le 14 d)
        have htt := Nat.mul_le_mul_right (t-1) (Nat.sub_le 14 d)
        omega
      · intro f hf z S hSc hvalues hFzero
        exact helper_vanish P F (14-d) d (asS_derivative_degree P 14 d hS) f z hFzero
          (source_derivative_vanish nodes u0 u1 P hb hc d hd f hf z S hSc hvalues)

/-- No source-dimension or retained-root hypothesis: actual received-word
contact data produce either the standard proper helper or a proper
curvature pair with explicit support bounds. -/
theorem exists_helper_or_curvature_pair
    {E : Type} [Field E] [CharP E 2130706433]
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K := K)) (hJi : Irreducible J)
    (hmid : 25 ≤ weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9)
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F)
    (hFT : 1700 < wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1 ≤ r) (hy : 1 ≤ y) (ht : 1 ≤ t)
    (hF : wt residualSWeights F ≤ r ∧ wt residualYSWeights F ≤ y ∧ wt residualTotalWeights F ≤ t)
    (phi : MvPolynomial (Fin 4) K →+* E) (hphiF : phi F=0)
    (hH : phi (2*RCN313.polyH K F) ≠ 0)
    (hphiJ : (asS J).map phi ≠ 0)
    (hroot : ((asS J).map phi).rootMultiplicity (SecondJetCarrierDichotomy.ratio phi F)=1) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
    ∃ Q : WholeSpaceCube6814.Poly (K := K), Q≠0 ∧ IsRelPrime J Q ∧
      ((asS Q).map phi).eval (SecondJetCarrierDichotomy.ratio phi F)=0 ∧
      weightedTotalDegree totalWeights Q ≤ 1700 ∧
      weightedTotalDegree middleWeights Q ≤ 98 ∧
      weightedTotalDegree slopeWeights Q ≤ 31 ∧ Q.degreeOf 1 ≤ 14 := by
  obtain ⟨P,hP,hnot,hb,hc⟩ := exists_interpolant_not_dvd_cube nodes u0 u1 hN J hJi.ne_zero hmid hB
  rcases helper_or_retained nodes u0 u1 P hP hb hc F hFi hFT r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  right
  have hp : (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio phi F))^3 ∣
      (asS P).map phi := by
    by_cases hz : (asS P).map phi=0
    · rw [hz]; exact dvd_zero _
    exact SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd P F phi 14 2
      (fun e he => (hb e he).2.1) hphiF hH hz
      (SecondJetOwnShape.factorial_ne (K := E) 2 (by omega)) hret.2
  obtain ⟨e,he,Q,hPQ,hJQ⟩ := remainder_of_not_cube J P hnot
  have hQ : Q≠0 := by intro hz; exact hJQ (by rw [hz]; exact dvd_zero _)
  have hzero : ((asS Q).map phi).eval (SecondJetCarrierDichotomy.ratio phi F)=0 := by
    by_contra hn
    rw [hPQ,map_mul,map_pow,Polynomial.map_mul,Polynomial.map_pow] at hp
    have hh := UniqueCurvatureOwner6814.simple_unique_owner_exponent
      ((asS J).map phi) ((asS Q).map phi) _ 3 e hphiJ hn hroot hp
    omega
  have hw := weights_of_bounds P hb
  have hbound (w : Fin 5 → ℕ) (C : ℕ) (h : weightedTotalDegree w P ≤ C) :
      weightedTotalDegree w Q ≤ C := by
    rw [hPQ,weight_mul _ _ _ (pow_ne_zero _ hJi.ne_zero) hQ] at h
    omega
  have hd := hw.2.2.2.2
  rw [hPQ,MvPolynomial.degreeOf_mul_eq (pow_ne_zero _ hJi.ne_zero) hQ] at hd
  exact ⟨Q,hQ,hJi.isRelPrime_iff_not_dvd.mpr hJQ,hzero,
    hbound _ _ hw.2.1,hbound _ _ hw.2.2.1,hbound _ _ hw.2.2.2.1,by omega⟩

#print axioms helper_or_retained
#print axioms exists_helper_or_curvature_pair
end
end ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814
