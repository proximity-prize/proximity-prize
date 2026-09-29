import ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814
import ProximityPrize.SubmissionLower.MovingSourceMixedOwnerRouting6814

/-! Nonlinear native failure supplies a genuine new proper helper or a
coprime owning cofactor with its full remaining multiplicity. -/
namespace ProximityPrize.SubmissionLower.WholeSpacePowerAlternative6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpaceSourceKernel6814 WholeSpaceSourceAlternative6814
open WholeSpacePowerBox6814 WholeSpacePowerCover6814 WholeSpacePowerSupplier6814
open MovingSourceNativeEnvelope6814 SecondJetCoefficients
open RCN234 RCN156

variable {K E N : Type} [Field K] [Field E]
variable [CharP K 2130706433] [CharP E 2130706433] [Fintype N]

/-- The entire avoidance-to-retention handoff. Multiplicity is retained as
3-e*m, rather than weakening the conclusion to one common root. Coupled
factor/cofactor degree charges are kept for the geometric counter. -/
theorem exists_helper_or_weighted_pair
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : Poly (K := K)) (hJi : Irreducible J) (m : ℕ) (hm : 0<m)
    (hs : 2≤J.degreeOf 1) (hms : m≤J.degreeOf 1)
    (h2s : 2*J.degreeOf 1≤weightedTotalDegree slopeWeights J)
    (hbu : weightedTotalDegree slopeWeights J≤weightedTotalDegree middleWeights J)
    (hut : weightedTotalDegree middleWeights J≤weightedTotalDegree totalWeights J)
    (hB : copies3 m*weightedTotalDegree slopeWeights J≤31)
    (hU : copies3 m*weightedTotalDegree middleWeights J≤98)
    (hT : copies3 m*weightedTotalDegree totalWeights J≤995)
    (hex : 3≤m → 5≤J.degreeOf 1)
    (hfail : 3*272069082261391681*m≤native m (J.degreeOf 1)
      (weightedTotalDegree slopeWeights J) (weightedTotalDegree middleWeights J)
      (weightedTotalDegree totalWeights J))
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F)
    (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (phi : MvPolynomial (Fin 4) K →+* E) (hphiF : phi F=0)
    (hH : phi (2*RCN313.polyH K F)≠0)
    (hphiJ : (asS J).map phi≠0)
    (hroot : ((asS J).map phi).rootMultiplicity (SecondJetCarrierDichotomy.ratio phi F)=m) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
    ∃ e<copies3 m, ∃ Q : Poly (K := K), Q≠0 ∧ IsRelPrime J Q ∧ 0<3-e*m ∧
      (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio phi F))^(3-e*m)∣(asS Q).map phi ∧
      e*weightedTotalDegree totalWeights J+weightedTotalDegree totalWeights Q≤1700 ∧
      e*weightedTotalDegree middleWeights J+weightedTotalDegree middleWeights Q≤98 ∧
      e*weightedTotalDegree slopeWeights J+weightedTotalDegree slopeWeights Q≤31 ∧
      e*J.degreeOf 1+Q.degreeOf 1≤14 := by
  obtain ⟨a,haq,ha,hgood⟩ := native_failure_has_box m (J.degreeOf 1)
    (weightedTotalDegree slopeWeights J) (weightedTotalDegree middleWeights J)
    (weightedTotalDegree totalWeights J) hm hs hms h2s hbu hut hB hU hT hex hfail
  obtain ⟨P,hP,hnot,hb,hcontact⟩ := exists_interpolant_not_dvd_power nodes u0 u1 hN J hJi.ne_zero a ha hgood
  rw [haq] at hnot
  rcases helper_or_retained nodes u0 u1 P hP hb hcontact F hFi hFT r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  have hp : (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio phi F))^3∣(asS P).map phi := by
    by_cases hz : (asS P).map phi=0
    · rw [hz]; exact dvd_zero _
    exact SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd P F phi 14 2
      (fun e he => (hb e he).2.1) hphiF hH hz
      (SecondJetOwnShape.factorial_ne (K := E) 2 (by omega)) hret.2
  obtain ⟨e,he,Q,hPQ,hQ,hcop⟩ := cofactor_of_not_power J P hJi (copies3 m) hnot
  have hpower := cofactor_root_power (MovingSourceOwnerSplit6814.rootPolynomialMap phi)
    (SecondJetCarrierDichotomy.ratio phi F) J P Q e m hPQ hphiJ hroot hp
  have hw := weights_of_bounds P hb
  have hbound (w : Fin 5 → ℕ) (C : ℕ) (h : weightedTotalDegree w P≤C) :
      e*weightedTotalDegree w J+weightedTotalDegree w Q≤C := by
    rwa [hPQ,weight_mul _ _ _ (pow_ne_zero _ hJi.ne_zero) hQ,weight_pow _ _ hJi.ne_zero] at h
  have hd := hw.2.2.2.2
  rw [hPQ,MvPolynomial.degreeOf_mul_eq (pow_ne_zero _ hJi.ne_zero) hQ,
    MvPolynomial.degreeOf_pow_eq _ _ _ hJi.ne_zero] at hd
  exact Or.inr ⟨e,he,Q,hQ,hcop,residual_order_positive m e hm he,hpower,
    hbound _ _ hw.2.1,hbound _ _ hw.2.2.1,hbound _ _ hw.2.2.2.1,hd⟩

#print axioms exists_helper_or_weighted_pair
end
end ProximityPrize.SubmissionLower.WholeSpacePowerAlternative6814
