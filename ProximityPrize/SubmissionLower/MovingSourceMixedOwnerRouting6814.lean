import ProximityPrize.SubmissionLower.MovingSourceTripleOwnerExclusion6814

/-! Prioritize owners inside the same small source, where the coupled
counter applies; otherwise retain actual unique ownership of that source.
The triple-root obstruction is connected to actual divisors of its P. -/
namespace ProximityPrize.SubmissionLower.MovingSourceMixedOwnerRouting6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MovingSourceOwnerSplit6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceCoupledClearing6814 MovingSourceTripleOwnerExclusion6814
open WholeSpaceCube6814 WholeSpaceCubeUniform6814
variable {K E : Type} [Field K] [Field E]
local notation "Poly5" => MvPolynomial (Fin 5) K

theorem small_source_first_split (ev : Poly5 →+* E) (P : Poly5) (hP : P≠0) (hz : ev P=0) :
    ∃ J, Irreducible J ∧ J∣P ∧ ev J=0 ∧
      (UniqueOwner ev J P ∨ ∃ D, Irreducible D ∧ D∣P ∧ ev D=0 ∧ IsRelPrime J D) := by
  obtain ⟨J,hJ,hJP,hroot,hsplit⟩ := two_source_owner_split ev P P hP hP hz
  refine ⟨J,hJ,hJP,hroot,?_⟩
  rcases hsplit with huni | ⟨D,hD,hDP,hdroot,hcop⟩
  · exact Or.inl huni.1
  · exact Or.inr ⟨D,hD,hDP.elim id id,hdroot,hcop⟩

theorem small_source_factor_triple_excluded [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 2985<RCN234.wt RCN156.residualTotalWeights F)
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (J : Poly5) (hJ : Irreducible J) (hdiv : J∣S.P)
    (hs : order J=3 ∨ order J=4) :
    ((SecondJetCoefficients.asS J).map (MovingSourceCarrierField6814.carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (MovingSourceCarrierField6814.carrierMap F) F)<3 := by
  have hP := source_nonzero F S
  obtain ⟨Q,hQ⟩ := hdiv
  have hQne : Q≠0 := by intro hz; apply hP; rw [hQ,hz,mul_zero]
  have hcap := (MovingSourceOwnerRouting6814.source_caps F S).2.2.1
  rw [hS.2.2.1,hQ,weight_mul _ _ _ hJ.ne_zero hQne] at hcap
  have hJcap : total J≤995 := by
    change MvPolynomial.weightedTotalDegree totalWeights J≤995
    omega
  exact small_cubic_quartic_rootMultiplicity_lt_three F hFT J hJ hJcap hs

#print axioms small_source_first_split
#print axioms small_source_factor_triple_excluded
end
end ProximityPrize.SubmissionLower.MovingSourceMixedOwnerRouting6814
