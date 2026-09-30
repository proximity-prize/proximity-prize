import ProximityPrize.SubmissionLower.MovingSourceTripleOwnerExclusion6814
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

end
end ProximityPrize.SubmissionLower.MovingSourceMixedOwnerRouting6814
