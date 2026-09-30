import ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814
namespace ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open MvPolynomial SecondJetCoefficients SecondJetCarrierDichotomy
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingFiberThreeSources6811
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 MovingSourceOwnerSplit6814
open MovingSourceNativeEnvelope6814 MovingSourceTwoProfiles6814
open RCN234 RCN156

variable {K : Type} [Field K]

theorem source_caps (F : MvPolynomial (Fin 4) K) (S : Source F) :
    weightedTotalDegree slopeWeights S.P≤S.B ∧ weightedTotalDegree middleWeights S.P≤S.U ∧
      weightedTotalDegree totalWeights S.P≤S.T ∧ S.P.degreeOf 1≤S.s := by
  refine ⟨Finset.sup_le ?_,Finset.sup_le ?_,Finset.sup_le ?_,MvPolynomial.degreeOf_le_iff.mpr S.hS⟩
  · intro e he
    simpa [weight_coords,slopeWeights,Nat.mul_comm] using (S.hshape e he).1
  · intro e he
    simpa [weight_coords,middleWeights] using (S.hshape e he).2.1
  · intro e he
    simpa [weight_coords,totalWeights] using (S.hshape e he).2.2

end
end ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814
