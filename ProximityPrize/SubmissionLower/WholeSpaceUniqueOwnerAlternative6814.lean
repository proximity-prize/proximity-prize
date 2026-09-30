import ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814
import ProximityPrize.SubmissionLower.MovingSourceMixedOwnerRouting6814
namespace ProximityPrize.SubmissionLower.WholeSpaceUniqueOwnerAlternative6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceCarrierField6814 MovingSourceOwnerSplit6814
open MovingSourceCoupledClearing6814 MovingSourceNativeEnvelope6814
open MovingSourceMixedOwnerRouting6814 MovingSourceNativeFactor6814
open WholeSpacePowerCover6814
open SecondJetCoefficients SecondJetCarrierDichotomy
open RCN234 RCN156

variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]

def multiplicity (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J : Poly (K := K)) : ℕ :=
  ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)

end
end ProximityPrize.SubmissionLower.WholeSpaceUniqueOwnerAlternative6814
