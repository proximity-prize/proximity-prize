import ProximityPrize.SubmissionLower.MovingFiberSourceSound6811

namespace ProximityPrize.SubmissionLower.Lower80860.TenPhase
open ProximityPrize.Benchmark RCN095 RCN140 RCN156 RCN234 RCN238 RCN266 RCN319
open Lower80860.Oracle Lower80860.BatchPhase
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

/-- The exact compact10 ordering: seven distinct sources, then repeat 3,4,5. -/
def sound : ℕ → PhaseSourceSound
  | 0 => SourceSound.Phase00.sound
  | 1 => SourceSound.Phase01.sound
  | 2 => SourceSound.Phase02.sound
  | 3 => SourceSound.Phase03.sound
  | 4 => SourceSound.Phase04.sound
  | 5 => SourceSound.Phase05.sound
  | 6 => SourceSound.Phase06.sound
  | 7 => SourceSound.Phase03.sound
  | 8 => SourceSound.Phase04.sound
  | _+9 => SourceSound.Phase05.sound

def kernel (u0 u1 : I → K) (j : ℕ) : PhaseKernelRealization (sound j) u0 u1 :=
  match j with
  | 0 => SourceSound.Phase00.kernel u0 u1
  | 1 => SourceSound.Phase01.kernel u0 u1
  | 2 => SourceSound.Phase02.kernel u0 u1
  | 3 => SourceSound.Phase03.kernel u0 u1
  | 4 => SourceSound.Phase04.kernel u0 u1
  | 5 => SourceSound.Phase05.kernel u0 u1
  | 6 => SourceSound.Phase06.kernel u0 u1
  | 7 => SourceSound.Phase03.kernel u0 u1
  | 8 => SourceSound.Phase04.kernel u0 u1
  | _+9 => SourceSound.Phase05.kernel u0 u1

end
end ProximityPrize.SubmissionLower.Lower80860.TenPhase

#print axioms ProximityPrize.SubmissionLower.Lower80860.TenPhase.kernel
