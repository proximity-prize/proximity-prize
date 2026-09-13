import ProximityPrize.SubmissionLower.BoundaryTailSourceSound6807
import ProximityPrize.SubmissionLower.BoundaryTailBasePhase6807

namespace ProximityPrize.SubmissionLower.Lower80820.TenPhase
open ProximityPrize.Benchmark RCN095 RCN140 RCN156 RCN234 RCN238 RCN266 RCN319
open Lower80820.Oracle Lower80820.BatchPhase
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

/-- The numerical cap and defect receipts remain explicit; every source kernel
and the ten-step semantic composition are supplied by proved constructions. -/
theorem bound_all
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181324 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i+gamma*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80820)
    (cap : ℕ → FlagDegree → ℕ) (defect : ℕ → FlagDegree → ℕ)
    (hbase : StateLocalRegularBoundOn H selected Gamma ambient (cap 0))
    (hdefect : ∀ j, j < 10 → PhaseDefectSound (cap j) (sound j).source
      (sound j).potential (defect j))
    (hcap : ∀ j, j < 10 → PhaseCapEquation (cap j) (cap (j+1)) (sound j).source
      (sound j).potential (defect j)) :
    ∀ n, n ≤ 10 → StateLocalRegularBoundOn H selected Gamma ambient (cap n) := by
  intro n
  induction n with
  | zero => intro _; exact hbase
  | succ j ih =>
      intro hj
      exact stateLocalRegularBoundOn_onePhase (sound j) u0 u1 (kernel u0 u1 j)
        H selected Gamma ambient hdegree hagreement hno (cap j) (cap (j+1)) (defect j)
        (ih (by omega)) (hdefect j (by omega)) (hcap j (by omega))

end
end ProximityPrize.SubmissionLower.Lower80820.TenPhase
