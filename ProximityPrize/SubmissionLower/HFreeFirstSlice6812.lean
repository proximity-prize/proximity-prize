import ProximityPrize.SubmissionLower.ActiveSliceAssembly6807
namespace ProximityPrize.SubmissionLower.HFreeFirstSlice6812
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
local notation "w" => RCN326.w

def hfreeFlag (r v z : ℕ) (C0 : FlagDegree) : FlagDegree :=
  (2*(w+1)) • (⟨z,v,r-1⟩ : FlagDegree) + 3 • C0

section Slice
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

structure HFreeSliceBudget (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (C0 : FlagDegree) : Prop where
  pole_le : ∀ W : Finset (Place E (CoordinateField E C)),
    3 * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
    ∑ nu ∈ W, (((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) nu +
        2*RCN026.zeroOrder E (CoordinateField E C) nu
          (SecondJetComponentRoots.coefficientMap phi C (polyH K F))) +
      3*flagPole nu.val (coordinate E C) C0)

end Slice

section Stage
variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "φE" => RingHom.comp (algebraMap (GenericField K) E) (polynomialEmbedding K)

variable [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

end Stage
end
end ProximityPrize.SubmissionLower.HFreeFirstSlice6812
