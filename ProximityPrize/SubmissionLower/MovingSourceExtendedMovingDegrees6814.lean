import ProximityPrize.SubmissionLower.MovingSourceExtendedPointCount6814
namespace ProximityPrize.SubmissionLower.MovingSourceExtendedMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedThickPair6814 MovingSourceExtendedPointCount6814

variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta : GenericField K →+* E)
local notation "Omega" => E
local notation "OmegaT" => GenericField E
local notation "phi" => RingHom.comp (coefficientEmbedding E) (codeMap eta)
local notation "lift" => MvPolynomial.map (coefficientEmbedding E)
local instance : Algebra (RatFunc E) OmegaT := targetAlgebra E
local instance : IsScalarTower E (RatFunc E) OmegaT := target_tower E

def frozenCarrier (F : MvPolynomial (Fin 4) K) := surfaceMap (codeMap eta) F
def frozenH (F : MvPolynomial (Fin 4) K) := surfaceMap (codeMap eta) (polyH K F)
def frozenG (F : MvPolynomial (Fin 4) K) := surfaceMap (codeMap eta) (polyG K F)
abbrev ExtendedFactorFamily (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) E)
    (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) E) :=
  RegularComponent E G (filteredCut n coeff (frozenH eta F) (frozenG eta F)) (frozenH eta F)

def extendedTargetCut (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) E)
    (Q A : MvPolynomial (Fin 3) E) : MvPolynomial (Fin 3) OmegaT :=
  eliminatedCut n (fun j => lift (coeff j)) (lift Q) (lift A) (initialCoordinate E)

theorem scalar_eq_lift (P : MvPolynomial (Fin 3) E) : scalarPolynomialMap E OmegaT P=lift P := by
  rw [scalarPolynomialMap,←coefficientEmbedding_eq_algebraMap E]

theorem lift_frozen (P : MvPolynomial (Fin 4) K) :
    lift (surfaceMap (codeMap eta) P)=surfaceMap phi P := by
  simp only [surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

theorem eval_lift_embedding (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (f : CoordinateField E C →ₐ[E] OmegaT) (P : MvPolynomial (Fin 3) E) :
    MvPolynomial.eval (embeddingPoint C f) (lift P)=f (coordinateEvaluation E C P) := by
  rw [MvPolynomial.eval_map,coefficientEmbedding_eq_algebraMap E]
  exact AlgHom.congr_fun (embeddingPoint_aeval C f) P

end
end ProximityPrize.SubmissionLower.MovingSourceExtendedMovingDegrees6814
