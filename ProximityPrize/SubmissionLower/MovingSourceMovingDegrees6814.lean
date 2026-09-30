import ProximityPrize.SubmissionLower.MovingSourceTargetField6814
namespace ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
local instance : Algebra (RatFunc Omega) OmegaT := targetAlgebra Omega
local instance : IsScalarTower Omega (RatFunc Omega) OmegaT := target_tower Omega

def baseCarrier (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) F
def baseH (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) (polyH K F)
def baseG (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) (polyG K F)

def targetCut (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega)
    (Q A : MvPolynomial (Fin 3) Omega) : MvPolynomial (Fin 3) OmegaT :=
  eliminatedCut n (fun j => lift (coeff j)) (lift Q) (lift A) (initialCoordinate Omega)

theorem scalar_eq_lift (P : MvPolynomial (Fin 3) Omega) : scalarPolynomialMap Omega OmegaT P=lift P := by
  rw [scalarPolynomialMap,←coefficientEmbedding_eq_algebraMap Omega]

theorem targetCut_small_flag
    (F : MvPolynomial (Fin 4) K) (a b s n : ℕ) (center : FlagDegree)
    (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega) (flags : Fin (n+1) → FlagDegree)
    (hH : PolynomialInFlag ⟨a,b+1,s+1⟩ (baseH F))
    (hG : PolynomialInFlag ⟨a,b,s+3⟩ (baseG F))
    (hcoeff : ∀ j, PolynomialInFlag (flags j) (coeff j))
    (heq : ∀ j, flags j+(n-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree)=center+n • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree))
    (Q A : MvPolynomial (Fin 3) Omega)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag (center+n • (⟨a,b+1,s+2⟩ : FlagDegree)) (targetCut n coeff Q A) := by
  have hh := (fiber_small_flags (E:=OmegaT) a b s n center (baseH F) (baseG F) Q A coeff flags
    hH hG hQ hA hcoeff heq).2
  simpa only [fiberCut,scalar_eq_lift,target_variable,targetCut] using hh

end
end ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814
