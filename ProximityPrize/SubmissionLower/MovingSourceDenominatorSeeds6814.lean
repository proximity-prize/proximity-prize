import ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814
import ProximityPrize.SubmissionLower.MovingSourceGenericField6814
namespace ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN001 RCN051 RCN068 RCN074 RCN086 RCN095 RCN135 RCN136 RCN238 RCN243 RCN244 RCN264
open MovingSourceLinearFlow6814 MovingSourceCarrierField6814
open MovingSourceFlatBaseChange6814 MovingSourceGenericField6814 MovingSourceReducedGamma6814

variable {K I : Type} [Field K]

theorem surfaceMap_relPrime (F H : MvPolynomial (Fin 4) K) (hF : F≠0) (hrel : IsRelPrime F H) :
    IsRelPrime (surfaceMap (polynomialEmbedding K) F) (surfaceMap (polynomialEmbedding K) H) := by
  have hFc : collectX K F≠0 := fun hz => hF ((collectX K).injective (hz.trans (map_zero _).symm))
  exact generic_coefficient_map_relPrime K (collectX K F) (collectX K H) hFc
    (isRelPrime_equiv (collectX K).toRingEquiv F H hrel)

variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

def denominatorSeeds (S : Stage K I Gamma x p flag errorCap stageSupport)
    (J : WholeSpaceCube6814.Poly (K:=K)) : Finset K :=
  Gamma.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
    (surfaceMap (polynomialEmbedding K) (linearH J))=0)

end
end ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814
