import ProximityPrize.SubmissionLower.MovingSourceReducedSeedTails6814
namespace ProximityPrize.SubmissionLower.MovingSourceProperSeedCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN121 RCN135 RCN136 RCN238 RCN243 RCN244 RCN264
open MovingSourceGammaProjections6814 MovingSourceLinearCycleFamily6814 MovingSourceProjectionFamily6814
open MovingSourceFrameZeroCount6814 MovingSourceReducedSeedTails6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814

private theorem sum_weighted_three {A : Type} [Fintype A]
    (m z u v : A → ℕ) (a b c : ℕ) :
    (∑ i, m i*(a*z i+b*u i+c*v i))=
      a*(∑ i, m i*z i)+b*(∑ i, m i*u i)+c*(∑ i, m i*v i) := by
  simp only [Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_left_comm]

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev stageSeeds (S : Stage K I Gamma x p flag errorCap stageSupport) (C : FirstTailComponent S) :=
  componentSeeds (GenericField K) S.G (globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (regularitySurface (polynomialEmbedding K) S.F) Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C

abbrev ProperLinearComponent
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H : MvPolynomial (Fin 4) K) :=
  {C : FirstTailComponent S //
    Transcendental (GenericField K) (coordinate (GenericField K) C.1 2) ∧
    surfaceMap (polynomialEmbedding K) H∉C.1 ∧
    ∃ delay, 1≤delay ∧ delay≤localMultiplicity S (canonicalLocalDVRFamily S hfirst) C ∧
      globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1+delay)∉C.1}

end
end ProximityPrize.SubmissionLower.MovingSourceProperSeedCount6814
