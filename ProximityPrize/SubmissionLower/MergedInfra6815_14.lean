import ProximityPrize.SubmissionLower.MergedInfra6815_9
import ProximityPrize.SubmissionLower.MergedInfra6815_12
import ProximityPrize.SubmissionLower.MergedInfra6815_6
import ProximityPrize.SubmissionLower.BoundaryTailGates
import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.MergedInfra6815_10
set_option Elab.async false
section MergedPart0
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
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
open scoped Classical BigOperators
open RCN002 RCN046 RCN057 RCN074 RCN084 RCN085 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTransportC2 LocatorHybridTailProvider
open BoundaryTailProvider CommonLinearChannels6807 MovingFiberThreeSources6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap : ℕ}
local notation "Ω" => GenericField K

def rawFirstFlag (t y r : ℕ) : FlagDegree :=
  RCN198.center (cellA t y) (cellB y r) (cellS r) +
    w • (⟨cellA t y,cellB y r+1,cellS r+2⟩ : FlagDegree)

def hfreeFirst (t y r : ℕ) : FlagDegree :=
  HFreeFirstSlice6812.hfreeFlag r (y-r) (t-y) unitAllFlag

def numerator {F : MvPolynomial (Fin 4) K} (source : Fin 3 → Source F)
    (scale t y r : ℕ) (flag : FlagDegree) : ℕ :=
  scale/3*flagMixed flag (hfreeFirst t y r) (cellNormal t y r) +
    ∑ j : Fin 3, (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(source j).d))+
      65539*weight (rawFirstFlag t y r) j*(scale/(source j).d))*
      flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag

def channel {t y r : ℕ}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r))
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag < p) :
    Fin 3 → MvPolynomial (Fin 3) Ω :=
  let common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed
  ![CommonLinearChannels6807.linearZ,CommonLinearChannels6807.linearU common.lam,
    CommonLinearChannels6807.linearA common.mu common.lam]

end
end ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingFiberFixedStage6811
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider LocatorHybridTransportC2
open BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

end
end ProximityPrize.SubmissionLower.MovingFiberFixedStage6811
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingFiberRegularGeometry6811
open scoped Classical BigOperators
open RCN081 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN137 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN319 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider LocatorHybridTransportC2
open BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

end
end ProximityPrize.SubmissionLower.MovingFiberRegularGeometry6811
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingFiberRegularData6811
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN260 RCN174 RCN275 RCN327
open RCN156 RCN234 LocatorHybridCells LocatorHybridCellsC1 RCN130 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

structure Data (nodes : I ↪ K) (u0 u1 : I → K) where
  D : ℕ
  t : ℕ
  y : ℕ
  r : ℕ
  Dlow : 131072 ≤ D
  Dchar : D < 2130706433
  tbound : t ≤ 7501
  ybound : y ≤ 142
  rbound : r ≤ 31
  rpos : 3 ≤ r
  ry : r+2 ≤ y
  yt : y+2 ≤ t
  F : MvPolynomial (Fin 4) K
  irreducible : Irreducible F
  rdegree : 0 < F.degreeOf 2
  box : F ∈ globalCoefficientBox K D w t r
  support : ResidualSupportData (cellSupport t y r) F
  selected : K → Polynomial K
  seeds : Finset K
  degree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w
  agreement : ∀ gamma ∈ seeds, 181265 ≤
    (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card
  solution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0
  regular : ∀ gamma ∈ seeds,
    specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0
  noPencil : NoLargeSelectedPencil selected seeds w 80879

namespace Data
variable {nodes : I ↪ K} {u0 u1 : I → K}

def restrict (S : Data nodes u0 u1) (Delta : Finset K) (hsub : Delta ⊆ S.seeds) :
    Data nodes u0 u1 :=
  { S with seeds := Delta
           degree := fun gamma h => S.degree gamma (hsub h)
           agreement := fun gamma h => S.agreement gamma (hsub h)
           solution := fun gamma h => S.solution gamma (hsub h)
           regular := fun gamma h => S.regular gamma (hsub h)
           noPencil := noLargeSelectedPencil_mono S.selected S.seeds Delta w 80879 hsub S.noPencil }

def pair (S : Data nodes u0 u1) (R capY T : ℕ) : UnequalParameters :=
  ⟨262144,131071,181265,S.y,S.r,S.t,capY,R,T⟩

def PairGates (S : Data nodes u0 u1) (R capY T : ℕ) : Prop :=
  (S.pair R capY T).mixedCost.y < 2130706433 ∧
  (S.pair R capY T).mixedCost.r < 2130706433 ∧
  (S.pair R capY T).mixedCost.z < 2130706433

theorem weights (S : Data nodes u0 u1) :
    wt residualSWeights S.F ≤ S.r ∧ wt residualYSWeights S.F ≤ S.y ∧
      wt residualTotalWeights S.F ≤ S.t := by
  have hs : cellS S.r+2 = S.r := by have := S.rpos; dsimp [cellS]; omega
  have hy : cellB S.y S.r+cellS S.r+3 = S.y := by have := S.ry; dsimp [cellB,cellS]; omega
  have ht : cellA S.t S.y+cellB S.y S.r+cellS S.r+3 = S.t := by
    have := S.yt; dsimp [cellA]; omega
  have h := S.support
  exact ⟨by simpa only [cellSupport,RCN198.support,hs] using h.s_weight,
    by simpa only [cellSupport,RCN198.support,hy] using h.ys_weight,
    by simpa only [cellSupport,RCN198.support,ht] using h.total_weight⟩

theorem proper_count_left (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (Q : MvPolynomial (Fin 4) K) (R capY T : ℕ) (hrel : IsRelPrime S.F Q)
    (hQ : Q.degreeOf 1 ≤ capY ∧ Q.degreeOf 2 ≤ R ∧ Q.degreeOf 3 ≤ T)
    (hgates : S.PairGates R capY T)
    (hzero : ∀ gamma ∈ S.seeds, specialization K (S.selected gamma) gamma Q=0) :
    S.seeds.card ≤ AsymmetricHelper.leftRegularCountCap (S.pair R capY T) := by
  have hF := SecondJetPairBounds.degree_caps_of_weights S.F S.r S.y S.t S.weights
  have hcount := SecondJetProperCounting.regular_seed_bound_left
    (S.pair R capY T) S.F Q S.irreducible S.rdegree hrel 2130706433
    hF.1 hF.2.1 hF.2.2 hQ.1 hQ.2.1 hQ.2.2 (by have := S.rpos; dsimp [pair]; omega)
    (by have := S.ybound; dsimp [pair]; omega)
    (by have := S.rbound; dsimp [pair]; omega)
    (by have := S.tbound; dsimp [pair]; omega)
    hgates.1 hgates.2.1 hgates.2.2 S.selected S.seeds Finset.univ nodes u0 u1
    nodes.injective.injOn (by simpa only [Finset.card_univ,pair] using hI)
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    S.degree S.agreement (by simpa only [pair,UnequalParameters.errors,
      (show (262144 - 181265 : ℕ) = 80879 by decide),RCN327.w] using S.noPencil)
    S.solution S.regular hzero
  exact SecondJetPairBounds.count_le_left_cap (S.pair R capY T) S.F hF.1 hF.2.1 hF.2.2
    S.seeds.card (by change 0 < (181265 - 131071 : ℕ); decide) hcount

end Data
end
end ProximityPrize.SubmissionLower.MovingFiberRegularData6811
end MergedPart4
