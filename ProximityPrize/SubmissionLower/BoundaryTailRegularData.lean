import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.BoundaryTailProvider
import ProximityPrize.SubmissionLower.BoundaryTailRegularGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailRegularData
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
  agreement : ∀ gamma ∈ seeds, 181333 ≤
    (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card
  solution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0
  regular : ∀ gamma ∈ seeds,
    specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0
  noPencil : NoLargeSelectedPencil selected seeds w 80811

namespace Data
variable {nodes : I ↪ K} {u0 u1 : I → K}

def restrict (S : Data nodes u0 u1) (Delta : Finset K) (hsub : Delta ⊆ S.seeds) :
    Data nodes u0 u1 :=
  { S with seeds := Delta
           degree := fun gamma h => S.degree gamma (hsub h)
           agreement := fun gamma h => S.agreement gamma (hsub h)
           solution := fun gamma h => S.solution gamma (hsub h)
           regular := fun gamma h => S.regular gamma (hsub h)
           noPencil := noLargeSelectedPencil_mono S.selected S.seeds Delta w 80811 hsub S.noPencil }

def pair (S : Data nodes u0 u1) (R capY T : ℕ) : UnequalParameters :=
  ⟨262144,131071,181333,S.y,S.r,S.t,capY,R,T⟩

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

theorem proper_count (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (Q : MvPolynomial (Fin 4) K) (R capY T : ℕ) (hrel : IsRelPrime S.F Q)
    (hQ : Q.degreeOf 1 ≤ capY ∧ Q.degreeOf 2 ≤ R ∧ Q.degreeOf 3 ≤ T)
    (hgates : S.PairGates R capY T)
    (hzero : ∀ gamma ∈ S.seeds, specialization K (S.selected gamma) gamma Q=0) :
    S.seeds.card ≤ (S.pair R capY T).regularCountCap := by
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
    S.degree S.agreement (by simpa only [pair,UnequalParameters.errors,(show (262144 - 181333 : ℕ) = 80811 by decide +kernel),RCN327.w] using S.noPencil)
    S.solution S.regular hzero
  exact SecondJetPairBounds.count_le_cap (S.pair R capY T) S.F hF.1 hF.2.1 hF.2.2
    S.seeds.card (by change 0 < (181333 - 131071 : ℕ); decide +kernel) hcount

def normal (S : Data nodes u0 u1) : ℕ :=
  flagMixed (originalCumulativeFlag S.F) (cellFirstTail S.t S.y S.r) (BoundaryTailProvider.cellNormal S.t S.y S.r)

def moving (S : Data nodes u0 u1) (B U L k n0 : ℕ) : ℕ :=
  flagMixed (originalCumulativeFlag S.F) (cellFirstTail S.t S.y S.r)
    (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)

theorem retained_scaled (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (P : SecondJetSupport.Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0) (hB : 2*(n0-(k+1)) ≤ B)
    (hn : n0 ≤ (SecondJetCoefficients.asS P).natDegree)
    (hdiv : ∀ d ≤ k, S.F ∣ SecondJetClearedHelper.helper P S.F (s-d) d)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : (k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ S.seeds,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff) ≠ 0) :
    (k+1)*S.seeds.card ≤ (k+1)*S.normal+65539*S.moving B U L k n0 := by
  exact BoundaryTailRegularGeometry.regular_seed_bound_scaled
    S.D S.t S.y S.r S.Dlow S.Dchar S.tbound S.ybound S.rbound S.rpos S.ry S.yt
    S.F S.irreducible S.rdegree S.box S.support S.selected S.seeds Finset.univ nodes u0 u1
    nodes.injective.injOn (by simpa only [Finset.card_univ] using hI)
    S.degree S.agreement S.solution S.regular S.noPencil
    P B U L s k n0 hS hP hBU hUL hdn hB hn hdiv h2 hfact hgood

end Data
end
end ProximityPrize.SubmissionLower.BoundaryTailRegularData

