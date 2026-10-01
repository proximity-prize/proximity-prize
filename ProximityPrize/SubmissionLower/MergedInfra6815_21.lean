import ProximityPrize.SubmissionLower.MergedInfra6815_14
import ProximityPrize.SubmissionLower.MergedInfra6815_6
import ProximityPrize.SubmissionLower.BoundaryTailGates
import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_15
import ProximityPrize.SubmissionLower.MergedInfra6815_18
import ProximityPrize.SubmissionLower.MergedInfra6815_16
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingFiberFixedStage6815
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
end ProximityPrize.SubmissionLower.MovingFiberFixedStage6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingFiberRegularGeometry6815
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
end ProximityPrize.SubmissionLower.MovingFiberRegularGeometry6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingFiberRegularData6815
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
  agreement : ∀ gamma ∈ seeds, 181245 ≤
    (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card
  solution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0
  regular : ∀ gamma ∈ seeds,
    specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0
  noPencil : NoLargeSelectedPencil selected seeds w 80899

namespace Data
variable {nodes : I ↪ K} {u0 u1 : I → K}

def restrict (S : Data nodes u0 u1) (Delta : Finset K) (hsub : Delta ⊆ S.seeds) :
    Data nodes u0 u1 :=
  { S with seeds := Delta
           degree := fun gamma h => S.degree gamma (hsub h)
           agreement := fun gamma h => S.agreement gamma (hsub h)
           solution := fun gamma h => S.solution gamma (hsub h)
           regular := fun gamma h => S.regular gamma (hsub h)
           noPencil := noLargeSelectedPencil_mono S.selected S.seeds Delta w 80899 hsub S.noPencil }

def pair (S : Data nodes u0 u1) (R capY T : ℕ) : UnequalParameters :=
  ⟨262144,131071,181245,S.y,S.r,S.t,capY,R,T⟩

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
      (show (262144 - 181245 : ℕ) = 80899 by decide),RCN327.w] using S.noPencil)
    S.solution S.regular hzero
  exact SecondJetPairBounds.count_le_left_cap (S.pair R capY T) S.F hF.1 hF.2.1 hF.2.2
    S.seeds.card (by change 0 < (181245 - 131071 : ℕ); decide) hcount

end Data
end
end ProximityPrize.SubmissionLower.MovingFiberRegularData6815
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingFiberProfile6815
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider
open MovingFiberRegularData6815 MovingFiberThreeSources6811 MovingFiberInterpolation6815 MovingFiberTotalAvoidance6815
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

structure Params where
  m : ℕ
  B : ℕ
  s : ℕ
  U : ℕ
  L : ℕ
  k : ℕ
  n0 : ℕ
  deriving DecidableEq, Repr

def Params.d (P : Params) : ℕ := P.k+1
def Params.flag (P : Params) : FlagDegree := SecondJetRelaxedFlag.budgetFlag P.B P.U P.L P.d P.n0
def Params.WellFormed (P : Params) : Prop :=
  2*P.s ≤ P.B ∧ P.B ≤ P.U ∧ P.U ≤ P.L ∧ P.k ≤ P.s ∧ P.s < P.m ∧
    P.k+1 ≤ P.n0 ∧ 2*(P.n0-(P.k+1)) ≤ P.B ∧ P.s < 2130706433
def number (cfg : Fin 3 → Params) (scale t y r : ℕ) (f : FlagDegree) : ℕ :=
  scale/3*flagMixed f (MovingFiberRetainedStage6811.hfreeFirst t y r) (cellNormal t y r) +
    ∑ j : Fin 3, (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(cfg j).d))+
      65539*weight (MovingFiberRetainedStage6811.rawFirstFlag t y r) j*(scale/(cfg j).d))*
      flagMixed f (MovingFiberThreeSources6811.direction j) (cfg j).flag

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {nodes : I ↪ K} {u0 u1 : I → K}

def helperCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair (P.B+P.s*(S.r-1)) (P.U+P.s*(S.y-1)) (P.L+P.s*(S.t-1)))
def coefficientCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair P.B P.U P.L)
def bound (S : Data nodes u0 u1) (cfg : Fin 3 → Params) (scale : ℕ) : ℕ :=
  max (Finset.univ.sup (fun j : Fin 3 => helperCap S (cfg j)))
    (number cfg scale S.t S.y S.r (originalCumulativeFlag S.F)/scale +
      ∑ j : Fin 3, coefficientCap S (cfg j))

end
end ProximityPrize.SubmissionLower.MovingFiberProfile6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingFiberCatalog6815
open MovingFiberProfile6815 MovingFiberInterpolation6815
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

local instance (P : Params) : Decidable P.WellFormed := by
  unfold Params.WellFormed
  infer_instance

def source0 : Params := ⟨132,54,24,180,1903,5,7⟩
def source1 : Params := ⟨134,56,25,180,3131,6,8⟩
def source2 : Params := ⟨136,56,25,185,2837,6,8⟩
def source3 : Params := ⟨116,46,21,158,3120,5,7⟩
def source4 : Params := ⟨114,45,21,155,3523,5,7⟩
def source5 : Params := ⟨158,63,29,215,3303,7,10⟩
def source6 : Params := ⟨166,73,34,226,3437,8,9⟩
def source7 : Params := ⟨114,47,21,154,3146,5,7⟩
def source8 : Params := ⟨142,56,26,193,3010,6,9⟩
def source9 : Params := ⟨174,76,36,236,2961,8,9⟩
def source10 : Params := ⟨170,71,32,231,3399,8,10⟩
def source11 : Params := ⟨98,41,19,132,2704,4,6⟩
def source12 : Params := ⟨142,59,27,193,2625,6,9⟩
def source13 : Params := ⟨158,69,32,214,2607,7,8⟩
def source14 : Params := ⟨146,58,27,198,2709,6,9⟩
def source15 : Params := ⟨98,41,19,133,2580,4,6⟩
def source16 : Params := ⟨150,60,28,204,2457,6,9⟩
def source17 : Params := ⟨162,71,33,218,2511,7,8⟩
def source18 : Params := ⟨114,47,22,155,3060,5,7⟩
def source19 : Params := ⟨166,66,31,226,2877,7,10⟩
def source20 : Params := ⟨174,76,36,237,2938,8,9⟩
def source21 : Params := ⟨111,46,22,151,3572,5,7⟩
def source22 : Params := ⟨189,83,39,256,3383,9,10⟩
def source23 : Params := ⟨114,45,20,155,3507,5,7⟩
def source24 : Params := ⟨190,84,40,258,3307,9,10⟩
def source25 : Params := ⟨111,46,21,151,3548,5,7⟩
def source26 : Params := ⟨189,83,39,257,3350,9,10⟩
def source27 : Params := ⟨72,31,14,98,1012,2,3⟩
def source28 : Params := ⟨104,45,21,142,1769,4,5⟩
def source29 : Params := ⟨104,45,21,141,1920,4,6⟩
def source30 : Params := ⟨136,59,27,185,2536,6,7⟩
def source31 : Params := ⟨130,53,24,177,3543,6,8⟩
def source32 : Params := ⟨158,62,29,215,3489,7,10⟩
def source33 : Params := ⟨186,82,39,253,3531,9,10⟩

def sources : Fin 34 → Params := ![source0,source1,source2,source3,source4,source5,source6,source7,source8,source9,source10,source11,source12,source13,source14,source15,source16,source17,source18,source19,source20,source21,source22,source23,source24,source25,source26,source27,source28,source29,source30,source31,source32,source33]
def groups : Fin 21 → Fin 3 → Params := ![![source0,source0,source0],![source1,source1,source1],![source2,source2,source2],![source3,source3,source3],![source4,source5,source6],![source7,source8,source9],![source10,source10,source10],![source11,source12,source13],![source11,source14,source13],![source15,source16,source17],![source18,source19,source20],![source21,source5,source22],![source23,source5,source24],![source25,source5,source24],![source25,source5,source26],![source21,source5,source26],![source27,source27,source27],![source28,source28,source28],![source29,source29,source29],![source30,source30,source30],![source31,source32,source33]]

theorem wellFormed (g : Fin 21) (j : Fin 3) : (groups g j).WellFormed := by
  have h : ∀ g : Fin 21, ∀ j : Fin 3, (groups g j).WellFormed := by decide +kernel
  exact h g j

theorem common_caps (g : Fin 21) (j : Fin 3) :
    (groups g j).B ≤ 84 ∧ (groups g j).U ≤ 258 ∧ (groups g j).L ≤ 3572 ∧ (groups g j).s ≤ 40 := by
  have h : ∀ g : Fin 21, ∀ j : Fin 3,
    (groups g j).B ≤ 84 ∧ (groups g j).U ≤ 258 ∧ (groups g j).L ≤ 3572 ∧ (groups g j).s ≤ 40 := by decide +kernel
  exact h g j

theorem exists_source {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) (i : Fin 34) :
    ∃ P, Interpolant (sources i).m (sources i).B (sources i).s (sources i).U
      (sources i).L (sources i).k (sources i).n0 nodes u0 u1 P := by
  fin_cases i
  · change ∃ P, Interpolant 132 54 24 180 1903 5 7 nodes u0 u1 P
    exact MovingFiberSources6815.P0.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 134 56 25 180 3131 6 8 nodes u0 u1 P
    exact MovingFiberSources6815.P1.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 136 56 25 185 2837 6 8 nodes u0 u1 P
    exact MovingFiberSources6815.P2.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 116 46 21 158 3120 5 7 nodes u0 u1 P
    exact MovingFiberSources6815.P3.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 114 45 21 155 3523 5 7 nodes u0 u1 P
    exact MovingFiberSources6815.P4.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 158 63 29 215 3303 7 10 nodes u0 u1 P
    exact MovingFiberSources6815.P5.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 166 73 34 226 3437 8 9 nodes u0 u1 P
    exact MovingFiberSources6815.P6.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 114 47 21 154 3146 5 7 nodes u0 u1 P
    exact MovingFiberSources6815.P7.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 142 56 26 193 3010 6 9 nodes u0 u1 P
    exact MovingFiberSources6815.P8.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 174 76 36 236 2961 8 9 nodes u0 u1 P
    exact MovingFiberSources6815.P9.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 170 71 32 231 3399 8 10 nodes u0 u1 P
    exact MovingFiberSources6815.P10.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 98 41 19 132 2704 4 6 nodes u0 u1 P
    exact MovingFiberSources6815.P11.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 142 59 27 193 2625 6 9 nodes u0 u1 P
    exact MovingFiberSources6815.P12.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 158 69 32 214 2607 7 8 nodes u0 u1 P
    exact MovingFiberSources6815.P13.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 146 58 27 198 2709 6 9 nodes u0 u1 P
    exact MovingFiberSources6815.P14.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 98 41 19 133 2580 4 6 nodes u0 u1 P
    exact MovingFiberSources6815.P15.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 150 60 28 204 2457 6 9 nodes u0 u1 P
    exact MovingFiberSources6815.P16.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 162 71 33 218 2511 7 8 nodes u0 u1 P
    exact MovingFiberSources6815.P17.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 114 47 22 155 3060 5 7 nodes u0 u1 P
    exact MovingFiberSources6815.P18.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 166 66 31 226 2877 7 10 nodes u0 u1 P
    exact MovingFiberSources6815.P19.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 174 76 36 237 2938 8 9 nodes u0 u1 P
    exact MovingFiberSources6815.P20.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 111 46 22 151 3572 5 7 nodes u0 u1 P
    exact MovingFiberSources6815.P21.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 189 83 39 256 3383 9 10 nodes u0 u1 P
    exact MovingFiberSources6815.P22.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 114 45 20 155 3507 5 7 nodes u0 u1 P
    exact MovingFiberSources6815.P23.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 190 84 40 258 3307 9 10 nodes u0 u1 P
    exact MovingFiberSources6815.P24.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 111 46 21 151 3548 5 7 nodes u0 u1 P
    exact MovingFiberSources6815.P25.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 189 83 39 257 3350 9 10 nodes u0 u1 P
    exact MovingFiberSources6815.P26.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 72 31 14 98 1012 2 3 nodes u0 u1 P
    exact MovingFiberSources6815.P27.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 104 45 21 142 1769 4 5 nodes u0 u1 P
    exact MovingFiberSources6815.P28.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 104 45 21 141 1920 4 6 nodes u0 u1 P
    exact MovingFiberSources6815.P29.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 136 59 27 185 2536 6 7 nodes u0 u1 P
    exact MovingFiberSources6815.P30.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 130 53 24 177 3543 6 8 nodes u0 u1 P
    exact MovingFiberSources6815.P31.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 158 62 29 215 3489 7 10 nodes u0 u1 P
    exact MovingFiberSources6815.P32.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 186 82 39 253 3531 9 10 nodes u0 u1 P
    exact MovingFiberSources6815.P33.exists_interpolant nodes u0 u1 hI

def groupIndices : Fin 21 → Fin 3 → Fin 34 := ![![0,0,0],![1,1,1],![2,2,2],![3,3,3],![4,5,6],![7,8,9],![10,10,10],![11,12,13],![11,14,13],![15,16,17],![18,19,20],![21,5,22],![23,5,24],![25,5,24],![25,5,26],![21,5,26],![27,27,27],![28,28,28],![29,29,29],![30,30,30],![31,32,33]]

theorem groups_eq_sources (g : Fin 21) (j : Fin 3) : groups g j = sources (groupIndices g j) := by
  have h : ∀ g : Fin 21, ∀ j : Fin 3, groups g j = sources (groupIndices g j) := by decide +kernel
  exact h g j

theorem exists_group {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) (g : Fin 21) :
    ∃ P : Fin 3 → SecondJetSupport.Poly (K := K), ∀ j,
      Interpolant (groups g j).m (groups g j).B (groups g j).s (groups g j).U
        (groups g j).L (groups g j).k (groups g j).n0 nodes u0 u1 (P j) := by
  classical
  have hex (j : Fin 3) : ∃ P, Interpolant (groups g j).m (groups g j).B (groups g j).s
      (groups g j).U (groups g j).L (groups g j).k (groups g j).n0 nodes u0 u1 P := by
    rw [groups_eq_sources g j]
    exact exists_source nodes u0 u1 hI (groupIndices g j)
  exact Classical.skolem.mp hex

end ProximityPrize.SubmissionLower.MovingFiberCatalog6815
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6815
open scoped BigOperators
open RCN095 RCN146 RCN260 RCN294 RCN327 LocatorHybridCells LocatorHybridCellsC1
open MovingFiberProfile6815 MovingFiberThreeSources6811 MovingFiberRegularData6815
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def first (a b c : ℕ) : FlagDegree := ⟨262144*c,262144*b+524288,262144*a+524291⟩
def normal (a b c : ℕ) : FlagDegree := ⟨131074*c,131074*b+131076,131074*a+262148⟩
def raw (a b c : ℕ) : FlagDegree := ⟨131073*c,131073*b+262146,131073*a+393218⟩
def graph (cfg : Fin 3 → Params) (scale : ℕ) (f : FlagDegree) (a b c : ℕ) : ℕ :=
  scale/3*flagMixed f (first a b c) (normal a b c) +
    ∑ j : Fin 3, (524288*weight (normal a b c) j*(scale/(3*(cfg j).d))+
      65539*weight (raw a b c) j*(scale/(cfg j).d))*
      flagMixed f (MovingFiberThreeSources6811.direction j) (cfg j).flag
def identityDegree (p : FlagDegree) (a b c : ℕ) : ℕ :=
  p.zOnly*(655365+262146*a)+p.yz*(1310730+524292*a)+
    p.all*(2097170+524292*a+524292*b+262146*c)
def pairNumerator (a b c capY capR capT : ℕ) : ℕ :=
  131073*((1+262142*(a+b+5))*((a+3)*capT+(a+b+c+5)*capR)+
    131071*(2*a+5)*((a+b+5)*capT+(a+b+c+5)*capY)+
    (1+262142*(a+b+c+5))*((a+b+5)*capR+(a+3)*capY))+
    80900*50174*((a+b+5)*capR+(a+3)*capY)
def coeff (P : Params) (a b c : ℕ) : ℕ := pairNumerator a b c P.U P.B P.L
def helper (P : Params) (a b c : ℕ) : ℕ :=
  pairNumerator a b c (P.U+P.s*(a+b+4)) (P.B+P.s*(a+2)) (P.L+P.s*(a+b+c+4))

theorem number_coordinates (cfg : Fin 3 → Params) (scale : ℕ) (f : FlagDegree) (a b c : ℕ) :
    number cfg scale (a+3+(b+2)+c) (a+3+(b+2)) (a+3) f = graph cfg scale f a b c := by
  have hy : a+3+(b+2)-(a+3) = b+2 := by omega
  have hz : a+3+(b+2)+c-(a+3+(b+2)) = c := by omega
  have hr2 : a+3-2 = a+1 := by omega
  have hb : b+2-1 = b+1 := by omega
  have hv2 : 131074*(b+2)-131072 = 131074*b+131076 := by omega
  have hfirst : MovingFiberRetainedStage6811.hfreeFirst (a+3+(b+2)+c) (a+3+(b+2)) (a+3) =
      first a b c := by
    have h : a+3-1 = a+2 := by omega
    unfold MovingFiberRetainedStage6811.hfreeFirst HFreeFirstSlice6812.hfreeFlag first unitAllFlag
    rw [hy,hz,h]
    show FlagDegree.mk (2*(RCN326.w+1)*c+3*0) (2*(RCN326.w+1)*(b+2)+3*0)
      (2*(RCN326.w+1)*(a+2)+3*1) = _
    rw [FlagDegree.mk.injEq,show RCN326.w = 131071 from rfl]
    exact ⟨by ring,by ring,by ring⟩
  have hn : BoundaryTailProvider.cellNormal (a+3+(b+2)+c) (a+3+(b+2)) (a+3) = normal a b c := by
    norm_num only [BoundaryTailProvider.cellNormal,BoundaryTailAlgebra.normalFlag,normal,w,hy,hz,hv2,
      FlagDegree.mk.injEq,true_and]
    omega
  have hraw : MovingFiberRetainedStage6811.rawFirstFlag (a+3+(b+2)+c) (a+3+(b+2)) (a+3) = raw a b c := by
    simp only [MovingFiberRetainedStage6811.rawFirstFlag,cellA,cellB,cellS,hz,hy,hb,hr2,
      RCN198.center,RCN198.direction,raw,w,unitYZFlag]
    change FlagDegree.mk (0+2*c+131071*c) (1+(2*(b+1)+1)+131071*(b+1+1))
      (0+(2*(a+1)+3)+131071*(a+1+2)) = _
    have e0 : 0+2*c+131071*c=131073*c := by ring
    have e1 : 1+(2*(b+1)+1)+131071*(b+1+1)=131073*b+262146 := by ring
    have e2 : 0+(2*(a+1)+3)+131071*(a+1+2)=131073*a+393218 := by ring
    rw [e0,e1,e2]
  have hw4 : 4*(w+1) = 524288 := rfl
  simp only [number,graph,hfirst,hn,hraw,hw4]

theorem identity_coordinates (f : FlagDegree) (a b c : ℕ) :
    identityCurveDegree f (cellA (a+3+(b+2)+c) (a+3+(b+2)))
      (cellB (a+3+(b+2)) (a+3)) (cellS (a+3)) w = identityDegree f a b c := by
  change identityCurveDegree f _ _ _ Lower80788.HybridIdentityC2.w = _
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  have ha : cellA (a+3+(b+2)+c) (a+3+(b+2)) = c := by dsimp [cellA]; omega
  have hb : cellB (a+3+(b+2)) (a+3) = b+1 := by dsimp [cellB]; omega
  have hs : cellS (a+3) = a+1 := by dsimp [cellS]; omega
  rw [ha,hb,hs]
  simp only [identityDegree]
  ring

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem pair_numerator (S : Data nodes u0 u1) (a b c : ℕ)
    (hr : S.r=a+3) (hy : S.y=a+3+(b+2)) (ht : S.t=a+3+(b+2)+c) (R U T : ℕ) :
    AsymmetricHelper.leftRegularNumerator (S.pair R U T) = pairNumerator a b c U R T := by
  have hR : 2*(a+3)-1=2*a+5 := by omega
  norm_num only [Data.pair,AsymmetricHelper.leftRegularNumerator,UnequalParameters.errors,
    UnequalParameters.gap,UnequalParameters.leftAgreement,UnequalParameters.mixedCost,dot,hr,hy,ht,hR,pairNumerator]
  ring

theorem uniform_gates (S : Data nodes u0 u1) (R U T : ℕ)
    (hR : R ≤ 1284) (hU : U ≤ 5898) (hT : T ≤ 303572) : S.PairGates R U T := by
  have hr := S.rbound
  have hy := S.ybound
  have ht := S.tbound
  have hm : (S.pair R U T).mixedCost.y ≤ 31*303572+7501*1284 ∧
      (S.pair R U T).mixedCost.r ≤ 142*303572+7501*5898 ∧
      (S.pair R U T).mixedCost.z ≤ 142*1284+31*5898 := by
    dsimp [Data.pair,UnequalParameters.mixedCost]
    constructor
    · exact Nat.add_le_add (Nat.mul_le_mul hr hT) (Nat.mul_le_mul ht hR)
    constructor
    · exact Nat.add_le_add (Nat.mul_le_mul hy hT) (Nat.mul_le_mul ht hU)
    · exact Nat.add_le_add (Nat.mul_le_mul hy hR) (Nat.mul_le_mul hr hU)
  exact ⟨hm.1.trans_lt (by decide),hm.2.1.trans_lt (by decide),hm.2.2.trans_lt (by decide)⟩

theorem catalog_gates (S : Data nodes u0 u1) (g : Fin 21) (j : Fin 3) :
    let P := MovingFiberCatalog6815.groups g j
    S.PairGates (P.B+P.s*(S.r-1)) (P.U+P.s*(S.y-1)) (P.L+P.s*(S.t-1)) ∧
    S.PairGates P.B P.U P.L := by
  dsimp only
  have hp := MovingFiberCatalog6815.common_caps g j
  have hr : S.r-1 ≤ 30 := by have := S.rbound; omega
  have hy : S.y-1 ≤ 141 := by have := S.ybound; omega
  have ht : S.t-1 ≤ 7500 := by have := S.tbound; omega
  constructor
  · apply uniform_gates
    · calc _ ≤ 84+40*30 := by gcongr; exact hp.1; exact hp.2.2.2
           _ ≤ 1284 := by decide
    · calc _ ≤ 258+40*141 := by gcongr; exact hp.2.1; exact hp.2.2.2
           _ ≤ 5898 := by decide
    · calc _ ≤ 3572+40*7500 := by gcongr; exact hp.2.2.1; exact hp.2.2.2
           _ ≤ 303572 := by decide
  · exact uniform_gates S _ _ _ (by omega) (by omega) (by omega)

def Own (S : Data nodes u0 u1) : Prop :=
  RCN130.originalCumulativeFlag S.F = ⟨S.t-S.y,S.y-S.r,S.r⟩

theorem own_total (S : Data nodes u0 u1) (hown : Own S) : RCN234.wt RCN156.residualTotalWeights S.F=S.t := by
  have h := (RCN130.originalCumulativeFlag_cumulative S.F).2.2
  rw [hown] at h
  have := S.ry
  have := S.yt
  dsimp only at h
  omega

end ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6815
end MergedPart5
