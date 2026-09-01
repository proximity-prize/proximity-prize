import ProximityPrize.SubmissionLower.CommonShearStagePrototype
import ProximityPrize.SubmissionLower.LocatorCover

namespace ProximityPrize.SubmissionLower.CommonShear6777ResidualPrototype

open scoped Classical
open RCN052 RCN174 RCN223 RCN238 RCN243 RCN259 RCN260 RCN286 RCN291
  RCN294 RCN303 RCN318 RCN319

noncomputable section

set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

def n : ℕ := 262144
def w : ℕ := 131071
def agreements : ℕ := 181618
def errors : ℕ := 80526
def weightedB : ℕ := 13802968
def LB : ℕ := 5951
def weightedC : ℕ := 47947152
def LC : ℕ := 149307

def residualStage : RCN260.UnequalParameters :=
  ⟨n, w, agreements, 105, 22, LB, 365, 80, LC⟩

def residualSingular : RCN318.TightParameters :=
  ⟨n, w, agreements, weightedB, LB, 22⟩

theorem exact_values :
    residualStage.agreement = ⟨95681831, 20840289, 39139635595⟩ ∧
    residualStage.mixedCost = ⟨3760834, 17849350, 16430⟩ ∧
    residualStage.regularCountCap = 3565225582151577 ∧
    CommonShearTightPrototype.countCap residualSingular =
      2363008288213364 := by
  decide

structure Gates : Prop where
  kD : w < residualSingular.kappa * residualSingular.D
  algebraic_pos : 1 ≤ residualSingular.algebraicCap
  implicit_small : residualSingular.implicitYCap < 2130706433
  algebraic_small : residualSingular.algebraicCap < 2130706433
  qY : (residualSingular.D - 1) / w ≤ residualStage.leftY
  leftZ_small : residualStage.leftZ < 2130706433
  mixedY_small : residualStage.mixedCost.y < 2130706433
  mixedR_small : residualStage.mixedCost.r < 2130706433
  mixedZ_small : residualStage.mixedCost.z < 2130706433

theorem gates : Gates := by
  constructor <;> decide

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem residual_count_lt
    (valid : Gates)
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (hbox : Q ∈ globalCoefficientBox K weightedB w LB 22)
    (hTcaps : T.degreeOf 1 ≤ 365 ∧ T.degreeOf 2 ≤ 80 ∧
      T.degreeOf 3 ≤ LC)
    (selected : K → Polynomial K) (seeds : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hQsolution : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma T = 0)
    (hagreement : ∀ gamma ∈ seeds, agreements ≤
      (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected seeds w errors) :
    seeds.card < residualStage.regularCountCap +
      CommonShearTightPrototype.countCap residualSingular + 1 := by
  apply CommonShearStagePrototype.asymmetric_stage_count_lt_of_regular_factors
    residualStage residualSingular Q T hQ 2130706433
    (by decide) (by decide) (by decide) (by decide) valid.kD
    valid.algebraic_pos valid.implicit_small valid.algebraic_small
    (by decide) (by decide) hbox (by decide) (by decide)
    valid.qY (by decide) (by decide) selected seeds nodes x u0 u1 hinj
    hnodes hdegree hQsolution hTsolution hagreement
    (by simpa [residualSingular, RCN318.TightParameters.errors,
      n, agreements, errors] using hno)
  exact RCN052.all_regularPairSeeds_bound residualStage Q T hQ hrel
    weightedB w LB 22 2130706433 hbox (by decide)
    valid.qY (by decide) (by decide)
    hTcaps.1 hTcaps.2.1 hTcaps.2.2 (by decide)
    (by decide) (by decide) valid.leftZ_small
    valid.mixedY_small valid.mixedR_small valid.mixedZ_small
    selected seeds nodes x u0 u1 hinj hnodes
    (by decide) (by decide) (by decide) (by decide)
    hdegree hagreement
    (by simpa [residualStage, RCN260.UnequalParameters.errors,
      n, agreements, errors] using hno)

end

end ProximityPrize.SubmissionLower.CommonShear6777ResidualPrototype
