import ProximityPrize.SubmissionLower.GH
import ProximityPrize.SubmissionLower.CommonShearTightPrototype

namespace ProximityPrize.SubmissionLower.CommonShearStagePrototype

open scoped Classical BigOperators
open RCN052 RCN174 RCN223 RCN238 RCN243 RCN259 RCN260 RCN291 RCN292
  RCN294 RCN299 RCN303 RCN318 RCN319

noncomputable section

set_option maxHeartbeats 6000000
set_option maxRecDepth 35000

variable {K Iota : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

/-- The asymmetric regular/singular cover with the implicit singular lane
discharged by the common-shear theorem.  The old mixed characteristic gate is
absent; the larger exact singular cap is exposed in the result. -/
theorem asymmetric_stage_count_lt_of_regular_factors
    (P : UnequalParameters)
    (S : RCN318.TightParameters)
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p]
    (hs : 1 ≤ S.s) (hsmall : S.s < p) (hw : 1 ≤ S.w)
    (hchar : S.w < p) (hDw : S.w < S.kappa * S.D)
    (hj : 1 ≤ S.algebraicCap)
    (hjYSmall : S.implicitYCap < p)
    (hjZSmall : S.algebraicCap < p)
    (hwa : S.w < S.a) (han : S.a ≤ S.n)
    (hbox : Q ∈ globalCoefficientBox K S.D S.w S.L S.s)
    (hgap : 0 < P.gap) (_hgapEq : S.gap = P.gap)
    (hY : (S.D - 1) / S.w ≤ P.leftY)
    (hR : S.s ≤ P.leftR) (hZ : S.L ≤ P.leftZ)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = S.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ S.w)
    (hQsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma T = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      S.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma S.w S.errors)
    (hregular : ∀ F : RCN052.RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card * P.gap ≤
        (P.n - P.w) * dot P.agreement (regularVector P F.1) +
          (P.errors + 1) * P.gap * (regularVector P F.1).z) :
    Gamma.card < P.regularCountCap +
      CommonShearTightPrototype.countCap S + 1 := by
  classical
  have hcover := card_le_regular_sum_add_singular Q T hQ
    S.D S.w S.L S.s p hs hsmall hw hDw hj hjZSmall hbox
    selected Gamma hQsolution hTsolution
  have hregularScaled := RCN052.sum_regular_counts_bound P Q T selected Gamma
    (regularVector_budgets P Q hQ S.D S.w S.L S.s (by omega) hbox hY hR hZ)
    hregular
  have hregularCap :
      (∑ F : RCN052.RegularIndex Q,
        (regularPairSeeds Q T selected Gamma F).card) ≤ P.regularCountCap :=
    P.regular_count_le _ hgap hregularScaled
  have hsingularOld :=
    CommonShearTightPrototype.singularSeeds_count_le_countCap
      S Q hQ hbox hs hsmall hw hchar hDw hj hjYSmall hjZSmall
      hwa han selected Gamma nodes x u0 u1 hinj hnodes hdegree hagreement
      hnoPencil
  have hsingular :
      (RCN052.singularSeeds Q selected Gamma).card ≤
        CommonShearTightPrototype.countCap S := by
    change (RCN291.singularSeeds Q selected Gamma).card ≤
      CommonShearTightPrototype.countCap S
    exact hsingularOld
  omega

end

end ProximityPrize.SubmissionLower.CommonShearStagePrototype
