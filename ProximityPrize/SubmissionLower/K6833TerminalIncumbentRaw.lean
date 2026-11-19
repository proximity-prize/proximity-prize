/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
import ProximityPrize.SubmissionLower.MergedInfra6815_14
import ProximityPrize.SubmissionLower.MergedInfra6815_6
import ProximityPrize.SubmissionLower.BoundaryTailGates
import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_18
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.HFreeDir6813

namespace ProximityPrize.SubmissionLower.K6833TerminalIncumbentRaw

noncomputable section

section FixedStage
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider LocatorHybridTransportC2
open BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433]

local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

theorem stage_seed_card_le
    (D t y r : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 8870) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 81076 flag w (cellSupport t y r))
    (hnodes : S.nodes.card = 262144)
    (hagreement : ∀ gamma ∈ Gamma, 181068 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz + flag.all ≤ y ∧ flag.zOnly + flag.yz + flag.all ≤ t)
    (hidentity : 131073 * 81077 * identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w ≤
      49997 * MovingFiberOrdinaryHigh6815.bound flag t y r) :
    Gamma.card ≤ MovingFiberOrdinaryHigh6815.bound flag t y r := by
  have hflagChar : flag.yz + flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433 := by omega
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator := (globalTailCut_dvd_iff (polynomialEmbedding K)
      (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hmixed := BoundaryTailGates.identity_gate flag t y r hr3 hr hy hry hyt hflag.1 hflag.2.1
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider S 181068
      (by simpa using hnodes) hagreement (by norm_num [w]) hTailNumerator D t r
      (by norm_num [w]) hDlow hDchar hbox hflagChar hmixed
    have hpositive : 1 ≤ identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hp := S.y_dependent
      have hd := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181068 _ hprovider hagreement
      (by norm_num [w]) (by rw [hnodes]; norm_num) hpositive
    have hinc' : Gamma.card * 49997 ≤
        131073 * 81077 * identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      simpa only [hnodes, w] using hinc
    apply Nat.le_of_mul_le_mul_left (c := 49997) _ (by decide)
    simpa only [Nat.mul_comm 49997 Gamma.card] using hinc'.trans hidentity
  · have hmixed := BoundaryTailGates.reduced_gate flag t y r hr3 hr hy hry hyt hflag.1 hflag.2.1
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (81076+1)*(BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail (BoundaryTailReduced.reducedBaseOrd S hTail hflagChar hmixed C)
        181068 D t r (by simpa using hnodes) hagreement (by norm_num [w]) (by norm_num [w])
        hDlow hDchar hbox (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed)
        (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hTail hflagChar hmixed C) hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hTail hflagChar hmixed C)
    have hts : cellA t y + cellB y r + cellS r + 4 = t + 1 := by
      dsimp [cellA, cellB, cellS]
      omega
    have hmov : 2 * (flag.zOnly + flag.yz + flag.all) *
        (cellA t y + cellB y r + cellS r + 4) < 2130706433 := by
      rw [hts]
      have hm := Nat.mul_le_mul (show 2 * (flag.zOnly + flag.yz + flag.all) ≤ 2 * 8870 by omega)
        (show t + 1 ≤ 8871 by omega)
      omega
    have hgate : 81076 + 1 ≤ (cellNormal t y r).yz := by
      unfold cellNormal
      rw [BoundaryTailAlgebra.normalFlag_eq_cell t y r hr3 hry]
      simpa only [add_yz, nsmul_yz, unitAllFlag, mul_zero, add_zero] using
        hybridC1Gate_of_le t y r 81076 hry (by norm_num)
    obtain ⟨provider⟩ := BoundaryTailRealization.exists_provider hr3 hry hyt (by norm_num [w])
      S hTail hflagChar hmixed hmov hgate htangent
    exact LocatorHybridTailProvider.stage_card_le_divisorBound S provider

end FixedStage

section RegularGeometry
open scoped Classical BigOperators
open RCN081 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN137 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN319 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider LocatorHybridTransportC2
open BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433]

local instance : DecidableEq I := Classical.decEq I

theorem regular_raw_seed_card_le
    (D t y r : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 8870) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r + 2 ≤ y) (hyt : y ≤ t)
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hFR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w t r)
    (hsupport : ResidualSupportData (cellSupport t y r) F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, 181068 ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hno : NoLargeSelectedPencil selected Gamma w 81076)
    (hidentity : ∀ f : FlagDegree, 131073 * 81077 * identityCurveDegree f (cellA t y) (cellB y r) (cellS r) w ≤
      49997 * MovingFiberOrdinaryHigh6815.bound f t y r) :
    Gamma.card ≤ MovingFiberOrdinaryHigh6815.bound (originalCumulativeFlag F) t y r := by
  have hFRsmall : F.degreeOf 2 < 2130706433 := (degreeOf_R_le_of_mem_box F D w t r hbox).trans_lt (by omega)
  have hs : cellS r + 2 = r := by dsimp [cellS]; omega
  have hys : cellB y r + cellS r + 3 = y := by dsimp [cellB, cellS]; omega
  have hts : cellA t y + cellB y r + cellS r + 3 = t := by dsimp [cellA, cellB, cellS]; omega
  have hcover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma hsolution
  have hstage (g : GeometricFactor K F) :
      (geometricSeeds K F selected Gamma g).card ≤
        MovingFiberOrdinaryHigh6815.bound (geometricCumulativeFlag K g) t y r := by
    let S0 := geometricResidualStageOfSupport K (cellSupport t y r) F hF hFR hFRsmall hsupport
      selected Gamma nodes x u0 u1 hinj hdegree hsolution hregular hno (by norm_num [w]) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub := geometricSeeds_subset K F selected Gamma g
    have hag : ∀ gamma ∈ geometricSeeds K F selected Gamma g, 181068 ≤ (S.agreementFiber gamma).card :=
      fun gamma hgamma => hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support F hF.ne_zero hsupport g
    have hf' : (geometricCumulativeFlag K g).all ≤ r ∧
        (geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all ≤ y ∧
        (geometricCumulativeFlag K g).zOnly + (geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all ≤ t := by
      simpa only [cellSupport, RCN198.support, hs, hys, hts] using hf
    exact stage_seed_card_le D t y r hDlow hDchar ht hy hr hr3 hry hyt S hnodes hag hbox hf'
      (hidentity _)
  have hb := geometricCumulativeFlag_budgets F hF.ne_zero
  calc
    Gamma.card ≤ ∑ g : GeometricFactor K F, (geometricSeeds K F selected Gamma g).card := hcover
    _ ≤ ∑ g : GeometricFactor K F, MovingFiberOrdinaryHigh6815.bound (geometricCumulativeFlag K g) t y r :=
      Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ _ := by
      unfold MovingFiberOrdinaryHigh6815.bound
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      exact Nat.add_le_add
        (LocatorFactorAggregate.sum_mixed_le (geometricCumulativeFlag K) _ _ _ hb.1 hb.2.1 hb.2.2)
        (Nat.mul_le_mul_left _ (LocatorFactorAggregate.sum_mixed_le (geometricCumulativeFlag K) _ _ _
          hb.1 hb.2.1 hb.2.2))

end RegularGeometry

end
end ProximityPrize.SubmissionLower.K6833TerminalIncumbentRaw

/- Retuned for the full 68.32 domain and the m=303 primary, November 2026. -/

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
