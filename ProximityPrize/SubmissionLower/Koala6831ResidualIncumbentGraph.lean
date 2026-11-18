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

namespace ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentGraph
noncomputable section

open RCN095 (FlagDegree)

set_option autoImplicit false

def axisPrice (price : Fin 3 → ℕ) (flag : FlagDegree) : ℕ :=
  flag.zOnly * price 0 + flag.yz * price 1 + flag.all * price 2

private theorem axisPrice_eq_cumulative (price : Fin 3 → ℕ)
    (hmono : price 0 ≤ price 1 ∧ price 1 ≤ price 2) (f : FlagDegree) :
    axisPrice price f = (f.zOnly + f.yz + f.all) * price 0 +
      (f.yz + f.all) * (price 1 - price 0) + f.all * (price 2 - price 1) := by
  have h1 : price 1 = price 0 + (price 1 - price 0) := by omega
  have h2 : price 2 = price 0 + (price 1 - price 0) + (price 2 - price 1) := by omega
  unfold axisPrice
  conv_lhs =>
    rw [h2]
    arg 1
    arg 2
    rw [h1]
  ring

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
    (D t y r scale : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 7501) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 81060 flag w (cellSupport t y r))
    (hnodes : S.nodes.card = 262144)
    (hagreement : ∀ gamma ∈ Gamma, 181084 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧ flag.zOnly+flag.yz+flag.all ≤ t)
    (source : Fin 3 → Source S.F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (hfree : HFreeDir6813.HFreeStageDir S)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0)
    (price : Fin 3 → ℕ)
    (hgraph : HFreeDir6813.numeratorDir source scale t y r flag ≤ axisPrice price flag)
    (hidentityAbs : scale*131073*81061*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w ≤
      50013 * axisPrice price flag) :
    scale * Gamma.card ≤ axisPrice price flag := by
  have hflagChar : flag.yz+flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly+flag.yz+flag.all < 2130706433 := by omega
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator := (globalTailCut_dvd_iff (polynomialEmbedding K)
      (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hmixed := BoundaryTailGates.identity_gate flag t y r hr3 hr hy hry (by omega) hflag.1 hflag.2.1
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider S 181084
      (by simpa using hnodes) hagreement (by norm_num [w]) hTailNumerator D t r
      (by norm_num [w]) hDlow hDchar hbox hflagChar hmixed
    have hpositive : 1 ≤ identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hp := S.y_dependent
      have hd := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181084 _ hprovider hagreement
      (by norm_num [w]) (by rw [hnodes]; norm_num) hpositive
    have hinc' : Gamma.card*50013 ≤ 131073*81061*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      simpa only [hnodes,w] using hinc
    apply Nat.le_of_mul_le_mul_left (c := 50013) _ (by decide)
    calc
      50013*(scale*Gamma.card) = scale*(Gamma.card*50013) := by ring
      _ ≤ scale*(131073*81061*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w) :=
        Nat.mul_le_mul_left _ hinc'
      _ ≤ _ := by simpa only [Nat.mul_assoc] using hidentityAbs
  · have hmixed := BoundaryTailGates.reduced_gate flag t y r hr3 hr hy hry (by omega) hflag.1 hflag.2.1
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (81060+1)*(BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail (BoundaryTailReduced.reducedBaseOrd S hTail hflagChar hmixed C)
        181084 D t r (by simpa using hnodes) hagreement (by norm_num [w]) (by norm_num [w])
        hDlow hDchar hbox (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed)
        (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hTail hflagChar hmixed C) hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hTail hflagChar hmixed C)
    have hmov : 2*(flag.zOnly+flag.yz+flag.all)*(t+1) < 2130706433 := by
      have hm := Nat.mul_le_mul (show 2*(flag.zOnly+flag.yz+flag.all) ≤ 2*7501 by omega)
        (show t+1 ≤ 7502 by omega)
      omega
    have hcount := HFreeDir6813.retained_stage_bound_dir t y r scale hr3 hry (by omega) S source hscale hscaleDiv hfree hTail
      hflagChar hmixed (by omega) hmov (by norm_num [w]) (by
        unfold cellNormal
        rw [BoundaryTailAlgebra.normalFlag_eq_cell t y r hr3 hry]
        simpa only [add_yz,nsmul_yz,unitAllFlag,mul_zero,add_zero] using
          hybridC1Gate_of_le t y r 81060 hry (by norm_num)) htangent h2 hfact hgood
    exact (by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hscale).mp hcount :
      scale * Gamma.card ≤ _).trans hgraph

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
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

theorem regular_graph_seed_card_mul_le
    (D t y r scale : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 7501) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hFR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w t r)
    (hsupport : ResidualSupportData (cellSupport t y r) F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, 181084 ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hno : NoLargeSelectedPencil selected Gamma w 81060)
    (source : Fin 3 → Source F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (hfree : ∀ (G : Finset K) (fl : FlagDegree) (S : ResidualStage (polynomialEmbedding K) G x
      2130706433 81060 fl w (cellSupport t y r)), S.F = F → HFreeDir6813.HFreeStageDir S)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0)
    (price : Fin 3 → ℕ)
    (hmono : price 0 ≤ price 1 ∧ price 1 ≤ price 2)
    (hgraph : ∀ f : FlagDegree, HFreeDir6813.numeratorDir source scale t y r f ≤ axisPrice price f)
    (hidentity : ∀ f : FlagDegree, scale*131073*81061*identityCurveDegree f (cellA t y) (cellB y r) (cellS r) w ≤
      50013 * axisPrice price f) :
    scale * Gamma.card ≤ axisPrice price (originalCumulativeFlag F) := by
  have hFRsmall : F.degreeOf 2 < 2130706433 := (degreeOf_R_le_of_mem_box F D w t r hbox).trans_lt (by omega)
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = y := by dsimp [cellB,cellS]; omega
  have hts : cellA t y+cellB y r+cellS r+3 = t := by dsimp [cellA,cellB,cellS]; omega
  have hcover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma hsolution
  have hstage (g : GeometricFactor K F) :
      scale*(geometricSeeds K F selected Gamma g).card ≤
        axisPrice price (geometricCumulativeFlag K g) := by
    let S0 := geometricResidualStageOfSupport K (cellSupport t y r) F hF hFR hFRsmall hsupport
      selected Gamma nodes x u0 u1 hinj hdegree hsolution hregular hno (by norm_num [w]) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub := geometricSeeds_subset K F selected Gamma g
    have hag : ∀ gamma ∈ geometricSeeds K F selected Gamma g, 181084 ≤ (S.agreementFiber gamma).card :=
      fun gamma hgamma => hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support F hF.ne_zero hsupport g
    have hf' : (geometricCumulativeFlag K g).all ≤ r ∧
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ y ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ t := by
      simpa only [cellSupport,RCN198.support,hs,hys,hts] using hf
    have hc := stage_seed_card_le D t y r scale hDlow hDchar ht hy hr hr3 hry hyt
      S hnodes hag hbox hf' source hscale hscaleDiv (hfree _ _ S rfl) h2 hfact
      (fun gamma hgamma j => hgood gamma (hsub hgamma) j) price (hgraph _) (hidentity _)
    simpa only [S,S0,reflagResidualStage,geometricResidualStageOfSupport,
      geometricCumulativeFlag] using hc
  have hb := geometricCumulativeFlag_budgets F hF.ne_zero
  calc
    scale*Gamma.card ≤ scale*∑ g : GeometricFactor K F, (geometricSeeds K F selected Gamma g).card :=
      Nat.mul_le_mul_left _ hcover
    _ = ∑ g : GeometricFactor K F, scale*(geometricSeeds K F selected Gamma g).card := Finset.mul_sum _ _ _
    _ ≤ ∑ g : GeometricFactor K F, axisPrice price (geometricCumulativeFlag K g) :=
      Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ _ := by
      simp only [axisPrice_eq_cumulative price hmono, Finset.sum_add_distrib, ← Finset.sum_mul]
      have ht' := hb.2.2
      have hy' := hb.2.1
      simp only [Finset.sum_add_distrib] at ht' hy'
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ ht') (Nat.mul_le_mul_right _ hy'))
        (Nat.mul_le_mul_right _ hb.1)

end RegularGeometry

end
end ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentGraph
