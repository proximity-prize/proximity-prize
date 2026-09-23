import ProximityPrize.SubmissionLower.MovingFiberFixedStage6811

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

theorem regular_seed_bound
    (D t y r scale : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 7501) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hFR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w t r)
    (hsupport : ResidualSupportData (cellSupport t y r) F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, 181265 ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hno : NoLargeSelectedPencil selected Gamma w 80879)
    (source : Fin 3 → Source F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (hfree : ∀ (G : Finset K) (fl : FlagDegree) (S : ResidualStage (polynomialEmbedding K) G x
      2130706433 80879 fl w (cellSupport t y r)), S.F = F → HFreeStage S)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0)
    (hidentity : ∀ f : FlagDegree, scale*131073*80880*identityCurveDegree f (cellA t y) (cellB y r) (cellS r) w ≤
      50194*MovingFiberRetainedStage6811.numerator source scale t y r f) :
    scale*Gamma.card ≤ MovingFiberRetainedStage6811.numerator source scale t y r (originalCumulativeFlag F) := by
  have hFRsmall : F.degreeOf 2 < 2130706433 := (degreeOf_R_le_of_mem_box F D w t r hbox).trans_lt (by omega)
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = y := by dsimp [cellB,cellS]; omega
  have hts : cellA t y+cellB y r+cellS r+3 = t := by dsimp [cellA,cellB,cellS]; omega
  have hcover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma hsolution
  have hstage (g : GeometricFactor K F) :
      scale*(geometricSeeds K F selected Gamma g).card ≤
        MovingFiberRetainedStage6811.numerator source scale t y r (geometricCumulativeFlag K g) := by
    let S0 := geometricResidualStageOfSupport K (cellSupport t y r) F hF hFR hFRsmall hsupport
      selected Gamma nodes x u0 u1 hinj hdegree hsolution hregular hno (by norm_num [w]) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub := geometricSeeds_subset K F selected Gamma g
    have hag : ∀ gamma ∈ geometricSeeds K F selected Gamma g, 181265 ≤ (S.agreementFiber gamma).card :=
      fun gamma hgamma => hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support F hF.ne_zero hsupport g
    have hf' : (geometricCumulativeFlag K g).all ≤ r ∧
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ y ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ t := by
      simpa only [cellSupport,RCN198.support,hs,hys,hts] using hf
    have hc := MovingFiberFixedStage6811.stage_bound D t y r scale hDlow hDchar ht hy hr hr3 hry hyt
      S hnodes hag hbox hf' source hscale hscaleDiv (hfree _ _ S rfl) h2 hfact
      (fun gamma hgamma j => hgood gamma (hsub hgamma) j) (hidentity _)
    have hm := (Nat.le_div_iff_mul_le hscale).mp hc
    dsimp only [S,S0,reflagResidualStage,geometricResidualStageOfSupport] at hm
    simpa only [Nat.mul_comm,geometricCumulativeFlag] using hm
  have hb := geometricCumulativeFlag_budgets F hF.ne_zero
  calc
    scale*Gamma.card ≤ scale*∑ g : GeometricFactor K F, (geometricSeeds K F selected Gamma g).card :=
      Nat.mul_le_mul_left _ hcover
    _ = ∑ g : GeometricFactor K F, scale*(geometricSeeds K F selected Gamma g).card := Finset.mul_sum _ _ _
    _ ≤ ∑ g : GeometricFactor K F,
        MovingFiberRetainedStage6811.numerator source scale t y r (geometricCumulativeFlag K g) :=
      Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ _ := MovingFiberRetainedStage6811.sum_numerator_le source scale t y r (geometricCumulativeFlag K)
      (originalCumulativeFlag F) hb.1 hb.2.1 hb.2.2

#print axioms regular_seed_bound
end
end ProximityPrize.SubmissionLower.MovingFiberRegularGeometry6811
