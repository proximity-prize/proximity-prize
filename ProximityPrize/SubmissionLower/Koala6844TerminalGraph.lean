import ProximityPrize.SubmissionLower.MergedInfra6815_22
-- Modified from prior Proximity Prize sources.


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped BigOperators
open RCN095 RCN146 RCN198 RCN287 RCN327 LocatorHybridCells


structure GraphGates (t y r : ℕ) : Prop where
  total_le : t ≤ 9678
  moving : 2 * t * (t+1) < 2130706433
  projection : BoundaryTailGates6808.Safe r y


def charge (cost : Fin 3 → ℕ) (f : FlagDegree) : ℕ :=
  f.zOnly * cost 0 + f.yz * cost 1 + f.all * cost 2


def identityCharge (scale t y r : ℕ) (f : FlagDegree) : ℕ :=
  (scale / 49890) * (131073 * 81184 *
    identityCurveDegree f (cellA t y) (cellB y r) (cellS r) w)

private theorem sum_charge_le {J : Type} [Fintype J] (cost : Fin 3 → ℕ)
    (hmono : cost 0 ≤ cost 1 ∧ cost 1 ≤ cost 2) (flags : J → FlagDegree) (total : FlagDegree)
    (hs : (∑ i, (flags i).all) ≤ total.all)
    (hm : (∑ i, ((flags i).yz + (flags i).all)) ≤ total.yz + total.all)
    (ht : (∑ i, ((flags i).zOnly + (flags i).yz + (flags i).all)) ≤
      total.zOnly + total.yz + total.all) :
    (∑ i, charge cost (flags i)) ≤ charge cost total := by
  simp only [charge, RCN131.linear_cost_cumulative _ _ _ _ hmono.1 hmono.2,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib] at hm ht
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ ht)
    (Nat.mul_le_mul_left _ hm)) (Nat.mul_le_mul_left _ hs)

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
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}


theorem stage_graph_bound
    (D t y r scale : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (gates : GraphGates t y r) (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 81183 flag w (cellSupport t y r))
    (hnodes : S.nodes.card = 262144)
    (hagreement : ∀ gamma ∈ Gamma, 180961 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧ flag.zOnly+flag.yz+flag.all ≤ t)
    (source : Fin 3 → Source S.F) (hscale : 0 < scale)
    (hscaleDiv : ∀ j, 3*(source j).d ∣ scale) (hgap : 49890 ∣ scale)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0)
    (cost : Fin 3 → ℕ) (hidentity : identityCharge scale t y r flag ≤ charge cost flag)
    (hgraph : HFreeDir6813.numeratorDir source scale t y r flag ≤ charge cost flag) :
    scale * Gamma.card ≤ charge cost flag := by
  have htotal := gates.total_le
  have hflagChar : flag.yz+flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly+flag.yz+flag.all < 2130706433 := by omega
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator := (globalTailCut_dvd_iff (polynomialEmbedding K)
      (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hmixed := BoundaryTailGates6808.identity_gate flag t y r gates.projection hflag.1 hflag.2.1
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider S 180961
      (by simpa using hnodes) hagreement (by norm_num [w]) hTailNumerator D t r
      (by norm_num [w]) hDlow hDchar hbox hflagChar hmixed
    have hpositive : 1 ≤ identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hp := S.y_dependent
      have hd := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 180961 _ hprovider hagreement
      (by norm_num [w]) (by rw [hnodes]; norm_num) hpositive
    have hinc' : Gamma.card*49890 ≤ 131073*81184*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      simpa only [hnodes,w] using hinc
    calc
      _ = (scale / 49890) * (Gamma.card * 49890) := by
        calc
          _ = ((scale / 49890) * 49890) * Gamma.card := by rw [Nat.div_mul_cancel hgap]
          _ = _ := by ac_rfl
      _ ≤ identityCharge scale t y r flag := Nat.mul_le_mul_left _ hinc'
      _ ≤ _ := hidentity
  · have hmixed := BoundaryTailGates6808.reduced_gate flag t y r gates.projection hflag.1 hflag.2.1
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (81183+1)*(BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail (BoundaryTailReduced.reducedBaseOrd S hTail hflagChar hmixed C)
        180961 D t r (by simpa using hnodes) hagreement (by norm_num [w]) (by norm_num [w])
        hDlow hDchar hbox (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed)
        (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hTail hflagChar hmixed C) hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hTail hflagChar hmixed C)
    have hmov : 2*(flag.zOnly+flag.yz+flag.all)*(t+1) < 2130706433 :=
      (Nat.mul_le_mul_right (t+1) (Nat.mul_le_mul_left 2 hflag.2.2)).trans_lt gates.moving
    have htot : (cellSupport t y r).total ≤ 9678 := by
      simp only [cellSupport, RCN198.support, cellA, cellB, cellS]
      omega
    have bound := HFreeDir6813.retained_stage_bound_dir t y r scale hr3 hry (by omega) S source hscale hscaleDiv
      (HFreeDir6813.hfree_stage_dir_of_gaps S htot) hTail hflagChar hmixed (by omega) hmov
      (by norm_num [w]) (by
        unfold cellNormal
        rw [BoundaryTailAlgebra.normalFlag_eq_cell t y r hr3 hry]
        simpa only [add_yz,nsmul_yz,unitAllFlag,mul_zero,add_zero] using
          hybridC1Gate_of_le t y r 81183 hry (by norm_num)) htangent h2 hfact hgood
    exact ((by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hscale).mp bound) :
      scale * Gamma.card ≤ HFreeDir6813.numeratorDir source scale t y r flag).trans hgraph

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
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

theorem regular_graph_bound
    (D t y r scale : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (gates : GraphGates t y r)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hFR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w t r)
    (hsupport : ResidualSupportData (cellSupport t y r) F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, 180961 ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hno : NoLargeSelectedPencil selected Gamma w 81183)
    (source : Fin 3 → Source F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0)
    (hgap : 49890 ∣ scale) (cost : Fin 3 → ℕ)
    (hmono : cost 0 ≤ cost 1 ∧ cost 1 ≤ cost 2)
    (hidentity : ∀ f, identityCharge scale t y r f ≤ charge cost f)
    (hgraph : ∀ f, HFreeDir6813.numeratorDir source scale t y r f ≤ charge cost f) :
    scale*Gamma.card ≤ charge cost (originalCumulativeFlag F) := by
  have htotal := gates.total_le
  have hFRsmall : F.degreeOf 2 < 2130706433 := (degreeOf_R_le_of_mem_box F D w t r hbox).trans_lt (by omega)
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = y := by dsimp [cellB,cellS]; omega
  have hts : cellA t y+cellB y r+cellS r+3 = t := by dsimp [cellA,cellB,cellS]; omega
  have hcover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma hsolution
  have hstage (g : GeometricFactor K F) :
      scale*(geometricSeeds K F selected Gamma g).card ≤
        charge cost (geometricCumulativeFlag K g) := by
    let S0 := geometricResidualStageOfSupport K (cellSupport t y r) F hF hFR hFRsmall hsupport
      selected Gamma nodes x u0 u1 hinj hdegree hsolution hregular hno (by norm_num [w]) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub := geometricSeeds_subset K F selected Gamma g
    have hag : ∀ gamma ∈ geometricSeeds K F selected Gamma g, 180961 ≤ (S.agreementFiber gamma).card :=
      fun gamma hgamma => hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support F hF.ne_zero hsupport g
    have hf' : (geometricCumulativeFlag K g).all ≤ r ∧
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ y ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ t := by
      simpa only [cellSupport,RCN198.support,hs,hys,hts] using hf
    have hc := stage_graph_bound D t y r scale hDlow hDchar gates hr3 hry hyt
      S hnodes hag hbox hf' source hscale hscaleDiv hgap h2 hfact
      (fun gamma hgamma j => hgood gamma (hsub hgamma) j) cost
      (hidentity _) (hgraph _)
    simpa only [geometricCumulativeFlag] using hc
  have hb := geometricCumulativeFlag_budgets F hF.ne_zero
  calc
    scale*Gamma.card ≤ scale*∑ g : GeometricFactor K F, (geometricSeeds K F selected Gamma g).card :=
      Nat.mul_le_mul_left _ hcover
    _ = ∑ g : GeometricFactor K F, scale*(geometricSeeds K F selected Gamma g).card := Finset.mul_sum _ _ _
    _ ≤ ∑ g : GeometricFactor K F,
        charge cost (geometricCumulativeFlag K g) :=
      Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ _ := sum_charge_le cost hmono (geometricCumulativeFlag K)
      (originalCumulativeFlag F) hb.1 hb.2.1 hb.2.2

end RegularGeometry

end

end ProximityPrize.SubmissionLower.Koala6844Terminal



