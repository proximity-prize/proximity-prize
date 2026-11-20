import ProximityPrize.SubmissionLower.Koala6844TerminalGraph
-- Modified from prior Proximity Prize sources.


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped Classical BigOperators
open RCN135 RCN136 RCN139 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095
open RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312
open RCN339 RCN330 RCN174 RCN319 RCN206 RCN287 RCN066 RCN338 RCN199 RCN207
open RCN271 RCN313 RCN234 RCN156 RCN341 RCN085 RCN087 RCN203 RCN084 RCN335
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open MovingFiberOrdinaryHigh6815 (bound)

open BoundaryTailIdentityArithmetic (newCost newNormal)

open Lower80788.HybridIdentityC2 in
theorem rawIdentityAbsorption (f : FlagDegree) (a b s : ℕ) (_ha : 0 ≤ a)
    (hb : 1 ≤ b) (hs : 1 ≤ s) :
    131073 * 81187 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a b s 131071 ≤
      49887 * newCost f a b s := by
  obtain ⟨b',rfl⟩ : ∃ b', b = b'+1 := ⟨b-1,by omega⟩
  obtain ⟨s',rfl⟩ : ∃ s', s = s'+1 := ⟨s-1,by omega⟩
  change 131073 * 81187 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a (b'+1) (s'+1)
    Lower80788.HybridIdentityC2.w ≤ _
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  simp [newCost, newNormal, reducedABS, rationalABS, mfibABS, mcutABS,
    flagMixed, unitAllFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring_nf
  omega
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

theorem stage_raw_bound (D t y r : ℕ)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hr3 : 3 ≤ r) (hb : r+2 ≤ y) (hyt : y ≤ t)
    (gates : GraphGates t y r)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 81186 flag
      w (cellSupport t y r))
    (hnodes : S.nodes.card = 180958+81186)
    (hagreement : ∀ gamma ∈ Gamma, 180958 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧
      flag.zOnly+flag.yz+flag.all ≤ t)
    : Gamma.card ≤ bound flag t y r := by
  have htotal := gates.total_le
  have hflagChar : flag.yz+flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly+flag.yz+flag.all < 2130706433 := by omega
  have hshort : w+1 ≤ D := by simpa only [RCN327.w] using hDlow
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator : S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w+1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hidentityGate := BoundaryTailGates6808.identity_gate flag t y r gates.projection hflag.1 hflag.2.1
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider
      (a := cellA t y) (b := cellB y r) (s := cellS r) S 180958 hnodes hagreement
      (by norm_num [RCN327.w]) hTailNumerator D t r
      (by norm_num [RCN327.w]) hshort hDchar hbox hflagChar hidentityGate
    have hpositive : 1 ≤ ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r)
        (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hy : 0 < S.G.degreeOf 1 := S.y_dependent
      have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 180958
      (ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w)
      hprovider hagreement (by norm_num [RCN327.w])
      (by rw [hnodes]; norm_num [RCN327.w]) hpositive
    have hscaled : Gamma.card * 49887 ≤ 49887 * bound flag t y r := by
      calc
        Gamma.card * 49887 = Gamma.card * (180958-w) := by norm_num [RCN327.w]
        _ ≤ (S.nodes.card-w) * (81186+1) *
            ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := hinc
        _ = 131073 * 81187 *
            ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) 131071 := by
          rw [hnodes]
          norm_num [RCN327.w]
        _ ≤ 49887 * bound flag t y r := by
          rw [MovingFiberOrdinaryHigh6815.bound_eq_abs flag t y r hr3 hb]
          exact rawIdentityAbsorption flag (cellA t y) (cellB y r) (cellS r)
            (by omega) (by unfold cellB; omega) (by unfold cellS; omega)
    apply Nat.le_of_mul_le_mul_right ?_ (by decide : 0 < 49887)
    simpa only [Nat.mul_comm] using hscaled
  · have hmixedRed := BoundaryTailGates6808.reduced_gate flag t y r gates.projection hflag.1 hflag.2.1
    have hmix : 2 * (flag.zOnly+flag.yz+flag.all) *
        (cellA t y+cellB y r+cellS r+4) < 2130706433 := by
      have ht : cellA t y + cellB y r + cellS r + 4 = t+1 := by
        dsimp [cellA, cellB, cellS]
        omega
      rw [ht]
      exact (Nat.mul_le_mul_right (t+1) (Nat.mul_le_mul_left 2 hflag.2.2)).trans_lt gates.moving
    have hrationalGate : 81186+1 ≤ (BoundaryTailProvider.cellNormal t y r).yz := by
      have hv : 2 ≤ y-r := by omega
      simp only [BoundaryTailProvider.cellNormal, BoundaryTailAlgebra.normalFlag, RCN327.w]
      omega
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G
          (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
            (81186+1) *
              (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixedRed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail
        (BoundaryTailReduced.reducedBaseOrd S hTail hflagChar hmixedRed C)
        180958 D t r hnodes hagreement
        (by norm_num [RCN327.w]) (by norm_num [RCN327.w]) hshort hDchar hbox
        (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixedRed)
        (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hTail hflagChar hmixedRed C)
        hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hTail hflagChar hmixedRed C)
    obtain ⟨provider⟩ := BoundaryTailRealization.exists_provider hr3 hb hyt
      (by norm_num [RCN327.w]) S hTail hflagChar hmixedRed hmix hrationalGate htangent
    exact stage_card_le_divisorBound S provider


end

noncomputable section

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

theorem regular_raw_bound
    (D t y r : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (gates : GraphGates t y r)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y ≤ t)
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hFR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w t r)
    (hsupport : ResidualSupportData (cellSupport t y r) F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, 180958 ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hno : NoLargeSelectedPencil selected Gamma w 81186)
    : Gamma.card ≤ MovingFiberOrdinaryHigh6815.bound (originalCumulativeFlag F) t y r := by
  have htotal := gates.total_le
  have hFRsmall : F.degreeOf 2 < 2130706433 := (degreeOf_R_le_of_mem_box F D w t r hbox).trans_lt (by omega)
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = y := by dsimp [cellB,cellS]; omega
  have hts : cellA t y+cellB y r+cellS r+3 = t := by dsimp [cellA,cellB,cellS]; omega
  have hcover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma hsolution
  have hstage (g : GeometricFactor K F) :
      (geometricSeeds K F selected Gamma g).card ≤
        MovingFiberOrdinaryHigh6815.bound (geometricCumulativeFlag K g) t y r := by
    let S0 := geometricResidualStageOfSupport K (cellSupport t y r) F hF hFR hFRsmall hsupport
      selected Gamma nodes x u0 u1 hinj hdegree hsolution hregular hno (by norm_num [w]) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub := geometricSeeds_subset K F selected Gamma g
    have hag : ∀ gamma ∈ geometricSeeds K F selected Gamma g, 180958 ≤ (S.agreementFiber gamma).card :=
      fun gamma hgamma => hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support F hF.ne_zero hsupport g
    have hf' : (geometricCumulativeFlag K g).all ≤ r ∧
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ y ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ t := by
      simpa only [cellSupport,RCN198.support,hs,hys,hts] using hf
    have hc := stage_raw_bound D t y r hDlow hDchar hr3 hry hyt gates
      S (by change nodes.card = 262144; exact hnodes) hag hbox hf'
    simpa only [geometricCumulativeFlag] using hc
  have hb := geometricCumulativeFlag_budgets F hF.ne_zero
  have hn := RCN084.sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
    (originalCumulativeFlag F) (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r)
    hb.1 hb.2.1 hb.2.2
  have hm := RCN084.sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
    (originalCumulativeFlag F) (cellMovingFiber t y r) (cellMovingCut t y r)
    hb.1 hb.2.1 hb.2.2
  calc
    _ ≤ ∑ g : GeometricFactor K F, (geometricSeeds K F selected Gamma g).card := hcover
    _ ≤ ∑ g : GeometricFactor K F, MovingFiberOrdinaryHigh6815.bound (geometricCumulativeFlag K g) t y r :=
      Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ _ := by
      unfold MovingFiberOrdinaryHigh6815.bound
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      exact Nat.add_le_add hn (Nat.mul_le_mul_left _ hm)

end RegularGeometry

end

end ProximityPrize.SubmissionLower.Koala6844Terminal



