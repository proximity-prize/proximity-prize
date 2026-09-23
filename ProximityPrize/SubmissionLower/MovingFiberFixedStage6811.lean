import ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
import ProximityPrize.SubmissionLower.BoundaryTailIdentity
import ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic
import ProximityPrize.SubmissionLower.BoundaryTailGates

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

theorem stage_bound
    (D t y r scale : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 7501) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80879 flag w (cellSupport t y r))
    (hnodes : S.nodes.card = 262144)
    (hagreement : ∀ gamma ∈ Gamma, 181265 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧ flag.zOnly+flag.yz+flag.all ≤ t)
    (source : Fin 3 → Source S.F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (hfree : HFreeStage S)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0)
    (hidentityAbs : scale*131073*80880*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w ≤
      50194*MovingFiberRetainedStage6811.numerator source scale t y r flag) :
    Gamma.card ≤ MovingFiberRetainedStage6811.numerator source scale t y r flag/scale := by
  have hflagChar : flag.yz+flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly+flag.yz+flag.all < 2130706433 := by omega
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator := (globalTailCut_dvd_iff (polynomialEmbedding K)
      (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hmixed := BoundaryTailGates.identity_gate flag t y r hr3 hr hy hry (by omega) hflag.1 hflag.2.1
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider S 181265
      (by simpa using hnodes) hagreement (by norm_num [w]) hTailNumerator D t r
      (by norm_num [w]) hDlow hDchar hbox hflagChar hmixed
    have hpositive : 1 ≤ identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hp := S.y_dependent
      have hd := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181265 _ hprovider hagreement
      (by norm_num [w]) (by rw [hnodes]; norm_num) hpositive
    have hinc' : Gamma.card*50194 ≤ 131073*80880*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      simpa only [hnodes,w] using hinc
    have hnum : scale*Gamma.card ≤ MovingFiberRetainedStage6811.numerator source scale t y r flag := by
      apply Nat.le_of_mul_le_mul_left (c := 50194) _ (by decide)
      calc
        50194*(scale*Gamma.card) = scale*(Gamma.card*50194) := by ring
        _ ≤ scale*(131073*80880*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w) :=
          Nat.mul_le_mul_left _ hinc'
        _ ≤ _ := by simpa only [Nat.mul_assoc] using hidentityAbs
    exact (Nat.le_div_iff_mul_le hscale).mpr (by simpa only [Nat.mul_comm] using hnum)
  · have hmixed := BoundaryTailGates.reduced_gate flag t y r hr3 hr hy hry (by omega) hflag.1 hflag.2.1
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (80879+1)*(BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail (BoundaryTailReduced.reducedBaseOrd S hTail hflagChar hmixed C)
        181265 D t r (by simpa using hnodes) hagreement (by norm_num [w]) (by norm_num [w])
        hDlow hDchar hbox (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed)
        (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hTail hflagChar hmixed C) hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hTail hflagChar hmixed C)
    have hmov : 2*(flag.zOnly+flag.yz+flag.all)*(t+1) < 2130706433 := by
      have hm := Nat.mul_le_mul (show 2*(flag.zOnly+flag.yz+flag.all) ≤ 2*7501 by omega)
        (show t+1 ≤ 7502 by omega)
      omega
    exact retained_stage_bound t y r scale hr3 hry (by omega) S source hscale hscaleDiv hfree hTail
      hflagChar hmixed (by omega) hmov (by norm_num [w]) (by
        unfold cellNormal
        rw [BoundaryTailAlgebra.normalFlag_eq_cell t y r hr3 hry]
        simpa only [add_yz,nsmul_yz,unitAllFlag,mul_zero,add_zero] using
          hybridC1Gate_of_le t y r 80879 hry (by norm_num)) htangent h2 hfact hgood

#print axioms stage_bound
end
end ProximityPrize.SubmissionLower.MovingFiberFixedStage6811
