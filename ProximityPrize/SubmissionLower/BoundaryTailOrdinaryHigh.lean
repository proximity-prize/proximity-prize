import ProximityPrize.SubmissionLower.BoundaryTailRealization
import ProximityPrize.SubmissionLower.BoundaryTailGates
import ProximityPrize.SubmissionLower.BoundaryTailIdentity
import ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic

namespace ProximityPrize.SubmissionLower.BoundaryTailOrdinaryHigh

open scoped Classical BigOperators
open RCN135 RCN136 RCN139 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095
open RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312
open RCN339 RCN330 RCN174 RCN319 RCN206 RCN287 RCN066 RCN338 RCN199 RCN207
open RCN271 RCN313 RCN234 RCN156 RCN341 RCN085 RCN146 RCN087 RCN203 RCN084 RCN335
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def bound (flag : FlagDegree) (t y r : ℕ) : ℕ :=
  flagMixed flag (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r) +
    65539 * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r)

theorem bound_eq_abs (flag : FlagDegree) (t y r : ℕ)
    (hr3 : 3 ≤ r) (hb : r+2 ≤ y) :
    bound flag t y r = BoundaryTailIdentityArithmetic.newCost flag
      (cellA t y) (cellB y r) (cellS r) := by
  have hfirst := SecondJetIdentity.cell_first_eq t y r
  have hnormal : BoundaryTailProvider.cellNormal t y r =
      Lower80788.HybridIdentityC2.rationalABS (cellA t y) (cellB y r) (cellS r) +
        131071 • unitAllFlag := by
    unfold BoundaryTailProvider.cellNormal
    rw [BoundaryTailAlgebra.normalFlag_eq_cell t y r hr3 hb,
      SecondJetIdentity.cell_normal_eq]
    rfl
  have hfiber : cellMovingFiber t y r =
      Lower80788.HybridIdentityC2.mfibABS (cellA t y) (cellB y r) (cellS r) := rfl
  have hrat : cellRational t y r =
      Lower80788.HybridIdentityC2.rationalABS (cellA t y) (cellB y r) (cellS r) :=
    SecondJetIdentity.cell_normal_eq t y r
  have hcut : cellMovingCut t y r =
      Lower80788.HybridIdentityC2.mcutABS (cellA t y) (cellB y r) (cellS r) := by
    simp only [cellMovingCut, Lower80788.HybridIdentityC2.mcutABS, hrat,
      RCN327.w, Nat.reduceAdd, Nat.reduceMul]
  unfold bound BoundaryTailIdentityArithmetic.newCost BoundaryTailIdentityArithmetic.newNormal
  rw [hfirst, hnormal, hfiber, hcut]

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

/-- The actual ordinary high-cell count at 80811 errors, including the
identity-first-tail branch. No positive Z-degree assumption is used. -/
theorem stage_card_le (D t y r : ℕ)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hr3 : 3 ≤ r) (hb : r+2 ≤ y) (hyt : y ≤ t)
    (hRcap : r ≤ 31) (hYcap : y ≤ 142) (hTcap : t ≤ 7501)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80811 flag
      w (cellSupport t y r))
    (hnodes : S.nodes.card = 181333+80811)
    (hagreement : ∀ gamma ∈ Gamma, 181333 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧
      flag.zOnly+flag.yz+flag.all ≤ t) :
    Gamma.card ≤ bound flag t y r := by
  have hflagChar : flag.yz+flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly+flag.yz+flag.all < 2130706433 := by omega
  have hshort : w+1 ≤ D := by simpa only [RCN327.w] using hDlow
  have hb1 : 1 ≤ cellB y r := by dsimp [cellB]; omega
  have hs1 : 1 ≤ cellS r := by dsimp [cellS]; omega
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator : S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w+1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hidentityGate := BoundaryTailGates.identity_gate flag t y r hr3 hRcap hYcap
      hb hyt hflag.1 hflag.2.1
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider
      (a := cellA t y) (b := cellB y r) (s := cellS r) S 181333 hnodes hagreement
      (by norm_num [RCN327.w]) hTailNumerator D t r
      (by norm_num [RCN327.w]) hshort hDchar hbox hflagChar hidentityGate
    have hpositive : 1 ≤ identityCurveDegree flag (cellA t y) (cellB y r)
        (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hy : 0 < S.G.degreeOf 1 := S.y_dependent
      have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181333
      (identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w)
      hprovider hagreement (by norm_num [RCN327.w])
      (by rw [hnodes]; norm_num [RCN327.w]) hpositive
    have habsorb := BoundaryTailIdentityArithmetic.generic_absorption flag
      (cellA t y) (cellB y r) (cellS r) (Nat.zero_le _) hb1 hs1
    have hscaled : Gamma.card * 50262 ≤ 50262 * bound flag t y r := by
      calc
        Gamma.card * 50262 = Gamma.card * (181333-w) := by norm_num [RCN327.w]
        _ ≤ (S.nodes.card-w) * (80811+1) *
            identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := hinc
        _ = 131073 * 80812 *
            identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) 131071 := by
          rw [hnodes]
          norm_num [RCN327.w]
        _ ≤ 50262 * BoundaryTailIdentityArithmetic.newCost flag
            (cellA t y) (cellB y r) (cellS r) := habsorb
        _ = 50262 * bound flag t y r := by rw [bound_eq_abs flag t y r hr3 hb]
    apply Nat.le_of_mul_le_mul_right ?_ (by decide : 0 < 50262)
    simpa only [Nat.mul_comm] using hscaled
  · have hmixedRed := BoundaryTailGates.reduced_gate flag t y r hr3 hRcap hYcap
      hb hyt hflag.1 hflag.2.1
    have hmix : 2 * (flag.zOnly+flag.yz+flag.all) *
        (cellA t y+cellB y r+cellS r+4) < 2130706433 := by
      have hf : flag.zOnly+flag.yz+flag.all ≤ 7501 := hflag.2.2.trans hTcap
      have ht : cellA t y+cellB y r+cellS r+4 ≤ 7502 := by
        dsimp [cellA, cellB, cellS]
        omega
      exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hf) ht).trans_lt (by decide)
    have hrationalGate : 80811+1 ≤ (BoundaryTailProvider.cellNormal t y r).yz := by
      have hv : 2 ≤ y-r := by omega
      simp only [BoundaryTailProvider.cellNormal, BoundaryTailAlgebra.normalFlag, RCN327.w]
      omega
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G
          (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
            (80811+1) *
              (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixedRed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail
        (BoundaryTailReduced.reducedBaseOrd S hTail hflagChar hmixedRed C)
        181333 D t r hnodes hagreement
        (by norm_num [RCN327.w]) (by norm_num [RCN327.w]) hshort hDchar hbox
        (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixedRed)
        (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hTail hflagChar hmixedRed C)
        hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hTail hflagChar hmixedRed C)
    obtain ⟨provider⟩ := BoundaryTailRealization.exists_provider hr3 hb hyt
      (by norm_num [RCN327.w]) S hTail hflagChar hmixedRed hmix hrationalGate htangent
    exact stage_card_le_divisorBound S provider

end
end ProximityPrize.SubmissionLower.BoundaryTailOrdinaryHigh
