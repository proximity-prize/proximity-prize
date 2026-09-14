import ProximityPrize.SubmissionLower.HigherRootIdentityBridge6810P3

namespace ProximityPrize.SubmissionLower.HigherRootSourceStage6810P3
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open BoundaryTailProvider
open RCN084 RCN146 RCN087 RCN335 RCN174 RCN275 RCN234 RCN156
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

theorem stage_card_le_dual
    (D t y r : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 7501) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80850 flag
      w (cellSupport t y r))
    (hnodes : S.nodes.card = 181294+80850)
    (hagreement : ∀ gamma ∈ Gamma, 181294 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧ flag.zOnly+flag.yz+flag.all ≤ t)
    (P : SecondJetSupport.Poly (K := K))
    (hS : ∀ e ∈ P.support, e 1 ≤ 21)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ 46 ∧ e 1+e 2+e 3 ≤ 158 ∧
      e 1+e 2+e 3+e 4 ≤ 2695)
    (hn : 7 ≤ (SecondJetCoefficients.asS P).natDegree)
    (hdiv : ∀ d ≤ 5, S.F ∣ SecondJetClearedHelper.helper P S.F (21-d) d)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : ((5).factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff) ≠ 0)
 :
    Gamma.card ≤ HigherRootFixedStage6810.dualNumerator flag t y r 6 ⟨2537,119,44⟩ / 36 := by
  have hV : SecondJetRelaxedFlag.budgetFlag 46 158 2695 (5+1) 7 = ⟨2537,119,44⟩ := rfl
  have hAbs := HigherRootIdentityBridge6810P3.identity_absorption_profile flag t y r hr3 hry (by omega)
  have hb := HigherRootFixedStage6810.stage_card_le_dual_of_identity_absorption
    D t y r hDlow hDchar ht hy hr hr3 hry hyt S hnodes hagreement hbox hflag
    P 46 158 2695 21 5 7 hS hP (by decide) (by decide) (by decide) (by decide)
    hn hdiv h2 hfact hgood (by simpa only [hV, Nat.reduceAdd, Nat.reducePow] using hAbs)
  simpa only [hV, Nat.reduceAdd, Nat.reducePow] using hb

end
end ProximityPrize.SubmissionLower.HigherRootSourceStage6810P3
