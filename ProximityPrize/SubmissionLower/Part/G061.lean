import ProximityPrize.SubmissionLower.Part.G060


section Compact_SecondJetFixedStage
/-! A scaled C2 stage bound from the actual second-jet component budgets.
The selected seeds avoid the global leading coefficient. Keeping the scaling
through the estimate permits summing geometric factors before rounding. -/
namespace ProximityPrize.SubmissionLower.SecondJetFixedStage
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open RCN084 RCN146 RCN087 RCN335 RCN174 RCN275 RCN234 RCN156
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

theorem stage_card_le_scaled
    (D t y r : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 6917) (hy : y ≤ 136) (hr : r ≤ 30)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80791 flag
      w (cellSupport t y r))
    (hnodes : S.nodes.card = 181353+80791)
    (hagreement : ∀ gamma ∈ Gamma, 181353 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧ flag.zOnly+flag.yz+flag.all ≤ t)
    (P : SecondJetSupport.Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0) (hB : 2*(n0-(k+1)) ≤ B)
    (hn : n0 ≤ (SecondJetCoefficients.asS P).natDegree)
    (hdiv : ∀ d ≤ k, S.F ∣ SecondJetClearedHelper.helper P S.F (s-d) d)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : (k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff) ≠ 0) :
    (k+1)*Gamma.card ≤
      (k+1)*flagMixed flag (cellFirstTail t y r) (cellHybridCoordinateC1 t y r)+
      (w+5)*flagMixed flag (cellFirstTail t y r)
        (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) := by
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = y := by dsimp [cellB,cellS]; omega
  have hts : cellA t y+cellB y r+cellS r+3 = t := by dsimp [cellA,cellB,cellS]; omega
  have hflagChar : flag.yz+flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly+flag.yz+flag.all < 2130706433 := by omega
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator := (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hmixed := Lower80788.HybridGatesC2.identity_mixed_gateC2
      (cellB y r) (cellS r) flag (by omega) (by omega) (by omega) (by omega)
    have hprovider := actual_identityCurveCountProvider S 181353 hnodes hagreement
      (by norm_num [RCN327.w]) hTailNumerator D t r (by norm_num [RCN327.w])
      hDlow hDchar hbox hflagChar hmixed
    have hpositive : 1 ≤ identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hp := S.y_dependent
      have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181353 _ hprovider hagreement
      (by norm_num [RCN327.w]) (by rw [hnodes]; norm_num) hpositive
    have hid := SecondJetIdentity.identity_le_normal flag t y r hyt hry hr3
    have hc : Gamma.card ≤ flagMixed flag (cellFirstTail t y r) (cellHybridCoordinateC1 t y r) := by
      have hh : Gamma.card*50282 ≤ 50282*
          flagMixed flag (cellFirstTail t y r) (cellHybridCoordinateC1 t y r) := by
        calc
          Gamma.card*50282 ≤ (S.nodes.card-w)*(80791+1)*
              identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := hinc
          _ = 131073*80792*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) 131071 := by
            rw [hnodes]; rfl
          _ ≤ _ := hid
      exact Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_comm] using hh) (by decide : 0 < 50282)
    exact (Nat.mul_le_mul_left (k+1) hc).trans (Nat.le_add_right _ _)
  · have hmixed := Lower80788.HybridGatesC2.reduced_mixed_gateC2
      (cellB y r) (cellS r) flag (by omega) (by omega) (by omega) (by omega)
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G
          (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
            (80791+1)*(reducedBudgetFamily S hTail hflagChar hmixed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail (reducedBaseOrd S hTail hflagChar hmixed C)
        181353 D t r hnodes hagreement (by norm_num [RCN327.w]) (by norm_num [RCN327.w])
        hDlow hDchar hbox (reducedBudgetFamily S hTail hflagChar hmixed)
        (reducedBudgetFamily_yzPositive S hTail hflagChar hmixed C) hall
        (reducedBudgetFamily_yzPole S hTail hflagChar hmixed C)
    exact SecondJetRetainedStage.stage_card_le_scaled t y r hr3 hry (by omega) S hTail
      hflagChar hmixed (hybridC1Gate_of_le t y r 80791 hry (by norm_num)) htangent
      P B U L s k n0 hS hP hBU hUL hdn hB hn hdiv h2 hfact hgood

end
end ProximityPrize.SubmissionLower.SecondJetFixedStage

end Compact_SecondJetFixedStage
