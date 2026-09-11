import ProximityPrize.SubmissionLower.Part.G057


section Compact_SecondJetRetainedStage
/-! A scaled C2 stage bound from the actual second-jet component budgets.
The selected seeds avoid the global leading coefficient. Keeping the scaling
through the estimate permits summing geometric factors before rounding. -/
namespace ProximityPrize.SubmissionLower.SecondJetRetainedStage
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

theorem stage_card_le_scaled
    (t y r : ℕ) (hr3 : 3 ≤ r) (hb : r+2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all < p ∧ flag.all < p ∧
      flag.zOnly+flag.yz+flag.all < p)
    (hmixedRed : (1+(w+1)*(2*(cellB y r+cellS r+3)-2))*flag.all+
      (flag.yz+flag.all)*((2*(cellS r+2)-2)*(w+1)) < p)
    (hgate : stageErrorCap+1 ≤ (cellHybridCoordinateC1 t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap+1)*(reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C)
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
  classical
  obtain ⟨budget,hcost,hmov⟩ := SecondJetRetainedBudgets.exists_retained_budgets
    (polynomialEmbedding K) S.F S.G
    (globalTailCut (polynomialEmbedding K) S.F (w+1)) S.G_dvd_surface
    P B U L s k n0 hS hP hBU hUL hdn hB hn hdiv h2 hfact
    (reducedBaseOrd S hfirstProper hflagChar hmixedRed) flag (cellFirstTail t y r)
    (unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
      (reducedUnitFamily S hfirstProper hflagChar hmixedRed)
      (reducedBaseOrd S hfirstProper hflagChar hmixedRed))
  let active := Finset.univ.filter (fun C : FirstTailComponent S =>
    surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff ∉ C.1)
  have hcost' : ∀ C : FirstTailComponent S,
      (budget C).zCost = (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).zCost C ∧
      (budget C).yzCost = (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C ∧
      (budget C).allCost = (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).allCost C := by
    intro C
    obtain ⟨hz,hy,ha⟩ := hcost C
    obtain ⟨ez,ey,ea⟩ := unitFamilyOfCongruentCut_costs
      (ordinary_sub_reducedFirstCut_dvd S)
      (reducedUnitFamily S hfirstProper hflagChar hmixedRed)
      (reducedBaseOrd S hfirstProper hflagChar hmixedRed) C
    exact ⟨hz.trans ez,hy.trans ey,ha.trans ea⟩
  have hinactive : ∀ C : FirstTailComponent S, C ∉ active →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card = 0 := by
    intro C hC
    apply SecondJetExceptionalComponents.component_empty_of_nonvanishing _ _ _
      (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff)
      Gamma _ C ?_ hgood
    simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hC
  obtain ⟨provider⟩ := SecondJetHybridProvider.exists_provider_on_active_components
    t y r hr3 hb hyt S hfirstProper (cellFirstTail t y r)
    (reducedBudgetFamily S hfirstProper hflagChar hmixedRed)
    (reducedBaseOrd S hfirstProper hflagChar hmixedRed)
    budget hcost' active (∑ C ∈ active, (budget C).movingCost) hinactive (le_refl _)
    hgate htangent
    (transportedWeightedResultantsGeneral S hfirstProper hflagChar hmixedRed)
  have hc := Nat.mul_le_mul_left (k+1) (stage_card_le_divisorBound S provider)
  have hm := Nat.mul_le_mul_left (w+5) hmov
  calc
    (k+1)*Gamma.card ≤ (k+1)*
        (flagMixed flag (cellFirstTail t y r) (cellHybridCoordinateC1 t y r)+
          (w+5)*(∑ C ∈ active, (budget C).movingCost)) := hc
    _ = (k+1)*flagMixed flag (cellFirstTail t y r) (cellHybridCoordinateC1 t y r)+
          (w+5)*((k+1)*(∑ C ∈ active, (budget C).movingCost)) := by ring
    _ ≤ _ := Nat.add_le_add_left hm _

end
end ProximityPrize.SubmissionLower.SecondJetRetainedStage

end Compact_SecondJetRetainedStage
