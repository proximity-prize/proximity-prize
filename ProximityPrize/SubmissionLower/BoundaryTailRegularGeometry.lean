import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.BoundaryTailProvider
import ProximityPrize.SubmissionLower.BoundaryTailFixedStage

namespace ProximityPrize.SubmissionLower.BoundaryTailRegularGeometry
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

open RCN081 RCN130 RCN221 RCN222 RCN137 RCN238 RCN275

theorem regular_seed_bound_scaled
    (D t y r : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 7501) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hFR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w t r)
    (hsupport : ResidualSupportData (cellSupport t y r) F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = 262144)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, 181333 ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected Gamma w 80811)
    (P : SecondJetSupport.Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0) (hB : 2*(n0-(k+1)) ≤ B)
    (hn : n0 ≤ (SecondJetCoefficients.asS P).natDegree)
    (hdiv : ∀ d ≤ k, F ∣ SecondJetClearedHelper.helper P F (s-d) d)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : (k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma)
        (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff) ≠ 0) :
    (k+1)*Gamma.card ≤
      (k+1)*flagMixed (originalCumulativeFlag F) (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r)+
      65539*flagMixed (originalCumulativeFlag F) (cellFirstTail t y r)
        (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) := by
  have hFRsmall : F.degreeOf 2 < 2130706433 :=
    (degreeOf_R_le_of_mem_box F D w t r hbox).trans_lt (by omega)
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = y := by dsimp [cellB,cellS]; omega
  have hts : cellA t y+cellB y r+cellS r+3 = t := by dsimp [cellA,cellB,cellS]; omega
  have hcover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma hsolution
  have hstage (g : GeometricFactor K F) :
      (k+1)*(geometricSeeds K F selected Gamma g).card ≤
        (k+1)*flagMixed (geometricCumulativeFlag K g) (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r)+
        65539*flagMixed (geometricCumulativeFlag K g) (cellFirstTail t y r)
          (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) := by
    let S0 := geometricResidualStageOfSupport K (cellSupport t y r) F hF hFR hFRsmall
      hsupport selected Gamma nodes x u0 u1 hinj hdegree hsolution hregular hno (by norm_num [RCN327.w]) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub := geometricSeeds_subset K F selected Gamma g
    have hag : ∀ gamma ∈ geometricSeeds K F selected Gamma g,
        181333 ≤ (S.agreementFiber gamma).card := by
      intro gamma hgamma
      exact hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support F hF.ne_zero hsupport g
    have hf' : (geometricCumulativeFlag K g).all ≤ r ∧
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ y ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+
          (geometricCumulativeFlag K g).all ≤ t := by
      simpa only [cellSupport,RCN198.support,hs,hys,hts] using hf
    exact BoundaryTailFixedStage.stage_card_le_scaled D t y r hDlow hDchar ht hy hr hr3 hry hyt
      S hnodes hag hbox hf' P B U L s k n0 hS hP hBU hUL hdn hB hn hdiv h2 hfact
      (fun gamma hgamma => hgood gamma (hsub hgamma))
  have hb := geometricCumulativeFlag_budgets F hF.ne_zero
  have hnormal := RCN084.sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
    (originalCumulativeFlag F) (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r) hb.1 hb.2.1 hb.2.2
  have hmove := RCN084.sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
    (originalCumulativeFlag F) (cellFirstTail t y r)
    (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) hb.1 hb.2.1 hb.2.2
  calc
    (k+1)*Gamma.card ≤ (k+1)*∑ g : GeometricFactor K F,
        (geometricSeeds K F selected Gamma g).card := Nat.mul_le_mul_left _ hcover
    _ = ∑ g : GeometricFactor K F, (k+1)*(geometricSeeds K F selected Gamma g).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ g : GeometricFactor K F,
        ((k+1)*flagMixed (geometricCumulativeFlag K g) (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r)+
          65539*flagMixed (geometricCumulativeFlag K g) (cellFirstTail t y r)
            (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)) := Finset.sum_le_sum (fun g _ => hstage g)
    _ = (k+1)*(∑ g : GeometricFactor K F,
        flagMixed (geometricCumulativeFlag K g) (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r))+
      65539*(∑ g : GeometricFactor K F,
        flagMixed (geometricCumulativeFlag K g) (cellFirstTail t y r)
          (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hnormal) (Nat.mul_le_mul_left _ hmove)

end
end ProximityPrize.SubmissionLower.BoundaryTailRegularGeometry
