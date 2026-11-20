import ProximityPrize.SubmissionLower.Koala6844TerminalGraph
import ProximityPrize.SubmissionLower.Koala6831MovingPairIncidence


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped Classical BigOperators
open RCN095 RCN130 RCN135 RCN136 RCN137 RCN138 RCN156 RCN159 RCN174 RCN198
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN275 RCN319 RCN327
open LocatorHybridCells Koala6831MovingPairIncidence

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4500000
set_option maxRecDepth 40000

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance terminalHelperDecidableK : DecidableEq K := Classical.decEq K
local instance terminalHelperDecidableI : DecidableEq I := Classical.decEq I
local instance terminalHelperCharP : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

theorem regular_terminal_pair_bound
    (F Q : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hFR : 0 < F.degreeOf 2)
    (hrel : IsRelPrime F Q) (t y r : ℕ) (hr3 : 3 ≤ r) (hry : r+2 ≤ y)
    (hyt : y ≤ t) (htchar : t < 2130706433)
    (hsupport : ResidualSupportData (cellSupport t y r) F)
    (right : FlagDegree) (hqflag : PolynomialInFlag right (surfaceMap (polynomialEmbedding K) Q))
    (hmixed : (right.yz + right.all) * r + y * right.all < 2130706433)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, 180960 ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hQ : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma Q = 0)
    (hno : NoLargeSelectedPencil selected Gamma w 81184) :
    Gamma.card * (180960 * 49889) ≤ flagMixed (originalCumulativeFlag F) right
      (scaledPairFlag (cellSupport t y r) 262144 w 180960 81184) := by
  classical
  let phi := polynomialEmbedding K
  let direction := scaledPairFlag (cellSupport t y r) 262144 w 180960 81184
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = y := by dsimp [cellB,cellS]; omega
  have hts : cellA t y+cellB y r+cellS r+3 = t := by dsimp [cellA,cellB,cellS]; omega
  have hFRsmall : F.degreeOf 2 < 2130706433 :=
    hsupport.coordinate_bounds.2.1.trans_lt (by simpa only [cellSupport,RCN198.support,hs] using (show r < 2130706433 by omega))
  have hproper (g : GeometricFactor K F) : ¬ g.1 ∣ surfaceMap phi Q := by
    have hg := surfaceFactors_spec phi F g.1 g.2
    have hpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 := by omega
    have hgeo : g.1 ∣ geometricSurfaceMap K (GenericField K) F := by
      simpa only [canonical_geometricSurfaceMap] using hg.2
    intro hdvd
    apply hF.not_isUnit
    apply hrel (dvd_refl F)
    exact (geometric_factor_dvd_iff K (GenericField K) F Q hF hpos g.1 hg.1 hgeo).mp
      (by simpa only [canonical_geometricSurfaceMap] using hdvd)
  have hcount (g : GeometricFactor K F) :
      (geometricSeeds K F selected Gamma g).card * (180960 * 49889) ≤
        flagMixed (geometricCumulativeFlag K g) right direction := by
    let Delta := geometricSeeds K F selected Gamma g
    let S := geometricResidualStageOfSupport K (cellSupport t y r) F hF hFR hFRsmall hsupport
      selected Gamma nodes x u0 u1 hinj hdegree hsolution hregular hno (by norm_num [w]) g
    have hsub := geometricSeeds_subset K F selected Gamma g
    have hf := geometricCumulativeFlag_le_support F hF.ne_zero hsupport g
    have hf' : (geometricCumulativeFlag K g).all ≤ r ∧
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ y ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ t := by
      simpa only [cellSupport,RCN198.support,hs,hys,hts] using hf
    have hmix : (right.yz + right.all) * (geometricCumulativeFlag K g).all +
        ((geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all) * right.all < 2130706433 :=
      (Nat.add_le_add (Nat.mul_le_mul_left _ hf'.1) (Nat.mul_le_mul_right _ hf'.2.1)).trans_lt hmixed
    have hgFlags := polynomialIn_surfaceCumulativeFlag g.1
    obtain ⟨budget, hseed⟩ := exists_regular_pair_budget phi F g.1 (surfaceMap phi Q)
      2130706433 (geometricCumulativeFlag K g) right S.G_dvd_surface
      S.irreducible_G (hproper g) S.y_dependent
      (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
      hgFlags hqflag (hf'.2.2.trans_lt htchar) hmix
    have hDeltaRegular (gamma : K) (hg : gamma ∈ Delta) :=
      selectedPoint_regular_of_specialization K F selected gamma (hregular gamma (hsub hg))
    have hQzero (gamma : K) (hg : gamma ∈ Delta) :
        MvPolynomial.eval (selectedPoint phi selected gamma) (surfaceMap phi Q) = 0 := by
      rw [selectedPoint_surface_evaluation,hQ gamma (hsub hg),map_zero]
    have hGzero (gamma : K) (hg : gamma ∈ Delta) :
        MvPolynomial.eval (selectedPoint phi selected gamma) g.1 = 0 := by
      exact S.on_component gamma hg
    have hp := regular_pair_seed_card_le phi (polynomialEmbedding_injective K)
      (cellSupport t y r) hsupport g.1 (surfaceMap phi Q) S.G_dvd_surface
      (geometricCumulativeFlag K g) right budget hseed selected Delta nodes x u0 u1 hinj
      2130706433 w 180960 81184 (by norm_num [w]) (by norm_num [w]) (by norm_num [w])
      (by rw [hnodes]; decide)
      (fun gamma hg => hdegree gamma (hsub hg)) (fun gamma hg => hsolution gamma (hsub hg))
      hDeltaRegular hGzero hQzero (fun gamma hg => hagreement gamma (hsub hg))
      (noLargeSelectedPencil_mono selected Gamma Delta w 81184 hsub hno)
    rw [hnodes] at hp
    exact mul_scale_le_of_pair_bound (cellSupport t y r) 262144 w 180960 81184 _
      (geometricCumulativeFlag K g) right (by norm_num [w]) (by decide) hp
  have cover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma hsolution
  have budget := geometricCumulativeFlag_budgets F hF.ne_zero
  calc
    _ ≤ (∑ g : GeometricFactor K F, (geometricSeeds K F selected Gamma g).card) * (180960 * 49889) :=
      Nat.mul_le_mul_right _ cover
    _ = ∑ g : GeometricFactor K F, (geometricSeeds K F selected Gamma g).card * (180960 * 49889) :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ g : GeometricFactor K F, flagMixed (geometricCumulativeFlag K g) right direction :=
      Finset.sum_le_sum (fun g _ => hcount g)
    _ ≤ _ := RCN084.sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
      (originalCumulativeFlag F) right direction budget.1 budget.2.1 budget.2.2

end

end ProximityPrize.SubmissionLower.Koala6844Terminal

