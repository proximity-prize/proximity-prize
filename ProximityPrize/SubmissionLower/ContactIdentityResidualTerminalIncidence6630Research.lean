import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidenceResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualIteration6630Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch

/-!
# Incidence consumers after terminal identity residualization

These theorems hide the entire finite residualization recursion behind one
geometric terminal-fiber provider.  The terminal stage has no identity cuts,
and its degree is exactly the original degree minus the total number of
removed nodes, so the existing linear incidence compression applies with no
ledger loss.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidence6630Research

open scoped Classical
open ContactIdentityResidualIteration6630Research
open ContactIdentityResidualIteration6630Research.ResidualStage6630
open ContactNearPencil6600ArithmeticResearch
open ContactNearPencil6630ArithmeticResearch
open ContactIncidence
open ContactPrimeSeedIncidence
open ContactFlagBezout6543Research

noncomputable section

set_option autoImplicit false

variable {K Omega Iota : Type} [Field K] [Field Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {p e : ℕ} [CharP Omega p] {flag : FlagDegree}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- One recursively stabilized incidence layer.  The provider only has to
bound fibers at terminal states; properness is supplied automatically from
the empty identity set. -/
theorem recursive_stratified_incidence_bound
    (hphi : Function.Injective phi) {w a : ℕ}
    (S : ResidualStage6630 phi Gamma x p e flag w)
    (degreeCost unitCost U V : ℕ)
    (hwa : w < a)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (S.agreementFiber gamma).card)
    (hfiber : ∀ D : S.TerminalDescendant, ∀ i ∈ D.stage.nodes,
      ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card ≤
        D.degree * degreeCost + unitCost)
    (hdegree : ∀ k ≤ w,
      (S.nodes.card - k) * (a - w) * (w - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ w,
      (S.nodes.card - k) * (a - w) ≤ V * (a - k)) :
    Gamma.card * (a - w) ≤ U * degreeCost + V * unitCost := by
  classical
  obtain ⟨D⟩ := S.exists_terminal_descendant hphi
  let k := w - D.degree
  have hk : k ≤ w := Nat.sub_le w D.degree
  have hDle : D.degree ≤ w := D.degree_le
  have hdegreeEq : D.degree = w - k := by
    dsimp only [k]
    omega
  have hnodeEq : D.stage.nodes.card = S.nodes.card - k := by
    simpa only [k] using D.nodes_card
  have hterminalAgreement : ∀ gamma ∈ Gamma,
      a - k ≤ (D.stage.agreementFiber gamma).card := by
    intro gamma hgamma
    exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
      (by simpa only [k] using D.agreement_card gamma hgamma)
  have hterminalFiber : ∀ i ∈ D.stage.nodes,
      (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card ≤
        D.degree * degreeCost + unitCost := by
    intro i hi
    exact hfiber D i hi
      (D.stage.proper_agreement_of_terminal D.terminal hi)
  have hrawTerminal := incidence_after_exempt_nodes
    (fun gamma i ↦ D.stage.Agrees gamma i)
    Gamma D.stage.nodes ∅ (a - k)
      (D.degree * degreeCost + unitCost)
    (by simp) hterminalAgreement (by
      intro i hi
      exact hterminalFiber i (by simpa using hi))
  have hraw : Gamma.card * (a - k) ≤
      (S.nodes.card - k) * ((w - k) * degreeCost + unitCost) := by
    simpa only [Finset.card_empty, Nat.sub_zero, hnodeEq, hdegreeEq] using
      hrawTerminal
  exact stratified_incidence_linear Gamma.card S.nodes.card a w k
    degreeCost unitCost U V hk hwa hraw (hdegree k hk) (hunit k hk)

/-- Scaled recursive layer used when the terminal geometric fiber theorem is
already multiplied by the invariant gap `a-w`. -/
theorem recursive_scaled_stratified_incidence_bound
    (hphi : Function.Injective phi) {w a : ℕ}
    (S : ResidualStage6630 phi Gamma x p e flag w)
    (degreeCost unitCost U V : ℕ)
    (hwa : w < a)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (S.agreementFiber gamma).card)
    (hfiber : ∀ D : S.TerminalDescendant, ∀ i ∈ D.stage.nodes,
      ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * (a - w) ≤
        D.degree * degreeCost + unitCost)
    (hdegree : ∀ k ≤ w,
      (S.nodes.card - k) * (a - w) * (w - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ w,
      (S.nodes.card - k) * (a - w) ≤ V * (a - k)) :
    Gamma.card * (a - w) ^ 2 ≤ U * degreeCost + V * unitCost := by
  classical
  obtain ⟨D⟩ := S.exists_terminal_descendant hphi
  let k := w - D.degree
  have hk : k ≤ w := Nat.sub_le w D.degree
  have hDle : D.degree ≤ w := D.degree_le
  have hdegreeEq : D.degree = w - k := by
    dsimp only [k]
    omega
  have hnodeEq : D.stage.nodes.card = S.nodes.card - k := by
    simpa only [k] using D.nodes_card
  have hterminalAgreement : ∀ gamma ∈ Gamma,
      a - k ≤ (D.stage.agreementFiber gamma).card := by
    intro gamma hgamma
    exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
      (by simpa only [k] using D.agreement_card gamma hgamma)
  let geometricCost := D.degree * degreeCost + unitCost
  have hgap : 0 < a - w := Nat.sub_pos_of_lt hwa
  have hterminalFiberDiv : ∀ i ∈ D.stage.nodes,
      (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card ≤
        geometricCost / (a - w) := by
    intro i hi
    apply (Nat.le_div_iff_mul_le hgap).mpr
    exact hfiber D i hi
      (D.stage.proper_agreement_of_terminal D.terminal hi)
  have hrawTerminal := incidence_after_exempt_nodes
    (fun gamma i ↦ D.stage.Agrees gamma i)
    Gamma D.stage.nodes ∅ (a - k) (geometricCost / (a - w))
    (by simp) hterminalAgreement (by
      intro i hi
      exact hterminalFiberDiv i (by simpa using hi))
  have hrawScaled : (Gamma.card * (a - w)) * (a - k) ≤
      (S.nodes.card - k) * ((w - k) * degreeCost + unitCost) := by
    calc
      (Gamma.card * (a - w)) * (a - k) =
          (Gamma.card * (a - k)) * (a - w) := by ring
      _ ≤ ((D.stage.nodes.card * (geometricCost / (a - w))) *
          (a - w)) := Nat.mul_le_mul_right (a - w) (by
            simpa only [Finset.card_empty, Nat.sub_zero] using hrawTerminal)
      _ = D.stage.nodes.card *
          ((geometricCost / (a - w)) * (a - w)) := by ring
      _ ≤ D.stage.nodes.card * geometricCost :=
        Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ = (S.nodes.card - k) *
          ((w - k) * degreeCost + unitCost) := by
        simp only [hnodeEq, geometricCost, hdegreeEq]
  have hlinear := stratified_incidence_linear
    (Gamma.card * (a - w)) S.nodes.card a w k
    degreeCost unitCost U V hk hwa hrawScaled
    (hdegree k hk) (hunit k hk)
  calc
    Gamma.card * (a - w) ^ 2 = (Gamma.card * (a - w)) * (a - w) := by ring
    _ ≤ U * degreeCost + V * unitCost := hlinear

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidence6630Research

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidence6630Research.recursive_stratified_incidence_bound
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidence6630Research.recursive_scaled_stratified_incidence_bound
