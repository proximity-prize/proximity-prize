import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch
import ProximityPrize.SubmissionLower.ContactRegularZeroBudget6676Research

/-! .

 -/

namespace ProximityPrize.SubmissionLower.ContactMovingRecursiveIncidence6719Research

open scoped Classical BigOperators
open ContactFlagBezout6543Research ContactResidualSupportParametersResearch
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveIterationResearch.CurveResidualStage
open ContactIdentityResidualGlobalTransformResearch
open ContactFlagAffineResidualAutomorphismResearch
open ContactIdentityResidualIncidenceResearch
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactNearPencilStratifiedIncidenceResearch
open ContactNearPencil6600ArithmeticResearch
open ContactRegularZeroBudget6676Research
open ContactIncidence

noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000

variable {K Ω I : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable {φ : Polynomial K →+* Ω} {Γ : Finset K} {x : I → K}
variable {p e d : ℕ} [CharP Ω p] {sf cf : FlagDegree}
variable {support : ResidualSupportParameters}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω
local instance : DecidableEq I := Classical.decEq I

/-- . -/
def InvariantAdvance
    (Inv : ∀ n, CurveResidualStage φ Γ x p e sf cf n support → Prop) : Prop :=
  ∀ n (A : CurveResidualStage φ Γ x p e sf cf n support),
    A.identities ≠ ∅ → A.identities.card ≤ n → Inv n A →
    ∃ B : CurveResidualStage φ Γ x p e sf cf (n-A.identities.card) support,
      Inv (n-A.identities.card) B ∧
      B.nodes.card = A.nodes.card-A.identities.card ∧
      ∀ γ ∈ Γ, (A.agreementFiber γ).card-A.identities.card ≤
        (B.agreementFiber γ).card

theorem exists_terminal_descendant_of_invariant_advance
    (Inv : ∀ n, CurveResidualStage φ Γ x p e sf cf n support → Prop)
    (hadvance : InvariantAdvance Inv)
    (S : CurveResidualStage φ Γ x p e sf cf d support) (hInv : Inv d S) :
    ∃ D : S.TerminalDescendant, Inv D.degree D.stage := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hempty : S.identities = ∅
      · refine ⟨{
          degree := d
          degree_le := le_rfl
          stage := S
          terminal := Or.inl hempty
          nodes_card := by simp
          agreement_card := by simp
        }, hInv⟩
      · by_cases hcard : S.identities.card ≤ d
        · have hkpos : 0 < S.identities.card := Finset.card_pos.mpr
            (Finset.nonempty_iff_ne_empty.mpr hempty)
          obtain ⟨Snext, hInvNext, hnodes, hagreements⟩ :=
            hadvance d S hempty hcard hInv
          have hdegree_lt : d - S.identities.card < d := by omega
          obtain ⟨Dnext, hDInv⟩ :=
            ih (d - S.identities.card) hdegree_lt Snext hInvNext
          have hDle : Dnext.degree ≤ d - S.identities.card :=
            Dnext.degree_le
          have hdegree_split : d - Dnext.degree =
              S.identities.card +
                ((d - S.identities.card) - Dnext.degree) := by
            omega
          refine ⟨{
            degree := Dnext.degree
            degree_le := Dnext.degree_le.trans
              (Nat.sub_le d S.identities.card)
            stage := Dnext.stage
            terminal := Dnext.terminal
            nodes_card := ?_
            agreement_card := ?_
          }, ?_⟩
          · rw [Dnext.nodes_card, hnodes, hdegree_split]
            exact Nat.sub_sub _ _ _
          · intro gamma hgamma
            have hstep := hagreements gamma hgamma
            have htail := Dnext.agreement_card gamma hgamma
            have hmono :
                ((S.agreementFiber gamma).card - S.identities.card) -
                    ((d - S.identities.card) - Dnext.degree) ≤
                  (Snext.agreementFiber gamma).card -
                    ((d - S.identities.card) - Dnext.degree) :=
              Nat.sub_le_sub_right hstep _
            calc
              (S.agreementFiber gamma).card - (d - Dnext.degree) =
                  ((S.agreementFiber gamma).card - S.identities.card) -
                    ((d - S.identities.card) - Dnext.degree) := by
                rw [hdegree_split]
                exact (Nat.sub_sub _ _ _).symm
              _ ≤ (Snext.agreementFiber gamma).card -
                    ((d - S.identities.card) - Dnext.degree) := hmono
              _ ≤ (Dnext.stage.agreementFiber gamma).card := htail
          · exact hDInv
        · have hmany : d < S.identities.card := Nat.lt_of_not_ge hcard
          refine ⟨{
            degree := d
            degree_le := le_rfl
            stage := S
            terminal := Or.inr
              ⟨hmany, S.card_le_pencil_of_many_identities hmany⟩
            nodes_card := by simp
            agreement_card := by simp
          }, hInv⟩


/-- .

 -/
theorem recursive_curve_stratified_incidence_of_regular_invariant
    {a : ℕ}
    (S : CurveResidualStage φ Γ x p e sf cf d support)
    (Inv : ∀ n, CurveResidualStage φ Γ x p e sf cf n support → Prop)
    (hadvance : InvariantAdvance Inv) (hinit : Inv d S)
    (degreeCost unitCost U V zCharge : ℕ)
    (hzero : ∀ n (A : CurveResidualStage φ Γ x p e sf cf n support),
      Inv n A → ∀ i ∈ A.nodes,
        agreementPolynomial φ A.F n (x i) (A.u0 i) (A.u1 i) ∉ A.primeIdeal →
        FiniteRegularZeroSetBound A.primeIdeal (regularitySurface φ A.F)
          (agreementPolynomial φ A.F n (x i) (A.u0 i) (A.u1 i))
          (n * degreeCost + unitCost))
    (hda : d < a)
    (hagreement : ∀ gamma ∈ Γ, a ≤ (S.agreementFiber gamma).card)
    (hlarge : ∀ D : S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Γ.card * (a - d) ≤ (e + 1) * (a - d) * zCharge)
    (hdegree : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Γ.card * (a - d) ≤
      U * degreeCost + V * unitCost + (e + 1) * (a - d) * zCharge := by
  classical
  obtain ⟨D, hDInv⟩ := exists_terminal_descendant_of_invariant_advance Inv hadvance S hinit
  rcases D.terminal with hproper | hpencil
  · let k := d - D.degree
    have hk : k ≤ d := Nat.sub_le d D.degree
    have hDle : D.degree ≤ d := D.degree_le
    have hdegreeEq : D.degree = d - k := by
      dsimp only [k]
      omega
    have hnodeEq : D.stage.nodes.card = S.nodes.card - k := by
      simpa only [k] using D.nodes_card
    have hterminalAgreement : ∀ gamma ∈ Γ,
        a - k ≤ (D.stage.agreementFiber gamma).card := by
      intro gamma hgamma
      exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
        (by simpa only [k] using D.agreement_card gamma hgamma)
    have hterminalFiber : ∀ i ∈ D.stage.nodes,
        (Γ.filter (fun gamma ↦ D.stage.Agrees gamma i)).card ≤
          D.degree * degreeCost + unitCost := by
      intro i hi
      have hz := hzero D.degree D.stage hDInv i hi
        (D.stage.proper_agreement_of_terminal hproper hi)
      exact agreement_fiber_card_le_of_regular_zero_bound φ D.stage.primeIdeal
        D.stage.F D.stage.selected Γ p D.degree
        D.stage.characteristic_bound D.stage.degree_le D.stage.solution
        D.stage.regular D.stage.on_prime
        (x i) (D.stage.u0 i) (D.stage.u1 i)
        (D.degree * degreeCost + unitCost) hz
    have hrawTerminal := incidence_after_exempt_nodes
      (fun gamma i ↦ D.stage.Agrees gamma i)
      Γ D.stage.nodes ∅ (a - k)
        (D.degree * degreeCost + unitCost)
      (by simp) hterminalAgreement (by
        intro i hi
        exact hterminalFiber i (by simpa using hi))
    have hraw : Γ.card * (a - k) ≤
        (S.nodes.card - k) * ((d - k) * degreeCost + unitCost) := by
      simpa only [Finset.card_empty, Nat.sub_zero, hnodeEq, hdegreeEq] using
        hrawTerminal
    have hmain : Γ.card * (a - d) ≤ U * degreeCost + V * unitCost :=
      stratified_incidence_linear Γ.card S.nodes.card a d k
        degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
    exact hmain.trans (Nat.le_add_right _ _)
  · have htail := hlarge D hpencil.1
    exact htail.trans (Nat.le_add_left _ _)


/-- .
 -/
theorem invariantAdvance_of_historical_transition
    (hφ : Function.Injective φ)
    (Inv : ∀ n, CurveResidualStage φ Γ x p e sf cf n support → Prop)
    (htransport : ∀ {n m}
      {A : CurveResidualStage φ Γ x p e sf cf n support}
      {B : CurveResidualStage φ Γ x p e sf cf m support},
      A.ResidualTransition B → Inv n A → Inv m B) : InvariantAdvance Inv := by
  intro n A hne hcard hInv
  obtain ⟨B, ht, hn, ha⟩ := A.advance_card_certified hφ hne hcard
  exact ⟨B, htransport ht hInv, hn, ha⟩

/-- .
 -/
theorem invariantAdvance_of_relation
    (Inv : ∀ n, CurveResidualStage φ Γ x p e sf cf n support → Prop)
    (Rel : ∀ {n m}, CurveResidualStage φ Γ x p e sf cf n support →
      CurveResidualStage φ Γ x p e sf cf m support → Prop)
    (hstep : ∀ n (A : CurveResidualStage φ Γ x p e sf cf n support),
      A.identities ≠ ∅ → A.identities.card ≤ n →
      ∃ B : CurveResidualStage φ Γ x p e sf cf (n-A.identities.card) support,
        Rel A B ∧ B.nodes.card = A.nodes.card-A.identities.card ∧
        ∀ γ ∈ Γ, (A.agreementFiber γ).card-A.identities.card ≤
          (B.agreementFiber γ).card)
    (htransport : ∀ {n m}
      {A : CurveResidualStage φ Γ x p e sf cf n support}
      {B : CurveResidualStage φ Γ x p e sf cf m support},
      Rel A B → Inv n A → Inv m B) : InvariantAdvance Inv := by
  intro n A hne hcard hInv
  obtain ⟨B, ht, hn, ha⟩ := hstep n A hne hcard
  exact ⟨B, htransport ht hInv, hn, ha⟩

end
end ProximityPrize.SubmissionLower.ContactMovingRecursiveIncidence6719Research
