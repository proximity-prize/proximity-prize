import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualSurfaceResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactIdentityZeroSafePencilResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualIterationResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch

/-!
# Incidence bookkeeping for iterated actual-identity residualization

The geometric residual transform sends every old agreement outside the
chosen identity set to a residual agreement.  This file records the exact
finite-set consequence and the arithmetic invariants needed if the
transformed component acquires a further identity set.

In particular, extracting identities in several rounds is lossless: after
replacing the successive sets by their disjoint union, the agreement gap
`a - w` and the node/degree difference `n - w` are unchanged.  Thus recursive
re-stratification is a genuine fallback for the score-66 route, rather than
an uncontrolled restart.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualIncidenceResearch

open ContactNearPencil6600ArithmeticResearch

section FiniteAgreement

variable {Node : Type*} [DecidableEq Node]

/-- If all chosen identity nodes are old agreements and every remaining old
agreement descends to a residual agreement, then deleting `I` loses exactly
at most `I.card` agreements. -/
theorem residual_agreement_card
    (nodes I : Finset Node) (oldRelation residualRelation : Node → Prop)
    [DecidablePred oldRelation] [DecidablePred residualRelation]
    (a : ℕ)
    (hI : I ⊆ nodes.filter oldRelation)
    (ha : a ≤ (nodes.filter oldRelation).card)
    (hdescend : ∀ i ∈ nodes \ I, oldRelation i → residualRelation i) :
    a - I.card ≤ ((nodes \ I).filter residualRelation).card := by
  have hsub : (nodes.filter oldRelation) \ I ⊆
      (nodes \ I).filter residualRelation := by
    intro i hi
    obtain ⟨hiold, hiI⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hinodes, hold⟩ := Finset.mem_filter.mp hiold
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hinodes, hiI⟩,
        hdescend i (Finset.mem_sdiff.mpr ⟨hinodes, hiI⟩) hold⟩
  calc
    a - I.card ≤ (nodes.filter oldRelation).card - I.card :=
      Nat.sub_le_sub_right ha I.card
    _ = ((nodes.filter oldRelation) \ I).card := by
      rw [Finset.card_sdiff_of_subset hI]
    _ ≤ ((nodes \ I).filter residualRelation).card :=
      Finset.card_le_card hsub

/-- Family-shaped form of `residual_agreement_card`.  It is the exact card
premise passed from the polynomial residual-family theorem to an incidence
caller. -/
theorem residual_family_agreement_card
    {Seed : Type*} (seeds : Finset Seed)
    (nodes I : Finset Node)
    (oldRelation residualRelation : Seed → Node → Prop)
    [∀ seed, DecidablePred (oldRelation seed)]
    [∀ seed, DecidablePred (residualRelation seed)]
    (a : ℕ)
    (hidentity : ∀ seed ∈ seeds, I ⊆ nodes.filter (oldRelation seed))
    (hagreement : ∀ seed ∈ seeds,
      a ≤ (nodes.filter (oldRelation seed)).card)
    (hdescend : ∀ seed ∈ seeds, ∀ i ∈ nodes \ I,
      oldRelation seed i → residualRelation seed i) :
    ∀ seed ∈ seeds,
      a - I.card ≤ ((nodes \ I).filter (residualRelation seed)).card := by
  intro seed hseed
  exact residual_agreement_card nodes I (oldRelation seed)
    (residualRelation seed) a (hidentity seed hseed)
    (hagreement seed hseed) (hdescend seed hseed)

end FiniteAgreement

section IteratedSets

variable {Node : Type*} [DecidableEq Node]

/-- A second identity set chosen only among the nodes remaining after `I`
is disjoint from `I`. -/
theorem disjoint_of_subset_sdiff
    (nodes I J : Finset Node) (hJ : J ⊆ nodes \ I) : Disjoint I J := by
  refine Finset.disjoint_left.mpr ?_
  intro i hiI hiJ
  exact (Finset.mem_sdiff.mp (hJ hiJ)).2 hiI

/-- Successive deletion is deletion by the union. -/
theorem sdiff_sdiff_eq_sdiff_union
    (nodes I J : Finset Node) :
    (nodes \ I) \ J = nodes \ (I ∪ J) := by
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- Cardinalities of successive identity strata add exactly. -/
theorem card_union_of_subset_sdiff
    (nodes I J : Finset Node) (hJ : J ⊆ nodes \ I) :
    (I ∪ J).card = I.card + J.card := by
  rw [Finset.card_union_of_disjoint (disjoint_of_subset_sdiff nodes I J hJ)]

/-- Subtracting the two strata successively is the same as subtracting their
union once. -/
theorem sub_cards_eq_sub_union_card
    (q : ℕ) (nodes I J : Finset Node) (hJ : J ⊆ nodes \ I) :
    (q - I.card) - J.card = q - (I ∪ J).card := by
  rw [Nat.sub_sub, card_union_of_subset_sdiff nodes I J hJ]

end IteratedSets

section Arithmetic

/-- Removing the same number of identities from agreements and degree
preserves the decoding gap. -/
theorem residual_gap_eq
    (a w k : ℕ) (hk : k ≤ w) (hwa : w ≤ a) :
    (a - k) - (w - k) = a - w := by
  omega

/-- The remaining-node count and residual degree have the same invariant
difference. -/
theorem residual_node_degree_eq
    (n w k : ℕ) (hk : k ≤ w) (hwn : w ≤ n) :
    (n - k) - (w - k) = n - w := by
  omega

/-- The invariants remain exact after a second extraction. -/
theorem iterated_residual_invariants
    (n a w k j : ℕ) (hkj : k + j ≤ w)
    (hwa : w ≤ a) (hwn : w ≤ n) :
    ((a - k) - j) - ((w - k) - j) = a - w ∧
      ((n - k) - j) - ((w - k) - j) = n - w := by
  constructor <;> omega

/-- A nonempty new identity stratum strictly decreases the residual degree,
so repeated residualization cannot cycle. -/
theorem residual_degree_strictly_decreases
    (w k j : ℕ) (hk : k ≤ w) (hjpos : 0 < j) (hj : j ≤ w - k) :
    (w - k) - j < w - k := by
  omega

/-- The exact score-66 degree and unit compression inequalities can be
reused after two rounds simply by replacing the round sizes by their sum. -/
theorem score6600_iterated_compression
    (k j : ℕ) (hkj : k + j ≤ w) :
    (n - (k + j)) * gap * (w - (k + j)) ≤
        degreeIncidence * (agreements - (k + j)) ∧
      (n - (k + j)) * gap ≤
        unitIncidence * (agreements - (k + j)) := by
  exact ⟨degree_part_bound (k + j) hkj,
    unit_part_bound (k + j) hkj⟩

end Arithmetic

/-! ## Terminal-state composition over the stabilized iteration state -/

section Terminalization

open scoped Classical
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualGlobalFlagResearch

noncomputable section

variable {K Omega Iota : Type} [Field K] [Field Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {p e : ℕ} [CharP Omega p]
variable {flag : ContactFlagBezout6543Research.FlagDegree}

/-- A terminal residual stage has no component-identity cut left. -/
def IsTerminalStage {d : ℕ}
    (S : ResidualStage phi Gamma x p e flag d) : Prop :=
  S.identities = ∅

/-- At a terminal stage every agreement cut on a remaining node is proper on
the current principal component.  This is the precise condition needed by
the flag/Bézout zero-count caller. -/
theorem terminal_iff_all_cuts_proper {d : ℕ}
    (S : ResidualStage phi Gamma x p e flag d) :
    IsTerminalStage S ↔
      ∀ i ∈ S.nodes,
        ContactPrimeSeedIncidence.agreementPolynomial
          phi S.F d (x i) (S.u0 i) (S.u1 i) ∉ S.componentIdeal := by
  classical
  constructor
  · intro hempty i hi hmem
    have hid : i ∈ S.identities := by
      exact Finset.mem_filter.mpr ⟨hi, hmem⟩
    rw [hempty] at hid
    simpa using hid
  · intro hproper
    change S.identities = ∅
    unfold ContactIdentityResidualIterationResearch.ResidualStage.identities
    unfold ContactComponentPencils.identityNodes
    exact Finset.filter_eq_empty_iff.mpr hproper

/-- The residual transform with zero affine pencil and unit nodal factor is
the identity.  This turns the syntactically transformed global flag theorem
into a theorem for an arbitrary current residual surface. -/
@[simp] theorem globalResidualHom_zero_zero_one
    (F : MvPolynomial (Fin 4) K) :
    globalResidualHom (0 : Polynomial K) 0 1 F = F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
      fin_cases i <;> simp [globalResidualImage, hF]

/-- Agreement support for an arbitrary surface carrying the three score-66
global weight hypotheses. -/
theorem surfaceMap_agreement_in_flag_of_surface_weights
    (F : MvPolynomial (Fin 4) K)
    (hS : ContactPost6464MinkowskiRecurrenceResearch.wt
      residualSWeights F ≤ 6)
    (hYS : ContactPost6464MinkowskiRecurrenceResearch.wt
      residualYSWeights F ≤ 33)
    (hTotal : ContactPost6464MinkowskiRecurrenceResearch.wt
      residualTotalWeights F ≤ 582)
    (d : ℕ) (coeffs : ℕ → K) (x0 u0 u1 : K) :
    ContactFlagBezout6543Research.PolynomialInFlag (residualAgreementFlag d)
      (ContactGenericSurface.surfaceMap phi
        (ContactTaylorNumerators.agreementNumerator F d coeffs x0 u0 u1)) := by
  have h := surfaceMap_globalResidual_agreement_in_flag
    phi (0 : Polynomial K) 0 1 F hS hYS hTotal d coeffs x0 u0 u1
  simpa using h

/-- At a terminal recursive stage, every remaining cut is simultaneously
proper on the current component and contained in the exact residual-degree
flag.  This is the complete local input expected by the terminal geometric
zero-count/Bézout caller. -/
theorem terminal_proper_cuts_in_residual_flag {d : ℕ}
    (S : ResidualStage phi Gamma x p e flag d)
    (hterminal : IsTerminalStage S) :
    ∀ i ∈ S.nodes,
      ContactPrimeSeedIncidence.agreementPolynomial
          phi S.F d (x i) (S.u0 i) (S.u1 i) ∉ S.componentIdeal ∧
        ContactFlagBezout6543Research.PolynomialInFlag
          (residualAgreementFlag d)
          (ContactPrimeSeedIncidence.agreementPolynomial
            phi S.F d (x i) (S.u0 i) (S.u1 i)) := by
  intro i hi
  refine ⟨(terminal_iff_all_cuts_proper S).mp hterminal i hi, ?_⟩
  exact surfaceMap_agreement_in_flag_of_surface_weights
    S.F S.surface_s_weight S.surface_ys_weight S.surface_total_weight
    d (fun j ↦ (j.factorial : K)⁻¹) (x i) (S.u0 i) (S.u1 i)

/-- One recursive edge.  All algebraic invariants live in the endpoint
`ResidualStage` types; the relation records the exact deleted nodes and
agreement transport needed to compose incidence counts. -/
inductive ResidualAdvance :
    (Σ d, ResidualStage phi Gamma x p e flag d) →
      (Σ d, ResidualStage phi Gamma x p e flag d) → Prop
  | step {d : ℕ} (S : ResidualStage phi Gamma x p e flag d)
      (hne : S.identities ≠ ∅)
      (Snext : ResidualStage phi Gamma x p e flag
        (d - S.identities.card))
      (hnodes : Snext.nodes = S.nodes \ S.identities)
      (hold : ∀ gamma ∈ Gamma, ∀ i ∈ S.identities,
        S.Agrees gamma i)
      (hdescend : ∀ gamma ∈ Gamma, ∀ i ∈ Snext.nodes,
        S.Agrees gamma i → Snext.Agrees gamma i) :
      ResidualAdvance ⟨d, S⟩ ⟨d - S.identities.card, Snext⟩

/-- Every nonterminal valid stage has a strict residual-advance successor.
This is a direct composition of `ResidualStage.advance`; no one-step
algebra is duplicated here. -/
theorem exists_strict_advance
    (hphi : Function.Injective phi) {d : ℕ}
    (S : ResidualStage phi Gamma x p e flag d)
    (hnot : ¬ IsTerminalStage S) :
    ∃ T : Σ d', ResidualStage phi Gamma x p e flag d',
      ResidualAdvance ⟨d, S⟩ T ∧ T.1 < d := by
  have hne : S.identities ≠ ∅ := hnot
  obtain ⟨hpos, Snext, hnodes, hold, hdescend⟩ :=
    S.advance hphi hne
  refine ⟨⟨d - S.identities.card, Snext⟩,
    ResidualAdvance.step S hne Snext hnodes hold hdescend, ?_⟩
  have hcap := S.identities_card_le
  change d - S.identities.card < d
  omega

/-- Reachability through zero or more strict identity-residualization
steps. -/
abbrev ResidualReachable := Relation.ReflTransGen
  (ResidualAdvance (phi := phi) (Gamma := Gamma) (x := x)
    (p := p) (e := e) (flag := flag))

/-- Repeated actual-identity residualization always reaches a terminal
stage.  Termination is by strict descent of the residual degree; the theorem
returns the full final state and the composed advance chain, not merely a
numeric bound. -/
theorem exists_terminal_reachable
    (hphi : Function.Injective phi) {d : ℕ}
    (S : ResidualStage phi Gamma x p e flag d) :
    ∃ T : Σ d', ResidualStage phi Gamma x p e flag d',
      ResidualReachable ⟨d, S⟩ T ∧ IsTerminalStage T.2 := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hterm : IsTerminalStage S
      · exact ⟨⟨d, S⟩, Relation.ReflTransGen.refl, hterm⟩
      · obtain ⟨⟨dnext, Snext⟩, hstep, hlt⟩ :=
          exists_strict_advance hphi S hterm
        obtain ⟨T, hreach, hterminal⟩ := ih dnext hlt Snext
        exact ⟨T, Relation.ReflTransGen.head hstep hreach, hterminal⟩

/-- Terminalization with the two numerical invariants needed by incidence.

If every seed has at least `a` agreements at the initial degree `d`, the
terminal stage of degree `dFinal` has at least `a-(d-dFinal)` agreements.
Simultaneously, `nodes.card-degree` is unchanged.  Hence both the decoding
gap and the sharp node coefficient survive an arbitrary number of residual
identity extractions. -/
theorem exists_terminal_with_incidence_data
    (hphi : Function.Injective phi) {d a : ℕ}
    (S : ResidualStage phi Gamma x p e flag d)
    (hda : d ≤ a)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (S.agreementFiber gamma).card) :
    ∃ T : Σ d', ResidualStage phi Gamma x p e flag d',
      ResidualReachable ⟨d, S⟩ T ∧
      IsTerminalStage T.2 ∧
      T.1 ≤ d ∧
      T.2.nodes.card - T.1 = S.nodes.card - d ∧
      ∀ gamma ∈ Gamma,
        a - (d - T.1) ≤ (T.2.agreementFiber gamma).card := by
  classical
  letI : DecidableEq Iota := Classical.decEq Iota
  induction d using Nat.strong_induction_on generalizing a with
  | h d ih =>
      by_cases hterm : IsTerminalStage S
      · refine ⟨⟨d, S⟩, Relation.ReflTransGen.refl, hterm,
          le_rfl, rfl, ?_⟩
        simpa using hagreement
      · have hne : S.identities ≠ ∅ := hterm
        obtain ⟨hpos, Snext, hnodes, hold, hdescend⟩ :=
          S.advance hphi hne
        let k := S.identities.card
        have hk : k ≤ d := S.identities_card_le
        have hlt : d - k < d := by
          dsimp only [k]
          omega
        have hdaNext : d - k ≤ a - k := Nat.sub_le_sub_right hda k
        have hnextAgreement : ∀ gamma ∈ Gamma,
            a - k ≤ (Snext.agreementFiber gamma).card := by
          intro gamma hgamma
          letI : S.componentIdeal.IsPrime := S.componentIdeal_isPrime
          have hidentity : S.identities ⊆
              S.nodes.filter (S.Agrees gamma) := by
            intro i hi
            exact Finset.mem_filter.mpr
              ⟨ContactComponentPencils.identityNodes_subset
                  phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d hi,
                hold gamma hgamma i hi⟩
          have hcard := residual_agreement_card
            S.nodes S.identities (S.Agrees gamma) (Snext.Agrees gamma)
            a hidentity (hagreement gamma hgamma)
            (fun i hi ↦ hdescend gamma hgamma i (by simpa [hnodes] using hi))
          simpa only [k, ResidualStage.agreementFiber, hnodes] using hcard
        obtain ⟨⟨dFinal, T⟩, hreach, hterminal, hdFinal,
            hnodeInvariant, hfinalAgreement⟩ :=
          ih (d - k) hlt Snext hdaNext hnextAgreement
        letI : S.componentIdeal.IsPrime := S.componentIdeal_isPrime
        have hidentitiesSub : S.identities ⊆ S.nodes :=
          ContactComponentPencils.identityNodes_subset
            phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d
        have hstepNode :
            Snext.nodes.card - (d - k) = S.nodes.card - d := by
          rw [hnodes, Finset.card_sdiff_of_subset hidentitiesSub]
          dsimp only [k]
          omega
        have hstep : ResidualAdvance ⟨d, S⟩ ⟨d - k, Snext⟩ := by
          exact ResidualAdvance.step S hne Snext hnodes hold hdescend
        refine ⟨⟨dFinal, T⟩,
          Relation.ReflTransGen.head hstep hreach, hterminal,
          ?_, ?_, ?_⟩
        · exact hdFinal.trans (Nat.sub_le d k)
        · exact hnodeInvariant.trans hstepNode
        · intro gamma hgamma
          have hbound := hfinalAgreement gamma hgamma
          change dFinal ≤ d - k at hdFinal
          have hdecomp :
              d - dFinal = k + ((d - k) - dFinal) := by
            omega
          have heq :
              a - (d - dFinal) =
                (a - k) - ((d - k) - dFinal) := by
            calc
              a - (d - dFinal) =
                  a - (k + ((d - k) - dFinal)) := by rw [hdecomp]
              _ = (a - k) - ((d - k) - dFinal) := by
                exact (Nat.sub_sub a k ((d - k) - dFinal)).symm
          rwa [heq]

end

end Terminalization

end ProximityPrize.SubmissionLower.ContactIdentityResidualIncidenceResearch
