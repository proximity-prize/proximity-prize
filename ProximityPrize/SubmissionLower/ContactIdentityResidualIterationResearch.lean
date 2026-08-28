import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualSurfaceResearch
import ProximityPrize.SubmissionLower.ContactIdentityZeroSafePencilResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch

/-!
# Iterated actual-identity residualization state

Raw agreement-polynomial covariance under nodal residualization is false.
This module therefore packages every invariant needed to remove a newly
created identity set and repeat.  A nonempty step strictly lowers the selected
polynomial degree, while preserving the surface flag, regularity, component
assignment, and the no-large-pencil condition.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualIterationResearch

open scoped Classical
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators ContactComponentPencils ContactPrimeSeedIncidence
open ContactIdentityResidualPencilResearch
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualSurfaceResearch
open ContactIdentityZeroSafePencilResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactFlagAffineResidualAutomorphismResearch
open ContactFlagBezout6543Research
open ContactFlagTriangularProjectionResearch

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

variable {K Omega Iota : Type} [Field K] [Field Omega]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

abbrev Poly3 (Omega : Type) [Field Omega] := MvPolynomial (Fin 3) Omega
abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-- Complete algebraic state at one residual degree.  `nodes` contains only
the nodes not removed at earlier identity stages. -/
structure ResidualStage
    (phi : Polynomial K →+* Omega) (Gamma : Finset K) (x : Iota → K)
    (p e : ℕ) [CharP Omega p] (flag : FlagDegree) (d : ℕ) where
  nodes : Finset Iota
  u0 : Iota → K
  u1 : Iota → K
  selected : K → Polynomial K
  F : Poly4 K
  G : Poly3 Omega
  irreducible_G : Irreducible G
  G_dvd_surface : G ∣ surfaceMap phi F
  y_dependent : 0 < G.degreeOf 1
  regular_proper : ¬ G ∣ surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F)
  flag_support : ContactFlagBezout6543Research.PolynomialInFlag flag G
  surface_s_weight : wt residualSWeights F ≤ 8
  surface_ys_weight : wt residualYSWeights F ≤ 43
  surface_total_weight : wt residualTotalWeights F ≤ 503
  x_injective : Set.InjOn x nodes
  degree_le : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ d
  solution : ∀ gamma ∈ Gamma,
    specialization K (selected gamma) gamma F = 0
  regular : ∀ gamma ∈ Gamma,
    MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
      (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
        (phi Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0
  on_component : ∀ gamma ∈ Gamma,
    MvPolynomial.eval (selectedPoint phi selected gamma) G = 0
  no_large_pencil : NoLargeSelectedPencil selected Gamma d e
  characteristic_bound : d < p

namespace ResidualStage

variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {p e : ℕ} [CharP Omega p] {flag : FlagDegree} {d : ℕ}

/-- The principal prime belonging to the current component. -/
def componentIdeal (S : ResidualStage phi Gamma x p e flag d) :
    Ideal (Poly3 Omega) := Ideal.span {S.G}

/-- All current agreement cuts that vanish identically on the current
component. -/
def identities (S : ResidualStage phi Gamma x p e flag d) : Finset Iota :=
  identityNodes phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d

/-- The actual received-word agreement relation at this stage. -/
def Agrees (S : ResidualStage phi Gamma x p e flag d)
    (gamma : K) (i : Iota) : Prop :=
  (S.selected gamma).eval (x i) = S.u0 i + gamma * S.u1 i

local instance (S : ResidualStage phi Gamma x p e flag d) :
    ∀ gamma i, Decidable (S.Agrees gamma i) := fun _ _ ↦ Classical.propDecidable _

def agreementFiber (S : ResidualStage phi Gamma x p e flag d)
    (gamma : K) : Finset Iota :=
  S.nodes.filter (S.Agrees gamma)

theorem componentIdeal_isPrime
    (S : ResidualStage phi Gamma x p e flag d) : S.componentIdeal.IsPrime := by
  exact Ideal.isPrime_span_singleton_of_prime S.irreducible_G.prime

theorem surface_mem_componentIdeal
    (S : ResidualStage phi Gamma x p e flag d) :
    surfaceMap phi S.F ∈ S.componentIdeal := by
  exact Ideal.mem_span_singleton.mpr S.G_dvd_surface

theorem regularity_not_mem_componentIdeal
    (S : ResidualStage phi Gamma x p e flag d) :
    surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) S.F) ∉
      S.componentIdeal := by
  intro h
  exact S.regular_proper (Ideal.mem_span_singleton.mp h)

theorem selected_point_ideal
    (S : ResidualStage phi Gamma x p e flag d)
    {gamma : K} (hgamma : gamma ∈ Gamma) :
    S.componentIdeal ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint phi S.selected gamma)).toRingHom := by
  change Ideal.span {S.G} ≤
    RingHom.ker
      (MvPolynomial.aeval (selectedPoint phi S.selected gamma)).toRingHom
  rw [Ideal.span_le]
  intro Q hQ
  simp only [Set.mem_singleton_iff] at hQ
  subst Q
  exact S.on_component gamma hgamma

/-- Every current identity node is an actual agreement for every selected
seed, including at residual degree zero. -/
theorem agrees_on_identities
    (S : ResidualStage phi Gamma x p e flag d) :
    ∀ gamma ∈ Gamma, ∀ i ∈ S.identities, S.Agrees gamma i := by
  let P := S.componentIdeal
  letI : P.IsPrime := S.componentIdeal_isPrime
  intro gamma hgamma i hi
  exact selected_agrees_on_identity_nodes
    phi P S.F S.nodes x S.u0 S.u1 p d S.characteristic_bound
    (S.selected gamma) gamma (S.degree_le gamma hgamma)
    (S.solution gamma hgamma) (S.regular gamma hgamma)
    (S.selected_point_ideal hgamma) i hi

/-- The zero-safe component reconstruction bounds every identity set by the
current residual degree. -/
theorem identities_card_le
    (S : ResidualStage phi Gamma x p e flag d) : S.identities.card ≤ d := by
  let P := S.componentIdeal
  letI : P.IsPrime := S.componentIdeal_isPrime
  exact identityNodes_card_le_of_r_dependent_principal_zero_safe
    phi P S.F S.surface_mem_componentIdeal S.regularity_not_mem_componentIdeal
    S.nodes x S.u0 S.u1 d S.x_injective S.G rfl S.y_dependent

/-- One nonempty identity extraction produces a complete next stage.  The
last two clauses expose exactly the agreement transport needed by recursive
incidence: removed identities are full agreements, and every remaining old
agreement descends to the new received word. -/
theorem advance
    (hphi : Function.Injective phi)
    (S : ResidualStage phi Gamma x p e flag d)
    (hne : S.identities ≠ ∅) :
    0 < S.identities.card ∧
      ∃ Snext : ResidualStage phi Gamma x p e flag
          (d - S.identities.card),
        Snext.nodes = S.nodes \ S.identities ∧
        (∀ gamma ∈ Gamma, ∀ i ∈ S.identities,
          S.Agrees gamma i) ∧
        ∀ gamma ∈ Gamma, ∀ i ∈ Snext.nodes,
          S.Agrees gamma i → Snext.Agrees gamma i := by
  classical
  let P := S.componentIdeal
  letI : P.IsPrime := S.componentIdeal_isPrime
  let J := S.identities
  have hJsub : J ⊆ S.nodes := identityNodes_subset
    phi P S.F S.nodes x S.u0 S.u1 d
  have hJcard : J.card ≤ d := S.identities_card_le
  have hJpos : 0 < J.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr (by simpa only [J] using hne))
  have hvalues : ∀ gamma ∈ Gamma, ∀ i ∈ J,
      (S.selected gamma).eval (x i) = S.u0 i + gamma * S.u1 i := by
    intro gamma hgamma i hi
    exact S.agrees_on_identities gamma hgamma i hi
  obtain ⟨P0, P1, residual, hP0, hP1, hresdeg, hnores, hnormal,
      hagree, hsolution, hregular⟩ :=
    exists_residual_family_with_surface_data
      phi hphi J S.nodes x S.u0 S.u1 d e hJsub hJcard S.x_injective
      S.selected Gamma S.degree_le hvalues S.no_large_pencil S.F
      S.solution S.regular
  let V : Polynomial K := Lagrange.nodal J x
  have hV : V ≠ 0 := (Lagrange.nodal_monic (s := J) (v := x)).ne_zero
  let Fres : Poly4 K := globalResidualHom P0 P1 V S.F
  let Gres : Poly3 Omega :=
    residualAlgHom (phi P0) (phi V) (phi P1)
      (phi P0.derivative) (phi V.derivative) (phi P1.derivative) S.G
  obtain ⟨hGirred, hGdiv, hGy, hGproper, hGflag⟩ :=
    residual_component_transport phi hphi P0 P1 V hV S.F S.G
      S.irreducible_G S.G_dvd_surface S.y_dependent S.regular_proper
      flag S.flag_support
  obtain ⟨hFs, hFys, hFtotal⟩ :=
    globalResidualHom_surface_flag_weights P0 P1 V S.F
      S.surface_s_weight S.surface_ys_weight S.surface_total_weight
  let u0res : Iota → K := fun i ↦ residualReceived J x S.u0 P0 i
  let u1res : Iota → K := fun i ↦ residualReceived J x S.u1 P1 i
  let Snext : ResidualStage phi Gamma x p e flag (d - J.card) := {
    nodes := S.nodes \ J
    u0 := u0res
    u1 := u1res
    selected := residual
    F := Fres
    G := Gres
    irreducible_G := hGirred
    G_dvd_surface := hGdiv
    y_dependent := hGy
    regular_proper := hGproper
    flag_support := hGflag
    surface_s_weight := hFs
    surface_ys_weight := hFys
    surface_total_weight := hFtotal
    x_injective := S.x_injective.mono (Finset.sdiff_subset)
    degree_le := hresdeg
    solution := hsolution
    regular := hregular
    on_component := by
      intro gamma hgamma
      have heval := eval_residualComponent_selectedPoint
        phi P0 P1 V (residual gamma) (S.selected gamma) gamma S.G
          (hnormal gamma hgamma)
      change MvPolynomial.eval
        (selectedPoint phi (fun _ ↦ residual gamma) gamma) Gres = 0
      exact heval.trans (S.on_component gamma hgamma)
    no_large_pencil := hnores
    characteristic_bound := lt_of_le_of_lt (Nat.sub_le d J.card)
      S.characteristic_bound
  }
  refine ⟨?hpos, Snext, rfl, ?_, ?_⟩
  · simpa only [J] using hJpos
  · intro gamma hgamma i hi
    exact S.agrees_on_identities gamma hgamma i hi
  · intro gamma hgamma i hi hold
    exact hagree gamma hgamma i (by simpa [Snext, J] using hi) hold

/-- Cardinal form of one advance step.  Removing the current identities loses
exactly that many nodes and at most that many agreements for each seed. -/
theorem advance_card
    (hphi : Function.Injective phi)
    (S : ResidualStage phi Gamma x p e flag d)
    (hne : S.identities ≠ ∅) :
    ∃ Snext : ResidualStage phi Gamma x p e flag
        (d - S.identities.card),
      Snext.nodes.card = S.nodes.card - S.identities.card ∧
      ∀ gamma ∈ Gamma,
        (S.agreementFiber gamma).card - S.identities.card ≤
          (Snext.agreementFiber gamma).card := by
  letI : S.componentIdeal.IsPrime := S.componentIdeal_isPrime
  obtain ⟨_, Snext, hnodes, hidAgree, hdescend⟩ := S.advance hphi hne
  have hIdentityNodesSubset : S.identities ⊆ S.nodes := by
    exact identityNodes_subset
      phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d
  refine ⟨Snext, ?_, ?_⟩
  · rw [hnodes, Finset.card_sdiff_of_subset hIdentityNodesSubset]
  · intro gamma hgamma
    have hIdentitySubset : S.identities ⊆ S.agreementFiber gamma := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨
        (identityNodes_subset phi S.componentIdeal S.F
          S.nodes x S.u0 S.u1 d) hi,
        hidAgree gamma hgamma i hi⟩
    have hRemainingSubset :
        S.agreementFiber gamma \ S.identities ⊆
          Snext.agreementFiber gamma := by
      intro i hi
      obtain ⟨holdFiber, hnotIdentity⟩ := Finset.mem_sdiff.mp hi
      obtain ⟨hinode, hold⟩ := Finset.mem_filter.mp holdFiber
      apply Finset.mem_filter.mpr
      refine ⟨?_, hdescend gamma hgamma i ?_ hold⟩
      · rw [hnodes]
        exact Finset.mem_sdiff.mpr ⟨hinode, hnotIdentity⟩
      · rw [hnodes]
        exact Finset.mem_sdiff.mpr ⟨hinode, hnotIdentity⟩
    calc
      (S.agreementFiber gamma).card - S.identities.card =
          (S.agreementFiber gamma \ S.identities).card := by
        rw [Finset.card_sdiff_of_subset hIdentitySubset]
      _ ≤ (Snext.agreementFiber gamma).card :=
        Finset.card_le_card hRemainingSubset

/-- A terminal descendant has no remaining identity agreement cuts.  Its
degree records the total number of removed nodes exactly, and its agreement
count loses at most the same total for every seed. -/
structure TerminalDescendant
    (S : ResidualStage phi Gamma x p e flag d) where
  degree : ℕ
  degree_le : degree ≤ d
  stage : ResidualStage phi Gamma x p e flag degree
  terminal : stage.identities = ∅
  nodes_card : stage.nodes.card = S.nodes.card - (d - degree)
  agreement_card : ∀ gamma ∈ Gamma,
    (S.agreementFiber gamma).card - (d - degree) ≤
      (stage.agreementFiber gamma).card

/-- At a terminal stage every remaining agreement polynomial is a proper cut
of the current principal component. -/
theorem proper_agreement_of_terminal
    (S : ResidualStage phi Gamma x p e flag d)
    (hterminal : S.identities = ∅) {i : Iota} (hi : i ∈ S.nodes) :
    ¬ S.G ∣ agreementPolynomial phi S.F d (x i) (S.u0 i) (S.u1 i) := by
  intro hdvd
  have hmem : i ∈ S.identities := by
    apply Finset.mem_filter.mpr
    exact ⟨hi, Ideal.mem_span_singleton.mpr hdvd⟩
  rw [hterminal] at hmem
  simpa using hmem

/-- Repeated actual-identity extraction always terminates.  This theorem is
well-founded on the current residual degree; the zero-safe identity cap makes
the endpoint `d = 0` part of the same proof. -/
theorem exists_terminal_descendant
    (hphi : Function.Injective phi)
    (S : ResidualStage phi Gamma x p e flag d) :
    Nonempty S.TerminalDescendant := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hterminal : S.identities = ∅
      · exact ⟨{
          degree := d
          degree_le := le_rfl
          stage := S
          terminal := hterminal
          nodes_card := by simp
          agreement_card := by simp
        }⟩
      · have hk : S.identities.card ≤ d := S.identities_card_le
        have hkpos : 0 < S.identities.card := Finset.card_pos.mpr
          (Finset.nonempty_iff_ne_empty.mpr hterminal)
        obtain ⟨Snext, hnodes, hagreements⟩ :=
          S.advance_card hphi hterminal
        have hdegree_lt : d - S.identities.card < d := by omega
        obtain ⟨Dnext⟩ := ih (d - S.identities.card) hdegree_lt Snext
        have hDle : Dnext.degree ≤ d - S.identities.card :=
          Dnext.degree_le
        have hdegree_split : d - Dnext.degree =
            S.identities.card +
              ((d - S.identities.card) - Dnext.degree) := by
          omega
        refine ⟨{
          degree := Dnext.degree
          degree_le := Dnext.degree_le.trans (Nat.sub_le d S.identities.card)
          stage := Dnext.stage
          terminal := Dnext.terminal
          nodes_card := ?_
          agreement_card := ?_
        }⟩
        · rw [Dnext.nodes_card, hnodes]
          rw [hdegree_split]
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

end ResidualStage

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualIterationResearch

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualIterationResearch.ResidualStage.advance
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualIterationResearch.ResidualStage.exists_terminal_descendant
