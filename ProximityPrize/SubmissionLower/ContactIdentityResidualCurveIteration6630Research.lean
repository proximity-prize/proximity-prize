import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIterationResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research

/-!
# Inner actual-identity residualization on an arbitrary regular curve prime

The outer residual stage follows a principal surface component.  A regular
curve component is instead an arbitrary prime ideal containing the surface
component `G` and the proper cut `T`, but not the regularity polynomial.
This module transports that exact ideal through the same triangular residual
automorphism.

Unlike a principal R-dependent component, an arbitrary curve prime may have
more identity nodes than the current degree.  Such a state is already the
large-pencil terminal branch.  Consequently `advance` is deliberately
stated only for the complementary mathematical range `0 < identities.card`
and `identities.card ≤ d`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIteration6630Research

open scoped Classical
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators ContactComponentPencils ContactPrimeSeedIncidence
open ContactIdentityResidualPencilResearch
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualSurfaceResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualGlobalFlag6630Research
open ContactPost6464MinkowskiRecurrenceResearch
open ContactFlagAffineResidualAutomorphismResearch
open ContactFlagBezout6543Research
open ContactFlagTriangularProjectionResearch
open ContactIdentityResidualPrimeTransportResearch

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option autoImplicit false

variable {K Omega Iota : Type} [Field K] [Field Omega]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

abbrev Poly3 (Omega : Type) [Field Omega] := MvPolynomial (Fin 3) Omega
abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-- Complete state for recursive proper-cut incidence on one arbitrary
regular curve prime.  Both ambient flag supports are fixed across steps. -/
structure CurveResidualStage6630
    (phi : Polynomial K →+* Omega) (Gamma : Finset K) (x : Iota → K)
    (p e : ℕ) [CharP Omega p]
    (surfaceFlag cutFlag : FlagDegree) (d : ℕ) where
  nodes : Finset Iota
  u0 : Iota → K
  u1 : Iota → K
  selected : K → Polynomial K
  F : Poly4 K
  G : Poly3 Omega
  T : Poly3 Omega
  primeData : RegularPrimeData G T
    (surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F))
  G_dvd_surface : G ∣ surfaceMap phi F
  G_flag_support : ContactFlagBezout6543Research.PolynomialInFlag surfaceFlag G
  T_flag_support : ContactFlagBezout6543Research.PolynomialInFlag cutFlag T
  surface_s_weight : wt residualSWeights F ≤ 8
  surface_ys_weight : wt residualYSWeights F ≤ 40
  surface_total_weight : wt residualTotalWeights F ≤ 617
  x_injective : Set.InjOn x nodes
  degree_le : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ d
  solution : ∀ gamma ∈ Gamma,
    specialization K (selected gamma) gamma F = 0
  regular : ∀ gamma ∈ Gamma,
    MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
      (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
        (phi Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0
  on_prime : ∀ gamma ∈ Gamma, primeData.ideal ≤ RingHom.ker
    (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom
  no_large_pencil : NoLargeSelectedPencil selected Gamma d e
  characteristic_bound : d < p

namespace CurveResidualStage6630

variable {phi : Polynomial K →+* Omega} {Gamma : Finset K}
variable {x : Iota → K} {p e : ℕ} [CharP Omega p]
variable {surfaceFlag cutFlag : FlagDegree} {d : ℕ}

def primeIdeal
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d) :
    Ideal (Poly3 Omega) := S.primeData.ideal

def identities
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d) :
    Finset Iota :=
  identityNodes phi S.primeIdeal S.F S.nodes x S.u0 S.u1 d

def Agrees
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (gamma : K) (i : Iota) : Prop :=
  (S.selected gamma).eval (x i) = S.u0 i + gamma * S.u1 i

local instance
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d) :
    ∀ gamma i, Decidable (S.Agrees gamma i) :=
  fun _ _ ↦ Classical.propDecidable _

def agreementFiber
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (gamma : K) : Finset Iota :=
  S.nodes.filter (S.Agrees gamma)

theorem primeIdeal_isPrime
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d) :
    S.primeIdeal.IsPrime := S.primeData.isPrime

theorem surface_mem_primeIdeal
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d) :
    surfaceMap phi S.F ∈ S.primeIdeal := by
  obtain ⟨Q, hQ⟩ := S.G_dvd_surface
  rw [hQ]
  exact S.primeData.ideal.mul_mem_right Q S.primeData.G_mem

theorem regularity_not_mem_primeIdeal
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d) :
    surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) S.F) ∉
      S.primeIdeal :=
  S.primeData.H_not_mem

/-- Identity cuts on the arbitrary curve prime are still actual agreements
for every selected solution. -/
theorem agrees_on_identities
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d) :
    ∀ gamma ∈ Gamma, ∀ i ∈ S.identities, S.Agrees gamma i := by
  let P := S.primeIdeal
  letI : P.IsPrime := S.primeIdeal_isPrime
  intro gamma hgamma i hi
  exact selected_agrees_on_identity_nodes
    phi P S.F S.nodes x S.u0 S.u1 p d S.characteristic_bound
    (S.selected gamma) gamma (S.degree_le gamma hgamma)
    (S.solution gamma hgamma) (S.regular gamma hgamma)
    (S.on_prime gamma hgamma) i hi

/-- The exact affine-equivalence certificate hidden inside one residual
advance.  Exposing it lets callers transport component-specific geometric
providers without rerunning a whole transformed component budget. -/
def ResidualTransition
    {dnext : ℕ}
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (Snext : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag dnext) : Prop :=
  ∃ (aY v bY aS bS cS : Omega) (hv : v ≠ 0),
    Snext.G = residualAlgHom aY v bY aS bS cS S.G ∧
    Snext.T = residualAlgHom aY v bY aS bS cS S.T ∧
    Snext.primeIdeal =
      S.primeIdeal.map
        (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom

/-- One inner residualization step.  The mapped ideal remains prime, keeps
`G` and `T`, excludes the transformed regularity polynomial, remains
non-point, and contains every transformed selected point. -/
theorem advance_certified
    (hphi : Function.Injective phi)
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (hne : S.identities ≠ ∅)
    (hcard : S.identities.card ≤ d) :
    0 < S.identities.card ∧
      ∃ Snext : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag
          (d - S.identities.card),
        ResidualTransition S Snext ∧
        Snext.nodes = S.nodes \ S.identities ∧
        (∀ gamma ∈ Gamma, ∀ i ∈ S.identities,
          S.Agrees gamma i) ∧
        ∀ gamma ∈ Gamma, ∀ i ∈ Snext.nodes,
          S.Agrees gamma i → Snext.Agrees gamma i := by
  classical
  let P := S.primeIdeal
  letI : P.IsPrime := S.primeIdeal_isPrime
  let J := S.identities
  have hJsub : J ⊆ S.nodes := identityNodes_subset
    phi P S.F S.nodes x S.u0 S.u1 d
  have hJcard : J.card ≤ d := by simpa only [J] using hcard
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
  have hvphi : phi V ≠ 0 := (map_ne_zero_iff phi hphi).mpr hV
  let Fres : Poly4 K := globalResidualHom P0 P1 V S.F
  let Gres : Poly3 Omega :=
    residualAlgHom (phi P0) (phi V) (phi P1)
      (phi P0.derivative) (phi V.derivative) (phi P1.derivative) S.G
  let Tres : Poly3 Omega :=
    residualAlgHom (phi P0) (phi V) (phi P1)
      (phi P0.derivative) (phi V.derivative) (phi P1.derivative) S.T
  let Hres : Poly3 Omega :=
    residualAlgHom (phi P0) (phi V) (phi P1)
      (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
      (surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) S.F))
  let Dmap : RegularPrimeData Gres Tres Hres := by
    simpa only [Gres, Tres, Hres] using
      S.primeData.mapResidual
        (phi P0) (phi V) (phi P1)
        (phi P0.derivative) (phi V.derivative) (phi P1.derivative) hvphi
  have hHres :
      surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) Fres) =
        MvPolynomial.C (phi V) * Hres := by
    simpa only [Fres, Hres] using
      surfaceMap_pderiv_globalResidualHom phi P0 P1 V S.F
  let Dnext : RegularPrimeData Gres Tres
      (surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) Fres)) := by
    have hu : IsUnit (MvPolynomial.C (phi V) : Poly3 Omega) :=
      (isUnit_iff_ne_zero.mpr hvphi).map MvPolynomial.C
    refine {
      ideal := Dmap.ideal
      isPrime := Dmap.isPrime
      G_mem := Dmap.G_mem
      T_mem := Dmap.T_mem
      H_not_mem := ?_
      ne_point := Dmap.ne_point
    }
    intro hmem
    apply Dmap.H_not_mem
    apply (Dmap.ideal.unit_mul_mem_iff_mem hu).mp
    rwa [← hHres]
  have hDnextIdeal : Dnext.ideal =
      S.primeData.ideal.map
        (residualEquiv
          (phi P0) (phi V) (phi P1)
          (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
          hvphi).toRingEquiv.toRingHom := by
    change Dmap.ideal = _
    simpa only [Dmap, id_eq, RegularPrimeData.mapResidual_ideal]
  have hGdiv : Gres ∣ surfaceMap phi Fres := by
    exact (residual_dvd_surfaceMap_globalResidualHom_iff
      phi hphi P0 P1 V hV S.G S.F).mpr S.G_dvd_surface
  have hGflag : ContactFlagBezout6543Research.PolynomialInFlag
      surfaceFlag Gres :=
    polynomialInFlag_residualAlgHom surfaceFlag S.G
      (phi P0) (phi V) (phi P1)
      (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
      S.G_flag_support
  have hTflag : ContactFlagBezout6543Research.PolynomialInFlag
      cutFlag Tres :=
    polynomialInFlag_residualAlgHom cutFlag S.T
      (phi P0) (phi V) (phi P1)
      (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
      S.T_flag_support
  obtain ⟨hFs, hFys, hFtotal⟩ :=
    globalResidualHom_surface_flag_weights6630 P0 P1 V S.F
      S.surface_s_weight S.surface_ys_weight S.surface_total_weight
  let u0res : Iota → K := fun i ↦ residualReceived J x S.u0 P0 i
  let u1res : Iota → K := fun i ↦ residualReceived J x S.u1 P1 i
  let Snext : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag
      (d - J.card) := {
    nodes := S.nodes \ J
    u0 := u0res
    u1 := u1res
    selected := residual
    F := Fres
    G := Gres
    T := Tres
    primeData := Dnext
    G_dvd_surface := hGdiv
    G_flag_support := hGflag
    T_flag_support := hTflag
    surface_s_weight := hFs
    surface_ys_weight := hFys
    surface_total_weight := hFtotal
    x_injective := S.x_injective.mono (Finset.sdiff_subset)
    degree_le := hresdeg
    solution := hsolution
    regular := hregular
    on_prime := by
      intro gamma hgamma
      have hcoords :
          forwardResidualPoint
              (phi P0) (phi V) (phi P1)
              (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
              (selectedPoint phi (fun _ ↦ residual gamma) gamma) =
            selectedPoint phi S.selected gamma := by
        funext i
        fin_cases i <;>
          simp [forwardResidualPoint, selectedPoint,
            ContactPolynomialSolutions.polynomialPoint,
            hnormal gamma hgamma, RingHom.comp_apply] <;> ring
      change Dnext.ideal ≤ RingHom.ker
        (MvPolynomial.aeval
          (selectedPoint phi (fun _ ↦ residual gamma) gamma)).toRingHom
      rw [hDnextIdeal]
      exact map_le_pointKernel_of_forward_eq
        (phi P0) (phi V) (phi P1)
        (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
        hvphi S.primeData.ideal
        (selectedPoint phi (fun _ ↦ residual gamma) gamma)
        (selectedPoint phi S.selected gamma) hcoords
        (S.on_prime gamma hgamma)
    no_large_pencil := hnores
    characteristic_bound := lt_of_le_of_lt (Nat.sub_le d J.card)
      S.characteristic_bound
  }
  refine ⟨?_, Snext, ?_, rfl, ?_, ?_⟩
  · simpa only [J] using hJpos
  · refine ⟨phi P0, phi V, phi P1, phi P0.derivative,
      phi V.derivative, phi P1.derivative, hvphi, rfl, rfl, ?_⟩
    change Dnext.ideal = _
    exact hDnextIdeal
  · intro gamma hgamma i hi
    exact S.agrees_on_identities gamma hgamma i hi
  · intro gamma hgamma i hi hold
    exact hagree gamma hgamma i (by simpa [Snext, J] using hi) hold

/-- Backward-compatible projection of `advance_certified`; existing incidence
callers do not need to mention the affine certificate. -/
theorem advance
    (hphi : Function.Injective phi)
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (hne : S.identities ≠ ∅)
    (hcard : S.identities.card ≤ d) :
    0 < S.identities.card ∧
      ∃ Snext : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag
          (d - S.identities.card),
        Snext.nodes = S.nodes \ S.identities ∧
        (∀ gamma ∈ Gamma, ∀ i ∈ S.identities,
          S.Agrees gamma i) ∧
        ∀ gamma ∈ Gamma, ∀ i ∈ Snext.nodes,
          S.Agrees gamma i → Snext.Agrees gamma i := by
  obtain ⟨hpos, Snext, _, hnodes, hid, hremaining⟩ :=
    S.advance_certified hphi hne hcard
  exact ⟨hpos, Snext, hnodes, hid, hremaining⟩

/-- More than `d` curve identities force the entire selected family into one
base-field affine pencil, hence the no-large-pencil hypothesis immediately
charges the branch. -/
theorem card_le_pencil_of_many_identities
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (hmany : d < S.identities.card) :
    Gamma.card ≤ e + 1 := by
  classical
  let P := S.primeIdeal
  letI : P.IsPrime := S.primeIdeal_isPrime
  have hvalues : ∀ t : {gamma : K // gamma ∈ Gamma}, ∀ i,
      i ∈ S.identities →
        (S.selected t.1).eval (x i) = S.u0 i + t.1 * S.u1 i := by
    intro t i hi
    exact S.agrees_on_identities t.1 t.2 i hi
  obtain ⟨P0, P1, hP0, hP1, _, hpencil⟩ :=
    exists_common_pencil_of_many_identities
      phi P S.F S.surface_mem_primeIdeal S.regularity_not_mem_primeIdeal
      S.nodes x S.u0 S.u1 d S.x_injective hmany
      (fun t : {gamma : K // gamma ∈ Gamma} ↦ t.1)
      (fun t ↦ S.selected t.1)
      (fun t ↦ S.degree_le t.1 t.2) hvalues
  have hfilter : Gamma.filter
      (fun gamma ↦ S.selected gamma =
        P0 + Polynomial.C gamma * P1) = Gamma :=
    Finset.filter_eq_self.mpr
      (fun gamma hgamma ↦ hpencil ⟨gamma, hgamma⟩)
  have hbound := S.no_large_pencil P0 P1 hP0 hP1
  rwa [hfilter] at hbound

/-- Cardinal form of an inner advance. -/
theorem advance_card
    (hphi : Function.Injective phi)
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (hne : S.identities ≠ ∅)
    (hcard : S.identities.card ≤ d) :
    ∃ Snext : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag
        (d - S.identities.card),
      Snext.nodes.card = S.nodes.card - S.identities.card ∧
      ∀ gamma ∈ Gamma,
        (S.agreementFiber gamma).card - S.identities.card ≤
          (Snext.agreementFiber gamma).card := by
  letI : S.primeIdeal.IsPrime := S.primeIdeal_isPrime
  obtain ⟨_, Snext, hnodes, hidAgree, hdescend⟩ :=
    S.advance hphi hne hcard
  have hIdentityNodesSubset : S.identities ⊆ S.nodes := by
    exact identityNodes_subset
      phi S.primeIdeal S.F S.nodes x S.u0 S.u1 d
  refine ⟨Snext, ?_, ?_⟩
  · rw [hnodes, Finset.card_sdiff_of_subset hIdentityNodesSubset]
  · intro gamma hgamma
    have hIdentitySubset : S.identities ⊆ S.agreementFiber gamma := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨hIdentityNodesSubset hi,
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

/-- Cardinal advance retaining the exact affine transition certificate. -/
theorem advance_card_certified
    (hphi : Function.Injective phi)
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (hne : S.identities ≠ ∅)
    (hcard : S.identities.card ≤ d) :
    ∃ Snext : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag
        (d - S.identities.card),
      ResidualTransition S Snext ∧
      Snext.nodes.card = S.nodes.card - S.identities.card ∧
      ∀ gamma ∈ Gamma,
        (S.agreementFiber gamma).card - S.identities.card ≤
          (Snext.agreementFiber gamma).card := by
  letI : S.primeIdeal.IsPrime := S.primeIdeal_isPrime
  obtain ⟨_, Snext, htransition, hnodes, hidAgree, hdescend⟩ :=
    S.advance_certified hphi hne hcard
  have hIdentityNodesSubset : S.identities ⊆ S.nodes := by
    exact identityNodes_subset
      phi S.primeIdeal S.F S.nodes x S.u0 S.u1 d
  refine ⟨Snext, htransition, ?_, ?_⟩
  · rw [hnodes, Finset.card_sdiff_of_subset hIdentityNodesSubset]
  · intro gamma hgamma
    have hIdentitySubset : S.identities ⊆ S.agreementFiber gamma := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨hIdentityNodesSubset hi,
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

/-- The exact terminal dichotomy for inner recursion.  Either every
remaining agreement is a proper cut of the terminal prime, or the selected
family has already paid the no-large-pencil charge. -/
structure TerminalDescendant
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d) where
  degree : ℕ
  degree_le : degree ≤ d
  stage : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag degree
  terminal : stage.identities = ∅ ∨
    (degree < stage.identities.card ∧ Gamma.card ≤ e + 1)
  nodes_card : stage.nodes.card = S.nodes.card - (d - degree)
  agreement_card : ∀ gamma ∈ Gamma,
    (S.agreementFiber gamma).card - (d - degree) ≤
      (stage.agreementFiber gamma).card

/-- At a proper terminal stage, every remaining agreement polynomial is
outside the transformed arbitrary prime. -/
theorem proper_agreement_of_terminal
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (hterminal : S.identities = ∅) {i : Iota} (hi : i ∈ S.nodes) :
    agreementPolynomial phi S.F d (x i) (S.u0 i) (S.u1 i) ∉
      S.primeIdeal := by
  intro hmem
  have hid : i ∈ S.identities :=
    Finset.mem_filter.mpr ⟨hi, hmem⟩
  rw [hterminal] at hid
  simpa using hid

/-- Recursive inner residualization terminates in the exact proper/pencil
dichotomy, preserving the total degree loss and losing no more agreements
than the number of removed identities. -/
theorem exists_terminal_descendant
    (hphi : Function.Injective phi)
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d) :
    Nonempty S.TerminalDescendant := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hempty : S.identities = ∅
      · exact ⟨{
          degree := d
          degree_le := le_rfl
          stage := S
          terminal := Or.inl hempty
          nodes_card := by simp
          agreement_card := by simp
        }⟩
      · by_cases hcard : S.identities.card ≤ d
        · have hkpos : 0 < S.identities.card := Finset.card_pos.mpr
            (Finset.nonempty_iff_ne_empty.mpr hempty)
          obtain ⟨Snext, hnodes, hagreements⟩ :=
            S.advance_card hphi hempty hcard
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
            degree_le := Dnext.degree_le.trans
              (Nat.sub_le d S.identities.card)
            stage := Dnext.stage
            terminal := Dnext.terminal
            nodes_card := ?_
            agreement_card := ?_
          }⟩
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
        · have hmany : d < S.identities.card := Nat.lt_of_not_ge hcard
          exact ⟨{
            degree := d
            degree_le := le_rfl
            stage := S
            terminal := Or.inr
              ⟨hmany, S.card_le_pencil_of_many_identities hmany⟩
            nodes_card := by simp
            agreement_card := by simp
          }⟩

/-- Generic invariant-carrying terminalization.  A caller only proves how its
component-specific provider crosses one certified affine transition; this
theorem composes it along the entire residual path while retaining the exact
terminal and agreement accounting. -/
theorem exists_terminal_descendant_with_invariant
    (hphi : Function.Injective phi)
    (Inv : ∀ n, CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag n → Prop)
    (htransport : ∀ {n m}
      {A : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag n}
      {B : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag m},
      ResidualTransition A B → Inv n A → Inv m B)
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (hInv : Inv d S) :
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
          obtain ⟨Snext, htransition, hnodes, hagreements⟩ :=
            S.advance_card_certified hphi hempty hcard
          have hdegree_lt : d - S.identities.card < d := by omega
          have hInvNext := htransport htransition hInv
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

end CurveResidualStage6630

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIteration6630Research

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIteration6630Research.CurveResidualStage6630.advance
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIteration6630Research.CurveResidualStage6630.exists_terminal_descendant
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIteration6630Research.CurveResidualStage6630.exists_terminal_descendant_with_invariant
