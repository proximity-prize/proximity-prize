import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIterationResearch

/-! .
 -/

namespace ProximityPrize.SubmissionLower.ContactActualResidualStep6719Research

open scoped Classical
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators ContactComponentPencils ContactPrimeSeedIncidence
open ContactIdentityResidualPencilResearch
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualSurfaceResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactResidualSupportParametersResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactFlagAffineResidualAutomorphismResearch
open ContactFlagBezout6543Research
open ContactFlagTriangularProjectionResearch
open ContactIdentityResidualPrimeTransportResearch
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveIterationResearch.CurveResidualStage

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

variable {K Omega Iota : Type} [Field K] [Field Omega]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

abbrev Poly3 (Omega : Type) [Field Omega] := MvPolynomial (Fin 3) Omega
abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

variable {phi : Polynomial K →+* Omega} {Gamma : Finset K}
variable {x : Iota → K} {p e : ℕ} [CharP Omega p]
variable {surfaceFlag cutFlag : FlagDegree} {d : ℕ}
variable {support : ResidualSupportParameters}

/-- . -/
def ActualResidualTransition
    {dnext : ℕ}
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
    (Snext : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag dnext support) : Prop :=
  ∃ (P0 P1 V : Polynomial K) (hv : phi V ≠ 0),
    Snext.F = globalResidualHom P0 P1 V S.F ∧
    Snext.G = residualAlgHom (phi P0) (phi V) (phi P1)
      (phi P0.derivative) (phi V.derivative) (phi P1.derivative) S.G ∧
    Snext.T = residualAlgHom (phi P0) (phi V) (phi P1)
      (phi P0.derivative) (phi V.derivative) (phi P1.derivative) S.T ∧
    Snext.primeIdeal = S.primeIdeal.map
      (residualEquiv (phi P0) (phi V) (phi P1)
        (phi P0.derivative) (phi V.derivative) (phi P1.derivative) hv).toRingEquiv.toRingHom

theorem ActualResidualTransition.toResidualTransition {dnext : ℕ}
    {S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support}
    {Snext : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag dnext support}
    (h : ActualResidualTransition S Snext) : ResidualTransition S Snext := by
  obtain ⟨P0, P1, V, hv, _, hG, hT, hprime⟩ := h
  exact ⟨phi P0, phi V, phi P1, phi P0.derivative,
    phi V.derivative, phi P1.derivative, hv, hG, hT, hprime⟩

/-- . -/
theorem actual_advance_certified
    (hphi : Function.Injective phi)
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
    (hne : S.identities ≠ ∅)
    (hcard : S.identities.card ≤ d) :
    0 < S.identities.card ∧
      ∃ Snext : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag
          (d - S.identities.card) support,
        ActualResidualTransition S Snext ∧
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
  let hsupport : ResidualSupportData support S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hsupportRes := hsupport.globalResidual P0 P1 V
  let u0res : Iota → K := fun i ↦ residualReceived J x S.u0 P0 i
  let u1res : Iota → K := fun i ↦ residualReceived J x S.u1 P1 i
  let Snext : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag
      (d - J.card) support := {
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
    surface_s_weight := hsupportRes.s_weight
    surface_ys_weight := hsupportRes.ys_weight
    surface_total_weight := hsupportRes.total_weight
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
  · refine ⟨P0, P1, V, hvphi, rfl, rfl, rfl, ?_⟩
    change Dnext.ideal = _
    exact hDnextIdeal
  · intro gamma hgamma i hi
    exact S.agrees_on_identities gamma hgamma i hi
  · intro gamma hgamma i hi hold
    exact hagree gamma hgamma i (by simpa [Snext, J] using hi) hold

/-- . -/
theorem actual_advance_card_certified
    (hphi : Function.Injective phi)
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
    (hne : S.identities ≠ ∅)
    (hcard : S.identities.card ≤ d) :
    ∃ Snext : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag
        (d - S.identities.card) support,
      ActualResidualTransition S Snext ∧
      Snext.nodes.card = S.nodes.card - S.identities.card ∧
      ∀ gamma ∈ Gamma,
        (S.agreementFiber gamma).card - S.identities.card ≤
          (Snext.agreementFiber gamma).card := by
  letI : S.primeIdeal.IsPrime := S.primeIdeal_isPrime
  obtain ⟨_, Snext, htransition, hnodes, hidAgree, hdescend⟩ :=
    actual_advance_certified hphi S hne hcard
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


end

end ProximityPrize.SubmissionLower.ContactActualResidualStep6719Research
