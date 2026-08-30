import ProximityPrize.SubmissionLower.ContactIdentityResidualIteration
import ProximityPrize.SubmissionLower.ContactIdentityResidualPrimeTransport

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIteration

open scoped Classical
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators ContactComponentPencils ContactPrimeSeedIncidence
open ContactIdentityResidualPencil
open ContactIdentityResidualGlobalTransform
open ContactIdentityResidualSurface
open ContactIdentityResidualGlobalFlag
open ContactResidualSupportParameters
open ContactPost6464MinkowskiRecurrence
open ContactFlagAffineResidualAutomorphism
open ContactFlagBezout
open ContactFlagTriangularProjection
open ContactIdentityResidualPrimeTransport

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

variable {K Omega Iota : Type} [Field K] [Field Omega]

local instance : DecidableEq Iota := Classical.decEq Iota

abbrev Poly3 (Omega : Type) [Field Omega] := MvPolynomial (Fin 3) Omega
abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

structure CurveResidualStage
    (phi : Polynomial K →+* Omega) (Gamma : Finset K) (x : Iota → K)
    (p e : ℕ) [CharP Omega p]
    (surfaceFlag cutFlag : FlagDegree) (d : ℕ)
    (support : ResidualSupportParameters :=
      ResidualSupportParameters.acceptedSupport) where
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
  G_flag_support : ContactFlagBezout.PolynomialInFlag surfaceFlag G
  T_flag_support : ContactFlagBezout.PolynomialInFlag cutFlag T
  surface_s_weight : wt residualSWeights F ≤ support.s
  surface_ys_weight : wt residualYSWeights F ≤ support.ys
  surface_total_weight : wt residualTotalWeights F ≤ support.total
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

namespace CurveResidualStage

variable {phi : Polynomial K →+* Omega} {Gamma : Finset K}
variable {x : Iota → K} {p e : ℕ} [CharP Omega p]
variable {surfaceFlag cutFlag : FlagDegree} {d : ℕ}
variable {support : ResidualSupportParameters}

def primeIdeal
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support) :
    Ideal (Poly3 Omega) := S.primeData.ideal

def identities
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support) :
    Finset Iota :=
  identityNodes phi S.primeIdeal S.F S.nodes x S.u0 S.u1 d

def Agrees
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
    (gamma : K) (i : Iota) : Prop :=
  (S.selected gamma).eval (x i) = S.u0 i + gamma * S.u1 i

local instance
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support) :
    ∀ gamma i, Decidable (S.Agrees gamma i) :=
  fun _ _ ↦ Classical.propDecidable _

def agreementFiber
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
    (gamma : K) : Finset Iota :=
  S.nodes.filter (S.Agrees gamma)

theorem primeIdeal_isPrime
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support) :
    S.primeIdeal.IsPrime := S.primeData.isPrime

theorem surface_mem_primeIdeal
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support) :
    surfaceMap phi S.F ∈ S.primeIdeal := by
  obtain ⟨Q, hQ⟩ := S.G_dvd_surface
  rw [hQ]
  exact S.primeData.ideal.mul_mem_right Q S.primeData.G_mem

theorem regularity_not_mem_primeIdeal
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support) :
    surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) S.F) ∉
      S.primeIdeal :=
  S.primeData.H_not_mem

theorem agrees_on_identities
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support) :
    ∀ gamma ∈ Gamma, ∀ i ∈ S.identities, S.Agrees gamma i := by
  let P := S.primeIdeal
  letI : P.IsPrime := S.primeIdeal_isPrime
  intro gamma hgamma i hi
  exact selected_agrees_on_identity_nodes
    phi P S.F S.nodes x S.u0 S.u1 p d S.characteristic_bound
    (S.selected gamma) gamma (S.degree_le gamma hgamma)
    (S.solution gamma hgamma) (S.regular gamma hgamma)
    (S.on_prime gamma hgamma) i hi

theorem card_le_pencil_of_many_identities
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
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

structure TerminalDescendant
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support) where
  degree : ℕ
  degree_le : degree ≤ d
  stage : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag degree support
  terminal : stage.identities = ∅ ∨
    (degree < stage.identities.card ∧ Gamma.card ≤ e + 1)
  nodes_card : stage.nodes.card = S.nodes.card - (d - degree)
  agreement_card : ∀ gamma ∈ Gamma,
    (S.agreementFiber gamma).card - (d - degree) ≤
      (stage.agreementFiber gamma).card

theorem proper_agreement_of_terminal
    (S : CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
    (hterminal : S.identities = ∅) {i : Iota} (hi : i ∈ S.nodes) :
    agreementPolynomial phi S.F d (x i) (S.u0 i) (S.u1 i) ∉
      S.primeIdeal := by
  intro hmem
  have hid : i ∈ S.identities :=
    Finset.mem_filter.mpr ⟨hi, hmem⟩
  rw [hterminal] at hid
  simp at hid

end CurveResidualStage

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIteration
