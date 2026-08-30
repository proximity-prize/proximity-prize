import ProximityPrize.SubmissionLower.ContactIdentityResidualSurface
import ProximityPrize.SubmissionLower.ContactResidualSupportParameters
namespace ProximityPrize.SubmissionLower.ContactIdentityResidualIteration

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

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

variable {K Omega Iota : Type} [Field K] [Field Omega]

abbrev Poly3 (Omega : Type) [Field Omega] := MvPolynomial (Fin 3) Omega
abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

structure ResidualStage
    (phi : Polynomial K →+* Omega) (Gamma : Finset K) (x : Iota → K)
    (p e : ℕ) [CharP Omega p] (flag : FlagDegree) (d : ℕ)
    (support : ResidualSupportParameters :=
      ResidualSupportParameters.acceptedSupport) where
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
  flag_support : ContactFlagBezout.PolynomialInFlag flag G
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
  on_component : ∀ gamma ∈ Gamma,
    MvPolynomial.eval (selectedPoint phi selected gamma) G = 0
  no_large_pencil : NoLargeSelectedPencil selected Gamma d e
  characteristic_bound : d < p

namespace ResidualStage

variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {p e : ℕ} [CharP Omega p] {flag : FlagDegree} {d : ℕ}
variable {support : ResidualSupportParameters}

def componentIdeal (S : ResidualStage phi Gamma x p e flag d support) :
    Ideal (Poly3 Omega) := Ideal.span {S.G}

def identities (S : ResidualStage phi Gamma x p e flag d support) : Finset Iota :=
  identityNodes phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d

def Agrees (S : ResidualStage phi Gamma x p e flag d support)
    (gamma : K) (i : Iota) : Prop :=
  (S.selected gamma).eval (x i) = S.u0 i + gamma * S.u1 i

local instance (S : ResidualStage phi Gamma x p e flag d support) :
    ∀ gamma i, Decidable (S.Agrees gamma i) := fun _ _ ↦ Classical.propDecidable _

def agreementFiber (S : ResidualStage phi Gamma x p e flag d support)
    (gamma : K) : Finset Iota :=
  S.nodes.filter (S.Agrees gamma)

theorem componentIdeal_isPrime
    (S : ResidualStage phi Gamma x p e flag d support) : S.componentIdeal.IsPrime := by
  exact Ideal.isPrime_span_singleton_of_prime S.irreducible_G.prime

theorem surface_mem_componentIdeal
    (S : ResidualStage phi Gamma x p e flag d support) :
    surfaceMap phi S.F ∈ S.componentIdeal := by
  exact Ideal.mem_span_singleton.mpr S.G_dvd_surface

theorem regularity_not_mem_componentIdeal
    (S : ResidualStage phi Gamma x p e flag d support) :
    surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) S.F) ∉
      S.componentIdeal := by
  intro h
  exact S.regular_proper (Ideal.mem_span_singleton.mp h)

theorem selected_point_ideal
    (S : ResidualStage phi Gamma x p e flag d support)
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

end ResidualStage

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualIteration
