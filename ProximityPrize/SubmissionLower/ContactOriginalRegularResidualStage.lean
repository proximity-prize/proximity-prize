import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag
import ProximityPrize.SubmissionLower.ContactIdentityResidualIteration
namespace ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage

open scoped Classical BigOperators
open ContactParameters
open ContactGenericInitialPoint ContactGenericSurface ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate ContactFactorCaps
open ContactPrimeSeedIncidence ContactPolynomialSolutions ContactInterpolation
open ContactTranslation ContactProperCutSeedCount
open ContactOriginalRegularSeedCount
open ContactRegularFactorFlag
open ContactIdentityResidualIteration
open ContactIdentityResidualGlobalFlag
open ContactResidualSupportParameters
open ContactPost6464MinkowskiRecurrence
open ContactFlagBezout

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable (K : Type) [Field K]

def geometricFlag {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : FlagDegree :=
  ⟨g.1.degreeOf (2 : Fin 3), g.1.degreeOf (0 : Fin 3),
    g.1.degreeOf (1 : Fin 3)⟩

theorem polynomialIn_geometricFlag {F : MvPolynomial (Fin 4) K}
    (g : GeometricFactor K F) : PolynomialInFlag (geometricFlag K g) g.1 := by
  intro d hd
  have h0 := MvPolynomial.monomial_le_degreeOf (0 : Fin 3) hd
  have h1 := MvPolynomial.monomial_le_degreeOf (1 : Fin 3) hd
  have h2 := MvPolynomial.monomial_le_degreeOf (2 : Fin 3) hd
  change d 1 ≤ g.1.degreeOf 1 ∧
    d 0 + d 1 ≤ g.1.degreeOf 0 + g.1.degreeOf 1 ∧
    d 0 + d 1 + d 2 ≤
      g.1.degreeOf 2 + g.1.degreeOf 0 + g.1.degreeOf 1
  omega

variable {Iota : Type}

def geometricResidualStageOfSupport
    (support : ResidualSupportParameters)
    {pchar errorCap degree : ℕ} [CharP K pchar]
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hRpos : 0 < F.degreeOf (2 : Fin 4))
    (hRsmall : F.degreeOf (2 : Fin 4) < pchar)
    (hsupport : ResidualSupportData support F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ degree)
    (hsolutions : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hnoPencil : NoLargeSelectedPencil selected Gamma degree errorCap)
    (hdegreeChar : degree < pchar)
    (g : GeometricFactor K F) :
    letI : CharP (GenericField K) pchar := genericField_charP K pchar
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K F selected Gamma g) x pchar errorCap
      (geometricFlag K g) degree support := by
  classical
  letI : CharP (GenericField K) pchar := genericField_charP K pchar
  have hgspec := surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
  have hgirred := hgspec.1
  have hgdiv := hgspec.2
  have hgate := geometric_factor_regular_gate K (GenericField K) F hF pchar
    hRpos hRsmall g.1 hgirred
    (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
  have hsub := geometricSeeds_subset K F selected Gamma g
  exact {
    nodes := nodes
    u0 := u0
    u1 := u1
    selected := selected
    F := F
    G := g.1
    irreducible_G := hgirred
    G_dvd_surface := hgdiv
    y_dependent := hgate.1
    regular_proper := by
      simpa only [canonical_geometricSurfaceMap] using hgate.2.2.2.2
    flag_support := polynomialIn_geometricFlag K g
    surface_s_weight := hsupport.s_weight
    surface_ys_weight := hsupport.ys_weight
    surface_total_weight := hsupport.total_weight
    x_injective := hinj
    degree_le := fun gamma hgamma ↦ hdegree gamma (hsub hgamma)
    solution := fun gamma hgamma ↦ hsolutions gamma (hsub hgamma)
    regular := fun gamma hgamma ↦
      selectedPoint_regular_of_specialization K F selected gamma
        (hregular gamma (hsub hgamma))
    on_component := fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2
    no_large_pencil := noLargeSelectedPencil_mono selected Gamma _ degree errorCap
      hsub hnoPencil
    characteristic_bound := hdegreeChar
  }

end

end ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage
