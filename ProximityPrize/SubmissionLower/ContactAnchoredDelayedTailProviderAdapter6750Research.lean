import ProximityPrize.SubmissionLower.ContactAnchoredDelayedTailLocalDVR6750Research
import ProximityPrize.SubmissionLower.ContactReducedAgreementFlagBridge6800Research
import ProximityPrize.SubmissionLower.ContactTwoTailResultantProvider6732Research
import ProximityPrize.SubmissionLower.ContactTwoTailTangentCost6732Research

 








namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredDelayedTailProviderAdapter6750Research

open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research ContactTwoTailRecurrence6731Research
open ContactProperCutSeedCount
open ContactPrimeSeedIncidence ContactFlagBezout6543Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactMovingAgreementCertificate6719Research
open ContactResidualSupportParametersResearch
open ContactAnchoredDelayedTailLocalDVR6750Research
open ContactReducedAgreementFlagBridge6800Research
open ContactTwoTailResultantProvider6732Research
open ContactTwoTailTangentCost6732Research
open ContactTranslation ContactInterpolation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {tightSupport : ResidualSupportParameters}

 
def loosenStage
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW tightSupport)
    (hs : tightSupport.s ≤ anchoredFixedSupport.s)
    (hys : tightSupport.ys ≤ anchoredFixedSupport.ys)
    (htotal : tightSupport.total ≤ anchoredFixedSupport.total) :
    AnchoredStage K I Gamma x p flag :=
  { S with
    surface_s_weight := S.surface_s_weight.trans hs
    surface_ys_weight := S.surface_ys_weight.trans hys
    surface_total_weight := S.surface_total_weight.trans htotal }

 

theorem loosenStage_one_le_localMultiplicity
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW tightSupport)
    (hs : tightSupport.s ≤ anchoredFixedSupport.s)
    (hys : tightSupport.ys ≤ anchoredFixedSupport.ys)
    (htotal : tightSupport.total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1)) :
    ∀ C, 1 ≤ localMultiplicity (loosenStage S hs hys htotal)
      (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper) C := by
  exact one_le_localMultiplicity (loosenStage S hs hys htotal) hfirstProper

 

theorem loosenStage_dichotomy_with_tangent
    {tailFlag1 : FlagDegree}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW tightSupport)
    (hs : tightSupport.s ≤ anchoredFixedSupport.s)
    (hys : tightSupport.ys ≤ anchoredFixedSupport.ys)
    (htotal : tightSupport.total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (anchoredErrors + 1) * B.yzCost C) :
    ∀ C : FirstTailComponent S,
      (∃ delay, 1 ≤ delay ∧
        delay ≤ localMultiplicity (loosenStage S hs hys htotal)
          (canonicalLocalDVRFamily (loosenStage S hs hys htotal)
            hfirstProper) C ∧
        globalTailCut (polynomialEmbedding K) S.F
          (anchoredW + 1 + delay) ∉ C.1) ∨
      ((∀ delay, globalTailCut (polynomialEmbedding K) S.F
          (anchoredW + 1 + delay) ∈ C.1) ∧
        (componentSeeds (GenericField K) S.G
          (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
            (anchoredErrors + 1) * B.yzCost C) := by
  intro C
  have dichotomy := local_order_tail_dichotomy (loosenStage S hs hys htotal)
    (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper)
    C hfirstProper
  rcases dichotomy.2 with hproper | hall
  · exact Or.inl hproper
  · exact Or.inr ⟨hall, htangent C hall⟩

 


def PolynomialInFlagMod6750 {Omega : Type} [Field Omega]
    (P : Ideal (MvPolynomial (Fin 3) Omega))
    (r : FlagDegree) (T2 : MvPolynomial (Fin 3) Omega) : Prop :=
  ∃ T2red, PolynomialInFlag r T2red ∧ T2 - T2red ∈ P

 


def reducedAgreementDirection6750
    (P : ResidualSupportParameters) : FlagDegree :=
  ⟨2 * (P.total - P.ys), 2 * (P.ys - P.s), 2 * P.s - 2⟩

 
def reducedResidualAgreementFlag6750
    (P : ResidualSupportParameters) (d : ℕ) : FlagDegree :=
  ⟨(reducedAgreementDirection6750 P).zOnly * d,
    1 + (reducedAgreementDirection6750 P).yz * d,
    (reducedAgreementDirection6750 P).all * d⟩

theorem reducedResidualAgreementFlag6750_ys
    (P : ResidualSupportParameters) (d : ℕ) :
    (reducedResidualAgreementFlag6750 P d).yz +
        (reducedResidualAgreementFlag6750 P d).all =
      1 + d * (2 * P.ys - 2) := by
  have hs := P.s_le_ys
  have h1 := P.one_le_s
  have hcoeff :
      2 * (P.ys - P.s) + (2 * P.s - 2) = 2 * P.ys - 2 := by
    rw [Nat.mul_sub_left_distrib]
    omega
  simp only [reducedResidualAgreementFlag6750,
    reducedAgreementDirection6750]
  rw [← hcoeff]
  ring

theorem reducedResidualAgreementFlag6750_total
    (P : ResidualSupportParameters) (d : ℕ) :
    (reducedResidualAgreementFlag6750 P d).zOnly +
        (reducedResidualAgreementFlag6750 P d).yz +
        (reducedResidualAgreementFlag6750 P d).all =
      1 + d * (2 * P.total - 2) := by
  have hs := P.s_le_ys
  have ht := P.ys_le_total
  have h1 := P.one_le_s
  have hcoeff : 2 * (P.total - P.ys) + 2 * (P.ys - P.s) +
      (2 * P.s - 2) = 2 * P.total - 2 := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    omega
  simp only [reducedResidualAgreementFlag6750,
    reducedAgreementDirection6750]
  rw [← hcoeff]
  ring

 

theorem laterTail_in_reduced_delay_secondFlag6750
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW tightSupport)
    (C : FirstTailComponent S) (delay : ℕ) (hdelay : 1 ≤ delay) :
    PolynomialInFlagMod6750 C.1
      (delay • reducedResidualAgreementFlag6750 tightSupport
        (anchoredW + 2))
      (globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1 + delay)) := by
  let d := anchoredW + 1 + delay
  let Tred := reducedGlobalTailCut (polynomialEmbedding K) S.F tightSupport.s d
  have hscale : d ≤ delay * (anchoredW + 2) := by
    dsimp only [d]
    norm_num [anchoredW]
    omega
  have hred :
      PolynomialInFlag (reducedResidualAgreementFlag6750 tightSupport d) Tred := by
    let Hsupport : ResidualSupportData tightSupport S.F :=
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
    apply reducedGlobalTailCut_in_flag (polynomialEmbedding K)
      (reducedResidualAgreementFlag6750 tightSupport d) S.F tightSupport.s
      tightSupport.ys tightSupport.total d
    · exact tightSupport.one_le_s
    · exact tightSupport.s_le_ys
    · exact tightSupport.s_le_ys.trans tightSupport.ys_le_total
    · exact tightSupport.two_le_ys
    · exact tightSupport.two_le_ys.trans tightSupport.ys_le_total
    · exact Hsupport.coordinate_bounds.2.1
    · exact S.surface_ys_weight
    · exact S.surface_total_weight
    · simp only [reducedResidualAgreementFlag6750,
        reducedAgreementDirection6750]
      have hs : 2 * (tightSupport.s - 1) = 2 * tightSupport.s - 2 := by
        omega
      rw [← hs]
      ring_nf
      exact le_rfl
    · rw [reducedResidualAgreementFlag6750_ys]
      have hys : 2 * (tightSupport.ys - 1) = 2 * tightSupport.ys - 2 := by
        omega
      rw [← hys]
      ring_nf
      exact le_rfl
    · rw [reducedResidualAgreementFlag6750_total]
      have htotal : 2 * (tightSupport.total - 1) =
          2 * tightSupport.total - 2 := by
        omega
      rw [← htotal]
      ring_nf
      exact le_rfl
  have hflag : PolynomialInFlag
      (delay • reducedResidualAgreementFlag6750 tightSupport (anchoredW + 2))
      Tred := by
    have hallFlag :
        (reducedResidualAgreementFlag6750 tightSupport d).all ≤
          (delay • reducedResidualAgreementFlag6750 tightSupport
            (anchoredW + 2)).all := by
      simp only [reducedResidualAgreementFlag6750,
        reducedAgreementDirection6750, nsmul_all]
      calc
        (2 * tightSupport.s - 2) * d ≤
            (2 * tightSupport.s - 2) * (delay * (anchoredW + 2)) :=
          Nat.mul_le_mul_left _ hscale
        _ = delay * ((2 * tightSupport.s - 2) * (anchoredW + 2)) := by ring
    have hysFlag :
        (reducedResidualAgreementFlag6750 tightSupport d).yz +
            (reducedResidualAgreementFlag6750 tightSupport d).all ≤
          (delay • reducedResidualAgreementFlag6750 tightSupport
              (anchoredW + 2)).yz +
            (delay • reducedResidualAgreementFlag6750 tightSupport
              (anchoredW + 2)).all := by
      rw [reducedResidualAgreementFlag6750_ys]
      simp only [nsmul_yz, nsmul_all]
      rw [← Nat.mul_add]
      rw [reducedResidualAgreementFlag6750_ys]
      calc
        1 + d * (2 * tightSupport.ys - 2) ≤
            delay + (delay * (anchoredW + 2)) *
              (2 * tightSupport.ys - 2) :=
          Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
        _ = delay *
            (1 + (anchoredW + 2) * (2 * tightSupport.ys - 2)) := by ring
    have htotalFlag :
        (reducedResidualAgreementFlag6750 tightSupport d).zOnly +
            (reducedResidualAgreementFlag6750 tightSupport d).yz +
            (reducedResidualAgreementFlag6750 tightSupport d).all ≤
          (delay • reducedResidualAgreementFlag6750 tightSupport
              (anchoredW + 2)).zOnly +
            (delay • reducedResidualAgreementFlag6750 tightSupport
              (anchoredW + 2)).yz +
            (delay • reducedResidualAgreementFlag6750 tightSupport
              (anchoredW + 2)).all := by
      rw [reducedResidualAgreementFlag6750_total]
      simp only [nsmul_zOnly, nsmul_yz, nsmul_all]
      rw [← Nat.mul_add, ← Nat.mul_add]
      rw [reducedResidualAgreementFlag6750_total]
      calc
        1 + d * (2 * tightSupport.total - 2) ≤
            delay + (delay * (anchoredW + 2)) *
              (2 * tightSupport.total - 2) :=
          Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
        _ = delay *
            (1 + (anchoredW + 2) * (2 * tightSupport.total - 2)) := by ring
    intro exponent hexponent
    have h := hred exponent hexponent
    exact ⟨h.1.trans hallFlag, h.2.1.trans hysFlag,
      h.2.2.trans htotalFlag⟩
  refine ⟨Tred, hflag, ?_⟩
  have hdvd : S.G ∣ globalTailCut (polynomialEmbedding K) S.F d - Tred := by
    have h := cut_dvd_globalTailCut_sub_reducedGlobalTailCut
      (polynomialEmbedding K) S.F S.G S.G_dvd_surface tightSupport.s d
    have hselector :
        (tailSelector6800 d : ℕ → K) = (tailSelector d : ℕ → K) := by
      funext j
      simp only [tailSelector6800, tailSelector]
    have hliteral : literalGlobalTailCut6800 (polynomialEmbedding K) S.F d =
        globalTailCut (polynomialEmbedding K) S.F d := by
      unfold literalGlobalTailCut6800 globalTailCut
      rw [hselector]
    rw [hliteral] at h
    simpa only [Tred] using h
  exact C.1.mem_of_dvd hdvd
    (regularComponent_G_mem (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
      (regularitySurface (polynomialEmbedding K) S.F) C)

 
theorem component_secondTail_card_le_mod
    {Omega Seed : Type} [Field Omega]
    {G T H T2 : MvPolynomial (Fin 3) Omega}
    {surfaceFlag firstTailFlag secondTailFlag : FlagDegree}
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H)
      surfaceFlag firstTailFlag)
    (C : RegularComponent Omega G T H)
    (seeds : Finset Seed) (point : Seed → Fin 3 → Omega)
    (hpoint_injective : Function.Injective point)
    (hT2flag : PolynomialInFlagMod6750 C.1 secondTailFlag T2)
    (hproper : T2 ∉ C.1)
    (hzero : ∀ gamma ∈ componentSeeds Omega G T H seeds point C,
      MvPolynomial.aeval (point gamma) T2 = 0) :
    (componentSeeds Omega G T H seeds point C).card ≤
      B.weightedCost secondTailFlag C := by
  classical
  let component := componentSeeds Omega G T H seeds point C
  let points := component.image point
  have hpointsPrime : ∀ v ∈ points,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime Omega G T H seeds point C gamma hgamma
  have hpointsZero : ∀ v ∈ points, MvPolynomial.aeval v T2 = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact hzero gamma hgamma
  obtain ⟨T2red, hT2redFlag, hcongr⟩ := hT2flag
  have hproperRed : T2red ∉ C.1 := by
    intro hred
    apply hproper
    simpa only [sub_add_cancel] using C.1.add_mem hcongr hred
  have hpointsZeroRed : ∀ v ∈ points,
      MvPolynomial.aeval v T2red = 0 := by
    intro v hv
    have hz := hpointsPrime v hv hcongr
    change MvPolynomial.aeval v (T2 - T2red) = 0 at hz
    rw [map_sub] at hz
    have heq : MvPolynomial.aeval v T2 =
        MvPolynomial.aeval v T2red := sub_eq_zero.mp hz
    exact heq ▸ hpointsZero v hv
  have hbound := (B.primeBudget C).zero_le secondTailFlag T2red
    hT2redFlag hproperRed points hpointsPrime hpointsZeroRed
  have hcard : points.card = component.card :=
    Finset.card_image_of_injective component hpoint_injective
  simpa only [points, component, hcard,
    PrimeFlagBudgetFamily.weightedCost] using hbound

 


theorem exists_delayedTailMultiplicityProvider_of_anchoredDVR
    {tailFlag1 tailFlag2 : FlagDegree}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW tightSupport)
    (hs : tightSupport.s ≤ anchoredFixedSupport.s)
    (hys : tightSupport.ys ≤ anchoredFixedSupport.ys)
    (htotal : tightSupport.total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
    (hlater : ∀ C : FirstTailComponent S, ∀ delay, 1 ≤ delay →
      PolynomialInFlagMod6750 C.1 (delay • tailFlag2)
        (globalTailCut (polynomialEmbedding K) S.F
          (anchoredW + 1 + delay)))
    (htangentGate : anchoredErrors + 1 ≤ tailFlag2.yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (anchoredErrors + 1) * B.yzCost C)
    (hresultants : RegularComponentWeightedInertiaResultantCertificate B
      (fun C => localMultiplicity (loosenStage S hs hys htotal)
        (canonicalLocalDVRFamily (loosenStage S hs hys htotal)
          hfirstProper) C)) :
    Nonempty (DelayedTailMultiplicityProvider
      (tailFlag1 := tailFlag1) (tailFlag2 := tailFlag2) S) := by
  classical
  let S0 := loosenStage S hs hys htotal
  let multiplicity : FirstTailComponent S → ℕ := fun C =>
    localMultiplicity S0 (canonicalLocalDVRFamily S0 hfirstProper) C
  have hone : ∀ C, 1 ≤ multiplicity C := by
    exact loosenStage_one_le_localMultiplicity S hs hys htotal hfirstProper
  have branchBound (C : FirstTailComponent S) :
      ((∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
          globalTailCut (polynomialEmbedding K) S.F
            (anchoredW + 1 + delay) ∉ C.1 ∧
          (componentSeeds (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
              multiplicity C * B.weightedCost tailFlag2 C) ∨
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F
          (anchoredW + 1 + delay) ∈ C.1)) := by
    have dichotomy := local_order_tail_dichotomy S0
      (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · left
      obtain ⟨delay, hdelay, hdelayMu, htail⟩ := hproper
      have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G
          (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C,
          MvPolynomial.aeval
            (selectedPoint (polynomialEmbedding K) S.selected gamma)
            (globalTailCut (polynomialEmbedding K) S.F
              (anchoredW + 1 + delay)) = 0 := by
        intro gamma hgamma
        have hGamma := componentSeeds_subset (GenericField K) S.G
          (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
        exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
          S.selected gamma anchoredW (anchoredW + 1 + delay)
          (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
      have hcount := component_secondTail_card_le_mod B C Gamma
        (selectedPoint (polynomialEmbedding K) S.selected)
        (selectedPoint_injective (polynomialEmbedding K) S.selected)
        (hlater C delay hdelay) htail hzero
      have hscale : B.weightedCost (delay • tailFlag2) C =
          delay * B.weightedCost tailFlag2 C := by
        simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
          nsmul_all]
        ring
      rw [hscale] at hcount
      exact ⟨delay, hdelay, hdelayMu, htail,
        hcount.trans
          (Nat.mul_le_mul_right (B.weightedCost tailFlag2 C) hdelayMu)⟩
    · exact Or.inr htangentBranch
  have providerDichotomy := loosenStage_dichotomy_with_tangent S hs hys htotal
    hfirstProper B htangent
  refine ⟨{
    budgetFamily := B
    multiplicity := multiplicity
    cost := fun C => multiplicity C * B.weightedCost tailFlag2 C
    one_le_multiplicity := hone
    tangentYZGate := htangentGate
    cost_le := fun _ => le_rfl
    divisor_le := ?_
    componentBound := ?_
    dichotomy := providerDichotomy }⟩
  · exact hresultants.divisor_le B multiplicity
  · intro C
    rcases branchBound C with hproper | htangentBranch
    · exact hproper.choose_spec.2.2.2
    · calc
        (componentSeeds (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
            (anchoredErrors + 1) * B.yzCost C :=
          htangent C htangentBranch
        _ ≤ B.weightedCost tailFlag2 C :=
          yzCost_mul_le_weightedCost B tailFlag2 C (anchoredErrors + 1)
            htangentGate
        _ = 1 * B.weightedCost tailFlag2 C := by simp
        _ ≤ multiplicity C * B.weightedCost tailFlag2 C :=
          Nat.mul_le_mul_right (B.weightedCost tailFlag2 C) (hone C)

 


theorem exists_delayedTailMultiplicityProvider_of_anchoredDVR_reduced
    {tailFlag1 : FlagDegree}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW tightSupport)
    (hs : tightSupport.s ≤ anchoredFixedSupport.s)
    (hys : tightSupport.ys ≤ anchoredFixedSupport.ys)
    (htotal : tightSupport.total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
    (htangentGate : anchoredErrors + 1 ≤
      (reducedResidualAgreementFlag6750 tightSupport
        (anchoredW + 2)).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (anchoredErrors + 1) * B.yzCost C)
    (hresultants : RegularComponentWeightedInertiaResultantCertificate B
      (fun C => localMultiplicity (loosenStage S hs hys htotal)
        (canonicalLocalDVRFamily (loosenStage S hs hys htotal)
          hfirstProper) C)) :
    Nonempty (DelayedTailMultiplicityProvider
      (tailFlag1 := tailFlag1)
      (tailFlag2 := reducedResidualAgreementFlag6750 tightSupport
        (anchoredW + 2)) S) := by
  apply exists_delayedTailMultiplicityProvider_of_anchoredDVR
    S hs hys htotal hfirstProper B
  · intro C delay hdelay
    exact laterTail_in_reduced_delay_secondFlag6750 S C delay hdelay
  · exact htangentGate
  · exact htangent
  · exact hresultants

end
end ContactAnchoredDelayedTailProviderAdapter6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredDelayedTailProviderAdapter6750Research.loosenStage_dichotomy_with_tangent
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredDelayedTailProviderAdapter6750Research.exists_delayedTailMultiplicityProvider_of_anchoredDVR
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredDelayedTailProviderAdapter6750Research.exists_delayedTailMultiplicityProvider_of_anchoredDVR_reduced
