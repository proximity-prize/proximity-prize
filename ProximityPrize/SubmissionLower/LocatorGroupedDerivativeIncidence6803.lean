import ProximityPrize.SubmissionLower.LocatorGroupedDerivativeFactor6803
import ProximityPrize.SubmissionLower.LocatorTriplePredecessorPrototype6803

/-!
# One grouped derivative-incidence charge per geometric factor

For one geometric factor `g` of an irreducible locator factor `F`, enumerate
the components of the single initial pair `(g, surfaceMap (dR 1 F))`.  A
nonempty component chooses its first escaping derivative.  The open part of
that derivative is counted by one curve-incidence argument and its zero fibre
by one finite-curve cut.  Empty components use the harmless default index
`1` and require no escape certificate.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedDerivativeIncidence6803

open scoped Classical BigOperators
open RCN001 RCN007 RCN052 RCN072 RCN135 RCN136 RCN137 RCN167 RCN222 RCN231
  RCN238 RCN243 RCN264 RCN286 RCN319
open LocatorDerivativeChain LocatorExactDerivativeChain6803
open LocatorGroupedDerivativeChain6803 LocatorGroupedDerivativeComponent6803
  LocatorGroupedDerivativeFactor6803 LocatorTriplePredecessorPrototype6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev InitialComponent
    (F : MvPolynomial (Fin 4) K) (g : GeometricFactor K F) :=
  RegularComponent (GenericField K) g.1
    (surfaceMap (polynomialEmbedding K) (dR 1 F)) 1

def initialComponentSeeds
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g) : Finset K :=
  componentSeeds (GenericField K) g.1
    (surfaceMap (polynomialEmbedding K) (dR 1 F)) 1
    (geometricExactSeeds F selected Gamma g)
    (selectedPoint (polynomialEmbedding K) selected) C

theorem initialComponentSeeds_subset_geometric
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g) :
    initialComponentSeeds F selected Gamma g C ⊆
      geometricExactSeeds F selected Gamma g :=
  componentSeeds_subset (GenericField K) g.1
    (surfaceMap (polynomialEmbedding K) (dR 1 F)) 1
    (geometricExactSeeds F selected Gamma g)
    (selectedPoint (polynomialEmbedding K) selected) C

theorem initialComponentSeeds_on_prime
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    {gamma : K} (hgamma : gamma ∈
      initialComponentSeeds F selected Gamma g C) :
    C.1 ≤ RingHom.ker
      (MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) selected gamma)).toRingHom :=
  componentSeeds_on_prime (GenericField K) g.1
    (surfaceMap (polynomialEmbedding K) (dR 1 F)) 1
    (geometricExactSeeds F selected Gamma g)
    (selectedPoint (polynomialEmbedding K) selected) C gamma hgamma

/-- A nonempty initial component has a first derivative which escapes it. -/
theorem initialComponent_firstEscape
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    (hnonempty : (initialComponentSeeds F selected Gamma g C).Nonempty) :
    Nonempty (FirstEscape C.1 F) := by
  let Delta := initialComponentSeeds F selected Gamma g C
  apply exists_firstEscape_of_nonempty_exact_component C.1 F selected Gamma Delta
    hnonempty
  · intro gamma hgamma
    have hgeom : gamma ∈ geometricExactSeeds F selected Gamma g :=
      initialComponentSeeds_subset_geometric F selected Gamma g C hgamma
    have hunion := geometricExactSeeds_subset_union F selected Gamma g hgeom
    obtain ⟨j, hj1, _, hj⟩ :=
      (mem_exactChainUnion_iff F selected Gamma gamma).mp hunion
    exact ⟨j, hj1, hj⟩
  · intro gamma hgamma
    exact initialComponentSeeds_on_prime F selected Gamma g C hgamma
  · exact regularComponent_T_mem (GenericField K) g.1
      (surfaceMap (polynomialEmbedding K) (dR 1 F)) 1 C

/-- The inactive default is never used in a counting hypothesis. -/
noncomputable def componentEscapeIndex
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g) : ℕ :=
  if h : (initialComponentSeeds F selected Gamma g C).Nonempty then
    (Classical.choice
      (initialComponent_firstEscape F selected Gamma g C h)).index
  else 1

theorem componentEscapeIndex_certificate
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    (hactive : (initialComponentSeeds F selected Gamma g C).Nonempty) :
    ∃ E : FirstEscape C.1 F,
      E.index = componentEscapeIndex F selected Gamma g C := by
  let E := Classical.choice
    (initialComponent_firstEscape F selected Gamma g C hactive)
  refine ⟨E, ?_⟩
  simp only [componentEscapeIndex, dif_pos hactive, E]

def componentCarrier
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g) :
    MvPolynomial (Fin 4) K :=
  dR (componentEscapeIndex F selected Gamma g C - 1) F

def componentGenericSeeds
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g) : Finset K :=
  escapeGenericSeeds F (componentEscapeIndex F selected Gamma g C)
    selected (initialComponentSeeds F selected Gamma g C)

def componentExceptionalSeeds
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g) : Finset K :=
  escapeExceptionalSeeds F (componentEscapeIndex F selected Gamma g C)
    selected (initialComponentSeeds F selected Gamma g C)

theorem geometricExactSeeds_component_partition
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) :
    geometricExactSeeds F selected Gamma g ⊆
      Finset.univ.biUnion fun C : InitialComponent F g ↦
        componentGenericSeeds F selected Gamma g C ∪
          componentExceptionalSeeds F selected Gamma g C := by
  intro gamma hgamma
  let point := selectedPoint (polynomialEmbedding K) selected
  have hG : MvPolynomial.eval (point gamma) g.1 = 0 :=
    (Finset.mem_filter.mp hgamma).2
  have hunion : gamma ∈ exactChainUnion F selected Gamma :=
    geometricExactSeeds_subset_union F selected Gamma g hgamma
  have hT : MvPolynomial.eval (point gamma)
      (surfaceMap (polynomialEmbedding K) (dR 1 F)) = 0 := by
    rw [selectedPoint_surface_evaluation,
      exactChainUnion_history F selected Gamma hunion 1 le_rfl, map_zero]
  have hH : MvPolynomial.eval (point gamma) (1 :
      MvPolynomial (Fin 3) (GenericField K)) ≠ 0 := by simp
  obtain ⟨C, hC⟩ := exists_regular_component (GenericField K) g.1
    (surfaceMap (polynomialEmbedding K) (dR 1 F)) 1
    (point gamma) hG hT hH
  have hDelta : gamma ∈ initialComponentSeeds F selected Gamma g C := by
    exact Finset.mem_filter.mpr ⟨hgamma, hC⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨C, Finset.mem_univ C, ?_⟩
  by_cases hzero : specialization K (selected gamma) gamma
      (dR (componentEscapeIndex F selected Gamma g C) F) = 0
  · apply Finset.mem_union_right
    exact (mem_escapeExceptionalSeeds F
      (componentEscapeIndex F selected Gamma g C) selected
      (initialComponentSeeds F selected Gamma g C) gamma).mpr
        ⟨hDelta, hzero⟩
  · apply Finset.mem_union_left
    exact (mem_escapeGenericSeeds F
      (componentEscapeIndex F selected Gamma g C) selected
      (initialComponentSeeds F selected Gamma g C) gamma).mpr
        ⟨hDelta, hzero⟩

theorem initialComponentSeeds_nonempty_of_partition_nonempty
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    (hactive : (componentGenericSeeds F selected Gamma g C ∪
      componentExceptionalSeeds F selected Gamma g C).Nonempty) :
    (initialComponentSeeds F selected Gamma g C).Nonempty := by
  rcases hactive with ⟨gamma, hgamma⟩
  rcases Finset.mem_union.mp hgamma with hmain | hexceptional
  · exact ⟨gamma, (mem_escapeGenericSeeds F
      (componentEscapeIndex F selected Gamma g C) selected
      (initialComponentSeeds F selected Gamma g C) gamma).mp hmain |>.1⟩
  · exact ⟨gamma, (mem_escapeExceptionalSeeds F
      (componentEscapeIndex F selected Gamma g C) selected
      (initialComponentSeeds F selected Gamma g C) gamma).mp hexceptional |>.1⟩

theorem componentGenericSeeds_regularSolution
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    {gamma : K} (hgamma : gamma ∈
      componentGenericSeeds F selected Gamma g C) :
    RegularSolution (componentCarrier F selected Gamma g C)
      (selected gamma) gamma := by
  have hdata := (mem_escapeGenericSeeds F
    (componentEscapeIndex F selected Gamma g C) selected
    (initialComponentSeeds F selected Gamma g C) gamma).mp hgamma
  have hDelta : (initialComponentSeeds F selected Gamma g C).Nonempty :=
    ⟨gamma, hdata.1⟩
  obtain ⟨E, hE⟩ := componentEscapeIndex_certificate
    F selected Gamma g C hDelta
  have hgammaE : gamma ∈ escapeGenericSeeds F E.index selected
      (initialComponentSeeds F selected Gamma g C) := by
    simpa only [componentGenericSeeds, hE] using hgamma
  have hregular := escapeGenericSeeds_regularSolution C.1 F E selected
    (initialComponentSeeds F selected Gamma g C)
    (fun gamma hgamma ↦
      initialComponentSeeds_on_prime F selected Gamma g C hgamma)
    hgammaE
  simpa only [componentCarrier, hE] using hregular

theorem componentExceptionalSeeds_derivative_zero
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    {gamma : K} (hgamma : gamma ∈
      componentExceptionalSeeds F selected Gamma g C) :
    specialization K (selected gamma) gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (componentCarrier F selected Gamma g C)) = 0 := by
  have hdata := (mem_escapeExceptionalSeeds F
    (componentEscapeIndex F selected Gamma g C) selected
    (initialComponentSeeds F selected Gamma g C) gamma).mp hgamma
  have hDelta : (initialComponentSeeds F selected Gamma g C).Nonempty :=
    ⟨gamma, hdata.1⟩
  obtain ⟨E, hE⟩ := componentEscapeIndex_certificate
    F selected Gamma g C hDelta
  have htwo := E.two_le
  have hsucc : componentEscapeIndex F selected Gamma g C - 1 + 1 =
      componentEscapeIndex F selected Gamma g C := by
    rw [← hE]
    omega
  have hderiv : MvPolynomial.pderiv (2 : Fin 4)
      (componentCarrier F selected Gamma g C) =
      dR (componentEscapeIndex F selected Gamma g C) F := by
    calc
      _ = dR (componentEscapeIndex F selected Gamma g C - 1 + 1) F := by
        rw [componentCarrier, dR_succ]
      _ = _ := by rw [hsucc]
  rw [hderiv]
  exact hdata.2

/-- Raw scaled grouped bound for one geometric factor.  The only supplied
hypotheses are the characteristic/projection gates for the fixed initial
pair and uniform coordinate caps for the component-dependent carrier and
escape derivative. -/
theorem geometricExactSeeds_grouped_card_le
    {Iota : Type}
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F)
    (hproper : ¬ g.1 ∣ surfaceMap (polynomialEmbedding K) (dR 1 F))
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (p w a errors : ℕ) [CharP (GenericField K) p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a)
    (han : a ≤ nodes.card)
    (hGdegree : ∀ j : Fin 3, g.1.degreeOf j < p)
    (hcutDegree : ∀ j k : Fin 3, j ≠ k →
      (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf j *
          g.1.degreeOf k +
        g.1.degreeOf j *
          (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf k < p)
    (hdegree : ∀ gamma ∈ geometricExactSeeds F selected Gamma g,
      (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ geometricExactSeeds F selected Gamma g,
      a ≤ (nodes.filter fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i).card)
    (hnoPencil : NoLargeSelectedPencil selected
      (geometricExactSeeds F selected Gamma g) w errors)
    (agreementCap escapeCap : Fin 3 → ℕ)
    (hagreementCap : ∀ C : InitialComponent F g,
      (componentGenericSeeds F selected Gamma g C ∪
        componentExceptionalSeeds F selected Gamma g C).Nonempty →
      ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial (polynomialEmbedding K)
        (componentCarrier F selected Gamma g C) w
        (x i) (u0 i) (u1 i)).degreeOf j ≤ agreementCap j)
    (hescapeCap : ∀ C : InitialComponent F g,
      (componentGenericSeeds F selected Gamma g C ∪
        componentExceptionalSeeds F selected Gamma g C).Nonempty →
      ∀ j,
      (surfaceMap (polynomialEmbedding K)
        (MvPolynomial.pderiv (2 : Fin 4)
          (componentCarrier F selected Gamma g C))).degreeOf j ≤
            escapeCap j) :
    (geometricExactSeeds F selected Gamma g).card * (a - w) ≤
      (nodes.card - w) * (∑ j, agreementCap j *
        coordinateMixedDegree (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F)) j) +
      (errors + 1) * (a - w) *
        coordinateMixedDegree (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F)) 2 +
      (a - w) * (∑ j, escapeCap j *
        coordinateMixedDegree (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F)) j) := by
  let S := geometricExactSeeds F selected Gamma g
  let T1 := surfaceMap (polynomialEmbedding K) (dR 1 F)
  let main : InitialComponent F g → Finset K :=
    componentGenericSeeds F selected Gamma g
  let exceptional : InitialComponent F g → Finset K :=
    componentExceptionalSeeds F selected Gamma g
  let carrier : InitialComponent F g → MvPolynomial (Fin 4) K :=
    componentCarrier F selected Gamma g
  apply grouped_first_escape_card_le (polynomialEmbedding K)
    selected S main exceptional carrier
    (geometricExactSeeds_component_partition F selected Gamma g)
    (fun C ↦ ?_) (fun C ↦ ?_) (fun C hactive ↦ ?_)
    (fun C hactive ↦ ?_)
    (fun C gamma hgamma ↦ ?_) (fun C gamma hgamma ↦ ?_)
    (fun C gamma hgamma ↦ ?_) (fun C gamma hgamma ↦ ?_)
    (fun C gamma hgamma ↦ ?_)
    nodes x u0 u1 hinj p w a errors hw hchar hwa han
    hdegree hagreement hnoPencil agreementCap escapeCap
    (coordinateMixedDegree (GenericField K) g.1 T1)
    hagreementCap hescapeCap
    (initial_components_degree_budget g.1 T1 p
      (RCN137.surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2).1
      hproper hGdegree hcutDegree)
  · intro gamma hgamma
    exact (mem_escapeGenericSeeds F
      (componentEscapeIndex F selected Gamma g C) selected
      (initialComponentSeeds F selected Gamma g C) gamma).mp hgamma |>.1
      |> initialComponentSeeds_subset_geometric F selected Gamma g C
  · exact initial_component_projections g.1 T1 p
      (RCN137.surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2).1
      hproper hGdegree hcutDegree C
  · have hDelta := initialComponentSeeds_nonempty_of_partition_nonempty
      F selected Gamma g C hactive
    obtain ⟨E, hE⟩ := componentEscapeIndex_certificate
      F selected Gamma g C hDelta
    change surfaceMap (polynomialEmbedding K)
      (componentCarrier F selected Gamma g C) ∈ C.1
    simpa only [componentCarrier, hE] using E.predecessor_mem
  · have hDelta := initialComponentSeeds_nonempty_of_partition_nonempty
      F selected Gamma g C hactive
    obtain ⟨E, hE⟩ := componentEscapeIndex_certificate
      F selected Gamma g C hDelta
    have htwo := E.two_le
    have hsucc : E.index - 1 + 1 = E.index := by omega
    have hcarrier : componentCarrier F selected Gamma g C =
        dR (E.index - 1) F := by
      simpa only [componentCarrier, hE]
    have hderiv : MvPolynomial.pderiv (2 : Fin 4)
        (componentCarrier F selected Gamma g C) = dR E.index F := by
      calc
        _ = MvPolynomial.pderiv (2 : Fin 4) (dR (E.index - 1) F) :=
          congrArg (MvPolynomial.pderiv (2 : Fin 4)) hcarrier
        _ = dR (E.index - 1 + 1) F :=
          (dR_succ (E.index - 1) F).symm
        _ = _ := by rw [hsucc]
    change surfaceMap (polynomialEmbedding K)
      (MvPolynomial.pderiv (2 : Fin 4)
        (componentCarrier F selected Gamma g C)) ∉ C.1
    rw [hderiv]
    exact E.escape_not_mem
  · exact (componentGenericSeeds_regularSolution F selected Gamma g C hgamma).1
  · have hregular :=
      (componentGenericSeeds_regularSolution F selected Gamma g C hgamma).2
    apply selectedPoint_regular_of_specialization K
      (componentCarrier F selected Gamma g C) selected gamma
    exact hregular
  · have hdata := (mem_escapeGenericSeeds F
      (componentEscapeIndex F selected Gamma g C) selected
      (initialComponentSeeds F selected Gamma g C) gamma).mp hgamma
    exact initialComponentSeeds_on_prime F selected Gamma g C hdata.1
  · exact componentExceptionalSeeds_derivative_zero
      F selected Gamma g C hgamma
  · have hdata := (mem_escapeExceptionalSeeds F
      (componentEscapeIndex F selected Gamma g C) selected
      (initialComponentSeeds F selected Gamma g C) gamma).mp hgamma
    exact initialComponentSeeds_on_prime F selected Gamma g C hdata.1

end

end ProximityPrize.SubmissionLower.LocatorGroupedDerivativeIncidence6803
