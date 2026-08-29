import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularComponentCover
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
import ProximityPrize.SubmissionLower.ActualCurveProjectionBounds
import ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum

/-!
# Selected-seed counting on an actual proper two-equation cut

Model label: gpt-5.

The actual regular minimal-prime cover, actual finite/separable projection
proofs, actual proper-function zero counts and selected-pencil incidence
are composed here. Original prime equations, characteristic gates and
point membership replace abstract component lists or per-prime count inputs.
The first intermediate theorem retains only a summed coordinate budget;
the following original-degree wrapper supplies it from actual field degrees.
No all-tail polynomiality hypothesis is used.
-/

namespace ProximityPrize.SubmissionLower.ContactProperCutSeedCount

open ActualCurveCoordinateField ActualCurveZeroCount ActualCurveProjectionBounds
open ActualCoordinateDegreeSum ActualPlanePositiveOrder
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω

def regularitySurface (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 3) Ω :=
  surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F)

theorem selectedPoint_evaluation (selected : K → Polynomial K) (γ : K)
    (Q : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ Q) =
      MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
        (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X)) Q := by
  rw [eval_surfaceMap]
  have hv : Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ) =
      polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]

theorem noLargeSelectedPencil_mono
    (selected : K → Polynomial K) (Γ Δ : Finset K) (w e : ℕ)
    (hsub : Δ ⊆ Γ) (hno : NoLargeSelectedPencil selected Γ w e) :
    NoLargeSelectedPencil selected Δ w e := by
  intro P₀ P₁ h₀ h₁
  apply le_trans (Finset.card_le_card ?_) (hno P₀ P₁ h₀ h₁)
  intro γ hγ
  obtain ⟨hΔ, hp⟩ := Finset.mem_filter.mp hγ
  exact Finset.mem_filter.mpr ⟨hsub hΔ, hp⟩

variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

/-- Compose the ACTUAL geometric per-prime incidence theorem, deriving its
finite/separable hypotheses from original proper equations and degree gates.
Only the summed projection budget is retained at this intermediate stage. -/
theorem proper_cut_seed_bound_of_projection_sum
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F) (hproper : ¬ G ∣ T)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hcutDegree : ∀ j k : Fin 3, j ≠ k →
      T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap budget : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
    (hbudget : ∀ i,
      (∑ C : RegularComponent Ω G T (regularitySurface φ F),
        actualCoordinateDegree Ω C.1 i) ≤ budget i) :
    Γ.card * (a - w) ≤ (nodes.card - w) * (∑ i, cap i * budget i) +
      (e + 1) * (a - w) * budget 2 := by
  classical
  let H := regularitySurface φ F
  have hHp : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) H ≠ 0 := by
    intro γ hγ
    change MvPolynomial.eval (selectedPoint φ selected γ)
      (surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0
    rw [selectedPoint_evaluation]
    exact hregular γ hγ
  let degree : RegularComponent Ω G T H → Fin 3 → ℕ :=
    fun C i => actualCoordinateDegree Ω C.1 i
  have hcomponent : ∀ C : RegularComponent Ω G T H,
      (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card * (a - w) ≤
        (nodes.card - w) * (∑ i, cap i * degree C i) +
          (e + 1) * (a - w) * degree C 2 := by
    intro C
    have hsub := componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
    have hgmem := regularComponent_G_mem Ω G T H C
    have htmem := regularComponent_T_mem Ω G T H C
    have hFmem : surfaceMap φ F ∈ C.1 :=
      ((Ideal.span_singleton_le_iff_mem (I := C.1)).mpr hgmem)
        (Ideal.mem_span_singleton.mpr hdiv)
    have hproj : ProjectionsFiniteSeparable Ω C.1 :=
      all_transcendental_coordinates_finite_separable Ω C.1 p G T hG hgmem htmem
        hproper hGdegree hcutDegree
    have hcount := prime_seed_incidence_sharp φ C.1 hproj
      (regularComponent_ne_point Ω G T H C) F hFmem
      (regularComponent_H_not_mem Ω G T H C) selected
      (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
      nodes x u₀ u₁ hinj p w a e hw hchar hwa han
      (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => hsolution γ (hsub hγ))
      (fun γ hγ => hregular γ (hsub hγ))
      (fun γ hγ => componentSeeds_on_prime Ω G T H Γ (selectedPoint φ selected) C γ hγ)
      (fun γ hγ => hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil) cap hcap
    exact hcount
  exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
    hGpoint hTpoint hHp (a - w) (nodes.card - w) (e + 1)
    cap budget degree hcomponent hbudget

/-- The actual regular component family consumes one original mixed
projection budget per coordinate, including its constant-coordinate members. -/
theorem regularComponents_degree_budget
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (p : ℕ) [CharP Ω p] (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hcutDegree : ∀ j k : Fin 3, j ≠ k →
      T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < p) :
    ∀ i, (∑ C : RegularComponent Ω G T (regularitySurface φ F),
      actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i := by
  intro i
  letI : ∀ C : RegularComponent Ω G T (regularitySurface φ F), C.1.IsPrime :=
    fun C => regularComponent_isPrime Ω G T (regularitySurface φ F) C
  have hneq : (Equiv.swap (0 : Fin 3) i) 1 ≠ (Equiv.swap (0 : Fin 3) i) 2 :=
    (Equiv.swap (0 : Fin 3) i).injective.ne (by decide)
  have hmixed : coordinateMixedDegree Ω G T i < p :=
    hcutDegree ((Equiv.swap (0 : Fin 3) i) 1) ((Equiv.swap (0 : Fin 3) i) 2) hneq
  exact sum_actualCoordinateDegree_at_le Ω
    (fun C : RegularComponent Ω G T (regularitySurface φ F) => C.1)
    Subtype.val_injective i p G T hG
    (regularComponent_G_mem Ω G T (regularitySurface φ F))
    (regularComponent_T_mem Ω G T (regularitySurface φ F))
    hproper hGdegree hmixed

/-- Complete proper-cut seed count from original equations and their
separated degree gates. No projection, zero-count, component-count, or
per-prime incidence inequality remains an input. -/
theorem proper_cut_seed_bound
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F) (hproper : ¬ G ∣ T)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hcutDegree : ∀ j k : Fin 3, j ≠ k →
      T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j) :
    Γ.card * (a - w) ≤
      (nodes.card - w) * (∑ i, cap i * coordinateMixedDegree Ω G T i) +
      (e + 1) * (a - w) * coordinateMixedDegree Ω G T 2 :=
  proper_cut_seed_bound_of_projection_sum φ F G T hG hdiv hproper selected Γ
    nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree hcutDegree
    hdegree hsolution hregular hGpoint hTpoint hagreement hnoPencil cap
    (coordinateMixedDegree Ω G T) hcap
    (regularComponents_degree_budget φ F G T p hG hproper hGdegree hcutDegree)

end

end ProximityPrize.SubmissionLower.ContactProperCutSeedCount
