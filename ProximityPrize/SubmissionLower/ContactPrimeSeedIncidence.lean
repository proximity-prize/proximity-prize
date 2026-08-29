import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveZeroCount
import ProximityPrize.SubmissionLower.ContactComponentPencils
import ProximityPrize.SubmissionLower.ContactIncidence

/-! .















 -/

namespace ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
open ContactGenericSurface ContactPolynomialSolutions ContactPolynomialRecovery
open ContactTaylorNumerators ContactComponentPencils ContactTranslation

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω]
variable (φ : Polynomial K →+* Ω)

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω

def selectedPoint (selected : K → Polynomial K) (γ : K) : Fin 3 → Ω :=
  fun i ↦ polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X) i.succ

theorem selectedPoint_seed (selected : K → Polynomial K) (γ : K) :
    selectedPoint φ selected γ (2 : Fin 3) = (φ.comp Polynomial.C) γ := rfl

/-- .
 -/
theorem selectedPoint_injective (selected : K → Polynomial K) :
    Function.Injective (selectedPoint φ selected) := by
  intro γ η h
  apply (φ.comp Polynomial.C).injective
  simpa only [selectedPoint_seed] using congrFun h (2 : Fin 3)

def agreementPolynomial (F : MvPolynomial (Fin 4) K) (w : ℕ) (x u₀ u₁ : K) :
    MvPolynomial (Fin 3) Ω :=
  surfaceMap φ (agreementNumerator F w (fun j ↦ (j.factorial : K)⁻¹) x u₀ u₁)

/-- .
 -/
theorem selected_agreement_zero_iff
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (p w : ℕ) [CharP Ω p] (hchar : w < p)
    (γ : K) (hdegree : (selected γ).natDegree ≤ w)
    (hsolution : specialization K (selected γ) γ F = 0)
    (hregular : MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (x u₀ u₁ : K) :
    MvPolynomial.aeval (selectedPoint φ selected γ)
      (agreementPolynomial φ F w x u₀ u₁) = 0 ↔
        (selected γ).eval x = u₀ + γ * u₁ := by
  change MvPolynomial.eval (selectedPoint φ selected γ)
    (surfaceMap φ (agreementNumerator F w (fun j ↦ (j.factorial : K)⁻¹) x u₀ u₁)) = 0 ↔ _
  rw [eval_surfaceMap]
  have hv : Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ) =
      polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact factorial_agreement_zero_iff_original_agreement (φ.comp Polynomial.C) F
    (selected γ) γ (φ Polynomial.X) hsolution hregular p w hchar hdegree x u₀ u₁

variable [IsAlgClosed Ω]
variable (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]

def componentCost (cap : Fin 3 → ℕ) : ℕ :=
  ∑ j, cap j * actualCoordinateDegree Ω P j

/-- .
 -/
theorem agreement_fiber_card_le
    (hproj : ProjectionsFiniteSeparable Ω P)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K) (Γ : Finset K)
    (p w : ℕ) [CharP Ω p] (hchar : w < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (x u₀ u₁ : K) (hproper : agreementPolynomial φ F w x u₀ u₁ ∉ P)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ j, (agreementPolynomial φ F w x u₀ u₁).degreeOf j ≤ cap j) :
    (Γ.filter (fun γ ↦ (selected γ).eval x = u₀ + γ * u₁)).card ≤ componentCost P cap := by
  classical
  let fiber := Γ.filter (fun γ ↦ (selected γ).eval x = u₀ + γ * u₁)
  let points := fiber.image (selectedPoint φ selected)
  have hpointsP : ∀ v ∈ points, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
    exact hpoint γ (Finset.mem_filter.mp hγ).1
  have hpointsF : ∀ v ∈ points,
      MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁) = 0 := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hΓ, hagree⟩ := Finset.mem_filter.mp hγ
    exact (selected_agreement_zero_iff φ F selected p w hchar γ
      (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
  have hcount := ActualCurveZeroCount.finite_zero_points_le_box Ω P hproj hnonpoint
    (agreementPolynomial φ F w x u₀ u₁) hproper cap hcap points hpointsP hpointsF
  have hcard : points.card = fiber.card :=
    Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
  rw [hcard] at hcount
  unfold componentCost
  exact_mod_cast hcount

/-- .
 -/
theorem coordinateDegree_pos_of_transcendental
    (hproj : ProjectionsFiniteSeparable Ω P) (j : Fin 3)
    (hj : Transcendental Ω (coordinate Ω P j)) :
    1 ≤ actualCoordinateDegree Ω P j := by
  letI : Algebra (RatFunc Ω) (CoordinateField Ω P) := rationalBaseAlgebra Ω P j hj
  letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω P) := (hproj j hj).1
  rw [actualCoordinateDegree_of_transcendental Ω P j hj]
  exact Module.finrank_pos

/-- .
 -/
def NoLargeSelectedPencil (selected : K → Polynomial K) (Γ : Finset K) (w e : ℕ) : Prop :=
  ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
    (Γ.filter (fun γ ↦ selected γ = P₀ + Polynomial.C γ * P₁)).card ≤ e + 1

variable {ι : Type*}

local instance : DecidableEq ι := Classical.decEq ι

/-- .
 -/
theorem prime_seed_incidence_sharp
    (hproj : ProjectionsFiniteSeparable Ω P)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 4) K)
    (hF : surfaceMap φ F ∈ P)
    (hH : surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i ↦ (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j) :
    Γ.card * (a - w) ≤ (nodes.card - w) * componentCost P cap +
      (e + 1) * (a - w) * actualCoordinateDegree Ω P 2 := by
  classical
  let I := identityNodes φ P F nodes x u₀ u₁ w
  let relation : K → ι → Prop := fun γ i ↦ (selected γ).eval (x i) = u₀ i + γ * u₁ i
  by_cases hI : I.card ≤ w
  · have hfiber : ∀ i ∈ nodes \ I, (Γ.filter (fun γ ↦ relation γ i)).card ≤ componentCost P cap := by
      intro i hi
      obtain ⟨hinodes, hnotI⟩ := Finset.mem_sdiff.mp hi
      have hproper : agreementPolynomial φ F w (x i) (u₀ i) (u₁ i) ∉ P := by
        intro hmem
        apply hnotI
        exact Finset.mem_filter.mpr ⟨hinodes, hmem⟩
      exact agreement_fiber_card_le φ P hproj hnonpoint F selected Γ p w hchar
        hdegree hsolution hregular hpoint (x i) (u₀ i) (u₁ i) hproper cap (hcap i hinodes)
    have hcount := ContactIncidence.sharp_incidence_bound relation Γ nodes I a w
      (componentCost P cap) (identityNodes_subset φ P F nodes x u₀ u₁ w) hI hwa han
      hagreement hfiber
    omega
  · have hc : w < I.card := Nat.lt_of_not_ge hI
    have hvalues : ∀ (t : {γ : K // γ ∈ Γ}) i, i ∈ I →
        (selected t.1).eval (x i) = u₀ i + t.1 * u₁ i := by
      intro t
      exact selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
        (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
        (hregular t.1 t.2) (hpoint t.1 t.2)
    obtain ⟨P₀, P₁, h₀, h₁, _, hpencil⟩ :=
      exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hc
        (fun t : {γ : K // γ ∈ Γ} ↦ t.1) (fun t ↦ selected t.1)
        (fun t ↦ hdegree t.1 t.2) hvalues
    have hfilter : Γ.filter (fun γ ↦ selected γ = P₀ + Polynomial.C γ * P₁) = Γ :=
      Finset.filter_eq_self.mpr (fun γ hγ ↦ hpencil ⟨γ, hγ⟩)
    have hΓ : Γ.card ≤ e + 1 := by
      have h := hnoPencil P₀ P₁ h₀ h₁
      rwa [hfilter] at h
    have hZ := seed_transcendental_of_many_identities φ P F hF hH nodes x u₀ u₁ w hw
      hinj hc hnonpoint
    have hδ := coordinateDegree_pos_of_transcendental P hproj (2 : Fin 3) hZ
    have hcharge : Γ.card * (a - w) ≤
        (e + 1) * (a - w) * actualCoordinateDegree Ω P 2 := by
      calc
        _ ≤ (e + 1) * (a - w) := Nat.mul_le_mul_right _ hΓ
        _ ≤ _ := by
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((e + 1) * (a - w)) hδ
    omega

/-- . -/
theorem prime_seed_incidence
    (hproj : ProjectionsFiniteSeparable Ω P)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 4) K)
    (hF : surfaceMap φ F ∈ P)
    (hH : surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i ↦ (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j) :
    Γ.card * (a - w) ≤ nodes.card * componentCost P cap +
      (e + 1) * (a - w) * actualCoordinateDegree Ω P 2 := by
  have h := prime_seed_incidence_sharp φ P hproj hnonpoint F hF hH selected Γ
    nodes x u₀ u₁ hinj p w a e hw hchar hwa han hdegree hsolution hregular hpoint
    hagreement hnoPencil cap hcap
  have hcost : (nodes.card - w) * componentCost P cap ≤ nodes.card * componentCost P cap :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  exact h.trans (Nat.add_le_add_right hcost _)

end

end ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
