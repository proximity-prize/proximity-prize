import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
import ProximityPrize.SubmissionLower.ActualCurveZeroCountSmall

/-!
# Selected-seed incidence with small characteristic-free projections

This is the sharp proper-node incidence theorem with the new actual
curve zero count.  All combinatorial and pencil branches are unchanged.
-/

namespace ProximityPrize.SubmissionLower.ContactPrimeSeedIncidenceSmall

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveZeroCount ActualCurveZeroCountSmall
open ContactGenericSurface ContactPolynomialSolutions
  ContactPolynomialRecovery ContactTaylorNumerators
  ContactComponentPencils ContactTranslation
open ContactPrimeSeedIncidence

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω]
variable (φ : Polynomial K →+* Ω)

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω

variable [IsAlgClosed Ω]
variable (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]

theorem agreement_fiber_card_le_small
    (p : ℕ) [CharP Ω p] (hp : p.Prime)
    (hproj : ProjectionsFiniteSmall Ω P p)
    (i₀ : Fin 3) (hi₀ : Transcendental Ω (coordinate Ω P i₀))
    (hsep₀ : letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
      rationalBaseAlgebra Ω P i₀ hi₀
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : Finset K) (w : ℕ) (hchar : w < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (x u₀ u₁ : K)
    (hproper : agreementPolynomial φ F w x u₀ u₁ ∉ P)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ j, (agreementPolynomial φ F w x u₀ u₁).degreeOf j ≤ cap j) :
    (Γ.filter (fun γ ↦ (selected γ).eval x = u₀ + γ * u₁)).card ≤
      componentCost P cap := by
  classical
  letI : ExpChar Ω p := ExpChar.prime hp
  let fiber := Γ.filter (fun γ ↦ (selected γ).eval x = u₀ + γ * u₁)
  let points := fiber.image (selectedPoint φ selected)
  have hpointsP : ∀ v ∈ points,
      P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
    exact hpoint γ (Finset.mem_filter.mp hγ).1
  have hpointsF : ∀ v ∈ points,
      MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁) = 0 := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hΓ, hagree⟩ := Finset.mem_filter.mp hγ
    exact (selected_agreement_zero_iff φ F selected p w hchar γ
      (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ)
      x u₀ u₁).mpr hagree
  have hcount := ActualCurveZeroCountSmall.finite_zero_points_le_box_of_separator
    Ω P p hp hproj i₀ hi₀ hsep₀
    (agreementPolynomial φ F w x u₀ u₁) hproper cap hcap
    points hpointsP hpointsF
  have hcard : points.card = fiber.card :=
    Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
  rw [hcard] at hcount
  unfold componentCost
  exact_mod_cast hcount

theorem coordinateDegree_pos_of_transcendental_small
    (p : ℕ) [CharP Ω p]
    (hproj : ProjectionsFiniteSmall Ω P p) (j : Fin 3)
    (hj : Transcendental Ω (coordinate Ω P j)) :
    1 ≤ actualCoordinateDegree Ω P j := by
  letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
    rationalBaseAlgebra Ω P j hj
  letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω P) :=
    (hproj j hj).1
  rw [actualCoordinateDegree_of_transcendental Ω P j hj]
  exact Module.finrank_pos

variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

theorem prime_seed_incidence_sharp_small
    (p : ℕ) [CharP Ω p] (hp : p.Prime)
    (hproj : ProjectionsFiniteSmall Ω P p)
    (i₀ : Fin 3) (hi₀ : Transcendental Ω (coordinate Ω P i₀))
    (hsep₀ : letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
      rationalBaseAlgebra Ω P i₀ hi₀
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 4) K)
    (hF : surfaceMap φ F ∈ P)
    (hH : surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K)
    (hinj : Set.InjOn x nodes)
    (w a e : ℕ) (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i ↦
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j) :
    Γ.card * (a - w) ≤ (nodes.card - w) * componentCost P cap +
      (e + 1) * (a - w) * actualCoordinateDegree Ω P 2 := by
  classical
  letI : ExpChar Ω p := ExpChar.prime hp
  let I := identityNodes φ P F nodes x u₀ u₁ w
  let relation : K → ι → Prop :=
    fun γ i ↦ (selected γ).eval (x i) = u₀ i + γ * u₁ i
  by_cases hI : I.card ≤ w
  · have hfiber : ∀ i ∈ nodes \ I,
        (Γ.filter (fun γ ↦ relation γ i)).card ≤ componentCost P cap := by
      intro i hi
      obtain ⟨hinodes, hnotI⟩ := Finset.mem_sdiff.mp hi
      have hproper : agreementPolynomial φ F w (x i) (u₀ i) (u₁ i) ∉ P := by
        intro hmem
        apply hnotI
        exact Finset.mem_filter.mpr ⟨hinodes, hmem⟩
      exact agreement_fiber_card_le_small φ P p hp hproj i₀ hi₀ hsep₀
        hnonpoint F selected Γ w hchar hdegree hsolution hregular hpoint
        (x i) (u₀ i) (u₁ i) hproper cap (hcap i hinodes)
    have hcount := ContactIncidence.sharp_incidence_bound relation Γ nodes I a w
      (componentCost P cap) (identityNodes_subset φ P F nodes x u₀ u₁ w)
      hI hwa han hagreement hfiber
    omega
  · have hc : w < I.card := Nat.lt_of_not_ge hI
    have hvalues : ∀ (t : {γ : K // γ ∈ Γ}) i, i ∈ I →
        (selected t.1).eval (x i) = u₀ i + t.1 * u₁ i := by
      intro t
      exact selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
        (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
        (hregular t.1 t.2) (hpoint t.1 t.2)
    obtain ⟨P₀, P₁, h₀, h₁, _, hpencil⟩ :=
      exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w
        hinj hc (fun t : {γ : K // γ ∈ Γ} ↦ t.1)
        (fun t ↦ selected t.1) (fun t ↦ hdegree t.1 t.2) hvalues
    have hfilter : Γ.filter
        (fun γ ↦ selected γ = P₀ + Polynomial.C γ * P₁) = Γ :=
      Finset.filter_eq_self.mpr (fun γ hγ ↦ hpencil ⟨γ, hγ⟩)
    have hΓ : Γ.card ≤ e + 1 := by
      have h := hnoPencil P₀ P₁ h₀ h₁
      rwa [hfilter] at h
    have hZ := seed_transcendental_of_many_identities φ P F hF hH
      nodes x u₀ u₁ w hw hinj hc hnonpoint
    have hδ := coordinateDegree_pos_of_transcendental_small P p hproj (2 : Fin 3) hZ
    have hcharge : Γ.card * (a - w) ≤
        (e + 1) * (a - w) * actualCoordinateDegree Ω P 2 := by
      calc
        _ ≤ (e + 1) * (a - w) := Nat.mul_le_mul_right _ hΓ
        _ ≤ _ := by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left ((e + 1) * (a - w)) hδ
    omega

end

end ProximityPrize.SubmissionLower.ContactPrimeSeedIncidenceSmall

#print axioms ProximityPrize.SubmissionLower.ContactPrimeSeedIncidenceSmall.agreement_fiber_card_le_small
#print axioms ProximityPrize.SubmissionLower.ContactPrimeSeedIncidenceSmall.prime_seed_incidence_sharp_small
