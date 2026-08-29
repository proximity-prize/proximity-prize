import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactPencilGeometry
import ProximityPrize.SubmissionLower.ContactIdentityPencil
import ProximityPrize.SubmissionLower.ContactGenericSurface
import ProximityPrize.SubmissionLower.ContactPolynomialRecovery

/-!
# Truncated contact reconstruction on an actual prime component

Model label: gpt-5.

The actual prime-quotient field supplies the regular initial point. The
degree-w truncated contact polynomial already recovers Y and R, without
assuming that any later Taylor numerator vanishes generically. Agreement
numerator membership is exactly an identity evaluation of this polynomial.
More than w identity nodes give a common base-field pencil, including all
selected genuine solutions on the component. Thus a whole R-dependent
surface has at most w identities; a pencil curve is nonvertical.

This avoids an all-tail polynomiality hypothesis in the counting interface.
It is not a global component-count or competition theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactComponentPencils

open ActualCurveCoordinateField ContactGenericSurface ContactPencilGeometry
open ContactGlobalPolynomiality ContactPolynomiality ContactPolynomialSolutions
open ContactPolynomialRecovery ContactTaylorNumerators ContactAgreementEvaluation
open ContactIdentityPencil ContactTranslation

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω]
variable (φ : Polynomial K →+* Ω)
variable (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]

def componentCoefficients : K →+* CoordinateField Ω P :=
  (algebraMap Ω (CoordinateField Ω P)).comp (φ.comp Polynomial.C)

def componentPoint : Fin 4 → CoordinateField Ω P :=
  Fin.cases (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X)) (coordinate Ω P)

theorem component_evaluation (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F =
      coordinateEvaluation Ω P (surfaceMap φ F) := by
  have hhom : MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) =
      (coordinateEvaluation Ω P).toRingHom.comp (surfaceMap φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [componentCoefficients, RingHom.comp_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [componentPoint, RingHom.comp_apply]
      · simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, surfaceMap_X_succ]
        rfl
  exact RingHom.congr_fun hhom F

theorem component_evaluation_zero_iff (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F = 0 ↔
      surfaceMap φ F ∈ P := by
  rw [component_evaluation]
  change surfaceMap φ F ∈ RingHom.ker (coordinateEvaluation Ω P).toRingHom ↔ _
  rw [coordinateEvaluation_ker]

variable (F : MvPolynomial (Fin 4) K)
variable (hF : surfaceMap φ F ∈ P)
variable (hH : surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P)

include hF in
theorem component_relation :
    MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F = 0 :=
  (component_evaluation_zero_iff φ P F).mpr hF

include hH in
theorem component_regular :
    MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P)
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0 :=
  (component_evaluation_zero_iff φ P _).not.mpr hH

def truncatedPolynomial (w : ℕ) : Polynomial (CoordinateField Ω P) :=
  globalPolynomial (componentCoefficients φ P) F (componentPoint φ P)
    (component_relation φ P F hF) (component_regular φ P F hH) w

theorem truncatedPolynomial_natDegree_le (w : ℕ) :
    (truncatedPolynomial φ P F hF hH w).natDegree ≤ w :=
  globalPolynomial_natDegree_le _ _ _ _ _ _

theorem truncatedPolynomial_initial_value (w : ℕ) :
    (truncatedPolynomial φ P F hF hH w).eval
      (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X)) = coordinate Ω P 0 :=
  globalPolynomial_initial_value (componentCoefficients φ P) F (componentPoint φ P)
    (component_relation φ P F hF) (component_regular φ P F hH) w

theorem truncatedPolynomial_initial_slope (w : ℕ) (hw : 1 ≤ w) :
    (truncatedPolynomial φ P F hF hH w).derivative.eval
      (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X)) = coordinate Ω P 1 :=
  globalPolynomial_initial_slope (componentCoefficients φ P) F (componentPoint φ P)
    (component_relation φ P F hF) (component_regular φ P F hH) w hw

theorem agreement_mem_iff_truncated_value (w : ℕ) (x u₀ u₁ : K) :
    surfaceMap φ (agreementNumerator F w (fun j => (j.factorial : K)⁻¹) x u₀ u₁) ∈ P ↔
      (truncatedPolynomial φ P F hF hH w).eval (componentCoefficients φ P x) =
        componentCoefficients φ P u₀ + coordinate Ω P 2 * componentCoefficients φ P u₁ := by
  rw [← component_evaluation_zero_iff]
  rw [factorial_agreement_zero_iff_actual_agreement (componentCoefficients φ P) F
    (componentPoint φ P) (component_relation φ P F hF) (component_regular φ P F hH)]
  rw [← globalPolynomial_eval]
  rfl

def identityNodes {ι : Type*} (nodes : Finset ι) (x u₀ u₁ : ι → K) (w : ℕ) : Finset ι := by
  classical
  exact nodes.filter (fun i => surfaceMap φ
    (agreementNumerator F w (fun j => (j.factorial : K)⁻¹) (x i) (u₀ i) (u₁ i)) ∈ P)

theorem identityNodes_subset {ι : Type*}
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (w : ℕ) :
    identityNodes φ P F nodes x u₀ u₁ w ⊆ nodes := by
  classical
  exact Finset.filter_subset _ _

/-- One generic truncated polynomial and all specified genuine selected
polynomials share the SAME original-field pencil. No later-tail premise. -/
theorem exists_common_pencil_of_many_identities {ι τ : Type*}
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (w : ℕ)
    (hinj : Set.InjOn x nodes)
    (hcard : w < (identityNodes φ P F nodes x u₀ u₁ w).card)
    (seed : τ → K) (selected : τ → Polynomial K)
    (hdegree : ∀ t, (selected t).natDegree ≤ w)
    (hvalues : ∀ t i, i ∈ identityNodes φ P F nodes x u₀ u₁ w →
      (selected t).eval (x i) = u₀ i + seed t * u₁ i) :
    ∃ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w ∧ P₁.natDegree ≤ w ∧
      truncatedPolynomial φ P F hF hH w =
        P₀.map (componentCoefficients φ P) + Polynomial.C (coordinate Ω P 2) *
          P₁.map (componentCoefficients φ P) ∧
      ∀ t, selected t = P₀ + Polynomial.C (seed t) * P₁ := by
  classical
  let I := identityNodes φ P F nodes x u₀ u₁ w
  let seeds : Option τ → CoordinateField Ω P := fun
    | none => coordinate Ω P 2
    | some t => componentCoefficients φ P (seed t)
  let polys : Option τ → Polynomial (CoordinateField Ω P) := fun
    | none => truncatedPolynomial φ P F hF hH w
    | some t => (selected t).map (componentCoefficients φ P)
  have hI : Set.InjOn x I := hinj.mono (identityNodes_subset φ P F nodes x u₀ u₁ w)
  have hd : ∀ t, (polys t).natDegree ≤ w := by
    intro t
    cases t with
    | none => exact truncatedPolynomial_natDegree_le φ P F hF hH w
    | some t => exact Polynomial.natDegree_map_le.trans (hdegree t)
  have hv : ∀ t i, i ∈ I → (polys t).eval (componentCoefficients φ P (x i)) =
      componentCoefficients φ P (u₀ i) + seeds t * componentCoefficients φ P (u₁ i) := by
    intro t i hi
    cases t with
    | none =>
      apply (agreement_mem_iff_truncated_value φ P F hF hH w (x i) (u₀ i) (u₁ i)).mp
      exact (Finset.mem_filter.mp hi).2
    | some t =>
      change ((selected t).map (componentCoefficients φ P)).eval _ = _
      rw [Polynomial.eval_map_apply, hvalues t i hi, map_add, map_mul]
  obtain ⟨P₀, P₁, h₀, h₁, hp⟩ := exists_basefield_affine_pencil_of_identity_nodes
    (componentCoefficients φ P) I x u₀ u₁ w hcard hI seeds polys hd hv
  refine ⟨P₀, P₁, h₀, h₁, hp none, ?_⟩
  intro t
  apply Polynomial.map_injective (componentCoefficients φ P) (componentCoefficients φ P).injective
  simpa only [polys, seeds, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C] using hp (some t)

theorem coordinates_affine_of_basefield_pencil (w : ℕ) (hw : 1 ≤ w)
    (P₀ P₁ : Polynomial K)
    (hp : truncatedPolynomial φ P F hF hH w =
      P₀.map (componentCoefficients φ P) + Polynomial.C (coordinate Ω P 2) *
        P₁.map (componentCoefficients φ P)) :
    coordinate Ω P 0 = algebraMap Ω (CoordinateField Ω P)
        ((P₀.map (φ.comp Polynomial.C)).eval (φ Polynomial.X)) +
      coordinate Ω P 2 * algebraMap Ω (CoordinateField Ω P)
        ((P₁.map (φ.comp Polynomial.C)).eval (φ Polynomial.X)) ∧
    coordinate Ω P 1 = algebraMap Ω (CoordinateField Ω P)
        ((P₀.map (φ.comp Polynomial.C)).derivative.eval (φ Polynomial.X)) +
      coordinate Ω P 2 * algebraMap Ω (CoordinateField Ω P)
        ((P₁.map (φ.comp Polynomial.C)).derivative.eval (φ Polynomial.X)) := by
  apply affine_coordinates_of_polynomial_pencil Ω P (φ Polynomial.X)
    (truncatedPolynomial φ P F hF hH w)
    (P₀.map (φ.comp Polynomial.C)) (P₁.map (φ.comp Polynomial.C))
  · simpa only [Polynomial.map_map, componentCoefficients] using hp
  · exact truncatedPolynomial_initial_value φ P F hF hH w
  · exact truncatedPolynomial_initial_slope φ P F hF hH w hw

include hF hH in
/-- Whole R-dependent hypersurfaces have at most w identity agreement
nodes, whether or not any later Taylor tail vanishes. -/
theorem identityNodes_card_le_of_r_dependent_principal {ι : Type*}
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (w : ℕ) (hw : 1 ≤ w)
    (hinj : Set.InjOn x nodes)
    (g : MvPolynomial (Fin 3) Ω) (hP : P = Ideal.span {g}) (hr : 0 < g.degreeOf 1) :
    (identityNodes φ P F nodes x u₀ u₁ w).card ≤ w := by
  by_contra h
  have hc : w < (identityNodes φ P F nodes x u₀ u₁ w).card := Nat.lt_of_not_ge h
  obtain ⟨P₀, P₁, _, _, hp, _⟩ :=
    exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hc
      (fun t : Empty => t.elim) (fun t : Empty => t.elim)
      (fun t => t.elim) (fun t => t.elim)
  have hy := (coordinates_affine_of_basefield_pencil φ P F hF hH w hw P₀ P₁ hp).1
  exact not_y_affine_of_r_dependent_principal Ω P g hP hr _ _ hy

include hF hH in
/-- Non-point primes with many identity nodes project nontrivially to the
actual seed coordinate. No polynomiality-locus assumption is present. -/
theorem seed_transcendental_of_many_identities {ι : Type*} [IsAlgClosed Ω]
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (w : ℕ) (hw : 1 ≤ w)
    (hinj : Set.InjOn x nodes)
    (hcard : w < (identityNodes φ P F nodes x u₀ u₁ w).card)
    (hnonpoint : ∀ v : Fin 3 → Ω, P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom) :
    Transcendental Ω (coordinate Ω P 2) := by
  obtain ⟨P₀, P₁, _, _, hp, _⟩ :=
    exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hcard
      (fun t : Empty => t.elim) (fun t : Empty => t.elim)
      (fun t => t.elim) (fun t => t.elim)
  obtain ⟨hy, hr⟩ := coordinates_affine_of_basefield_pencil φ P F hF hH w hw P₀ P₁ hp
  exact seed_transcendental_of_affine_coordinates Ω P hnonpoint _ _ _ _ hy hr

/-- Original selected solutions on the ACTUAL prime satisfy each of its
identity nodes. The input is ideal containment in their point kernel, not
an assumed interpolation identity. -/
theorem selected_agrees_on_identity_nodes {ι : Type*}
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (p w : ℕ) [CharP Ω p]
    (hw : w < p) (S : Polynomial K) (γ : K) (hdegree : S.natDegree ≤ w)
    (hsolution : specialization K S γ F = 0)
    (hregular : MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : P ≤ RingHom.ker (MvPolynomial.aeval
      (fun i : Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)).toRingHom) :
    ∀ i ∈ identityNodes φ P F nodes x u₀ u₁ w,
      S.eval (x i) = u₀ i + γ * u₁ i := by
  classical
  intro i hi
  have hmem := (Finset.mem_filter.mp hi).2
  have hz := hpoint hmem
  change MvPolynomial.eval
    (fun i : Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)
    (surfaceMap φ (agreementNumerator F w (fun j => (j.factorial : K)⁻¹)
      (x i) (u₀ i) (u₁ i))) = 0 at hz
  rw [eval_surfaceMap] at hz
  have hv : Fin.cases (φ Polynomial.X)
      (fun i : Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ) =
      polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at hz
  exact (factorial_agreement_zero_iff_original_agreement (φ.comp Polynomial.C) F S γ
    (φ Polynomial.X) hsolution hregular p w hw hdegree (x i) (u₀ i) (u₁ i)).mp hz

end

end ProximityPrize.SubmissionLower.ContactComponentPencils
