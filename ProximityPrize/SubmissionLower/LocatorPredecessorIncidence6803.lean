import ProximityPrize.SubmissionLower.LocatorExactDerivativeChain6803

/-!
# Direct predecessor incidence on a derivative-chain curve

An exact stage-`j` seed also zeros `dR (j-1) F`.  When that predecessor is
proper on a curve component, it itself is a much cheaper zero-counting
function than the reconstructed agreement polynomial.  This file supplies the
pointwise and finite-curve adapters; deciding proper versus repeated components
is handled separately.
-/

namespace ProximityPrize.SubmissionLower.LocatorPredecessorIncidence6803

open scoped Classical BigOperators
open RCN002 RCN005 RCN007 RCN136 RCN231 RCN238 RCN313 RCN319

noncomputable section

set_option autoImplicit false

variable {K Omega : Type} [Field K] [Field Omega]

/-- Specialization zero is exactly zero of the surface polynomial at the
selected geometric point. -/
theorem selected_surface_zero
    (phi : Polynomial K →+* Omega) (G : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (gamma : K)
    (hzero : specialization K (selected gamma) gamma G = 0) :
    MvPolynomial.aeval (selectedPoint phi selected gamma)
      (surfaceMap phi G) = 0 := by
  change MvPolynomial.eval (selectedPoint phi selected gamma)
    (surfaceMap phi G) = 0
  rw [eval_surfaceMap]
  have hv : Fin.cases (phi Polynomial.X) (selectedPoint phi selected gamma) =
      polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
        (phi Polynomial.X) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact polynomialPoint_relation (phi.comp Polynomial.C) G
    (selected gamma) gamma (phi Polynomial.X) hzero

variable [IsAlgClosed Omega]

/-- If the predecessor surface polynomial is proper on a prime curve
component, its degree box directly bounds the number of exact chain seeds on
that component. -/
theorem predecessor_component_card_le
    (phi : Polynomial K →+* Omega)
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hproj : ProjectionsFiniteSeparable Omega P)
    (hnonpoint : ∀ v : Fin 3 → Omega,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (G : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hpoint : ∀ gamma ∈ Gamma, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
    (hproper : surfaceMap phi G ∉ P)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i, (surfaceMap phi G).degreeOf i ≤ cap i) :
    Gamma.card ≤ componentCost P cap := by
  classical
  let points := Gamma.image (selectedPoint phi selected)
  have hpointsP : ∀ v ∈ points,
      P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact hpoint gamma hgamma
  have hpointsG : ∀ v ∈ points,
      MvPolynomial.aeval v (surfaceMap phi G) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact selected_surface_zero phi G selected gamma
      (hsolution gamma hgamma)
  have hcount := finite_zero_points_le_box Omega P hproj hnonpoint
    (surfaceMap phi G) hproper cap hcap points hpointsP hpointsG
  have hcard : points.card = Gamma.card :=
    Finset.card_image_of_injective _ (selectedPoint_injective phi selected)
  rw [hcard] at hcount
  unfold componentCost
  exact_mod_cast hcount

end

end ProximityPrize.SubmissionLower.LocatorPredecessorIncidence6803
