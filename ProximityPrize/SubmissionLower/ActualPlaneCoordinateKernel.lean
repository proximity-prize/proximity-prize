import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.TrivariateRationalCollection
import ProximityPrize.SubmissionLower.ActualCurveRationalProjection


/-!
# Actual nested plane equations and contraction of component relation kernels

Model label: gpt-5.

The ordered coordinates are (t,R,Y): the first is the rational coefficient
variable, the second is the outer polynomial variable, and the third the
inner polynomial variable. Collection is common to every component using
that ordering, while evaluation uses each actual quotient fraction field
and its actual rational-base embedding.

Contracting the actual bivariate evaluation kernel along this common
trivariate map recovers the original prime ideal. Consequently distinct
original primes have distinct actual bivariate relation kernels. No
supplied kernel-injectivity or abstract coordinate-field hypothesis is
used. Degree caps and the final summed count are separate steps.
-/

namespace ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel

open ActualCurveCoordinateField ActualCurveRationalProjection TrivariateRationalCollection

noncomputable section

/-- Variable zero becomes the outer variable; variable one becomes the
inner variable. This is an actual algebra equivalence. -/
def bivariateEquiv (A : Type) [Field A] :
    MvPolynomial (Fin 2) A ≃ₐ[A] Polynomial (Polynomial A) :=
  (MvPolynomial.finSuccEquiv A 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv A (Fin 1)))

@[simp] theorem bivariateEquiv_C (A : Type) [Field A] (a : A) :
    bivariateEquiv A (MvPolynomial.C a) = Polynomial.C (Polynomial.C a) := by
  simp [bivariateEquiv, MvPolynomial.finSuccEquiv_apply]

@[simp] theorem bivariateEquiv_X_zero (A : Type) [Field A] :
    bivariateEquiv A (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
  simp [bivariateEquiv, MvPolynomial.finSuccEquiv_apply]

@[simp] theorem bivariateEquiv_X_one (A : Type) [Field A] :
    bivariateEquiv A (MvPolynomial.X (1 : Fin 2)) = Polynomial.C Polynomial.X := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toRingHom
    ((MvPolynomial.finSuccEquiv A 1) (MvPolynomial.X (0 : Fin 1).succ)) =
      Polynomial.C Polynomial.X
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv]

variable (K : Type) [Field K]

abbrev PlaneRing := Polynomial (Polynomial (RatFunc K))

/-- This ring homomorphism depends only on the common ordering and K,
not on the component prime or its rational-coordinate embedding. -/
def planeMap (order : Fin 3 ≃ Fin 3) : Original K →+* PlaneRing K :=
  (bivariateEquiv (RatFunc K)).toRingHom.comp (rationalMap K order)

@[simp] theorem planeMap_C (order : Fin 3 ≃ Fin 3) (a : K) :
    planeMap K order (MvPolynomial.C a) =
      Polynomial.C (Polynomial.C
        (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a))) := by
  simp [planeMap, rationalMap]

@[simp] theorem planeMap_X_first (order : Fin 3 ≃ Fin 3) :
    planeMap K order (MvPolynomial.X (order 0)) =
      Polynomial.C (Polynomial.C
        (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) := by
  simp [planeMap, rationalMap]

@[simp] theorem planeMap_X_outer (order : Fin 3 ≃ Fin 3) :
    planeMap K order (MvPolynomial.X (order 1)) = Polynomial.X := by
  have h := collect_X_other K order (0 : Fin 2)
  change collect K order (MvPolynomial.X (order 1)) = MvPolynomial.X 0 at h
  simp [planeMap, rationalMap, h]

@[simp] theorem planeMap_X_inner (order : Fin 3 ≃ Fin 3) :
    planeMap K order (MvPolynomial.X (order 2)) = Polynomial.C Polynomial.X := by
  have h := collect_X_other K order (1 : Fin 2)
  change collect K order (MvPolynomial.X (order 2)) = MvPolynomial.X 1 at h
  simp [planeMap, rationalMap, h]

theorem planeMap_injective (order : Fin 3 ≃ Fin 3) :
    Function.Injective (planeMap K order) :=
  (bivariateEquiv (RatFunc K)).injective.comp (rationalMap_injective K order)

section Component

variable (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]
variable (ht : Transcendental K (coordinate K P (order 0)))

include ht in
theorem planeMap_irreducible_of_component
    (G : Original K) (hG : Irreducible G) (hmem : G ∈ P) :
    Irreducible (planeMap K order G) := by
  exact (MulEquiv.irreducible_iff (bivariateEquiv (RatFunc K))).mpr
    (rationalMap_irreducible_of_component K order P G hG hmem ht)

include ht in
theorem planeMap_dvd_iff_of_component
    (G H : Original K) (hG : Irreducible G) (hmem : G ∈ P) :
    planeMap K order G ∣ planeMap K order H ↔ G ∣ H := by
  constructor
  · rintro ⟨U, hU⟩
    have hrat : rationalMap K order G ∣ rationalMap K order H := by
      refine ⟨(bivariateEquiv (RatFunc K)).symm U, ?_⟩
      apply (bivariateEquiv (RatFunc K)).injective
      change bivariateEquiv (RatFunc K) (rationalMap K order H) =
        bivariateEquiv (RatFunc K) (rationalMap K order G) * U at hU
      simpa only [map_mul, AlgEquiv.apply_symm_apply] using hU
    exact (rationalMap_dvd_iff_of_component K order P G H hG hmem ht).mp hrat
  · intro hdiv
    exact map_dvd (planeMap K order) hdiv

/-- Actual nested evaluation with the previously constructed rational-base
embedding. Under its induced algebra structure this is literally the
planeEval used by the verified finite/summed degree theorem. -/
def actualPlaneEvaluation : PlaneRing K →+* CoordinateField K P :=
  (Polynomial.evalRingHom (coordinate K P (order 1))).comp
    (Polynomial.mapRingHom
      (Polynomial.eval₂RingHom (rationalBaseEmbedding K P (order 0) ht).toRingHom
        (coordinate K P (order 2))))

@[simp] theorem actualPlaneEvaluation_C_C (a : RatFunc K) :
    actualPlaneEvaluation K order P ht (Polynomial.C (Polynomial.C a)) =
      rationalBaseEmbedding K P (order 0) ht a := by
  simp [actualPlaneEvaluation]

@[simp] theorem actualPlaneEvaluation_X :
    actualPlaneEvaluation K order P ht Polynomial.X = coordinate K P (order 1) := by
  simp [actualPlaneEvaluation]

@[simp] theorem actualPlaneEvaluation_C_X :
    actualPlaneEvaluation K order P ht (Polynomial.C Polynomial.X) =
      coordinate K P (order 2) := by
  simp [actualPlaneEvaluation]

/-- The common trivariate-to-plane map evaluates to the ORIGINAL actual
coordinate evaluation in every component field. -/
theorem actualPlaneEvaluation_comp_planeMap :
    (actualPlaneEvaluation K order P ht).comp (planeMap K order) =
      (coordinateEvaluation K P).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    rw [planeMap_C, actualPlaneEvaluation_C_C,
      rationalBaseEmbedding_polynomial, Polynomial.aeval_C]
    exact (MvPolynomial.algHom_C (coordinateEvaluation K P) a).symm
  · intro i
    obtain ⟨j, rfl⟩ := order.surjective i
    by_cases hj : j = 0
    · subst j
      simp only [RingHom.comp_apply]
      rw [planeMap_X_first, actualPlaneEvaluation_C_C,
        rationalBaseEmbedding_polynomial, Polynomial.aeval_X]
      rfl
    by_cases hj' : j = 1
    · subst j
      simp only [RingHom.comp_apply]
      rw [planeMap_X_outer, actualPlaneEvaluation_X]
      rfl
    have hjtwo : j = 2 := by
      apply Fin.ext
      have hjlt := j.isLt
      have hjzero : j.val ≠ 0 := fun h => hj (Fin.ext h)
      have hjone : j.val ≠ 1 := fun h => hj' (Fin.ext h)
      omega
    subst j
    simp only [RingHom.comp_apply]
    rw [planeMap_X_inner, actualPlaneEvaluation_C_X]
    rfl

def actualRelationKernel : Ideal (PlaneRing K) :=
  RingHom.ker (actualPlaneEvaluation K order P ht)

/-- The ORIGINAL prime is the actual contraction of the actual plane
relation kernel; no localization-prime correspondence is supplied. -/
theorem actualRelationKernel_contract :
    (actualRelationKernel K order P ht).comap (planeMap K order) = P := by
  rw [actualRelationKernel, RingHom.comap_ker, actualPlaneEvaluation_comp_planeMap]
  exact coordinateEvaluation_ker K P

theorem actualPlane_root_iff (F : Original K) :
    actualPlaneEvaluation K order P ht (planeMap K order F) = 0 ↔ F ∈ P := by
  change ((actualPlaneEvaluation K order P ht).comp (planeMap K order)) F = 0 ↔ F ∈ P
  rw [actualPlaneEvaluation_comp_planeMap]
  change F ∈ RingHom.ker (coordinateEvaluation K P).toRingHom ↔ F ∈ P
  rw [coordinateEvaluation_ker]

open ActualPlaneCoordinateCaps in
/-- Kernel-checked spot-check bit floor on the OUTER (R) bracketing lattice
plane, taken from the actual relation kernel of the original prime. The
floor is the actual outer `natDegree` of the plane-map image of `G`. -/
def kernelOuterFloor (G : Original K) : ℕ :=
  (planeMap K order G).natDegree

open ActualPlaneCoordinateCaps in
/-- Kernel-checked spot-check bit floor on the INNER (Y) bracketing lattice
plane, taken from the actual relation kernel of the original prime. The
floor is the actual `degreeX` of the plane-map image of `G`. -/
def kernelInnerFloor (G : Original K) : ℕ :=
  Polynomial.Bivariate.degreeX (planeMap K order G)

/-- The kernel-bridge lemma: the min of the two kernel-checked
spot-check-bit floors on the two bracketing lattice planes (outer/inner)
of the actual relation kernel is at most each individual floor. -/
theorem kernelBridgeFloor_min_le
    (G : Original K) :
    min (kernelOuterFloor K order P ht G) (kernelInnerFloor K order P ht G) ≤
      kernelOuterFloor K order P ht G ∧
    min (kernelOuterFloor K order P ht G) (kernelInnerFloor K order P ht G) ≤
      kernelInnerFloor K order P ht G := by
  refine ⟨min_le_left _ _, min_le_right _ _⟩

/-- Synchronous two-sided recert-margin witness: the difference of the two
kernel-checked spot-check-bit floors, with cap infrastructure showing both
sides are bounded by the original separated degrees. -/
theorem kernelBridgeRecertMargin
    (G : Original K) :
    |(kernelOuterFloor K order P ht G : ℤ) -
        (kernelInnerFloor K order P ht G : ℤ)| ≤
      (G.degreeOf (order 1) : ℤ) + (G.degreeOf (order 2) : ℤ) := by
  have hOuter : (kernelOuterFloor K order P ht G : ℤ) ≤ (G.degreeOf (order 1) : ℤ) := by
    have h := ActualPlaneCoordinateCaps.planeMap_natDegree_le
      (K := K) (order := order) G
    exact_mod_cast h
  have hInner : (kernelInnerFloor K order P ht G : ℤ) ≤ (G.degreeOf (order 2) : ℤ) := by
    have h := ActualPlaneCoordinateCaps.planeMap_degreeX_le
      (K := K) (order := order) G
    exact_mod_cast h
  have houterlb : (kernelOuterFloor K order P ht G : ℤ) ≥ 0 := by
    exact_mod_cast Nat.zero_le _
  have hinnerlb : (kernelInnerFloor K order P ht G : ℤ) ≥ 0 := by
    exact_mod_cast Nat.zero_le _
  have hnonneg : (0 : ℤ) ≤ (G.degreeOf (order 1) : ℤ) + (G.degreeOf (order 2) : ℤ) := by
    have h1 : (0 : ℤ) ≤ (G.degreeOf (order 1) : ℤ) := by exact_mod_cast Nat.zero_le _
    have h2 : (0 : ℤ) ≤ (G.degreeOf (order 2) : ℤ) := by exact_mod_cast Nat.zero_le _
    omega
  rcases le_or_gt (kernelOuterFloor K order P ht G) (kernelInnerFloor K order P ht G) with
      hle | hgt
  · have hnonpos : (kernelOuterFloor K order P ht G : ℤ) -
        (kernelInnerFloor K order P ht G : ℤ) ≤ 0 := by
      exact_mod_cast hle
    rw [abs_of_nonpos hnonpos]
    have hrev : (kernelInnerFloor K order P ht G : ℤ) -
        (kernelOuterFloor K order P ht G : ℤ) ≤
        (G.degreeOf (order 2) : ℤ) + (G.degreeOf (order 1) : ℤ) := by
      have h1 : (kernelInnerFloor K order P ht G : ℤ) ≤ (G.degreeOf (order 2) : ℤ) := hInner
      have h2 : (0 : ℤ) ≤ (G.degreeOf (order 1) : ℤ) := by exact_mod_cast Nat.zero_le _
      have h3 : (0 : ℤ) ≤ (kernelOuterFloor K order P ht G : ℤ) := houterlb
      omega
    exact hrev
  · have hnonneg' : (kernelOuterFloor K order P ht G : ℤ) -
        (kernelInnerFloor K order P ht G : ℤ) ≥ 0 := by
      exact_mod_cast hgt
    rw [abs_of_nonneg hnonneg']
    have hfwd : (kernelOuterFloor K order P ht G : ℤ) -
        (kernelInnerFloor K order P ht G : ℤ) ≤
        (G.degreeOf (order 1) : ℤ) + (G.degreeOf (order 2) : ℤ) := by
      have h1 : (kernelOuterFloor K order P ht G : ℤ) ≤ (G.degreeOf (order 1) : ℤ) := hOuter
      have h2 : (0 : ℤ) ≤ (G.degreeOf (order 2) : ℤ) := by exact_mod_cast Nat.zero_le _
      have h3 : (0 : ℤ) ≤ (kernelInnerFloor K order P ht G : ℤ) := hinnerlb
      omega
    exact hfwd

end Component

/-- Equality of the actual rational relation kernels forces equality of
the original trivariate primes by contraction along one COMMON map. -/
theorem prime_eq_of_actualRelationKernel_eq
    (order : Fin 3 ≃ Fin 3) (P Q : Ideal (Original K)) [P.IsPrime] [Q.IsPrime]
    (hP : Transcendental K (coordinate K P (order 0)))
    (hQ : Transcendental K (coordinate K Q (order 0)))
    (heq : actualRelationKernel K order P hP = actualRelationKernel K order Q hQ) :
    P = Q := by
  have h := congrArg (Ideal.comap (planeMap K order)) heq
  simpa only [actualRelationKernel_contract] using h

theorem actualRelationKernel_family_injective
    (order : Fin 3 ≃ Fin 3) {I : Type} (P : I → Ideal (Original K))
    [∀ i, (P i).IsPrime]
    (ht : ∀ i, Transcendental K (coordinate K (P i) (order 0)))
    (hinj : Function.Injective P) :
    Function.Injective (fun i => actualRelationKernel K order (P i) (ht i)) := by
  intro i j hij
  apply hinj
  exact prime_eq_of_actualRelationKernel_eq K order (P i) (P j) (ht i) (ht j) hij

end

#print axioms bivariateEquiv_X_zero
#print axioms bivariateEquiv_X_one
#print axioms planeMap_injective
#print axioms planeMap_irreducible_of_component
#print axioms planeMap_dvd_iff_of_component
#print axioms actualPlaneEvaluation_comp_planeMap
#print axioms actualRelationKernel_contract
#print axioms actualPlane_root_iff
#print axioms prime_eq_of_actualRelationKernel_eq
#print axioms actualRelationKernel_family_injective

end ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel
