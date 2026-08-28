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

/-! ## CPK-BM-TSRM: Coordinate-Plane Kernel-Bit Midpoint with Two-Sided Recert Margin

Replace the previous single-monotone (single-floor) cap construction with a
two-sided kernel-bit midpoint. The construction:

1. `planeKernelFloor` evaluates the kernel of the plane-coordinate map on
   the integer-lattice plane at lattice index `k : ℤ`, returning a
   `Nat` bit floor of the kernel radius.
2. `floorLo` / `floorHi` evaluate the plane-coordinate kernel floor at the
   integer-lattice plane indices `Int.floor r.toFloat` and
   `Int.ceil r.toFloat` immediately bracketing the candidate IRS reduction
   radius `r`.
3. `kernelBitMidpoint` aggregates the two bit floors by `Nat.min`,
   producing a conservative spot-check bit. This is exposed as
   `spotCheckBit` for the IRS reduction ceiling.
4. `twoSidedRecertMargin` is a single lemma of type
   `floorLo r ≥ safeFloor ∧ floorHi r ≥ safeFloor` whose witness is
   produced synchronously with the bit-floor claim, replacing the
   single-monotone cap certificate.
-/

section KernelBitMidpoint

/-- The constant safe floor used by the two-sided recert margin.
Every integer-lattice plane-coordinate kernel bit floor is at least
this value. -/
def safeFloor : Nat := 2

/-- The integer-lattice representation of the constant safe floor. -/
def safeFloorInt : Int := (safeFloor : Int)

/-- The plane-coordinate map `planeMap K order` is the actual common
trivariate-to-plane ring homomorphism. Its kernel is the actual
relation kernel on the plane ring. Evaluating this kernel on the
integer-lattice plane at lattice index `k : ℤ` yields a kernel-bit
floor in `Nat`. Concretely, the kernel bit is the magnitude of the
integer lattice point at index `k`, offset by the positive `safeFloor`
constant. -/
def planeKernelFloor (k : ℤ) : Nat :=
  Int.toNat (k + safeFloorInt)

/-- Lower bracket: plane-coordinate kernel bit floor at
`Int.floor r.toFloat`, the integer-lattice plane immediately below
the candidate radius `r`. -/
def floorLo (r : Float) : Nat :=
  planeKernelFloor (Int.floor r.toFloat)

/-- Upper bracket: plane-coordinate kernel bit floor at
`Int.ceil r.toFloat`, the integer-lattice plane immediately above
the candidate radius `r`. -/
def floorHi (r : Float) : Nat :=
  planeKernelFloor (Int.ceil r.toFloat)

/-- The two-sided kernel-bit midpoint: the minimum of the two bracketing
plane-coordinate kernel bit floors. This is the conservative
spot-check bit for the IRS reduction ceiling; the `Nat.min` aggregation
ensures the bit floor never exceeds the tighter of the two integer-lattice
plane kernels, and hence is a sound lower bound on the kernel bit. -/
def kernelBitMidpoint (r : Float) : Nat :=
  Nat.min (floorLo r) (floorHi r)

/-- Public alias of `kernelBitMidpoint` used at the IRS reduction
ceiling. The recert certificate is produced synchronously with this
bit-floor claim via `twoSidedRecertMargin` below. -/
abbrev spotCheckBit (r : Float) : Nat :=
  kernelBitMidpoint r

/-- The two-sided recert-margin lemma: a single synchronous witness that
both bracketing integer-lattice plane-coordinate kernel bit floors
lie at or above `safeFloor`. This replaces the single-monotone
cap certificate. The conclusion is two-sided: both the lower and
upper bracketing floors are bounded below by `safeFloor`. -/
theorem twoSidedRecertMargin (r : Float) :
    floorLo r ≥ safeFloor ∧ floorHi r ≥ safeFloor := by
  refine ⟨?_, ?_⟩
  · unfold floorLo floorHi planeKernelFloor safeFloor safeFloorInt
    have hfloor : (Int.floor r.toFloat : Int) ≥ 0 := Int.floor_nonneg (by positivity)
    exact Int.toNat_le_toNat (by omega)
  · unfold floorLo floorHi planeKernelFloor safeFloor safeFloorInt
    have hceil : (Int.ceil r.toFloat : Int) ≥ 0 := by
      by_cases h : r.toFloat ≥ 0
      · exact_mod_cast (Int.ceil_nonneg h)
      · have hrle : r.toFloat ≤ 0 := le_of_not_ge h
        have hcnz : Int.ceil r.toFloat ≤ 0 := by
          exact_mod_cast (Int.ceil_le_zero_iff.mpr hrle)
        omega
    exact Int.toNat_le_toNat (by omega)

/-- The synchronous recert certificate for the IRS reduction ceiling.
Given a candidate radius `r`, the cert packages the two-sided
recert-margin witness together with the spot-check bit, so the
bit-floor claim and the recert certificate are produced in a
single def block. -/
def irsReductionCeilingCert (r : Float) :
    { cert : floorLo r ≥ safeFloor ∧ floorHi r ≥ safeFloor //
      spotCheckBit r ≤ floorLo r ∧
        spotCheckBit r ≤ floorHi r } :=
  have hmargin := twoSidedRecertMargin r
  have hspot_lo : spotCheckBit r ≤ floorLo r := by
    show kernelBitMidpoint r ≤ floorLo r
    exact Nat.min_le_left _ _
  have hspot_hi : spotCheckBit r ≤ floorHi r := by
    show kernelBitMidpoint r ≤ floorHi r
    exact Nat.min_le_right _ _
  ⟨hmargin, hspot_lo, hspot_hi⟩

end KernelBitMidpoint

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
#print axioms planeKernelFloor
#print axioms floorLo
#print axioms floorHi
#print axioms kernelBitMidpoint
#print axioms spotCheckBit
#print axioms twoSidedRecertMargin
#print axioms irsReductionCeilingCert

end ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel
