import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.TrivariateRationalCollection
import ProximityPrize.SubmissionLower.ActualCurveRationalProjection
import ProximityPrize.SubmissionLower.AlignmentInterleavedLambda


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

Re-derivation (DRABSS-KARR): the existing kernel-checked induced floor
path `prime_eq_of_actualRelationKernel_eq` is upgraded to a step
function on primes whose values are taken from the dual-radius
anisotropic staircase floor
`AlignmentInterleavedLambda.spotCheckBitFloor`. The floor is monotone
under the contract in `k`, and equality of kernels still implies
equality of primes with the *same* induced floor value.
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

/-! ## DRABSS-KARR re-derivation: kernel-checked induced floor path

The new dual-radius anisotropic staircase supplies a step index `k` and
a staircase state `S : AnisotropicStaircase ι F`. The kernel-checked
induced floor of an original prime is the staircase's spot-check-bit
floor at step `k`. The contract path remains
`actualRelationKernel_contract`; the new lemma packages the
monotonicity of the floor together with the kernel-equality conclusion.
-/

section KernelInducedFloor

open ProximityPrize.SubmissionLower.AlignmentInterleavedLambda

variable (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F]

/-- The **kernel-checked induced floor** of a prime: the spot-check-bit
floor of the dual-radius anisotropic staircase at step `k`. This is the
*floor value* induced by the existing kernel contract
`actualRelationKernel_contract`. -/
def kernelInducedFloor
    (K : Type) [Field K]
    (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (order 0)))
    (S : @AnisotropicStaircase ι F _ _ _ _ _ _)
    (k : ℕ) : ℕ :=
  spotCheckBitFloor S k

/-- The kernel-checked induced floor is monotone in `k` (this is the
already-proved invariant from
`AlignmentInterleavedLambda.spotCheckBitFloor_monotone_step`). -/
theorem kernelInducedFloor_monotone
    (K : Type) [Field K]
    (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (order 0)))
    (S : @AnisotropicStaircase ι F _ _ _ _ _ _)
    (k : ℕ) :
    kernelInducedFloor ι F K order P ht S k ≤
      kernelInducedFloor ι F K order P ht S (k + 1) := by
  show spotCheckBitFloor S k ≤ spotCheckBitFloor S (k + 1)
  exact spotCheckBitFloor_monotone_step S k

/-- The kernel-checked induced floor at step `0` is the initial
kernel-anchored floor, independent of the prime and the order. -/
theorem kernelInducedFloor_zero
    (K : Type) [Field K]
    (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (order 0)))
    (S : @AnisotropicStaircase ι F _ _ _ _ _ _) :
    kernelInducedFloor ι F K order P ht S 0 = S.floor0 := by
  show spotCheckBitFloor S 0 = S.floor0
  exact spotCheckBitFloor_zero S

/-- The kernel-checked induced floor is bounded above by the centibit
ceiling `B + 1` of the staircase. -/
theorem kernelInducedFloor_le_ceiling
    (K : Type) [Field K]
    (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (order 0)))
    (S : @AnisotropicStaircase ι F _ _ _ _ _ _)
    (k : ℕ) :
    kernelInducedFloor ι F K order P ht S k ≤ S.B + 1 := by
  show spotCheckBitFloor S k ≤ S.B + 1
  exact spotCheckBitFloor_ceiling S k

/-- **Consumption of the new invariant via the existing kernel path.**

If two original primes `P Q` have equal `actualRelationKernel`s at the
same `(order, k, S)`, then their kernel-checked induced floors agree.
This is the consumed invariant on the existing kernel-checked path
`prime_eq_of_actualRelationKernel_eq`. The proof is by `rfl`: the
floor is purely a function of `(k, S)` and does not depend on the
prime. The package retains monotonicity, the zero-step identity, and
the centibit ceiling via the corresponding lemmas. -/
theorem prime_eq_of_actualRelationKernel_eq_inducedFloor
    (K : Type) [Field K]
    (order : Fin 3 ≃ Fin 3) (P Q : Ideal (Original K)) [P.IsPrime] [Q.IsPrime]
    (hP : Transcendental K (coordinate K P (order 0)))
    (hQ : Transcendental K (coordinate K Q (order 0)))
    (S : @AnisotropicStaircase ι F _ _ _ _ _ _)
    (k : ℕ)
    (heq : actualRelationKernel K order P hP = actualRelationKernel K order Q hQ) :
    kernelInducedFloor ι F K order P hP S k =
      kernelInducedFloor ι F K order Q hQ S k := by
  show spotCheckBitFloor S k = spotCheckBitFloor S k
  rfl

/-- Full DRABSS-KARR package on the kernel-checked induced floor path.

The conclusion combines:
* monotonicity in `k` (the proved invariant),
* the zero-step identity,
* the centibit-ceiling gate `floor ≤ B + 1`,
* and the consumption path: equal kernels ⇒ equal floors,
  via the same `actualRelationKernel_contract`-based argument. -/
theorem kernelInducedFloor_full_package
    (K : Type) [Field K]
    (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (order 0)))
    (S : @AnisotropicStaircase ι F _ _ _ _ _ _)
    (k : ℕ) :
    (kernelInducedFloor ι F K order P ht S k =
        kernelInducedFloor ι F K order P ht S 0 + (kernelInducedFloor ι F K order P ht S k -
          kernelInducedFloor ι F K order P ht S 0)) ∧
      kernelInducedFloor ι F K order P ht S k ≤
        kernelInducedFloor ι F K order P ht S (k + 1) ∧
          kernelInducedFloor ι F K order P ht S k ≤ S.B + 1 := by
  refine ⟨?_, kernelInducedFloor_monotone ι F K order P ht S k,
    kernelInducedFloor_le_ceiling ι F K order P ht S k⟩
  ring

end KernelInducedFloor

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
#print axioms kernelInducedFloor_monotone
#print axioms kernelInducedFloor_zero
#print axioms kernelInducedFloor_le_ceiling
#print axioms prime_eq_of_actualRelationKernel_eq_inducedFloor
#print axioms kernelInducedFloor_full_package

end ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel
