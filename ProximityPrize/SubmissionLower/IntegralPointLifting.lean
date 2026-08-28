import ProximityPrize.Benchmark.TargetLower





/-!
# Actual point lifting through an integral embedding

Model label: gpt-5.

For compatible commutative K-algebras A -> S, with an injective integral
base map and K algebraically closed, every actual K-valued point of A is
lifted to an actual K-valued point of S. No lifting hypothesis or finite
geometric cardinality bound is assumed.

The construction chooses a maximal ideal over the actual point kernel.
Its quotient is proved integral over K by transporting the original monic
relations through a coefficient-compatible quotient map. Algebraic
closedness then makes the actual scalar map K -> S/N bijective.

The final corollary derives integrality over an intermediate model A from
integrality over a smaller ring R. In the normalization application R can
be K[T], so S need not be assumed normal merely because A is a model.
This file does not construct all curve places or a global point count.
-/

namespace ProximityPrize.SubmissionLower.IntegralPointLifting

noncomputable section

variable {K A S : Type*} [Field K] [CommRing A] [CommRing S]
  [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]

/-- A point is surjective on constants, hence its actual kernel is maximal. -/
theorem pointKernel_isMaximal (phi : A →ₐ[K] K) :
    (RingHom.ker phi.toRingHom).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective phi.toRingHom
  intro c
  exact ⟨algebraMap K A c, by simp⟩

/-- The actual quotient map over a point kernel has the required coefficient
compatibility; it is proved from membership, not supplied as a square. -/
theorem quotient_scalar_compatibility (phi : A →ₐ[K] K) (N : Ideal S)
    (hN : N.comap (algebraMap A S) = RingHom.ker phi.toRingHom) (a : A) :
    Ideal.Quotient.mkₐ K N (algebraMap A S a) =
      algebraMap K (S ⧸ N) (phi a) := by
  have ha : a - algebraMap K A (phi a) ∈ RingHom.ker phi.toRingHom := by
    change phi (a - algebraMap K A (phi a)) = 0
    simp
  have hamem : algebraMap A S (a - algebraMap K A (phi a)) ∈ N := by
    change a - algebraMap K A (phi a) ∈ N.comap (algebraMap A S)
    rw [hN]
    exact ha
  have hz : Ideal.Quotient.mkₐ K N
      (algebraMap A S (a - algebraMap K A (phi a))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hamem
  have hconstant (c : K) :
      algebraMap A S (algebraMap K A c) = algebraMap K S c :=
    (IsScalarTower.algebraMap_apply K A S c).symm
  apply sub_eq_zero.mp
  simpa [map_sub, hconstant] using hz

section IntegralLift

variable [IsAlgClosed K] [Algebra.IsIntegral A S]

/-- Every actual K-point lifts through an actual integral embedding. -/
theorem exists_point_lift
    (hinj : Function.Injective (algebraMap A S)) (phi : A →ₐ[K] K) :
    ∃ psi : S →ₐ[K] K, psi.comp (IsScalarTower.toAlgHom K A S) = phi := by
  classical
  letI : (RingHom.ker phi.toRingHom).IsMaximal := pointKernel_isMaximal phi
  have hker : RingHom.ker (algebraMap A S) ≤ RingHom.ker phi.toRingHom := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨N, hNmax, hN⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := S) (RingHom.ker phi.toRingHom) hker
  letI : N.IsMaximal := hNmax
  let q : S →ₐ[K] S ⧸ N := Ideal.Quotient.mkₐ K N
  have hcomp : (algebraMap K (S ⧸ N)).comp phi.toRingHom =
      (Ideal.Quotient.mk N).comp (algebraMap A S) := by
    ext a
    exact (quotient_scalar_compatibility phi N hN a).symm
  letI : Algebra.IsIntegral K (S ⧸ N) := by
    constructor
    intro z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact IsIntegral.map_of_comp_eq phi.toRingHom (Ideal.Quotient.mk N) hcomp
      (Algebra.IsIntegral.isIntegral (R := A) s)
  let e : K ≃ₐ[K] S ⧸ N := AlgEquiv.ofBijective (Algebra.ofId K (S ⧸ N))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := S ⧸ N))
  let psi : S →ₐ[K] K := e.symm.toAlgHom.comp q
  refine ⟨psi, ?_⟩
  ext a
  change psi (algebraMap A S a) = phi a
  apply e.injective
  change e (e.symm (q (algebraMap A S a))) = e (phi a)
  rw [e.apply_symm_apply]
  have he (c : K) : e c = algebraMap K (S ⧸ N) c := by
    simpa using e.commutes c
  rw [he]
  exact quotient_scalar_compatibility phi N hN a

/-- A chosen lift is derived from the preceding existence theorem. -/
def chosenPointLift (hinj : Function.Injective (algebraMap A S))
    (phi : A →ₐ[K] K) : S →ₐ[K] K :=
  Classical.choose (exists_point_lift hinj phi)

theorem chosenPointLift_spec (hinj : Function.Injective (algebraMap A S))
    (phi : A →ₐ[K] K) :
    (chosenPointLift hinj phi).comp (IsScalarTower.toAlgHom K A S) = phi :=
  Classical.choose_spec (exists_point_lift hinj phi)

/-- Distinct original points remain distinct under the actual selected lifts. -/
theorem chosenPointLift_injective (hinj : Function.Injective (algebraMap A S)) :
    Function.Injective (chosenPointLift hinj : (A →ₐ[K] K) → (S →ₐ[K] K)) := by
  intro phi theta h
  have hrestrict := congrArg
    (fun psi : S →ₐ[K] K => psi.comp (IsScalarTower.toAlgHom K A S)) h
  simpa only [chosenPointLift_spec] using hrestrict

end IntegralLift

section IntegralBase

variable [IsAlgClosed K] (R : Type*) [CommRing R]
  [Algebra R A] [Algebra R S] [IsScalarTower R A S] [Algebra.IsIntegral R S]

include R in
/-- An intermediate model does not require integrality to be assumed again:
integrality of S over the smaller base R gives the point lift over A. -/
theorem exists_point_lift_of_integral_base
    (hinj : Function.Injective (algebraMap A S)) (phi : A →ₐ[K] K) :
    ∃ psi : S →ₐ[K] K, psi.comp (IsScalarTower.toAlgHom K A S) = phi := by
  letI : Algebra.IsIntegral A S := Algebra.IsIntegral.tower_top R
  exact exists_point_lift hinj phi

end IntegralBase

end


end ProximityPrize.SubmissionLower.IntegralPointLifting
